module Distribution.Client.Dependency.Modular.Explore
    ( backjump
    , backjumpAndExplore
    ) where

import Data.Foldable as F
import Data.Map as M

import Distribution.Client.Dependency.Modular.Assignment
import Distribution.Client.Dependency.Modular.Dependency
import Distribution.Client.Dependency.Modular.Log
import Distribution.Client.Dependency.Modular.Message
import Distribution.Client.Dependency.Modular.Package
import qualified Distribution.Client.Dependency.Modular.PSQ as P
import qualified Distribution.Client.Dependency.Modular.ConflictSet as CS
import Distribution.Client.Dependency.Modular.Tree
import qualified Distribution.Client.Dependency.Types as T

-- | This function takes the variable we're currently considering, an
-- initial conflict set and a
-- list of children's logs. Each log yields either a solution or a
-- conflict set. The result is a combined log for the parent node that
-- has explored a prefix of the children.
--
-- We can stop traversing the children's logs if we find an individual
-- conflict set that does not contain the current variable. In this
-- case, we can just lift the conflict set to the current level,
-- because the current level cannot possibly have contributed to this
-- conflict, so no other choice at the current level would avoid the
-- conflict.
--
-- If any of the children might contain a successful solution, we can
-- return it immediately. If all children contain conflict sets, we can
-- take the union as the combined conflict set.
--
-- The initial conflict set corresponds to the justification that we
-- have to choose this goal at all. There is a reason why we have
-- introduced the goal in the first place, and this reason is in conflict
-- with the (virtual) option not to choose anything for the current
-- variable. See also the comments for 'avoidSet'.
--
backjump :: T.EnableBackjumping -> Var QPN
         -> ConflictSet QPN -> ConflictMap -> P.PSQ k (ConflictMap -> (ConflictSetLog a, ConflictMap))
         -> (ConflictSetLog a, ConflictMap)
backjump (T.EnableBackjumping enableBj) var initial cm xs =
    F.foldr combine logBackjump xs initial cm
  where
    combine :: (ConflictMap -> (ConflictSetLog a, ConflictMap))
            -> (ConflictSet QPN -> ConflictMap -> (ConflictSetLog a, ConflictMap))
            ->  ConflictSet QPN -> ConflictMap -> (ConflictSetLog a, ConflictMap)
    combine x f csAcc cm =
      let (l, cm') = x cm
      in case l of
           T.Done x  -> (T.Done x, cm')
           T.Fail cs
             | enableBj && not (var `CS.member` cs) -> logBackjump cs cm'
             | otherwise                            -> f (csAcc `CS.union` cs) cm'
           T.Step m ms ->
             let (l', cm'') = combine (\ x -> (ms, x)) f csAcc cm'
             in  (T.Step m l', cm'')
{-
    combine (T.Fail cs)   f csAcc
      | enableBj && not (var `CS.member` cs) = logBackjump cs
      | otherwise                = f (csAcc `CS.union` cs)
    combine (T.Step m ms) f cs   = T.Step m (combine ms f cs)
-}

    logBackjump :: ConflictSet QPN -> ConflictMap -> (ConflictSetLog a, ConflictMap)
    logBackjump cs cm' = (failWith (Failure cs Backjump) cs, cm')

type ConflictSetLog = T.Progress Message (ConflictSet QPN)

type ConflictMap = Map (Var QPN) Int

getBestGoal :: ConflictMap -> P.PSQ (OpenGoal ()) a -> (OpenGoal (), a)
getBestGoal cm =
  P.maximumBy
    ( flip (M.findWithDefault 0) cm
    . (\ (Goal v _) -> v)
    . close
    )

-- | A tree traversal that simultaneously propagates conflict sets up
-- the tree from the leaves and creates a log.
exploreLog :: T.EnableBackjumping -> Tree QGoalReason
           -> (Assignment -> ConflictMap -> (ConflictSetLog (Assignment, RevDepMap), ConflictMap))
exploreLog enableBj = cata go
  where
    go :: TreeF QGoalReason (Assignment -> ConflictMap -> (ConflictSetLog (Assignment, RevDepMap), ConflictMap))
                         -> (Assignment -> ConflictMap -> (ConflictSetLog (Assignment, RevDepMap), ConflictMap))
    go (FailF c fr)          _  cm       = (failWith (Failure c fr) c, cm)
    go (DoneF rdm)           a  cm       = (succeedWith Success (a, rdm), cm)
    go (PChoiceF qpn gr     ts) (A pa fa sa) cm  =
      backjump enableBj (P qpn) (avoidSet (P qpn) gr) cm $ -- try children in order,
      P.mapWithKey                                -- when descending ...
        (\ i@(POption k _) r cm ->
          let (l, cm') = r (A (M.insert qpn k pa) fa sa) cm
          in  (tryWith (TryP qpn i) l, cm')
        )
      ts
    go (FChoiceF qfn gr _ _ ts) (A pa fa sa) cm  =
      backjump enableBj (F qfn) (avoidSet (F qfn) gr) cm $ -- try children in order,
      P.mapWithKey                                -- when descending ...
        (\ k r cm ->
          let (l, cm') = r (A pa (M.insert qfn k fa) sa) cm
          in  (tryWith (TryF qfn k) l, cm')
        )
      ts
    go (SChoiceF qsn gr _   ts) (A pa fa sa) cm  =
      backjump enableBj (S qsn) (avoidSet (S qsn) gr) cm $ -- try children in order,
      P.mapWithKey                                -- when descending ...
        (\ k r cm ->
          let (l, cm') = r (A pa fa (M.insert qsn k sa)) cm
          in  (tryWith (TryS qsn k) l, cm')
        )
      ts
    go (GoalChoiceF        ts) a cm          =
      let (k, v) = getBestGoal cm ts
          (l, cm') = v a cm
      in (continueWith (Next (close k)) l, cm')

-- | Build a conflict set corresponding to the (virtual) option not to
-- choose a solution for a goal at all.
--
-- In the solver, the set of goals is not statically determined, but depends
-- on the choices we make. Therefore, when dealing with conflict sets, we
-- always have to consider that we could perhaps make choices that would
-- avoid the existence of the goal completely.
--
-- Whenever we actual introduce a choice in the tree, we have already established
-- that the goal cannot be avoided. This is tracked in the "goal reason".
-- The choice to avoid the goal therefore is a conflict between the goal itself
-- and its goal reason. We build this set here, and pass it to the 'backjump'
-- function as the initial conflict set.
--
-- This has two effects:
--
-- - In a situation where there are no choices available at all (this happens
-- if an unknown package is requested), the initial conflict set becomes the
-- actual conflict set.
--
-- - In a situation where we backjump past the current node, the goal reason
-- of the current node will be added to the conflict set.
--
avoidSet :: Var QPN -> QGoalReason -> ConflictSet QPN
avoidSet var gr =
  CS.fromList (var : goalReasonToVars gr)

-- | Interface.
backjumpAndExplore :: T.EnableBackjumping
                   -> Tree QGoalReason -> Log Message (Assignment, RevDepMap)
backjumpAndExplore enableBj t =
    toLog $ fst $ exploreLog enableBj t (A M.empty M.empty M.empty) M.empty
  where
    toLog :: T.Progress step fail done -> Log step done
    toLog = T.foldProgress T.Step (const (T.Fail ())) T.Done
