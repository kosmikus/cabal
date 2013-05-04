module Distribution.Client.Dependency.Modular.Builder where

-- Building the search tree.
--
-- In this phase, we build a search tree that is too large, i.e, it contains
-- invalid solutions. We keep track of the open goals at each point. We
-- nondeterministically pick an open goal (via a goal choice node), create
-- subtrees according to the index and the available solutions, and extend the
-- set of open goals by superficially looking at the dependencies recorded in
-- the index.
--
-- For each goal, we keep track of all the *reasons* why it is being
-- introduced. These are for debugging and error messages, mainly. A little bit
-- of care has to be taken due to the way we treat flags. If a package has
-- flag-guarded dependencies, we cannot introduce them immediately. Instead, we
-- store the entire dependency.

import Control.Monad.Reader hiding (sequence, mapM)
import Data.List as L
import Data.Map as M
import Prelude hiding (sequence, mapM)
import Debug.Trace

import Distribution.Client.Dependency.Modular.Dependency
import Distribution.Client.Dependency.Modular.Flag
import Distribution.Client.Dependency.Modular.Index
import Distribution.Client.Dependency.Modular.Package
import Distribution.Client.Dependency.Modular.PSQ as P
import Distribution.Client.Dependency.Modular.Tree
import Distribution.Client.Dependency.Modular.Version

-- | The state needed during the build phase of the search tree.
data BuildState = BS {
  index  :: Index,           -- ^ information about packages and their dependencies
  irdeps :: InstRevDeps,     -- ^ information about reverse dependencies of installed packages
  scope  :: Scope,           -- ^ information about encapsulations
  rdeps  :: RevDepMap,       -- ^ set of all package goals, completed and open, with reverse dependencies
  open   :: PSQ OpenGoal (), -- ^ set of still open goals (flag and package goals)
  next   :: BuildType        -- ^ kind of node to generate next
}

-- | Extend the set of open goals with the new goals listed.
--
-- We also adjust the map of overall goals, and keep track of the
-- reverse dependencies of each of the goals.
extendOpen :: QPN -> [OpenGoal] -> BuildState -> BuildState
extendOpen qpn' gs s@(BS { rdeps = gs', open = o' }) = go gs' o' gs
  where
    go :: RevDepMap -> PSQ OpenGoal () -> [OpenGoal] -> BuildState
    go g o []                                             = s { rdeps = g, open = o }
    go g o (ng@(OpenGoal (Flagged _ _ _ _)    _gr) : ngs) = go g (cons ng () o) ngs
    go g o (ng@(OpenGoal (Stanza  _   _  )    _gr) : ngs) = go g (cons ng () o) ngs
    go g o (ng@(OpenGoal (Simple (Dep qpn _)) _gr) : ngs)
      | qpn == qpn'                                       = go                       g              o  ngs
                                       -- we ignore self-dependencies at this point; TODO: more care may be needed
      | qpn `M.member` g                                  = go (M.adjust (qpn':) qpn g)             o  ngs
      | otherwise                                         = go (M.insert qpn [qpn']  g) (cons ng () o) ngs
                                       -- code above is correct; insert/adjust have different arg order

-- | Variant of extendOpen for reverse dependencies.
--
-- TODO: Should be unified with 'extendOpen'. The difference is in
-- the way we update the reverse dependency map (oh, the irony). We
-- really only need to update the goal set here. The dependencies of
-- the new goal will take care of the ordering constraints.
extendOpen' :: QPN -> [OpenGoal] -> BuildState -> BuildState
extendOpen' qpn' gs s@(BS { rdeps = gs', open = o' }) = go gs' o' gs
  where
    go :: RevDepMap -> PSQ OpenGoal () -> [OpenGoal] -> BuildState
    go g o []                                             = s { rdeps = g, open = o }
    go g o (ng@(OpenGoal (Simple (Dep qpn _)) _gr) : ngs)
      | qpn == qpn'                                       = go                      g              o  ngs
                                       -- we ignore self-dependencies at this point; TODO: more care may be needed
      | qpn `M.member` g                                  = go                      g              o  ngs
      | otherwise                                         = go (M.insert qpn [] g) (cons ng () o) ngs
                                       -- code above is correct; insert/adjust have different arg order
    go g o (_ng                                    : ngs) = go g o ngs -- should not happen, we only add simple goals for revdeps

-- | Update the current scope by taking into account the encapsulations that
-- are defined for the current package.
establishScope :: QPN -> Encaps -> BuildState -> BuildState
establishScope (Q pp pn) ecs s =
    s { scope = L.foldl (\ m e -> M.insert e pp' m) (scope s) ecs }
  where
    pp' = pn : pp -- new path

-- | Given the current scope, qualify all the package names in the given set of
-- dependencies and then extend the set of open goals accordingly.
scopedExtendOpen :: QPN -> I -> PI QPN -> QGoalReasonChain -> FlaggedDeps PN -> FlagInfo -> [PI PN] ->
                    BuildState -> BuildState
scopedExtendOpen qpn i grqpi gr fdeps fdefs rdeps s = trace (show qrdeps) (extendOpen' qpn rgs (extendOpen qpn gs s))
  where
    sc     = scope s
    qfdeps = L.map (fmap (qualify sc)) fdeps -- qualify all the package names
    qfdefs = L.map (\ (fn, b) -> Flagged (FN (PI qpn i) fn) b [] []) $ M.toList fdefs
    qrdeps = L.map (\ (PI pn _) -> Dep (qualify sc pn) (Constrained [])) rdeps
    rgs    = L.map (flip OpenGoal (RDependency grqpi : gr) . Simple)  qrdeps
    gs     = L.map (flip OpenGoal (PDependency grqpi : gr)         ) (qfdeps ++ qfdefs)

data BuildType = Goals | OneGoal OpenGoal | Instance QPN I PInfo QGoalReasonChain (Map Ver [PI PN])

build :: BuildState -> Tree (QGoalReasonChain, Scope)
build = ana go
  where
    go :: BuildState -> TreeF (QGoalReasonChain, Scope) BuildState

    -- If we have a choice between many goals, we just record the choice in
    -- the tree. We select each open goal in turn, and before we descend, remove
    -- it from the queue of open goals.
    go bs@(BS { rdeps = rds, open = gs, next = Goals })
      | P.null gs = DoneF rds
      | otherwise = GoalChoiceF (P.mapWithKey (\ g (_sc, gs') -> bs { next = OneGoal g, open = gs' })
                                              (P.splits gs))

    -- If we have already picked a goal, then the choice depends on the kind
    -- of goal.
    --
    -- For a package, we look up the instances available in the global info,
    -- and then handle each instance in turn.
    go bs@(BS { index = idx, scope = sc, next = OneGoal (OpenGoal (Simple (Dep qpn@(Q _ pn) _)) gr), irdeps = ird }) =
      case M.lookup pn idx of
        Nothing  -> FailF (toConflictSet (Goal (P qpn) gr)) (BuildFailureNotInIndex pn)
        Just pis -> PChoiceF qpn (gr, sc) (P.fromList cs)
            -- TODO: data structure conversion is rather ugly here
          where
            pis'      = M.toList pis
            cs        = L.map (\ (i, info) -> (i, bs { next = Instance qpn i info gr installed })) pis'
            -- We also compute info about installed package ids, so that we can discover reinstalls.
            installed = M.fromList [ (v, rd) | (I v (Inst ipid), _) <- pis', let rd = ird [ipid] ]

    -- For a flag, we create only two subtrees, and we create them in the order
    -- that is indicated by the flag default.
    --
    -- TODO: Should we include the flag default in the tree?
    go bs@(BS { scope = sc, next = OneGoal (OpenGoal (Flagged qfn@(FN (PI qpn _) _) (FInfo b m) t f) gr) }) =
      FChoiceF qfn (gr, sc) trivial m (P.fromList (reorder b
        [(True,  (extendOpen qpn (L.map (flip OpenGoal (FDependency qfn True  : gr)) t) bs) { next = Goals }),
         (False, (extendOpen qpn (L.map (flip OpenGoal (FDependency qfn False : gr)) f) bs) { next = Goals })]))
      where
        reorder True  = id
        reorder False = reverse
        trivial = L.null t && L.null f

    go bs@(BS { scope = sc, next = OneGoal (OpenGoal (Stanza qsn@(SN (PI qpn _) _) t) gr) }) =
      SChoiceF qsn (gr, sc) trivial (P.fromList
        [(False,                                                                        bs  { next = Goals }),
         (True,  (extendOpen qpn (L.map (flip OpenGoal (SDependency qsn : gr)) t) bs) { next = Goals })])
      where
        trivial = L.null t

    -- For a particular instance, we change the state: we update the scope,
    -- and furthermore we update the set of goals.
    --
    -- TODO: We could inline this above.
    go bs@(BS { next = Instance qpn i (PInfo fdeps fdefs ecs _) gr iRevDeps }) =
      go ((establishScope qpn ecs
             (scopedExtendOpen qpn i (PI qpn i) gr fdeps fdefs (revdeps i) bs))
             { next = Goals })
      where
        revdeps (I v InRepo) = let r = M.findWithDefault [] v iRevDeps in trace (show (i, iRevDeps, r)) r
        revdeps _            = []

-- | Interface to the tree builder. Just takes an index and a list of package names,
-- and computes the initial state and then the tree from there.
buildTree :: Index -> InstRevDeps -> Bool -> [PN] -> Tree (QGoalReasonChain, Scope)
buildTree idx iRevDeps ind igs =
    build (BS idx iRevDeps sc
                  (M.fromList (L.map (\ qpn -> (qpn, []))                                                     qpns))
                  (P.fromList (L.map (\ qpn -> (OpenGoal (Simple (Dep qpn (Constrained []))) [UserGoal], ())) qpns))
                  Goals)
  where
    sc | ind       = makeIndependent igs
       | otherwise = emptyScope
    qpns           = L.map (qualify sc) igs
