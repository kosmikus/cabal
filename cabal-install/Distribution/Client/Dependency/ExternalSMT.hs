{-# LANGUAGE GADTs, KindSignatures, StandaloneDeriving #-}
module Distribution.Client.Dependency.ExternalSMT where

import Control.Monad.State

import Distribution.Client.ComponentDeps as CD
import Distribution.Client.Dependency.Modular.Solver
  ( SolverConfig(..) )
import Distribution.Client.Dependency.Types
import Distribution.System
  ( Platform(..) )
import Distribution.Client.InstallPlan hiding (Installed)
import Distribution.Client.Types as CT
import Distribution.PackageDescription as PD
import qualified Distribution.Simple.PackageIndex as SI
import Distribution.InstalledPackageInfo as IPI
import Distribution.Package hiding (installedPackageId)
import Distribution.Client.PackageIndex as CI
import Distribution.Compiler
  ( CompilerInfo(..),
    CompilerId(..) )
import Distribution.Version
import Distribution.Text

import Data.List as L
import Data.Map as M hiding (assocs)
import Data.Set as S
import Data.Maybe

import qualified SimpleSMT as SMT

-- import Debug.Trace (trace)

import Prelude hiding (pi)

type Index a = Map PackageName a
type SVersion = Integer

(!@) :: (Ord a, Show a) => Map a b -> a -> b
m !@ k = case M.lookup k m of
  Nothing -> error $ "!@: " ++ show k ++ " not found"
  Just v  -> v

findPackage :: Index PackageInfo -> PackageName -> PackageInfo
findPackage idx pn = case M.lookup pn idx of
  Nothing -> unknownPackageInfo
  Just pi -> pi

-- We use the following convention for solver versions:
--
-- negative numbers correspond to installed instances
-- positive numbers correspond to source instances
-- 0 corresponds to not installing the package
--
data PackageInfo = PackageInfo
  { piAssocs :: [(Version, SVersion)]
  , piFrom   :: Map InstalledPackageId SVersion
  , piTo     :: Map SVersion InstanceInfo
  , piFlags  :: Set FlagName  -- automatic flags only
  } deriving Show

unknownPackageInfo :: PackageInfo
unknownPackageInfo = PackageInfo [] M.empty M.empty S.empty

data Instance = Instance { instVersion :: Version, instLocation :: Location }
  deriving Show

data Location = Source | Installed InstalledPackageId
  deriving Show

data PackageInstance = PackageInstance PackageName Instance
  deriving Show

showInstance :: Instance -> String
showInstance (Instance ver Source)                                = display ver
showInstance (Instance ver (Installed (InstalledPackageId ipid))) = display ver ++ "/installed" ++ shortId ipid
  where
    -- A hack to extract the beginning of the package ABI hash
    shortId = snip (splitAt 4) (++ "...") .
              snip ((\ (x, y) -> (reverse x, y)) . break (=='-') . reverse) ('-':)
    snip p f xs = case p xs of
                    (ys, zs) -> (if L.null zs then id else f) ys

data InstanceInfo = InstanceInfo { iiInstance :: Instance, iiDeps :: SDepsFree }
  deriving Show

data GlobalFlag = GlobalFlag PackageName FlagName
  deriving (Show, Eq, Ord)

data SolvedPackage = SolvedPackage
  { spkgInstance :: PackageInstance
  , spkgFlags    :: FlagAssignment
  , spkgStanzas  :: [OptionalStanza]
  , spkgDeps     :: ComponentDeps [PackageInstance]
  }

data Vars = Vars
  { vSolver :: SMT.Solver
  , vPkgs   :: Map PackageName SMT.SExpr
  , vFlags  :: Map GlobalFlag SMT.SExpr
  }

sPkg :: PackageName -> StateT Vars IO SMT.SExpr
sPkg pn = do
  vs <- gets vPkgs
  case M.lookup pn vs of
    Just v  -> return v
    Nothing -> do
      slv <- gets vSolver
      v <- lift $ SMT.declare slv (pkgVarName pn) SMT.tInt
      modify (\ s -> s { vPkgs = M.insert pn v vs })
      return v

sFlag :: GlobalFlag -> StateT Vars IO SMT.SExpr
sFlag gf = do
  vs <- gets vFlags
  case M.lookup gf vs of
    Just v  -> return v
    Nothing -> do
      slv <- gets vSolver
      v <- lift $ SMT.declare slv (flagVarName gf) SMT.tBool
      modify (\ s -> s { vFlags = M.insert gf v vs })
      return v

pkgVarName :: PackageName -> String
pkgVarName (PackageName pn) = "pkg/" ++ pn

flagVarName :: GlobalFlag -> String
flagVarName (GlobalFlag (PackageName pn) (FlagName fn)) = "flag/" ++ pn ++ "/" ++ fn

externalSMTResolver :: SolverConfig -> DependencyResolver
externalSMTResolver _sc platform cinfo iidx sidx _pprefs pcs pns =
  let gfa  = mkGlobalFlagAssignment pcs
      idx  = processIndexes platform cinfo gfa iidx sidx
      clo  = closure idx pns
      pcs' = packageConstraints idx pcs
      pns' = targets pns
      tclo = translate $ sAnd' [clo, pcs', pns']
  in  do
        putStrLn "Collecting constraints ..."
        slv <- SMT.newSolver "z3" ["-smt2", "-nw", "-in"] Nothing
        (sexpr, fs) <- runStateT tclo (Vars slv M.empty M.empty)
        putStrLn "Transferring to z3 ..."
        SMT.assert slv sexpr
        putStrLn "Solving ..."
        r <- SMT.check slv
        case r of
          SMT.Sat -> do
            -- Let's try to translate back the results
            results <- SMT.getConsts slv $  L.map pkgVarName  (M.keys (vPkgs  fs))
                                         ++ L.map flagVarName (M.keys (vFlags fs))
            putStr $ unlines [ var ++ ": " ++ show b
                             | (var, SMT.Bool b) <- results
                             ]
            putStr $ unlines [ var ++ ": " ++ showInstance (iiInstance ii)
                             | (var, SMT.Int ver) <- results
                             , ver /= 0
                             , let pi = idx M.! PackageName (drop 4 var) -- TODO: oh no!
                             , let ii = piTo pi M.! ver
                             ]
          _   -> print r
        error "unimplemented"

-- | Translates a list of target package names into a solver condition.
--
-- The targets are required to be installed, so we require that the package
-- variables for each of these are not 0.
targets :: [PackageName] -> SDeps Bool
targets = sAnd' . L.map (\ pn -> SNot (SEq (SPkg pn) (SVer 0)))

-- | Translates package constraints into a solver condition.
--
-- The following happens:
--
--    * For version constraints, we generate a corresponding dependency
--      constraint. However, version constraints are considered to be optional;
--      i.e., only if the package is actually selected for installation, the
--      specified version range applies. This means that we also allow the
--      package variable to be set to 0.
--
--    * For installed constraints, we require that the corresponding package
--      variable is at least 0.
--
--    * For source constraints, we require that the corresponding package
--      variable is at most 0.
--
--    * Flags are not handled here. If flags are specified explicitly, no
--      solver variable will be generated for them anymore, so there is no
--      resulting condition. Instead, we use 'mkGlobalFlagAssignment'.
--
-- TODO: Stanza constraints are not yet handled.
--
packageConstraints :: Index PackageInfo -> [PackageConstraint] -> SDeps Bool
packageConstraints idx = sAnd' . L.map go
  where
    go :: PackageConstraint -> SDeps Bool
    go (PackageConstraintVersion pn vr) = SOr (SEq (SPkg pn) (SVer 0)) (packageDependency idx (Dependency pn vr))
    go (PackageConstraintInstalled pn)  = SLe (SPkg pn) (SVer 0)
    go (PackageConstraintSource pn)     = SGe (SPkg pn) (SVer 0)
    go (PackageConstraintFlags _pn _fa) = SBool True
    go (PackageConstraintStanzas _ _)   = SBool True

-- TODO: One thing to keep in mind: if we just treat flag constraints as creating
-- a global assignment, we won't catch conflicting flag constraints as errors, but
-- rather ignore all but one.
mkGlobalFlagAssignment :: [PackageConstraint] -> Map GlobalFlag Bool
mkGlobalFlagAssignment = M.fromList . L.concatMap go
  where
    go (PackageConstraintFlags pn fa) = L.map (\ (fn, b) -> (GlobalFlag pn fn, b)) fa
    go _                              = []

closure :: Index PackageInfo -> [PackageName] -> SDeps Bool
closure idx = go S.empty
  where
    go :: Set PackageName -> [PackageName] -> SDeps Bool
    go _visited []             = SBool True
    go  visited (pn : pns)
      -- | trace (unPackageName pn) False = undefined
      | pn `S.member` visited = go visited pns
      | otherwise             = let pi  = findPackage idx pn
                                    SDepsFree c candidates = packageCondition pn pi
                                in  SAnd c (go (S.insert pn visited) (pns ++ candidates))

--------------------------------------------------------------------------
-- Solver dependency expressions
--------------------------------------------------------------------------

-- Abstract syntax for solver conditions.
data SDeps :: * -> * where
  SBool :: Bool                           -> SDeps Bool
  SVer  :: Integer                        -> SDeps Integer
  SPkg  :: PackageName                    -> SDeps Integer
  SFlag :: GlobalFlag                     -> SDeps Bool
  SEq   :: SDeps a -> SDeps a             -> SDeps Bool
  SLe   :: SDeps Integer -> SDeps Integer -> SDeps Bool
  SGe   :: SDeps Integer -> SDeps Integer -> SDeps Bool
  SAnd  :: SDeps Bool -> SDeps Bool       -> SDeps Bool
  SOr   :: SDeps Bool -> SDeps Bool       -> SDeps Bool
  SNot  :: SDeps Bool                     -> SDeps Bool

deriving instance Show (SDeps a)

data SDepsFree = SDepsFree (SDeps Bool) [PackageName]
  deriving Show

sAnd' :: [SDeps Bool] -> SDeps Bool
sAnd' [] = SBool True
sAnd' xs = foldr1 SAnd xs

sAnd :: [SDepsFree] -> SDepsFree
sAnd [] = SDepsFree (SBool True) []
sAnd xs = foldr1 (cmb SAnd) xs

sOr' :: [SDeps Bool] -> SDeps Bool
sOr' [] = SBool False
sOr' xs = foldr1 SOr xs

sOr :: [SDepsFree] -> SDepsFree
sOr [] = SDepsFree (SBool False) []
sOr xs = foldr1 (cmb SOr) xs

cmb :: (SDeps Bool -> SDeps Bool -> SDeps Bool) -> SDepsFree -> SDepsFree -> SDepsFree
cmb op (SDepsFree d1 pn1) (SDepsFree d2 pn2) = SDepsFree (op d1 d2) (pn1 ++ pn2)

cmb1 :: (SDeps Bool -> SDeps Bool) -> SDepsFree -> SDepsFree
cmb1 op (SDepsFree d pn) = SDepsFree (op d) pn

translate :: SDeps a -> StateT Vars IO SMT.SExpr
translate (SBool b)    = return $ SMT.bool b
translate (SVer i)     = return $ SMT.int i
translate (SPkg pn)    = sPkg  pn
translate (SFlag gf)   = sFlag gf
translate (SEq  d1 d2) = liftM2 SMT.eq  (translate d1) (translate d2)
translate (SLe  d1 d2) = liftM2 SMT.leq (translate d1) (translate d2)
translate (SGe  d1 d2) = liftM2 SMT.geq (translate d1) (translate d2)
translate (SAnd d1 d2) = liftM2 SMT.and (translate d1) (translate d2)
translate (SOr  d1 d2) = liftM2 SMT.or  (translate d1) (translate d2)
translate (SNot d)     = liftM  SMT.not (translate d)

freePkgs :: SDeps a -> [PackageName]
freePkgs (SPkg pn)    = [pn]
freePkgs (SEq  d1 d2) = freePkgs d1 ++ freePkgs d2
freePkgs (SLe  d1 d2) = freePkgs d1 ++ freePkgs d2
freePkgs (SGe  d1 d2) = freePkgs d1 ++ freePkgs d2
freePkgs (SAnd d1 d2) = freePkgs d1 ++ freePkgs d2
freePkgs (SOr  d1 d2) = freePkgs d1 ++ freePkgs d2
freePkgs _            = []

--------------------------------------------------------------------------
-- Index conversion (start)
--------------------------------------------------------------------------

packageCondition :: PackageName -> PackageInfo -> SDepsFree
packageCondition pn pi =
    sOr
  $ SDepsFree (SEq (SPkg pn) (SVer 0)) []
  : L.map (\ (sv, i) -> cmb1 (SAnd (SEq (SPkg pn) (SVer sv))) (iiDeps i)) assocs
  where
    assocs = M.toList (piTo pi)

processIndexes :: Platform
               -> CompilerInfo
               -> Map GlobalFlag Bool
               -> SI.InstalledPackageIndex
               -> CI.PackageIndex SourcePackage
               -> Index PackageInfo
processIndexes platform cinfo gfa iidx sidx = result
  where
    combine :: PackageInfo -> PackageInfo -> PackageInfo
    combine (PackageInfo a1 f1 t1 flg1) (PackageInfo a2 _ t2 flg2) =
      PackageInfo (a1 ++ a2) f1 (M.union t1 t2) (S.union flg1 flg2)

    result :: Index PackageInfo
    result = M.unionWith combine (processInstalledIndex                    result iidx)
                                 (processSourceIndex    platform cinfo gfa result sidx)

processInstalledIndex :: Index PackageInfo -> SI.InstalledPackageIndex -> Index PackageInfo
processInstalledIndex final idx =
  M.fromList $ L.map (\ (pn, insts) -> (pn, mkInstalledPackageInfo final idx insts))
                     (SI.allPackagesByName idx)

installedPackage :: Index PackageInfo -> SI.InstalledPackageIndex -> InstalledPackageInfo -> InstanceInfo
installedPackage final idx ipi = InstanceInfo inst deps
  where
    inst = Instance
      (pkgVersion $ sourcePackageId ipi)
      (Installed $ installedPackageId ipi)
    deps = sAnd (L.map ((\ (pn, v) -> SDepsFree (SEq (SPkg pn) (SVer v)) [pn]) . fromIpid) (IPI.depends ipi))

    -- Looking up the dependencies is not trivial.
    -- We first use the installed package index to find the package name
    -- belonging to an installed package id; then we use the reverse
    -- mapping in the final index.
    --
    -- TODO: We have to handle broken packages properly.
    fromIpid :: InstalledPackageId -> (PackageName, SVersion)
    fromIpid ipid = case SI.lookupInstalledPackageId idx ipid of
      Nothing   -> error "installedPackage: TODO / internal error"
      Just ipi' -> let pn = pkgName (sourcePackageId ipi')
                       pi = findPackage final pn
                   in (pn, piFrom pi !@ ipid)

mkInstalledPackageInfo :: Index PackageInfo -> SI.InstalledPackageIndex -> [InstalledPackageInfo] -> PackageInfo
mkInstalledPackageInfo final idx ipis = pi
  where
    assocs  = zip [-1, -2 ..] (L.map (installedPackage final idx) ipis)
    assocs' = L.map (\ (s, i) -> (instVersion $ iiInstance i, s)) assocs
    rassocs = zip (L.map installedPackageId ipis) [-1, -2 ..]
    pi      = PackageInfo assocs' (M.fromList rassocs) (M.fromList assocs) S.empty

processSourceIndex :: Platform
                   -> CompilerInfo
                   -> Map GlobalFlag Bool
                   -> Index PackageInfo -> CI.PackageIndex SourcePackage -> Index PackageInfo
processSourceIndex platform cinfo gfa final idx =
  M.fromList $ L.map (mkSourcePackageInfo platform cinfo gfa final)
                     (CI.allPackagesByName idx)

mkSourcePackageInfo :: Platform
                    -> CompilerInfo
                    -> Map GlobalFlag Bool
                    -> Index PackageInfo
                    -> [SourcePackage]
                    -> (PackageName, PackageInfo)
mkSourcePackageInfo platform cinfo gfa final = go
  where
    go []           = error "mkSourcePackageInfo: internal error, empty list"
    go ps @ (p : _) = (pkgName $ packageInfoId p, pi)
      where
        assocs  = zip [1 ..] (L.map (sourcePackage platform cinfo gfa final) ps)
        assocs' = L.map (\ (s, i) -> (instVersion $ iiInstance i, s)) assocs
        flags   = S.fromList $ L.concatMap (L.map flagName . genPackageFlags . CT.packageDescription) ps
        pi      = PackageInfo assocs' M.empty (M.fromList assocs) flags

sourcePackage :: Platform
              -> CompilerInfo
              -> Map GlobalFlag Bool
              -> Index PackageInfo
              -> SourcePackage
              -> InstanceInfo
sourcePackage platform cinfo gfa final sp = InstanceInfo inst deps
  where
    GenericPackageDescription pkg flags libs exes _tests _benchs = CT.packageDescription sp
    pn   = pkgName (package pkg)
    inst = Instance (pkgVersion $ packageInfoId sp) Source

    conv :: CondTree ConfVar [Dependency] a -> SDepsFree
    conv = processCondTree platform cinfo final gfa flags pn
    -- TODO: Handle components properly
    deps = sAnd (maybe (SDepsFree (SBool True) []) conv libs : L.map (conv . snd) exes)

processCondTree :: Platform
                -> CompilerInfo
                -> Index PackageInfo
                -> Map GlobalFlag Bool
                -> [Flag]
                -> PackageName
                -> CondTree ConfVar [Dependency] a
                -> SDepsFree
processCondTree platform cinfo final gfa flags pn (CondNode _info ds branches) =
     sAnd
  $  L.map (processDependency            final             ) ds
  ++ L.map (processBranch platform cinfo final gfa flags pn) branches

processBranch :: Platform
              -> CompilerInfo
              -> Index PackageInfo
              -> Map GlobalFlag Bool
              -> [Flag]
              -> PackageName
              -> ( Condition ConfVar
                 , CondTree ConfVar [Dependency] a
                 , Maybe (CondTree ConfVar [Dependency] a)
                 )
              -> SDepsFree
processBranch platform@(Platform arch os) cinfo final gfa flags pn (cond, thenPart, maybeElsePart) =
  go cond (                                   processCondTree platform cinfo final gfa flags pn  thenPart     )
          (maybe (SDepsFree (SBool True) []) (processCondTree platform cinfo final gfa flags pn) maybeElsePart)
  where
    go :: Condition ConfVar -> SDepsFree -> SDepsFree -> SDepsFree
    go (Lit True)          t _ = t
    go (Lit False)         _ f = f
    go (CNot c)            t f = go c f t
    go (CAnd c d)          t f = go c (go d t f) f
    go (COr  c d)          t f = go c t (go d t f)
    go (Var (Flag flag))   t f = case isKnown of
      Nothing    -> cmb SOr (cmb SAnd            sflag  t)
                            (cmb SAnd (cmb1 SNot sflag) f)
      Just True  -> t
      Just False -> f
      where
        sflag :: SDepsFree
        sflag = SDepsFree (SFlag (GlobalFlag pn flag)) []
        isKnown :: Maybe Bool
        isKnown = case M.lookup (GlobalFlag pn flag) gfa of
          Nothing -> fmap flagDefault (find (\ x -> flagName x == flag && flagManual x) flags)
          Just b  -> Just b

    go (Var (OS os'))      t f
      | os == os'              = t
      | otherwise              = f
    go (Var (Arch arch'))  t f
      | arch == arch'          = t
      | otherwise              = f
    go (Var (Impl cf cvr)) t f
      -- TODO: This is marked as not completely ok in the modular solver.
      |        matchImpl               (compilerInfoId     cinfo)
        || any matchImpl (fromMaybe [] (compilerInfoCompat cinfo)) = t
      | otherwise              = f
      where
        matchImpl :: CompilerId -> Bool
        matchImpl (CompilerId cf' cv) = cf == cf' && cv `withinRange` cvr


processDependency :: Index PackageInfo -> Dependency -> SDepsFree
processDependency final d@(Dependency pn _) = SDepsFree (packageDependency final d) [pn]

packageDependency :: Index PackageInfo -> Dependency -> SDeps Bool
packageDependency final (Dependency pn vr) =
    sOr'
  $ L.map (\ (_, sv) -> SEq (SPkg pn) (SVer sv))
  $ L.filter (\ (v, _) -> v `withinRange` vr)
  $ piAssocs (findPackage final pn)

--------------------------------------------------------------------------
-- Index conversion (end)
--------------------------------------------------------------------------
--
-- Taken from Modular.Configured and Modular.ConfiguredConversion:

mkPlan :: Platform
       -> CompilerInfo
       -> SI.InstalledPackageIndex
       -> CI.PackageIndex SourcePackage
       -> [SolvedPackage]
       -> Either [PlanProblem] InstallPlan
mkPlan platform cinfo iidx sidx spkgs =
  new platform cinfo False (SI.fromList (L.map (convSolvedPackage iidx sidx) spkgs))

convPackageInstance :: PackageInstance -> Either InstalledPackageId PackageId
convPackageInstance (PackageInstance _  (Instance _ (Installed i))) = Left i
convPackageInstance (PackageInstance pn (Instance v Source)       ) = Right (PackageIdentifier pn v)

convSolvedPackage :: SI.InstalledPackageIndex
                  -> CI.PackageIndex SourcePackage
                  -> SolvedPackage
                  -> PlanPackage
convSolvedPackage iidx sidx (SolvedPackage pi0 fa stanzas deps) =
  case convPackageInstance pi0 of
    Left pi  -> PreExisting $ InstalledPackage
                  (fromJust $ SI.lookupInstalledPackageId iidx pi)
                  (L.map confSrcId $ CD.nonSetupDeps (fmap (L.map mkConfiguredId) deps))
    Right pi -> Configured $ ConfiguredPackage
                  (fromJust $ CI.lookupPackageId sidx pi)
                  fa stanzas (fmap (L.map mkConfiguredId) deps)

mkConfiguredId :: PackageInstance -> ConfiguredId
mkConfiguredId (PackageInstance pn (Instance v loc)) =
  ConfiguredId sourceId installedId
  where
    sourceId    = PackageIdentifier pn v
    installedId = case loc of
      Installed pi -> pi
      Source       -> fakeInstalledPackageId sourceId
