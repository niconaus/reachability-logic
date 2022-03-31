{-|
Module      : Solver
Description : Solves a predicate tree to find the simplest solution
Copyright   : (c) Nico Naus, 2022
Maintainer  : niconaus@vt.edu
Stability   : experimental
This module defines the functions to search though a predicate tree and find the
simplest predicate that is satisfiable
-}
module Solver (findPredicate, satisfiable) where

import Types

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.SBV.Dynamic as S
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad.IO.Class (liftIO)
import Data.SBV
import Data.SBV.Internals (SBV(..), SVal, VarContext(NonQueryVar))


-- | This function performs a breadth first search to find a predicate that is satisfiable
findPredicate :: PredTree -> Maybe (Types.Predicate)
findPredicate (Node ps ts) = case (foldr (\p1 res -> case res of
                                                      Just p -> Just p
                                                      Nothing -> if satisfiable p1 then Just p1 else Nothing) Nothing ps) of
                               Just p -> Just p
                               Nothing -> findPredicate ts
findPredicate Empty        = Nothing

-- | Takes a predicate and returns a bool indicating if it is satisfiable
satisfiable :: Types.Predicate -> Bool
satisfiable p = unsafePerformIO $ isSatisfiable $ makePredicate p

makePredicate :: Types.Predicate -> S.Symbolic (SBV Bool)
makePredicate p = do
  ss <- makeMap p
  pure $ SBV $ predToSMT ss p

makeMap :: Types.Predicate -> Symbolic (M.Map String S.SVal)
makeMap p = do
  vars <- traverse (uncurry createFree) (S.toList $ gatherFree p)
  pure $ M.fromList vars

--TODO: Region size not taken into account
predToSMT :: M.Map String S.SVal -> Types.Predicate -> S.SVal
predToSMT m (Expr e) = exprToSMT m e
predToSMT m (Exists _ e) = predToSMT m e
predToSMT m (PAnd p1 p2) = S.svAnd (predToSMT m p1) (predToSMT m p2)
predToSMT m (AL (Region r1 _) (Region r2 _)) = exprToSMT m (App r1 Eq r2)
predToSMT m (SP (Region r1 _) (Region r2 _)) = exprToSMT m (Not (App r1 Eq r2))

exprToSMT :: M.Map String S.SVal -> E -> S.SVal
exprToSMT _ (Num i) = S.svInteger (S.KBounded True 32) (toInteger i)
exprToSMT m (Var x) = case M.lookup ("v_" ++ show x) m of
  Just val -> val
  Nothing -> error "Variable not found in var-map"
exprToSMT m (App e1 Eq e2) = S.svEqual (exprToSMT m e1) (exprToSMT m e2)
exprToSMT m (App e1 Plus e2) = S.svPlus (exprToSMT m e1) (exprToSMT m e2)
exprToSMT m (App e1 Minus e2) = S.svMinus (exprToSMT m e1) (exprToSMT m e2)
exprToSMT m (App e1 Mult e2) = S.svTimes (exprToSMT m e1) (exprToSMT m e2)
exprToSMT m (App e1 Mod e2) = S.svRem (exprToSMT m e1) (exprToSMT m e2)
exprToSMT m (App e1 Geq e2) = S.svGreaterEq (exprToSMT m e1) (exprToSMT m e2)
exprToSMT m (App e1 Greater e2) = S.svGreaterThan (exprToSMT m e1) (exprToSMT m e2)
exprToSMT m (App e1 Leq e2) = S.svLessEq (exprToSMT m e1) (exprToSMT m e2)
exprToSMT m (App e1 Less e2) = S.svLessThan (exprToSMT m e1) (exprToSMT m e2)
exprToSMT m (App e1 And e2) = S.svAnd (exprToSMT m e1) (exprToSMT m e2)
exprToSMT m (App e1 Or e2) = S.svOr (exprToSMT m e1) (exprToSMT m e2)
exprToSMT m (Not e) = S.svNot (exprToSMT m e)
exprToSMT m (Deref (Region r _)) = case M.lookup ("mem_" ++ show r) m of
  Just val -> val
  Nothing -> error "Memory region not found in var-map"

gatherFree :: Types.Predicate -> S.Set (String, S.Kind)
gatherFree (Expr e) = gatherFreeE e
gatherFree (Exists mv p) = S.union (gatherFree p) (S.singleton ("mv_" ++ show mv, S.KBounded True 32))
gatherFree (PAnd p1 p2) = S.union (gatherFree p1) (gatherFree p2)
gatherFree (SP (Region e1 _) (Region e2 _)) = S.union (gatherFreeE e1) (gatherFreeE e2)
gatherFree (AL (Region e1 _) (Region e2 _)) = S.union (gatherFreeE e1) (gatherFreeE e2)

gatherFreeE :: E -> S.Set (String, S.Kind)
gatherFreeE (Num _)         = S.empty
gatherFreeE (Var v)       = S.singleton ("v_" ++ show v, S.KBounded True 32)
gatherFreeE (App e1 _ e2) = gatherFreeE e1 <> gatherFreeE e2
gatherFreeE (Not e)       = gatherFreeE e
gatherFreeE (Deref (Region e _)) = gatherFreeE e <> S.singleton ("mem_" ++ show e, S.KBounded True 32)

createFree :: String -> Kind -> S.Symbolic (String, SVal)
createFree n k = do
  s <- symbolicEnv
  x <- liftIO $ S.svMkSymVar (NonQueryVar Nothing) k (Just n) s
  pure (n,x)
