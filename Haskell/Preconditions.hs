{-|
Module      : Preconditions
Description : Precondition generation module
Copyright   : (c) Nico Naus, 2022
Maintainer  : niconaus@vt.edu
Stability   : experimental
This module defines the precondition generation functions
-}
module Preconditions (preconditions, precondition) where

import Types
import Solver
import qualified Data.Map as M

-- | given a statement and postrestrict, the "smallest" precondition is returned
precondition :: Prog -> Predicate -> Maybe (Types.Predicate)
precondition prog post = findPredicate $ preconditions prog post

-- | given a program and predicate, the resulting precondition predicate tree is calculated
preconditions :: Treeish tree => Prog -> Predicate -> tree
preconditions (l,blocks) p = case M.lookup l blocks of
  Nothing -> error "initial block cannot be found"
  Just b -> (tauB b blocks p)

-- | precondition helper function. takes a block, blocks, predicate
tauB :: Treeish tree => B -> M.Map L B -> Predicate -> tree
tauB Exit _ p = leaf p
tauB (IndirectJump e) blocks p = junction [ tauB b blocks p `restrict` Expr (App (Num l) Eq e) | (l,b) <- M.toList blocks]
tauB (Jump e l1 l2) blocks p = case (M.lookup l1 blocks, M.lookup l2 blocks) of
  (Nothing, _) -> error "jump label to non-existing block"
  (_, Nothing) -> error "jump label to non-existing block"
  (Just b1, Just b2) -> junction [tauB b1 blocks p `restrict` Expr e,
                                  tauB b2 blocks p `restrict` Expr (Not e)]
tauB (Seq s b) blocks p = tauS s `extend` tauB b blocks p

tauS :: Treeish tree => S -> Predicate -> tree
tauS (Assign v e) p   = leaf (predSubst (Var v) e p)
tauS (NDAssign v e) p = leaf (Exists v (PAnd p (Expr e)))
tauS (Store r v) p    = leafs (tauStore r v p)

tauStore :: R -> V -> Predicate -> [Predicate]
tauStore r v (Expr p)                           = [ PAnd (Expr e) p1 | (e,p1) <- tauStoreE r v p ]
tauStore r v (PAnd p1 p2)                       = [ PAnd p1' p2' | p1' <- tauStore r v p1, p2' <- tauStore r v p2 ]
tauStore r v (Exists mv0 p)                     = [ Exists mv0 p' | p' <- tauStore r v p ]
tauStore r v (SP (Region e1 s1) (Region e2 s2)) = [ PAnd (SP (Region e1' s1) (Region e2' s2)) (PAnd p1 p2) | (e1', p1) <- tauStoreE r v e1, (e2',p2) <- tauStoreE r v e2]
tauStore r v (AL (Region e1 s1) (Region e2 s2)) = [ PAnd (AL (Region e1' s1) (Region e2' s2)) (PAnd p1 p2) | (e1', p1) <- tauStoreE r v e1, (e2',p2) <- tauStoreE r v e2]

-- | given a region, value, MetaVar and predicate,
-- | calculate the result of assigning that value to that region,
-- | and the predicate that belongs to it.
tauStoreE :: R -> V -> E -> [(E,Predicate)]
tauStoreE _ _    (Num n) = [(Num n, Expr true)]
tauStoreE _ _    (Var x) = [(Var x, Expr true)]
tauStoreE r v (Deref (Region a s)) = [(Deref (Region a s), SP (Region a s) r),
                                      (Var v             , AL (Region a s) r)]
tauStoreE r v     (App e1 op e2) = [(App e1' op e2', PAnd p1 p2) | (e1',p1) <- tauStoreE r v e1, (e2',p2) <- tauStoreE r v e2]
tauStoreE r v     (Not e)        = [(Not e',p) | (e',p) <- tauStoreE r v e]
