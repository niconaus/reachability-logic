{-|
Module      : Interpreter
Description : Interpreter for Jump Programs
Copyright   : (c) Marc Schoolderman, 2022
Maintainer  : niconaus@vt.edu
Stability   : experimental
This module defines an interpreter (i.e. executable semantics) to play around with Jump programs
-}
module Interpreter where

import System.IO()
import System.Random
import Types
import Data.Map

-- | given a statement and postcondition, the "smallest" precondition is returned

type State = (Map String Int, Map Int Int)

type Oracle m = V -> E -> State -> m Int

noND :: Oracle Maybe
noND _ _ _ = Nothing

userND :: Oracle IO
userND mv e st = putStrLn ("Enter value for "++show (Var mv)++", where: "++show e) >> loop
 where loop = do
         s <- getLine
         let i = read s
         if eval (eSubst (Var mv) (Num i) e) st /= 0 then
           return (read s)
         else
           putStrLn "Try again" >> loop

presetND :: [Int] -> Oracle []
presetND src mv e st = [ k | k <- src, eval (eSubst (Var mv) (Num k) e) st /= 0 ]

{- these two will not typically be very useful -}
allND :: Oracle []
allND = presetND (0:nzints)
  where nzints = 1 : -1 : fmap (\x->signum x*(abs x+1)) nzints

randND :: Oracle IO
randND mv e st = randomIO `until_` (\x->eval (eSubst (Var mv) (Num x) e) st /= 0)
  where until_ m p = m >>= \x->putStrLn(show x) >> if p x then return x else until_ m p

run :: Monad m => Prog -> Oracle m -> m State
run (n, blocks) oracle = runB (blocks!n) (Data.Map.empty, Data.Map.empty)
  where runB Exit             = return
        runB (Seq s b)        = (>>= runB b) . runS s
        runB (Jump e l1 l2)   = (\st->blocks!if eval e st/=0 then l1 else l2) >>= runB
        runB (IndirectJump e) = (\st->blocks!eval e st) >>= runB

        runS (Assign v e)           st@(var,mem) = return (insert v (eval e st) var, mem)
        runS (NDAssign v e   )      st@(var,mem) = do i <- oracle v e st; return (insert v i var, mem)
        runS (Store (Region e _) v) st@(var,mem) = return (var, insert (eval e st) (eval (Var v) st) mem)

eval :: E -> State -> Int
eval (Num k) _     = k
eval (Var k) (v,_) = v!k
eval (Deref (Region e _)) st@(_,m) = m!eval e st
eval (Not e) st = if eval e st == 0 then -1 else 0
eval (App a op b) st = perform op (eval a st) (eval b st)
  where perform :: Op -> Int -> Int -> Int
        perform Plus = (+)
        perform Minus= (-)
        perform Mult = (*)
        perform Mod  = mod
        perform Eq   = (int.).(==)
        perform Leq  = (int.).(<=)
        perform Geq  = (int.).(>=)
        perform Less = (int.).(<)
        perform Greater = (int.).(>)
        perform And = \x y->if x==0 then x else y
        perform Or  = \x y->if x==0 then y else x
        int bv = if bv then -1 else 0
