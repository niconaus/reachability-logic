{-# LANGUAGE FlexibleInstances #-}
{-|
Module      : Types
Description : Type declarations and helper functions
Copyright   : (c) Nico Naus, 2022
Maintainer  : niconaus@vt.edu
Stability   : experimental
This module defines the types of expressions, statements and predicates, including helper functions
-}
module Types where

import qualified Data.Map as M
import Data.List

-- PROGRAM

type Blocks = M.Map L B
type Prog = (L, Blocks)

-- BLOCK

data B = Seq S B
       | Jump E L L
       | IndirectJump E
       | Exit deriving (Show)

-- STATEMENTS

data S = Assign V E
       | NDAssign V E
       | Store R V deriving (Ord, Eq)

-- EXPRESSIONS

data E = Num Int | Var V
       | Deref R
       | App E Op E | Not E deriving (Ord, Eq)

data R = Region E Int deriving (Ord, Eq)
type V = String
type L = Int -- label
data Op = Plus | Minus | Mult | Mod | Eq | Leq
        | Geq | Less | Greater | And | Or deriving (Ord, Eq)

-- PREDICATES

data Predicate = Exists V Predicate
               | SP R R | AL R R
               | PAnd Predicate Predicate
               | Expr E deriving (Ord, Eq)

data PredTree = Node [Predicate] PredTree | Empty

-- TYPE INSTANCES

instance Show Op where
  show Plus = " + "
  show Less = " < "
  show Mult = " * "
  show Eq = " == "
  show Leq = " <= "
  show And = " && "
  show Or  = " || "
  show Minus = " - "
  show Mod = " % "
  show Geq = " >= "
  show Greater = " > "

instance Show E where
  show (Num i) = show i
  show (Var v) = v
  show (App e1 op e2) = "(" ++ show e1 ++ show op ++ show e2 ++ ")"
  show (Not e)        = "~" ++ show e
  --show (Deref (Region r l)) = "Deref [[ " ++ show r ++ " , " ++ show l ++ " ]]"
  show (Deref (Region r _)) = "!" ++ show r

true :: E
true = App (Num 0) Eq (Num 0)

instance Show S where
  show (Assign v e)   = v ++ ":=" ++ show e
  show (NDAssign v e) = v ++ "?:=" ++ show e
  show (Store r e)    = show r ++ "|->" ++ show e

instance Show PredTree where
  show (Node ps pt) = foldr (++) "\n" (map ((++"; ").show) ps) ++ show pt
  show Empty = ""

instance Show Predicate where
  show (Exists mv p) = "∃" ++ show mv ++ "." ++ show p
  show (SP r1 r2) = "[" ++ show r1 ++ "]⋈[" ++ show r2 ++ "]"
  show (AL r1 r2) = "[" ++ show r1 ++ "]≐[" ++ show r2 ++ "]"
  show (PAnd r1 r2) = bracket r1 ++ " ∧ " ++ bracket r2
    where bracket p@(Exists _ _) = "(" ++ show p ++ ")"
          bracket p = show p
  show (Expr e) = show e

instance Show R where
  show (Region e i) = show e ++ "#" ++ show i

-- GENERALIZED TREEISH INTERFACE

class Treeish tree where
  empty :: tree
  leaf :: Predicate -> tree
  junction :: [tree] -> tree

  restrict :: tree -> Predicate -> tree
  extend :: (Predicate -> tree) -> tree -> tree

  leafs :: [Predicate] -> tree
  leafs = junction . map leaf

instance Treeish PredTree where
  empty    = Empty
  leaf p   = simpNode [p] Empty
  leafs ps = simpNode ps Empty
  {- note: these are 100% the same as the original code; but the new definition is backwards-compatible and seems cleaner -}
  --restrict = predTreeAnd . (Node [])
  --junction = foldl mergeTrees empty
  restrict = predTreeAnd
  junction [lt,rt] = Node [] $ mergeTrees lt rt     -- (subsumed by the next definition, but let's keep it in)
  junction ts = Node [] $ foldl mergeTrees empty ts
  extend   = mapPT

{- isomorphic with original PredTree -}
instance Treeish [[Predicate]] where
  empty    = []
  leaf p   = [p] : empty
  leafs ps = ps : empty
  junction ts = [] : foldr (zipWithOpt (++)) [] ts
  restrict tree e = [ map (e `PAnd`) preds | preds <- tree ]
  extend f (ps:pt) = foldr (zipWithOpt(++)) ([]:extend f pt) (map f ps)
  extend _ [] = []

{- simplest implementation, close to the paper spec, will not always terminate -}
instance Treeish [Predicate] where
  empty = []
  leaf p = [p]
  restrict ps p1 = map (p1 `PAnd`) ps
  junction = foldr (++) []
  extend f = foldr (++) [] . map f

{- attempt at something resembling actual trees -}
data Fangorn = Fangorn [Predicate] [Fangorn]

instance Show Fangorn where
  show = Data.List.intercalate "\n" . preShow
    where preShow :: Fangorn -> [String]
          preShow (Fangorn ps trees) = [case ps of [] -> "_"; _ -> show (foldr1 PAnd ps)] ++ (map prefix.concat.map preShow) trees
          prefix s@('↳':_) = '\t':s
          prefix s@('\t':_) = '\t':s
          prefix s = '↳':'\t':s

instance Treeish Fangorn where
  empty  = leaf (Expr (Not true))
  leaf p = Fangorn [p] []
  leafs ps = if null ps then empty else Fangorn [] [Fangorn [p] [] | p <- ps]
  junction ts = Fangorn [] ts
  restrict (Fangorn ps trees) p2 = Fangorn (p2:ps) trees
  extend f (Fangorn ps0 trees0) = treebeard ps0 trees0
    where treebeard [] []    = f (Expr true)
          treebeard ps []    = f (foldr1 PAnd ps)
          treebeard ps trees = Fangorn [] (map (\(Fangorn ps2 t')->treebeard (ps++ps2) t') trees)

{- a more intelligent tree -}
data Mirkwood = Mirkwood [Predicate] [Mirkwood]

class Forest forest where
  toFangorn :: forest -> Fangorn

instance Forest Fangorn  where toFangorn = id
instance Forest Mirkwood where toFangorn (Mirkwood ps trees) = Fangorn ps (map toFangorn trees)

{- this mapping does not preserve the semantics, but a breadth-first/depth-first search should look the same -}
instance Forest PredTree where
  toFangorn (Node ps sub) = junction [leafs ps, toFangorn sub]
  toFangorn Empty = empty

instance Show Mirkwood where show = show . toFangorn

instance Treeish Mirkwood where
  empty  = leaf (Expr (Not true))
  leaf p = Mirkwood [simp p] []
  leafs ps = let trees = [Mirkwood [p] [] | p <- ps, let p' = simp p, p' /= Expr (Not true)] in if null trees then empty else Mirkwood [] trees
  junction ts = Mirkwood [] ts
  restrict (Mirkwood ps trees) p2 = Mirkwood (p2:ps) trees
  extend f (Mirkwood ps trees) = gimli (if null ps then Expr true else foldr1 PAnd ps) trees
    where legolas p []    = f p
          legolas p stree = Mirkwood [] (map (\(Mirkwood ps2 t')->gimli (foldr PAnd p ps2) t') stree)
          --legolas p stree = case [legolas p' t' | Mirkwood ps2 t' <- stree, let p' = simp (foldr PAnd p ps2), p' /= Expr (Not true)] of
          --                    [] -> empty
          --                    ts -> Mirkwood [] ts
          gimli p stree = let p' = simp p in if p' == Expr (Not true) then empty else legolas p' stree

-- HELPER FUNCTIONS

{- a guided tree walk; using real priority queues would be better;
   if the "enqueue" function is "++", breadth-first search strategy is used;
   if it is "flip (++)", depth first strategy is used -}

deforest :: Forest tree => ([Fangorn] -> [Fangorn] -> [Fangorn]) -> tree -> [Predicate]
deforest enqueue treeish = walk (enqueue [] [extend leaf $ toFangorn treeish])
  where walk (Fangorn [p] []  : queue) = p : walk queue
        walk (Fangorn [] tree : queue) = walk (enqueue queue tree)
        walk [] = []
        walk _  = error "Fangorn forest could not be deforestated?"

strategy :: (Fangorn->Fangorn->Ordering) -> ([Fangorn]->[Fangorn]->[Fangorn])
strategy rank = \x y->foldr (insertBy rank) x (sortBy rank y)
--strategy rank mingle = (sortBy rank .) . mingle  -- inefficient version

strategy' :: (Fangorn->Fangorn->Ordering) -> ([Fangorn]->[Fangorn]->[Fangorn])
strategy' rank = \x y->foldr (insertBy') x (sortBy rank y)
 where insertBy' x [] = [x]
       insertBy' x (y:ys) = case rank x y of
                               LT -> x:y:ys
                               _  -> y:insertBy' x ys

heuristic :: ([Fangorn]->[Fangorn]->[Fangorn])
heuristic = strategy (\(Fangorn ps _) (Fangorn qs _)->compare qs ps)
--heuristic = strategy cmp
--  where cmp (Fangorn _ []) (Fangorn _ []) = EQ -- this should be similar too 'lookahead 1' and 'fastheur'
--        cmp (Fangorn _ []) (Fangorn _ _)  = LT
--        cmp (Fangorn _ _) (Fangorn _ [])  = GT
--        cmp _ _ = EQ

lookahead :: Int -> ([Fangorn]->[Fangorn]->[Fangorn])
lookahead n = strategy (\x y->compare (score x) (score y))
  where shallowness :: Fangorn -> Int
        shallowness (Fangorn _ []) = 0
        shallowness (Fangorn _ ts) = 1 + (minimum $ map shallowness ts)
        score = shallowness . takeFangorn n

fastheur :: ([Fangorn]->[Fangorn]->[Fangorn]) -> ([Fangorn]->[Fangorn]->[Fangorn])
fastheur op x y = uncurry (++) $ partition isLeaf $ op x y
 where isLeaf (Fangorn _ ts) = null ts

{- a list "concatenation" that is not order-preserving, with "obvious" benefits -}
(+~+) :: [a] -> [a] -> [a]
x +~+ [] = x
[] +~+ x = x
(x:xs) +~+ (y:ys) = x:y:xs+~+ys

zipWithOpt :: (a -> a -> a) -> [a] -> [a] -> [a]
zipWithOpt _ [] ys = ys
zipWithOpt _ xs [] = xs
zipWithOpt f (x:xs) (y:ys) = f x y : zipWithOpt f xs ys

mergeTrees :: PredTree -> PredTree -> PredTree
mergeTrees Empty tr = tr
mergeTrees tr Empty = tr
mergeTrees (Node p1 t1) (Node p2 t2) = Node (p1 ++ p2) (mergeTrees t1 t2)

mapPT :: (Predicate -> PredTree) -> PredTree -> PredTree
mapPT f (Node ps pt) = foldr mergeTrees (Node [] (mapPT f pt)) (map f ps)
mapPT _ Empty = Empty

takeTree :: Int -> PredTree -> PredTree
takeTree _ Empty = Empty
takeTree 0 (Node _ _) = Empty
takeTree i (Node ps pt) = Node ps (takeTree (i-1) pt)

simpNode :: [Predicate] -> (PredTree -> PredTree)
simpNode ps = Node [ e | e <- ps, simp e /= Expr (Not true) ]

predTreeAnd :: PredTree -> Predicate -> PredTree
predTreeAnd (Node preds tree) e = Node (map (\p -> PAnd p e) preds) (predTreeAnd tree e)
predTreeAnd Empty _ = Empty -- TODO: is this case correct???

takeFangorn :: Int -> Fangorn -> Fangorn
takeFangorn 0 (Fangorn ps _)     = Fangorn ps []
takeFangorn i (Fangorn ps trees) = Fangorn ps (map (takeFangorn (i-1))  trees)

-- SAFE SUBSTITUTION IN EXPRESSIONS/PREDICATES

eSubst :: E -> E -> E -> E
eSubst v e expr = if v == expr then e else
                  case expr of Not e1 -> Not (eSubst v e e1)
                               App e1 op e2 -> App (eSubst v e e1) op (eSubst v e e2)
                               Deref (Region e1 l) -> Deref (Region (eSubst v e e1) l)
                               _ -> expr

predSubst :: E -> E -> Predicate -> Predicate
predSubst v e (Exists mv p)     = if v == Var mv then Exists mv p else
                                  if isBoundBy mv (Expr e) then let mv' = mv++"'" in predSubst v e (Exists mv' (predSubst (Var mv) (Var mv') p))
                                  else Exists mv (predSubst v e p)
predSubst v e (Expr e1)        = Expr (eSubst v e e1)
predSubst v e (SP (Region e1 i1) (Region e2 i2)) = SP (Region (eSubst v e e1) i1) (Region (eSubst v e e2) i2)
predSubst v e (AL (Region e1 i1) (Region e2 i2)) = AL (Region (eSubst v e e1) i1) (Region (eSubst v e e2) i2)
predSubst v e (PAnd p1 p2)     = PAnd (predSubst v e p1) (predSubst v e p2)

isBoundBy :: V -> Predicate -> Bool
isBoundBy bv pr = not (null [undefined | Var v <-atoms pr, v==bv])
  where
    atoms :: Predicate -> [E]
    atoms (Exists mv p) = filter (/=Var mv) $ atoms p
    atoms (SP (Region a _) (Region b _)) = atoms (Expr a) ++ atoms (Expr b)
    atoms (AL (Region a _) (Region b _)) = atoms (Expr a) ++ atoms (Expr b)
    atoms (PAnd a b) = atoms a ++ atoms b
    atoms (Expr (Deref (Region e _))) = atoms (Expr e)
    atoms (Expr (Not e)) = atoms (Expr e)
    atoms (Expr (App a _ b)) = atoms (Expr a) ++ atoms (Expr b)
    atoms (Expr e) = [e]

-- THE SIMPLISTIC SIMPLIFICATION ENGINE

simp :: Predicate -> Predicate
simp (Expr e) = Expr $ simpE e

simp p@(PAnd _ _)
       = case conj p of
         [] -> Expr true
         cs -> if absurd cs then Expr (Not true) else foldr1 PAnd cs
  where conj = subsume . rewriteEq . map simp' . unravel
        unravel :: Predicate -> [Predicate]
        unravel (PAnd p1 p2) = unravel p1 ++ unravel p2
        unravel (AL r1 r2) = [if r1 <= r2 then AL r1 r2 else AL r2 r1]
        unravel (SP r1 r2) = [if r1 <= r2 then SP r1 r2 else SP r2 r1]
        --unravel (AL (Region r1 _) (Region r2 _)) = [if r1 <= r2 then Expr (App r1 Eq r2) else Expr (App r2 Eq r1)]
        --unravel (SP (Region r1 _) (Region r2 _)) = [if r1 <= r2 then Expr (Not (App r1 Eq r2)) else Expr (Not (App r2 Eq r1))]
        unravel (Expr (App p1 And p2)) = unravel (Expr p1) ++ unravel (Expr p2)
        unravel (Expr (Not (App p1 Or p2))) = unravel (Expr (Not p1)) ++ unravel (Expr (Not p2))
        unravel (Exists mv p1) = let (bound, unbound) = partition (isBoundBy mv) (conj p1) in unbound ++ if null bound then [] else [Exists mv (foldr1 PAnd bound)]
        unravel p1 = [p1]

        simp' p1@(Exists _ _) = p1 -- already simplified by 'unravel'
        simp' p1 = simp p1

        -- remove superfluous predicates; simple version:
        subsume = map head . Data.List.group . Data.List.sort . filter ((/=)(Expr true))
        -- detect contradictions; simple version:
        --absurd ps = elem (Expr (Not true)) ps
        absurd (Expr (Not e):ps) = elem (Expr e) (Expr true:ps) || absurd ps
        absurd (Expr e:ps) = elem (Expr$Not e) ps || absurd ps
        absurd (SP r1 r2:ps) = elem (AL r1 r2) ps || absurd ps
        absurd (AL r1 r2:ps) = elem (SP r1 r2) ps || absurd ps
        absurd (Exists _ p1:ps) = absurd [p1] || absurd ps
        absurd (_:ps) = absurd ps
        absurd [] = False

simp (Exists mv p) = if not (isBoundBy mv p') then p' else
                     case p' of
                          Expr (App (Var v') Eq _) -> if mv == v' then Expr true else Exists mv p'
                          _ -> Exists mv p'
   where p' = simp p

simp (AL r1' r2') = case (simpR r1', simpR r2') of (r1,r2) -> if r1 == r2 then Expr true else AL r1 r2
simp (SP r1' r2') = case (simpR r1', simpR r2') of (r1,r2) -> if r1 == r2 then Expr (Not true) else SP r1 r2

simpR :: R -> R
simpR (Region e s) = Region (simpE e) s

-- | Simplification of E' expressions
-- | Note: the expression language should be simpler
simpE :: E -> E
simpE (App e1 op e2) = perform op (simpE e1, simpE e2)
  where
    perform Mult (Num 0, _)  = Num 0
    perform Plus (Num x, Num y)  = Num(x+y)
    perform Mult (Num x, Num y)  = Num(x*y)
    perform Minus (Num x, Num y) = Num(x-y)
    perform Plus  (x,Num 0) = x
    perform Minus (x,Num 0) = x
    perform Plus (App x Plus (Num k),Num z) = App x Plus  (Num $ k + z)
    perform Minus(App x Minus(Num k),Num z) = App x Minus (Num $ k + z)
    perform Plus (e@(App x Plus (App (Num k) Mult y)), App (Num k') Mult z) = if y==z then App x Plus  (simpE$App (Num (k+k')) Mult y) else App e Plus z
    perform Minus(e@(App x Minus(App (Num k) Mult y)), App (Num k') Mult z) = if y==z then App x Minus (simpE$App (Num (k+k')) Mult y) else App e Minus z
    perform Plus (e@(App x Plus y),  App (Num k') Mult z) = if y==z then App x Plus  (simpE$App (Num (1+k')) Mult y) else App e Plus z
    perform Minus(e@(App x Minus y), App (Num k') Mult z) = if y==z then App x Minus (simpE$App (Num (1+k')) Mult y) else App e Minus z
    perform Plus (e@(App x Plus (App (Num k) Mult y)),z) = if y==z then App x Plus  (simpE$App (Num (k+1)) Mult y) else App e Plus z
    perform Minus(e@(App x Minus(App (Num k) Mult y)),z) = if y==z then App x Minus (simpE$App (Num (k+1)) Mult y) else App e Minus z
    perform Plus (e@(App x Plus y),z)   = if y==z then App x Plus  (App (Num 2) Mult y) else App e Plus z
    perform Minus(e@(App x Minus y),z)  = if y==z then App x Minus (App (Num 2) Mult y) else if e==z then Num 0 else App e Minus z
    perform Minus (e@(App x Plus y),z) = if y==z then x else if e==z then Num 0 else App e Minus z
    perform Plus (e@(App x Minus y), z) = if y==z then x else App e Plus z
    perform Minus (x,y) = if x==y then Num 0 else App x Minus y
    perform Mod (Num x, Num y)   = Num(x `mod` y)
    perform Eq (Num x, Num y) = if x==y then true else Not true
    perform Eq (lhs@(App x Plus k), rhs@(App x' Plus m)) = if x==x' then App k Eq m else App lhs Eq rhs
    perform Eq (lhs@(App x Minus k), rhs@(App x' Minus m)) = if x==x' then App k Eq m else App lhs Eq rhs
    perform Eq (App x Minus (Num k), Num q) = App x Eq (Num (k+q))
    perform Eq (x, y) = if x==y then true else App x Eq y
    perform Less (e@(App x Plus (Num k)), y) = if x==y && k > 0 then Not true else App e Less y
    perform Greater (y,e@(App x Plus (Num k))) = if x==y && k > 0 then Not true else App e Less y
    perform Greater (e@(App x Minus (Num k)),y) = if x==y && k > 0 then Not true else App e Greater y
    perform Less (y,e@(App x Minus (Num k))) = if x==y && k > 0 then Not true else App e Greater y
    perform Leq (Num x, Num y) = if x<=y then true else Not true
    perform Leq (x, y) = if x==y then true else App x Leq y
    perform Geq (Num x, Num y) = if x>=y then true else Not true
    perform Geq (x, y) = if x==y then true else App x Geq y
    perform Less (Num x, Num y) = if x<y then true else Not true
    perform Less (x, y) = if x==y then Not true else App x Less y
    perform Greater (Num x, Num y) = if x>y then true else Not true
    perform Greater (x, y) = if x==y then Not true else App x Greater y
    perform Or (x, y) = if x==Not true then y else if y==Not true then x else
                        if x==true || y==true then true else (App x Or y)
    perform And (x, y)= if x==true then y else if y==true then x else
                        if x==Not true || y==Not true then Not true else (App x And y)
    perform op' (x, y) = App x op' y

simpE (Deref (Region e s)) = Deref (Region (simpE e) s)
simpE (Not e) = case simpE e of Not e1 -> e1
                                App a Or b -> App (simpE (Not a)) And (simpE (Not b))
                                e1 -> Not e1
simpE e = e

-- | Rewriting stuff based on (in)equalities rules
rewriteEq :: [Predicate] -> [Predicate]
rewriteEq ps = map Expr (subsume equalities) ++ map (foldl (.) simp $ map (uncurry predSubst) equalities) ps
 where
   equalities = [ if x >= y then (x,y) else (y,x) | App x Eq y <- trans $ map ineq [ e | Expr e <- ps ] ]
   ineq (App x Greater y) = ineq (App y Less x)
   ineq (App x Geq y)     = ineq (App y Leq x)
   ineq (App x Less y)    = Not (ineq (App x Geq y))
   ineq (Not x)           = case Not (ineq x) of Not (Not e) -> e
                                                 e -> e
   ineq x                 = x

   trans = foldr (\e es-> (case e of
                           App x Leq (Num k) -> if any (\e'->e'==Not (App x Leq (Num (k-1))) || e'==App (Num k) Leq x) es then App x Eq (Num k) else e
                           App (Num k) Leq x -> if any (\e'->e'==Not (App (Num (k+1)) Leq x) || e'==App x Leq (Num k)) es then App x Eq (Num k) else e
                           App x Leq y -> if elem (App y Leq x) es then App x Eq y else e
                           Not (App x Leq y) -> if elem (Not (App y Leq x)) es then App (Num 0) Eq (Num 1) else e {- generate an absurdity -}
                           _ -> e):es) []

   subsume :: [(E,E)] -> [E]
   subsume = foldr (\e@(x,y) es->App x Eq y : [ e2' | e2 <- es, let e2' = simpE (uncurry eSubst e e2), e2' /= true]) []
