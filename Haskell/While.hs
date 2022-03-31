{-# LANGUAGE FlexibleInstances #-}
module While (W(..), jlang, thenDo, elseDo) where

import Types
import qualified Data.Map as M

-- WHILE LANGUAGE to JUMP LANGUAGE

data W = While E W | If E W W | Do [W] | Stm S | W `Until` E
       | Goto String | Label String W deriving Show

data FancyTuple a b = a :§ b

infix 0 :§

jlang :: W -> Prog
jlang whilecode = link jumpcode
 where
  jumpcode :§ locs = compile whilecode 0 Exit
  (==>) = (,)
  compile (Stm s) n cont = [n==>Seq s cont] :§ []
  compile (While e b) n cont = [(l+2)==>Jump e l (l+1), (l+1)==>cont] ++ body :§ loc
    where body@((l,_):_) :§ loc = compile b n (Jump e l (l+1))
  compile (If e thn els) n cont = [(l'+2)==>Jump e l l', (l'+1)==>cont] ++ thn' ++ els' :§ loc1++loc2
    where thn'@((l,_):_)  :§ loc1 = compile thn n     (Jump true (l'+1) (l'+1))
          els'@((l',_):_) :§ loc2 = compile els (l+1) (Jump true (l'+1) (l'+1))
  compile (Do []) n cont = [n==>cont] :§ []
  compile (Do (w:ws)) n cont = stm ++ rest :§ loc1++loc2
    where ((l,blk):rest) :§ loc2 = compile (Do ws) n cont
          stm :§ loc1 = compile w l blk

  compile (b `Until` e) n cont = [(l+2)==>Jump true l l, (l+1)==>cont] ++ body :§ loc
    where body@((l,_):_) :§ loc = compile b n (Jump e (l+1) l)

  compile (Goto l) n _ = let k = labels M.! l in [n==>Jump true k k] :§ []
  compile (Label label w) n cont = [(l+1)==>Jump true l l] ++ body :§ (label,l):loc
    where body@((l,_):_) :§ loc = compile w n cont

  labels = M.fromList locs

  link blocks@((n,_):_) = (n, M.fromList blocks)
  link _ = error "this cannot happen"


-- some sugar for the problematic If syntax

thenDo :: (W -> W -> W) -> [W] -> W -> W
x `thenDo` y = x (Do y)

elseDo :: (W -> W) -> [W] -> W
x `elseDo` y = x (Do y)
