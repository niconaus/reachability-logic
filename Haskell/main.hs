import Examples as P
import Types
import Preconditions
import System.IO
import System.Environment
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Control.Parallel (par, pseq)

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  args <- getArgs
  let limit = if null args then id else
              case reads (head args) of [(n,"")] -> take n
                                        _        -> id

  let exploitTree = extend (leaf.simp) $ preconditions P.program P.post :: Mirkwood
  --print exploitTree
  --print $ forceTree $ takeTree 50 exploitTree

  start <- getCurrentTime
  mapM_ print $ limit $ filter (/=Expr (Not true)) $ deforest (fastheur (++)) exploitTree
  end <- getCurrentTime
  putStrLn $ show (end `diffUTCTime` start) ++ " elapsed."


-- for interactive use
exploits :: (Prog,Predicate) -> [Predicate]
exploits (prog,post) = filter (/=Expr (Not true)) $ deforest (fastheur (++)) exploitTree
  where exploitTree =  extend (leaf.simp) $ preconditions prog post :: Mirkwood


forceTree :: PredTree -> PredTree
forceTree Empty = Empty
forceTree (Node ls tr) = force ls `par` (forceTree tr `par` Node ls tr)

force :: [a] -> ()
force xs = (go xs) `pseq` ()
            where go (_:xs) = go xs
                  go [] = 1
