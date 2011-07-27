
module Main where

import qualified Data.ByteString.Char8 as B
import Data.Int (Int32)
import System.Environment (getArgs)
import qualified Zookeeper as Zoo

main :: IO ()

main = do
  (host_port:cmd:args) <- getArgs
  zh <- Zoo.init host_port (Just watcher) 10000
  run zh cmd args
  where watcher _zh zEventType zState path =
          putStrLn ("watch: '" ++ path ++ "' :: "
                    ++ show zEventType ++ " " ++ show zState)

-- TODO we should probably encode the value as UTF-8 in "create" and "set"
run :: Zoo.ZHandle -> String -> [String] -> IO ()

run zh "create" (path:value:_) = do
  res <- Zoo.create zh path (Just $ B.pack value)
         Zoo.OpenAclUnsafe Zoo.defaultCreateMode
  print res

run zh "get" (path:_) = do
  (val, stat) <- Zoo.get zh path Zoo.NoWatch
  print (val, stat)

run zh "getChildren" (path:_) = do
  children <- Zoo.getChildren zh path Zoo.NoWatch
  print children

run zh "set" (path:value:version) =
  Zoo.set zh path (Just $ B.pack value) (intVersion version)

run zh "delete" (path:version) =
  Zoo.delete zh path (intVersion version)

run _zh cmd _args = error ("Unknown command: " ++ cmd)

intVersion :: [String] -> Int32

intVersion [] = 0
intVersion (v:_) = read v
