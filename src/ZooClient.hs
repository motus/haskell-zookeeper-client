
module Main where

import qualified Data.ByteString.Char8 as B
import System.Environment (getArgs)
import qualified Zookeeper as Zoo

main :: IO ()

main = do
  (host_port:cmd:args) <- getArgs
  zh <- Zoo.init host_port nullWatcher 10000
  run zh cmd args
  where nullWatcher _zh zEventType zState path =
          putStrLn ("watch: '" ++ path ++ "' :: "
                    ++ show zEventType ++ " " ++ show zState)

-- TODO we should probably encode the value as UTF-8 in "create" and "set"
run :: Zoo.ZHandle -> String -> [String] -> IO ()

run zh "create" [path, value] = do
  res <- Zoo.create zh path (Just $ B.pack value)
         Zoo.OpenAclUnsafe Zoo.defaultCreateMode
  print res

run zh "get" [path] = do
  (val, stat) <- Zoo.get zh path Zoo.NoWatch
  print (val, stat)

run zh "getChildren" [path] = do
  children <- Zoo.getChildren zh path Zoo.NoWatch
  print children

run zh "set" (path:value:version) = do
  Zoo.set zh path (Just $ B.pack value) (intVersion version)

run zh "delete" (path:version) = do
  Zoo.delete zh path (intVersion version)

intVersion :: [String] -> Int

intVersion [] = 0
intVersion [v] = read v
