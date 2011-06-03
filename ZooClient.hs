
module Main where

import qualified Zookeeper as Zoo

main = do
  zh   <- Zoo.init "localhost:3181" nullWatcher 10000
  path <- Zoo.create zh "/xyz" "value" 0
  val  <- Zoo.get zh "/xyz" Zoo.NoWatch
  putStrLn val
  -- Zoo.close zh
  where nullWatcher zh zType zState path = putStrLn path

