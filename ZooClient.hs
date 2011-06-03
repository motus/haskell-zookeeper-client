
module Main where

import qualified Zookeeper as Zoo

main = do
  zh <- Zoo.init "localhost:3181" nullWatcher 10000
  Zoo.close zh
  where nullWatcher zh zType zState path = putStrLn path


