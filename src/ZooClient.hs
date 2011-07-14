
module Main where

import qualified Zookeeper as Zoo

main :: IO ()

main = do
  zh   <- Zoo.init "localhost:3181" nullWatcher 10000
  path <- Zoo.create zh "/xyz" (Just "value")
          Zoo.OpenAclUnsafe Zoo.defaultCreateMode
  (val, stat) <- Zoo.get zh path Zoo.NoWatch
  print (path, val, stat)
  -- Zoo.close zh
  where nullWatcher _zh _zEventType _zState path = putStrLn path
