
module Main where

import qualified Zookeeper as Zoo

main = do
  zh   <- Zoo.init "localhost:3181" nullWatcher 10000
  path <- Zoo.create zh "/xyz" (Just "value")
          Zoo.OpenAclUnsafe Zoo.defaultCreateMode
  (val, stat) <- Zoo.get zh "/xyz" Zoo.NoWatch
  print (val, stat)
  -- Zoo.close zh
  where nullWatcher zh zEventType zState path = putStrLn path

