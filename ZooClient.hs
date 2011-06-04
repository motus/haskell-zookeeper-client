
module Main where

import qualified Zookeeper as Zoo

main = do
  zh   <- Zoo.init "localhost:3181" nullWatcher 10000
  path <- Zoo.create zh "/xyz" (Just "value")
          Zoo.OpenAclUnsafe Zoo.defaultCreateMode
  val  <- Zoo.get zh "/xyz" Zoo.NoWatch
  putStrLn val
  -- Zoo.close zh
  where nullWatcher zh zEventType zState path = putStrLn path

