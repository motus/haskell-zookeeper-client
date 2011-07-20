module Paths_zookeeper (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName
  ) where

import Data.Version (Version(..))
import System.Environment (getEnv)

version :: Version
version = Version {versionBranch = [0,0,1], versionTags = []}

bindir, libdir, datadir, libexecdir :: FilePath

bindir     = "/home/tsuraan/.cabal/bin"
libdir     = "/home/tsuraan/.cabal/lib/zookeeper-0.0.1/ghc-6.12.3"
datadir    = "/home/tsuraan/.cabal/share/zookeeper-0.0.1"
libexecdir = "/home/tsuraan/.cabal/libexec"

getBinDir, getLibDir, getDataDir, getLibexecDir :: IO FilePath
getBinDir = catch (getEnv "zookeeper_bindir") (\_ -> return bindir)
getLibDir = catch (getEnv "zookeeper_libdir") (\_ -> return libdir)
getDataDir = catch (getEnv "zookeeper_datadir") (\_ -> return datadir)
getLibexecDir = catch (getEnv "zookeeper_libexecdir") (\_ -> return libexecdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
