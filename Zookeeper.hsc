
{-# LANGUAGE ForeignFunctionInterface #-}

module Zookeeper (zInit, zClose, WatcherFunc) where

import Foreign
import Foreign.C.Types
import Foreign.C.Error
import Foreign.C.String

-- Exported data types:

data ZHBlob   = ZHBlob
data VoidBlob = VoidBlob -- C pointer placeholder

type ZHandle = ForeignPtr ZHBlob
type VoidPtr = Ptr VoidBlob

type WatcherImpl = Ptr ZHBlob -> Int -> Int -> CString -> VoidPtr -> IO ()
type WatcherFunc = ZHandle -> Int -> Int -> String -> IO ()

-- Exported interface:

zInit  :: String -> WatcherFunc -> Int -> IO ZHandle
zClose :: ZHandle -> IO () -- FIXME: IO Int

-- C functions:

#include <zookeeper.h>

foreign import ccall unsafe
  "zookeeper.h zookeeper_init" zookeeper_init ::
  CString -> FunPtr WatcherImpl -> Int -> 
  VoidPtr -> VoidPtr -> Int -> IO (Ptr ZHBlob)

foreign import ccall unsafe
  "zookeeper_init.h &zookeeper_close" zookeeper_close_ptr ::
  FunPtr (Ptr ZHBlob -> IO ()) -- FIXME: IO Int

foreign import ccall unsafe
  "zookeeper.h zookeeper_close" zookeeper_close ::
  Ptr ZHBlob -> IO () -- FIXME: IO Int
  
foreign import ccall "wrapper"
  wrapWatcherImpl :: WatcherImpl -> IO (FunPtr WatcherImpl)

-- Internal functions:

wrapWatcher func =
  wrapWatcherImpl (\zhBlob zType zState csPath _ = do
    path <- peekCString csPath
    zh <- newForeignPtr_ zhBlob
    func zh zType zState path)

-- Implementation of exported functions:

zInit host watcher timeout =
  withCString host (\csHost -> do
    watcherPtr <- wrapWatcher watcher
    zh <- throwErrnoIfNull
      ("zInit: " ++ host)
      (zookeeper_init csHost watcherPtr timeout nullPtr nullPtr 0)
    newForeignPtr zookeeper_close_ptr zh)

zClose = finalizeForeignPtr

