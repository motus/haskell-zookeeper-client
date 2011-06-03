
{-# LANGUAGE ForeignFunctionInterface #-}

module Zookeeper (
  init, close,
  recvTimeout, state,
  create, delete, get,
  WatcherFunc, State(..), Watch(..)) where

import Prelude hiding (init)

import Foreign
import Foreign.C.Types
import Foreign.C.Error
import Foreign.C.String

-- Exported data types:

data ZHBlob   = ZHBlob
data VoidBlob = VoidBlob -- C pointer placeholder

type ZHandle = ForeignPtr ZHBlob
type VoidPtr = Ptr VoidBlob

data State = ExpiredSession | AuthFailed | Connecting |
             Associating | Connected deriving (Show)

data EventType = Created | Deleted | Changed | Child |
                 Session | NotWatching

data Watch = Watch | NoWatch deriving (Show)

type WatcherImpl = Ptr ZHBlob -> Int -> Int -> CString -> VoidPtr -> IO ()
type WatcherFunc = ZHandle -> EventType -> State -> String -> IO ()

-- Exported interface:

init  :: String -> WatcherFunc -> Int -> IO ZHandle
close :: ZHandle -> IO ()

recvTimeout :: ZHandle -> IO Int
state       :: ZHandle -> IO State

create :: ZHandle -> String -> String -> Int -> IO String
delete :: ZHandle -> String -> Int -> IO ()
get    :: ZHandle -> String -> Watch -> IO String

-- C functions:

#include <zookeeper.h>

foreign import ccall "wrapper"
  wrapWatcherImpl :: WatcherImpl -> IO (FunPtr WatcherImpl)

foreign import ccall unsafe
  "zookeeper.h zookeeper_init" zookeeper_init ::
  CString -> FunPtr WatcherImpl -> Int ->
  VoidPtr -> VoidPtr -> Int -> IO (Ptr ZHBlob)

foreign import ccall unsafe
  "zookeeper_init.h &zookeeper_close" zookeeper_close_ptr ::
  FunPtr (Ptr ZHBlob -> IO ()) -- FIXME: IO Int

foreign import ccall unsafe
  "zookeeper.h zookeeper_close" zookeeper_close ::
  Ptr ZHBlob -> IO Int

foreign import ccall unsafe
  "zookeeper.h zoo_recv_timeout" zoo_recv_timeout ::
  Ptr ZHBlob -> IO Int

foreign import ccall unsafe
  "zookeeper.h zoo_state" zoo_state ::
  Ptr ZHBlob -> IO Int

foreign import ccall unsafe
  "zookeeper.h zoo_create" zoo_create ::
  Ptr ZHBlob -> CString -> CString -> Int -> VoidPtr -> -- ACL_vector
  Int -> CString -> Int -> IO Int

foreign import ccall unsafe
  "zookeeper.h zoo_delete" zoo_delete ::
  Ptr ZHBlob -> CString -> Int -> IO Int

foreign import ccall unsafe
  "zookeeper.h zoo_get" zoo_get ::
  Ptr ZHBlob -> CString -> Int -> CString -> Ptr Int -> VoidPtr -> IO Int

-- Internal functions:

wrapWatcher func =
  wrapWatcherImpl (\zhBlob zEventType zState csPath _ -> do
    path <- peekCString csPath
    zh <- newForeignPtr_ zhBlob
    func zh (zooEvent zEventType) (zooState zState) path)

zooState (#const ZOO_EXPIRED_SESSION_STATE) = ExpiredSession
zooState (#const ZOO_AUTH_FAILED_STATE    ) = AuthFailed
zooState (#const ZOO_CONNECTING_STATE     ) = Connecting
zooState (#const ZOO_ASSOCIATING_STATE    ) = Associating
zooState (#const ZOO_CONNECTED_STATE      ) = Connected

zooEvent (#const ZOO_CREATED_EVENT    ) = Created
zooEvent (#const ZOO_DELETED_EVENT    ) = Deleted
zooEvent (#const ZOO_CHANGED_EVENT    ) = Changed
zooEvent (#const ZOO_CHILD_EVENT      ) = Child
zooEvent (#const ZOO_SESSION_EVENT    ) = Session
zooEvent (#const ZOO_NOTWATCHING_EVENT) = NotWatching

watchFlag Watch   = 1
watchFlag NoWatch = 0

pathBufferSize  = 1024
valueBufferSize = 2048

-- Implementation of exported functions:

init host watcher timeout =
  withCString host (\csHost -> do
    watcherPtr <- wrapWatcher watcher
    zh <- throwErrnoIfNull
      ("init: " ++ host)
      (zookeeper_init csHost watcherPtr timeout nullPtr nullPtr 0)
    newForeignPtr zookeeper_close_ptr zh)

close = finalizeForeignPtr

recvTimeout zh = withForeignPtr zh zoo_recv_timeout

state zh = withForeignPtr zh zoo_state >>= (return . zooState)

create zh path value flags = do
  (_, newPath) <- throwErrnoIf ((/=0) . fst) ("create: " ++ path) $
    withForeignPtr zh (\zhPtr ->
      withCString path (\pathPtr ->
        withCStringLen value (\(valuePtr, valueLen) ->
          allocaBytes pathBufferSize (\buf -> do
            err <- zoo_create zhPtr pathPtr
                     valuePtr valueLen nullPtr flags buf pathBufferSize
            bufStr <- peekCString buf
            return (err, bufStr)))))
  return newPath

delete zh path version =
  throwErrnoIf_ (/=0) ("delete: " ++ path) $
    withForeignPtr zh (\zhPtr ->
      withCString path (\pathPtr ->
        zoo_delete zhPtr pathPtr version))

get zh path watch = do
  (_, val) <- throwErrnoIf ((/=0) . fst) ("get: " ++ path) $
    withForeignPtr zh (\zhPtr ->
      withCString path (\pathPtr ->
        alloca (\bufLen ->
          allocaBytes valueBufferSize (\buf -> do
            poke bufLen valueBufferSize
            err <- zoo_get zhPtr pathPtr (watchFlag watch) buf bufLen nullPtr
            resultLen <- peek bufLen
            bufStr <- peekCStringLen (buf, resultLen)
            return (err, bufStr)))))
  return val

