
{-# LANGUAGE ForeignFunctionInterface #-}

module Zookeeper (
  init, close,
  recvTimeout, state,
  create, delete, get,
  defaultCreateMode,
  WatcherFunc, State(..), Watch(..), EventType(..),
  CreateMode(..), Acl(..), Acls(..), Stat(..)) where

import Prelude hiding (init)

import Data.Bits
import Data.Word

import Foreign
import Foreign.C.Types
import Foreign.C.Error
import Foreign.C.String

-- Exported data types:

data ZHBlob   = ZHBlob
type ZHandle  = ForeignPtr ZHBlob

data VoidBlob = VoidBlob -- C pointer placeholder
type VoidPtr  = Ptr VoidBlob

data State = ExpiredSession | AuthFailed | Connecting |
             Associating | Connected deriving (Show)

data EventType = Created | Deleted | Changed | Child |
                 Session | NotWatching

data Watch = Watch | NoWatch deriving (Show)

data CreateMode = CreateMode {
  create_ephemeral :: Bool,
  create_sequence  :: Bool
}

data Acl = Acl {
  acl_scheme :: String,
  acl_id     :: String,
  acl_read   :: Bool,
  acl_write  :: Bool,
  acl_create :: Bool,
  acl_delete :: Bool,
  acl_admin  :: Bool,
  acl_all    :: Bool
}

data Acls = OpenAclUnsafe | ReadAclUnsafe | CreatorAllAcl | AclList [Acl]

data AclsBlob = AclsBlob

data Stat = Stat {
  stat_czxid          :: Word64,
  stat_mzxid          :: Word64,
  stat_ctime          :: Word64,
  stat_mtime          :: Word64,
  stat_version        :: Word32,
  stat_cversion       :: Word32,
  stat_aversion       :: Word32,
  stat_ephemeralOwner :: Word64,
  stat_dataLength     :: Word32,
  stat_numChildren    :: Word32,
  stat_pzxid          :: Word64
}

type WatcherImpl = Ptr ZHBlob -> Int -> Int -> CString -> VoidPtr -> IO ()
type WatcherFunc = ZHandle -> EventType -> State -> String -> IO ()

-- Exported interface:

defaultCreateMode :: CreateMode

init  :: String -> WatcherFunc -> Int -> IO ZHandle
close :: ZHandle -> IO ()

recvTimeout :: ZHandle -> IO Int
state       :: ZHandle -> IO State

create :: ZHandle -> String -> Maybe String ->
          Acls -> CreateMode -> IO String

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
  Ptr ZHBlob -> CString -> CString -> Int -> Ptr AclsBlob ->
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

bitOr True val res = val .|. res
bitOr False _  res = res

createModeInt (CreateMode create_ephemeral create_sequence) =
  bitOr create_ephemeral (#const ZOO_EPHEMERAL) $
  bitOr create_sequence  (#const ZOO_SEQUENCE ) 0

aclPermsInt :: Acl -> Word32
aclPermsInt (Acl acl_scheme acl_id acl_read acl_write
             acl_create acl_delete acl_admin acl_all) =
  bitOr acl_read   (#const ZOO_PERM_READ  ) $
  bitOr acl_write  (#const ZOO_PERM_WRITE ) $
  bitOr acl_create (#const ZOO_PERM_CREATE) $
  bitOr acl_delete (#const ZOO_PERM_DELETE) $
  bitOr acl_admin  (#const ZOO_PERM_ADMIN ) $
  bitOr acl_all    (#const ZOO_PERM_ALL   ) 0

--withAclVector OpenAclUnsafe func = func (#const ZOO_OPEN_ACL_UNSAFE)
--withAclVector ReadAclUnsafe func = func (#const ZOO_READ_ACL_UNSAFE)
--withAclVector CreatorAllAcl func = func (#const ZOO_CREATOR_ALL_ACL)

withAclVector (AclList acls) func =
  allocaBytes (#size struct ACL_vector) (\avPtr -> do
    (#poke struct ACL_vector, count) avPtr len
    allocaBytes (len * (#size struct ACL)) (\aclPtr ->
      copyAcls acls aclPtr aclPtr func))
  where len = length acls
        copyAcls [] base _ func = func base
        copyAcls (acl:rest) base ptr func =
          withCString (acl_scheme acl) (\schemePtr ->
            withCString (acl_id acl) (\idPtr -> do
              (#poke struct ACL, perms    ) ptr (aclPermsInt acl)
              (#poke struct ACL, id.scheme) ptr schemePtr
              (#poke struct ACL, id.id    ) ptr idPtr
              copyAcls rest base (plusPtr ptr (#size struct ACL)) func))

withMaybeCStringLen Nothing    func = func (nullPtr, -1)
withMaybeCStringLen (Just str) func = withCStringLen str func

watchFlag Watch   = 1
watchFlag NoWatch = 0

pathBufferSize  = 1024
valueBufferSize = 2048

-- Implementation of exported functions:

defaultCreateMode = CreateMode True False

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

create zh path value acl flags = do
  (_, newPath) <- throwErrnoIf ((/=0) . fst) ("create: " ++ path) $
    withForeignPtr zh (\zhPtr ->
      withCString path (\pathPtr ->
        withAclVector acl (\aclPtr ->
          withMaybeCStringLen value (\(valuePtr, valueLen) ->
            allocaBytes pathBufferSize (\buf -> do
              err <- zoo_create zhPtr pathPtr valuePtr valueLen
                       aclPtr (createModeInt flags) buf pathBufferSize
              bufStr <- peekCString buf
              return (err, bufStr))))))
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

