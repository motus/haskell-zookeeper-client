
{-# LANGUAGE ForeignFunctionInterface #-}

module Zookeeper (
  init, close,
  recvTimeout, state,
  create, delete, get, getChildren, set,
  getAcl, setAcl,
  defaultCreateMode,
  WatcherFunc, State(..), Watch(..), EventType(..),
  CreateMode(..), Acl(..), Acls(..), Stat(..)) where

import Prelude hiding (init)

import Data.Bits
import Data.Word
import Control.Monad

import Foreign
import Foreign.C.Types
import Foreign.C.Error
import Foreign.C.String

-- Exported data types:

data ZHBlob  = ZHBlob
type ZHandle = ForeignPtr ZHBlob

data State = ExpiredSession | AuthFailed | Connecting |
             Associating | Connected deriving (Eq, Show)

data EventType = Created | Deleted | Changed | Child |
                 Session | NotWatching deriving (Eq, Show)

data Watch = Watch | NoWatch deriving (Eq, Show)

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
} deriving (Eq, Show)

data Acls = OpenAclUnsafe | ReadAclUnsafe | CreatorAllAcl |
            AclList [Acl] deriving (Eq, Show)

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
} deriving (Show)

type WatcherImpl = Ptr ZHBlob -> Int -> Int -> CString -> VoidPtr -> IO ()
type WatcherFunc = ZHandle -> EventType -> State -> String -> IO ()

-- Exported interface:

defaultCreateMode :: CreateMode

init        :: String -> WatcherFunc -> Int -> IO ZHandle
close       :: ZHandle -> IO ()

recvTimeout :: ZHandle -> IO Int
state       :: ZHandle -> IO State

create      :: ZHandle -> String -> Maybe String ->
               Acls -> CreateMode -> IO String

delete      :: ZHandle -> String -> Int -> IO ()
get         :: ZHandle -> String -> Watch -> IO (String, Stat)
getChildren :: ZHandle -> String -> Watch -> IO [String]
set         :: ZHandle -> String -> Maybe String -> Int -> IO ()

getAcl      :: ZHandle -> String -> IO (Acls, Stat)
setAcl      :: ZHandle -> String -> Int -> Acls -> IO ()

-- C functions:

data VoidBlob = VoidBlob -- C pointer placeholder
type VoidPtr  = Ptr VoidBlob

data AclsBlob = AclsBlob
data StatBlob = StatBlob

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

foreign import ccall safe "zookeeper.h &ZOO_OPEN_ACL_UNSAFE"
   zoo_open_acl_unsafe_ptr :: Ptr AclsBlob

foreign import ccall safe "zookeeper.h &ZOO_READ_ACL_UNSAFE"
   zoo_read_acl_unsafe_ptr :: Ptr AclsBlob

foreign import ccall safe "zookeeper.h &ZOO_CREATOR_ALL_ACL"
   zoo_creator_all_ptr :: Ptr AclsBlob

foreign import ccall unsafe
  "zookeeper.h zoo_delete" zoo_delete ::
  Ptr ZHBlob -> CString -> Int -> IO Int

foreign import ccall unsafe
  "zookeeper.h zoo_get" zoo_get ::
  Ptr ZHBlob -> CString -> Int -> CString ->
  Ptr Int -> Ptr StatBlob -> IO Int

foreign import ccall unsafe
  "zookeeper.h zoo_set" zoo_set ::
  Ptr ZHBlob -> CString -> CString -> Int -> Int -> IO Int

foreign import ccall unsafe
  "zookeeper.h zoo_get_children" zoo_get_children ::
  Ptr ZHBlob -> CString -> Int -> VoidPtr -> IO Int

foreign import ccall unsafe
  "zookeeper.h zoo_get_acl" zoo_get_acl ::
  Ptr ZHBlob -> CString -> Ptr AclsBlob -> Ptr StatBlob -> IO Int

foreign import ccall unsafe
  "zookeeper.h zoo_set_acl" zoo_set_acl ::
  Ptr ZHBlob -> CString -> Int -> Ptr AclsBlob -> IO Int

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

createAcl :: String -> String -> Word32 -> Acl
createAcl aclScheme aclId flags = Acl {
  acl_scheme = aclScheme,
  acl_id     = aclId,
  acl_read   = flags .&. (#const ZOO_PERM_READ  ) /= 0,
  acl_write  = flags .&. (#const ZOO_PERM_WRITE ) /= 0,
  acl_create = flags .&. (#const ZOO_PERM_CREATE) /= 0,
  acl_delete = flags .&. (#const ZOO_PERM_DELETE) /= 0,
  acl_admin  = flags .&. (#const ZOO_PERM_ADMIN ) /= 0,
  acl_all    = flags .&. (#const ZOO_PERM_ALL   ) /= 0
}

withAclVector OpenAclUnsafe func = func zoo_open_acl_unsafe_ptr
withAclVector ReadAclUnsafe func = func zoo_read_acl_unsafe_ptr
withAclVector CreatorAllAcl func = func zoo_creator_all_ptr

withAclVector (AclList acls) func =
  allocaBytes (#size struct ACL_vector) (\avPtr -> do
    (#poke struct ACL_vector, count) avPtr len
    allocaBytes (len * (#size struct ACL)) (\aclPtr ->
      writeAcls acls aclPtr aclPtr func))
  where len = length acls
        writeAcls [] base _ func = func base
        writeAcls (acl:rest) base ptr func =
          withCString (acl_scheme acl) (\schemePtr ->
            withCString (acl_id acl) (\idPtr -> do
              (#poke struct ACL, perms    ) ptr (aclPermsInt acl)
              (#poke struct ACL, id.scheme) ptr schemePtr
              (#poke struct ACL, id.id    ) ptr idPtr
              writeAcls rest base (plusPtr ptr (#size struct ACL)) func))

copyAclVec avPtr = do
  len  <- (#peek struct ACL_vector, count) avPtr
  vec  <- (#peek struct ACL_vector, data ) avPtr
  acls <- mapM (copyAcl . plusPtr vec . (* #size struct ACL)) [0..len-1]
  return $ AclList acls

copyAcl ptr = do
  perms  <- (#peek struct ACL, perms    ) ptr
  scheme <- (#peek struct ACL, id.scheme) ptr >>= peekCString
  idStr  <- (#peek struct ACL, id.id    ) ptr >>= peekCString
  return $ createAcl scheme idStr perms

copyStat stat = do
  stat_czxid          <- (#peek struct Stat, czxid         ) stat
  stat_mzxid          <- (#peek struct Stat, mzxid         ) stat
  stat_ctime          <- (#peek struct Stat, ctime         ) stat
  stat_mtime          <- (#peek struct Stat, mtime         ) stat
  stat_version        <- (#peek struct Stat, version       ) stat
  stat_cversion       <- (#peek struct Stat, cversion      ) stat
  stat_aversion       <- (#peek struct Stat, aversion      ) stat
  stat_ephemeralOwner <- (#peek struct Stat, ephemeralOwner) stat
  stat_dataLength     <- (#peek struct Stat, dataLength    ) stat
  stat_numChildren    <- (#peek struct Stat, numChildren   ) stat
  stat_pzxid          <- (#peek struct Stat, pzxid         ) stat
  return (Stat stat_czxid stat_mzxid stat_ctime stat_mtime
    stat_version stat_cversion stat_aversion
    stat_ephemeralOwner stat_dataLength stat_numChildren stat_pzxid)

copyStringVec bufPtr = do
  len <- (#peek struct String_vector, count) bufPtr
  vec <- (#peek struct String_vector, data ) bufPtr
  mapM (peekCString <=< peek . plusPtr vec . (* #size char*)) [0..len-1]

withMaybeCStringLen Nothing    func = func (nullPtr, -1)
withMaybeCStringLen (Just str) func = withCStringLen str func

watchFlag Watch   = 1
watchFlag NoWatch = 0

pathBufferSize   =  1024
valueBufferSize  = 20480
stringVectorSize =  1024
aclsVectorSize   =    64

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
          allocaBytes valueBufferSize (\buf ->
            allocaBytes (#size struct Stat) (\statPtr -> do
              poke bufLen valueBufferSize
              err <- zoo_get zhPtr pathPtr
                       (watchFlag watch) buf bufLen statPtr
              resultLen <- peek bufLen
              bufStr <- peekCStringLen (buf, resultLen)
              stat <- copyStat statPtr
              return (err, (bufStr, stat)))))))
  return val

getChildren zh path watch = do
  (_, val) <- throwErrnoIf ((/=0) . fst) ("get_children: " ++ path) $
    withForeignPtr zh (\zhPtr ->
      withCString path (\pathPtr ->
        allocaBytes (#size struct String_vector) (\vecPtr ->
          allocaBytes (stringVectorSize * (#size char*)) (\stringsPtr -> do
            (#poke struct String_vector, count) vecPtr stringVectorSize
            (#poke struct String_vector, data ) vecPtr stringsPtr
            err <- zoo_get_children zhPtr pathPtr (watchFlag watch) vecPtr
            vec <- copyStringVec vecPtr
            return (err, vec)))))
  return val

set zh path value version =
  throwErrnoIf_ (/=0) ("set: " ++ path) $
    withForeignPtr zh (\zhPtr ->
      withCString path (\pathPtr ->
        withMaybeCStringLen value (\(valuePtr, valueLen) ->
          zoo_set zhPtr pathPtr valuePtr valueLen version)))

getAcl zh path = do
  (_, val) <- throwErrnoIf ((/=0) . fst) ("get_acl: " ++ path) $
    withForeignPtr zh (\zhPtr ->
      withCString path (\pathPtr ->
        allocaBytes (#size struct ACL_vector) (\aclsPtr ->
          allocaBytes (aclsVectorSize * (#size struct ACL)) (\aclsData ->
            allocaBytes (#size struct Stat) (\statPtr -> do
              (#poke struct ACL_vector, count) aclsPtr aclsVectorSize
              (#poke struct ACL_vector, data ) aclsPtr aclsData
              err  <- zoo_get_acl zhPtr pathPtr aclsPtr statPtr
              acls <- copyAclVec aclsPtr
              stat <- copyStat statPtr
              return (err, (acls, stat)))))))
  return val

setAcl zh path version acls =
  throwErrnoIf_ (/=0) ("set_acl: " ++ path) $
    withForeignPtr zh (\zhPtr ->
      withCString path (\pathPtr ->
        withAclVector acls (\aclsPtr ->
          zoo_set_acl zhPtr pathPtr version aclsPtr)))

