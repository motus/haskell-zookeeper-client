
{-# LANGUAGE ForeignFunctionInterface #-}

module Zookeeper (
  init, close,
  recvTimeout, state, isUnrecoverable, setDebugLevel,
  create, delete, exists, get, getChildren, set,
  getAcl, setAcl,
  defaultCreateMode, createAcl,
  WatcherFunc, State(..), Watch(..), LogLevel(..), ZooError(..),
  EventType(..), CreateMode(..), Acl(..), Acls(..), Stat(..),
  ZHandle(..)) where

import Prelude hiding (init)

import Data.Bits
import Data.Word
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B
import Data.Typeable

import Control.Monad
import Control.Exception

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
                 Session | NotWatching | Unknown Int deriving (Eq, Show)

data Watch = Watch | NoWatch deriving (Eq, Show)

data LogLevel = LogDisabled | LogError | LogWarn | LogInfo | LogDebug
                deriving (Eq, Ord, Show)

data ZooError =
    ErrOk
  | ErrRuntimeInconsistency    String
  | ErrDataInconsistency       String
  | ErrConnectionLoss          String
  | ErrMarshallingError        String
  | ErrUnimplemented           String
  | ErrOperationTimeout        String
  | ErrBadArguments            String
  | ErrInvalidState            String
  | ErrNoNode                  String
  | ErrNoAuth                  String
  | ErrBadVersion              String
  | ErrNoChildrenForEphemerals String
  | ErrNodeExists              String
  | ErrNotEmpty                String
  | ErrSessionExpired          String
  | ErrInvalidCallback         String
  | ErrInvalidAcl              String
  | ErrAuthFailed              String
  | ErrClosing                 String
  | ErrNothing                 String
  | ErrSessionMoved            String
  | ErrCode Int                String
  deriving (Eq, Show, Typeable)

instance Exception ZooError

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

isUnrecoverable   :: ZHandle -> IO Bool
setDebugLevel     :: LogLevel -> IO ()

createAcl   :: String -> String -> Word32 -> Acl

init        :: String -> WatcherFunc -> Int -> IO ZHandle
close       :: ZHandle -> IO ()

recvTimeout :: ZHandle -> IO Int
state       :: ZHandle -> IO State

create      :: ZHandle -> String -> Maybe ByteString ->
               Acls -> CreateMode -> IO String

delete      :: ZHandle -> String -> Int -> IO ()
exists      :: ZHandle -> String -> Watch -> IO (Maybe Stat)
get         :: ZHandle -> String -> Watch -> IO (Maybe ByteString, Stat)
getChildren :: ZHandle -> String -> Watch -> IO [String]
set         :: ZHandle -> String -> Maybe ByteString -> Int -> IO ()

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

foreign import ccall safe
  "zookeeper.h zookeeper_init" zookeeper_init ::
  CString -> FunPtr WatcherImpl -> Int ->
  VoidPtr -> VoidPtr -> Int -> IO (Ptr ZHBlob)

foreign import ccall safe
  "zookeeper_init.h &zookeeper_close" zookeeper_close_ptr ::
  FunPtr (Ptr ZHBlob -> IO ()) -- actually, -> IO Int

foreign import ccall unsafe
  "zookeeper.h zoo_recv_timeout" zoo_recv_timeout ::
  Ptr ZHBlob -> IO Int

foreign import ccall unsafe
  "zookeeper.h zoo_state" zoo_state ::
  Ptr ZHBlob -> IO Int

foreign import ccall safe
  "zookeeper.h zoo_create" zoo_create ::
  Ptr ZHBlob -> CString -> CString -> Int -> Ptr AclsBlob ->
  Int -> CString -> Int -> IO Int

foreign import ccall safe "zookeeper.h &ZOO_OPEN_ACL_UNSAFE"
   zoo_open_acl_unsafe_ptr :: Ptr AclsBlob

foreign import ccall safe "zookeeper.h &ZOO_READ_ACL_UNSAFE"
   zoo_read_acl_unsafe_ptr :: Ptr AclsBlob

foreign import ccall safe "zookeeper.h &ZOO_CREATOR_ALL_ACL"
   zoo_creator_all_ptr :: Ptr AclsBlob

foreign import ccall safe
  "zookeeper.h zoo_delete" zoo_delete ::
  Ptr ZHBlob -> CString -> Int -> IO Int

foreign import ccall safe
  "zookeeper.h zoo_exists" zoo_exists ::
  Ptr ZHBlob -> CString -> Int -> Ptr StatBlob -> IO Int

foreign import ccall safe
  "zookeeper.h zoo_get" zoo_get ::
  Ptr ZHBlob -> CString -> Int -> CString ->
  Ptr Int -> Ptr StatBlob -> IO Int

foreign import ccall safe
  "zookeeper.h zoo_set" zoo_set ::
  Ptr ZHBlob -> CString -> CString -> Int -> Int -> IO Int

foreign import ccall safe
  "zookeeper.h zoo_get_children" zoo_get_children ::
  Ptr ZHBlob -> CString -> Int -> VoidPtr -> IO Int

foreign import ccall safe
  "zookeeper.h zoo_get_acl" zoo_get_acl ::
  Ptr ZHBlob -> CString -> Ptr AclsBlob -> Ptr StatBlob -> IO Int

foreign import ccall safe
  "zookeeper.h zoo_set_acl" zoo_set_acl ::
  Ptr ZHBlob -> CString -> Int -> Ptr AclsBlob -> IO Int

foreign import ccall unsafe
  "zookeeper.h is_unrecoverable" is_unrecoverable ::
  Ptr ZHBlob -> IO Int

foreign import ccall unsafe
  "zookeeper.h zoo_set_debug_level" zoo_set_debug_level ::
  Int -> IO ()

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
zooEvent code                           = Unknown code

zooError _ (#const ZOK                     ) = return ()
zooError s (#const ZRUNTIMEINCONSISTENCY   ) = throw $ ErrRuntimeInconsistency    s
zooError s (#const ZDATAINCONSISTENCY      ) = throw $ ErrDataInconsistency       s
zooError s (#const ZCONNECTIONLOSS         ) = throw $ ErrConnectionLoss          s
zooError s (#const ZMARSHALLINGERROR       ) = throw $ ErrMarshallingError        s
zooError s (#const ZUNIMPLEMENTED          ) = throw $ ErrUnimplemented           s
zooError s (#const ZOPERATIONTIMEOUT       ) = throw $ ErrOperationTimeout        s
zooError s (#const ZBADARGUMENTS           ) = throw $ ErrBadArguments            s
zooError s (#const ZINVALIDSTATE           ) = throw $ ErrInvalidState            s
zooError s (#const ZNONODE                 ) = throw $ ErrNoNode                  s
zooError s (#const ZNOAUTH                 ) = throw $ ErrNoAuth                  s
zooError s (#const ZBADVERSION             ) = throw $ ErrBadVersion              s
zooError s (#const ZNOCHILDRENFOREPHEMERALS) = throw $ ErrNoChildrenForEphemerals s
zooError s (#const ZNODEEXISTS             ) = throw $ ErrNodeExists              s
zooError s (#const ZNOTEMPTY               ) = throw $ ErrNotEmpty                s
zooError s (#const ZSESSIONEXPIRED         ) = throw $ ErrSessionExpired          s
zooError s (#const ZINVALIDCALLBACK        ) = throw $ ErrInvalidCallback         s
zooError s (#const ZINVALIDACL             ) = throw $ ErrInvalidAcl              s
zooError s (#const ZAUTHFAILED             ) = throw $ ErrAuthFailed              s
zooError s (#const ZCLOSING                ) = throw $ ErrClosing                 s
zooError s (#const ZNOTHING                ) = throw $ ErrNothing                 s
zooError s (#const ZSESSIONMOVED           ) = throw $ ErrSessionMoved            s

zooError s errno | errno > 0 = throwErrno s
                 | otherwise = throw $ ErrCode errno s

checkError msg io = io >>= zooError msg

checkErrorIs code msg io = io >>= check msg
  where check _ (#const ZOK) = return False
        check msg err | err == code = return True
                      | otherwise   = zooError msg err >> return True

zooLogLevel LogDisabled = 0
zooLogLevel LogError    = (#const ZOO_LOG_LEVEL_ERROR)
zooLogLevel LogWarn     = (#const ZOO_LOG_LEVEL_WARN )
zooLogLevel LogInfo     = (#const ZOO_LOG_LEVEL_INFO )
zooLogLevel LogDebug    = (#const ZOO_LOG_LEVEL_DEBUG)

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
withMaybeCStringLen (Just str) func = B.useAsCStringLen str func

packMaybeCStringLen buf len
  | len == maxBound || len < 0 = return Nothing
  | otherwise = liftM Just $ B.packCStringLen (buf, len)

watchFlag Watch   = 1
watchFlag NoWatch = 0

pathBufferSize   =  1024
valueBufferSize  = 20480
stringVectorSize =  1024
aclsVectorSize   =    64

-- Implementation of exported functions:

defaultCreateMode = CreateMode True False

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

init host watcher timeout =
  withCString host (\csHost -> do
    watcherPtr <- wrapWatcher watcher
    zh <- throwErrnoIfNull ("init: " ++ host) $
      zookeeper_init csHost watcherPtr timeout nullPtr nullPtr 0
    newForeignPtr zookeeper_close_ptr zh)

close = finalizeForeignPtr

recvTimeout zh = withForeignPtr zh zoo_recv_timeout

state zh = liftM zooState $ withForeignPtr zh zoo_state

isUnrecoverable zh = checkErrorIs (#const ZINVALIDSTATE)
  "is_unrecoverable" (withForeignPtr zh is_unrecoverable)

setDebugLevel = zoo_set_debug_level . zooLogLevel

create zh path value acl flags =
  withForeignPtr zh (\zhPtr ->
    withCString path (\pathPtr ->
      withAclVector acl (\aclPtr ->
        withMaybeCStringLen value (\(valuePtr, valueLen) ->
          allocaBytes pathBufferSize (\buf -> do
            checkError ("create: " ++ path) $
              zoo_create zhPtr pathPtr valuePtr valueLen
                aclPtr (createModeInt flags) buf pathBufferSize
            peekCString buf)))))

delete zh path version =
  checkError ("delete: " ++ path) $
    withForeignPtr zh (\zhPtr ->
      withCString path (\pathPtr ->
        zoo_delete zhPtr pathPtr version))

exists zh path watch =
  withForeignPtr zh (\zhPtr ->
    withCString path (\pathPtr ->
      allocaBytes (#size struct Stat) (\statPtr -> do
        err <- checkErrorIs (#const ZNONODE) ("exists: " ++ path) $
                 zoo_exists zhPtr pathPtr (watchFlag watch) statPtr
        getStat err statPtr)))
  where getStat False ptr = liftM Just $ copyStat ptr
        getStat _ _       = return Nothing

get zh path watch =
  withForeignPtr zh (\zhPtr ->
    withCString path (\pathPtr ->
      alloca (\bufLen ->
        allocaBytes valueBufferSize (\buf ->
          allocaBytes (#size struct Stat) (\statPtr -> do
            poke bufLen valueBufferSize
            checkError ("get: " ++ path) $
              zoo_get zhPtr pathPtr (watchFlag watch) buf bufLen statPtr
            stat <- copyStat statPtr
            maybeBuf <- peek bufLen >>= packMaybeCStringLen buf
            return (maybeBuf, stat))))))

getChildren zh path watch =
  withForeignPtr zh (\zhPtr ->
    withCString path (\pathPtr ->
      allocaBytes (#size struct String_vector) (\vecPtr ->
        allocaBytes (stringVectorSize * (#size char*)) (\stringsPtr -> do
          (#poke struct String_vector, count) vecPtr stringVectorSize
          (#poke struct String_vector, data ) vecPtr stringsPtr
          checkError ("get_children: " ++ path) $
            zoo_get_children zhPtr pathPtr (watchFlag watch) vecPtr
          copyStringVec vecPtr))))

set zh path value version =
  withForeignPtr zh (\zhPtr ->
    withCString path (\pathPtr ->
      withMaybeCStringLen value (\(valuePtr, valueLen) ->
        checkError ("set: " ++ path) $
          zoo_set zhPtr pathPtr valuePtr valueLen version)))

getAcl zh path =
  withForeignPtr zh (\zhPtr ->
    withCString path (\pathPtr ->
      allocaBytes (#size struct ACL_vector) (\aclsPtr ->
        allocaBytes (aclsVectorSize * (#size struct ACL)) (\aclsData ->
          allocaBytes (#size struct Stat) (\statPtr -> do
            (#poke struct ACL_vector, count) aclsPtr aclsVectorSize
            (#poke struct ACL_vector, data ) aclsPtr aclsData
            checkError ("get_acl: " ++ path) $
              zoo_get_acl zhPtr pathPtr aclsPtr statPtr
            acls <- copyAclVec aclsPtr
            stat <- copyStat statPtr
            return (acls, stat))))))

setAcl zh path version acls =
  withForeignPtr zh (\zhPtr ->
    withCString path (\pathPtr ->
      withAclVector acls (\aclsPtr ->
        checkError ("set_acl: " ++ path) $
          zoo_set_acl zhPtr pathPtr version aclsPtr)))
