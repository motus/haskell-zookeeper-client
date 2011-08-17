{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Zookeeper (
  init, close, setWatcher,
  recvTimeout, state, isUnrecoverable, setDebugLevel,
  create, delete, exists, get, getChildren, set,
  getAcl, setAcl,
  defaultCreateMode, createAcl,
  WatcherFunc, State(..), Watch(..), LogLevel(..), ZooError(..),
  EventType(..), CreateMode(..), Acl(..), Acls(..), Stat(..),
  ZHandle, CBlob(..)) where

import Prelude hiding (init)

import Data.Bits
import Data.Word
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B
import Data.Typeable

import Control.Applicative
import Control.Monad
import Control.Exception
import Control.Concurrent.MVar

import Foreign
import Foreign.C.Types
import Foreign.C.Error
import Foreign.C.String

-- Exported data types:

data CBlob = CBlob

type ZHPtr   = Ptr CBlob
type ZHandleInternal = ForeignPtr CBlob

data ZHandle = ZHandle { zh_ptr          :: ZHandleInternal
                       , zh_value_buffer :: MVar CString
                       }

data State = ExpiredSession
           | AuthFailed
           | Connecting
           | Associating
           | Connected
           | State Int deriving (Eq, Show)

data EventType = Created
               | Deleted
               | Changed
               | Child
               | Session
               | NotWatching
               | Event Int deriving (Eq, Show)

data Watch = Watch | NoWatch deriving (Eq, Show)

data LogLevel = LogDisabled
              | LogError
              | LogWarn
              | LogInfo
              | LogDebug deriving (Eq, Ord, Show)

data ZooError = ErrOk
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
  stat_czxid          :: Int64,
  stat_mzxid          :: Int64,
  stat_ctime          :: Int64,
  stat_mtime          :: Int64,
  stat_version        :: Int32,
  stat_cversion       :: Int32,
  stat_aversion       :: Int32,
  stat_ephemeralOwner :: Int64,
  stat_dataLength     :: Int32,
  stat_numChildren    :: Int32,
  stat_pzxid          :: Int64
} deriving (Show)

type WatcherImpl = ZHPtr -> CInt -> CInt -> CString -> VoidPtr -> IO ()
type WatcherFunc = ZHandle -> EventType -> State -> String -> IO ()

-- C functions:

type VoidPtr = Ptr CBlob
type AclsPtr = Ptr CBlob
type StatPtr = Ptr CBlob

#include <zookeeper.h>

foreign import ccall "wrapper"
  wrapWatcherImpl :: WatcherImpl -> IO (FunPtr WatcherImpl)

foreign import ccall safe
  "zookeeper.h zookeeper_init" zookeeper_init ::
  CString -> FunPtr WatcherImpl -> CInt ->
  VoidPtr -> VoidPtr -> CInt -> IO ZHPtr

foreign import ccall safe
  "zookeeper_init.h &zookeeper_close" zookeeper_close_ptr ::
  FunPtr (ZHPtr -> IO ()) -- actually, -> IO CInt

foreign import ccall unsafe
  "zookeeper.h zoo_recv_timeout" zoo_recv_timeout ::
  ZHPtr -> IO CInt

foreign import ccall unsafe
  "zookeeper.h zoo_state" zoo_state ::
  ZHPtr -> IO CInt

foreign import ccall safe
  "zookeeper.h zoo_set_watcher" zoo_set_watcher ::
  ZHPtr -> FunPtr WatcherImpl -> IO () -- actually, IO (FunPtr WatcherImpl)

foreign import ccall safe
  "zookeeper.h zoo_create" zoo_create ::
  ZHPtr -> CString -> CString -> CInt -> AclsPtr ->
  CInt -> CString -> CInt -> IO CInt

foreign import ccall safe "zookeeper.h &ZOO_OPEN_ACL_UNSAFE"
   zoo_open_acl_unsafe_ptr :: AclsPtr

foreign import ccall safe "zookeeper.h &ZOO_READ_ACL_UNSAFE"
   zoo_read_acl_unsafe_ptr :: AclsPtr

foreign import ccall safe "zookeeper.h &ZOO_CREATOR_ALL_ACL"
   zoo_creator_all_ptr :: AclsPtr

foreign import ccall safe
  "zookeeper.h zoo_delete" zoo_delete ::
  ZHPtr -> CString -> CInt -> IO CInt

foreign import ccall safe
  "zookeeper.h zoo_exists" zoo_exists ::
  ZHPtr -> CString -> CInt -> StatPtr -> IO CInt

foreign import ccall safe
  "zookeeper.h zoo_get" zoo_get ::
  ZHPtr -> CString -> CInt -> CString ->
  Ptr CInt -> StatPtr -> IO CInt

foreign import ccall safe
  "zookeeper.h zoo_set" zoo_set ::
  ZHPtr -> CString -> CString -> CInt -> CInt -> IO CInt

foreign import ccall safe
  "zookeeper.h zoo_get_children" zoo_get_children ::
  ZHPtr -> CString -> CInt -> VoidPtr -> IO CInt

foreign import ccall safe
  "zookeeper.h zoo_get_acl" zoo_get_acl ::
  ZHPtr -> CString -> AclsPtr -> StatPtr -> IO CInt

foreign import ccall safe
  "zookeeper.h zoo_set_acl" zoo_set_acl ::
  ZHPtr -> CString -> CInt -> AclsPtr -> IO CInt

foreign import ccall unsafe
  "zookeeper.h is_unrecoverable" is_unrecoverable ::
  ZHPtr -> IO CInt

foreign import ccall unsafe
  "zookeeper.h zoo_set_debug_level" zoo_set_debug_level ::
  CInt -> IO ()

-- Internal functions:

wrapWatcher :: ZHandle -> WatcherFunc -> IO (FunPtr WatcherImpl)
wrapWatcher zh func = do
  wrapWatcherImpl (\_zhBlob zEventType zState csPath _ctx -> do
    path <- peekCString csPath
    -- zh <- newForeignPtr_ zhBlob
    func zh (zooEvent zEventType) (zooState zState) path)


zooState :: CInt -> State
zooState (#const ZOO_EXPIRED_SESSION_STATE) = ExpiredSession
zooState (#const ZOO_AUTH_FAILED_STATE    ) = AuthFailed
zooState (#const ZOO_CONNECTING_STATE     ) = Connecting
zooState (#const ZOO_ASSOCIATING_STATE    ) = Associating
zooState (#const ZOO_CONNECTED_STATE      ) = Connected
zooState code                               = State $ fromIntegral code

zooEvent :: CInt -> EventType
zooEvent (#const ZOO_CREATED_EVENT    ) = Created
zooEvent (#const ZOO_DELETED_EVENT    ) = Deleted
zooEvent (#const ZOO_CHANGED_EVENT    ) = Changed
zooEvent (#const ZOO_CHILD_EVENT      ) = Child
zooEvent (#const ZOO_SESSION_EVENT    ) = Session
zooEvent (#const ZOO_NOTWATCHING_EVENT) = NotWatching
zooEvent code                           = Event $ fromIntegral code

zooError :: String -> CInt -> IO ()
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
                 | otherwise = throw $ ErrCode (fromIntegral errno) s

checkError :: String -> IO CInt -> IO ()
checkError msg io = io >>= zooError msg

checkErrorIs :: CInt -> String -> IO CInt -> IO Bool
checkErrorIs code msg io = io >>= check
  where check (#const ZOK) = return False
        check err | err == code = return True
                  | otherwise   = zooError msg err >> return True

zooLogLevel :: LogLevel -> CInt
zooLogLevel LogDisabled = 0
zooLogLevel LogError    = (#const ZOO_LOG_LEVEL_ERROR)
zooLogLevel LogWarn     = (#const ZOO_LOG_LEVEL_WARN )
zooLogLevel LogInfo     = (#const ZOO_LOG_LEVEL_INFO )
zooLogLevel LogDebug    = (#const ZOO_LOG_LEVEL_DEBUG)

bitOr :: Bits a => Bool -> a -> a -> a
bitOr True val res = val .|. res
bitOr False _  res = res

createModeInt :: Bits a => CreateMode -> a
createModeInt mode =
  bitOr (create_ephemeral mode) (#const ZOO_EPHEMERAL) $
  bitOr (create_sequence mode) (#const ZOO_SEQUENCE ) 0

aclPermsInt :: Acl -> Int32
aclPermsInt Acl{..} =
  bitOr acl_read  (#const ZOO_PERM_READ  ) $
  bitOr acl_write  (#const ZOO_PERM_WRITE ) $
  bitOr acl_create (#const ZOO_PERM_CREATE) $
  bitOr acl_delete (#const ZOO_PERM_DELETE) $
  bitOr acl_admin (#const ZOO_PERM_ADMIN ) $
  bitOr acl_all   (#const ZOO_PERM_ALL   ) 0

withAclVector :: Acls -> (AclsPtr -> IO b) -> IO b
withAclVector OpenAclUnsafe func = func zoo_open_acl_unsafe_ptr
withAclVector ReadAclUnsafe func = func zoo_read_acl_unsafe_ptr
withAclVector CreatorAllAcl func = func zoo_creator_all_ptr

withAclVector (AclList acls) func =
  allocaBytes (#size struct ACL_vector) (\avPtr -> do
    (#poke struct ACL_vector, count) avPtr len
    allocaBytes (len * (#size struct ACL)) (\aclPtr ->
      writeAcls acls aclPtr aclPtr))
  where len = length acls
        writeAcls [] base _ = func base
        writeAcls (acl:rest) base ptr =
          withCString (acl_scheme acl) (\schemePtr ->
            withCString (acl_id acl) (\idPtr -> do
              (#poke struct ACL, perms    ) ptr (aclPermsInt acl)
              (#poke struct ACL, id.scheme) ptr schemePtr
              (#poke struct ACL, id.id    ) ptr idPtr
              writeAcls rest base (plusPtr ptr (#size struct ACL))))

copyAclVec :: Ptr b -> IO Acls
copyAclVec avPtr = do
  len  <- (#peek struct ACL_vector, count) avPtr
  vec  <- (#peek struct ACL_vector, data ) avPtr
  acls <- mapM (copyAcl . plusPtr vec . (* #size struct ACL)) [0..len-1]
  return $ AclList acls

copyAcl :: Ptr b -> IO Acl
copyAcl ptr = do
  perms  <- (#peek struct ACL, perms    ) ptr
  scheme <- (#peek struct ACL, id.scheme) ptr >>= peekCString
  idStr  <- (#peek struct ACL, id.id    ) ptr >>= peekCString
  return $ createAcl scheme idStr perms

copyStat :: Ptr b -> IO Stat
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
  return $ Stat { stat_czxid, stat_mzxid, stat_ctime, stat_mtime,
                  stat_version, stat_cversion, stat_aversion,
                  stat_ephemeralOwner, stat_dataLength,
                  stat_numChildren, stat_pzxid }

copyStringVec :: Ptr b -> IO [String]
copyStringVec bufPtr = do
  len::CInt <- (#peek struct String_vector, count) bufPtr
  vec <- (#peek struct String_vector, data ) bufPtr
  mapM (peekCString <=< peek . plusPtr vec . (* #size char*) . fromIntegral) [0..len-1]

withMaybeCStringLen :: Maybe ByteString -> (CStringLen -> IO a) -> IO a
withMaybeCStringLen Nothing    func = func (nullPtr, -1)
withMaybeCStringLen (Just str) func = B.useAsCStringLen str func

packMaybeCStringLen :: Ptr CChar -> Int -> IO (Maybe ByteString)
packMaybeCStringLen buf len
  | len < 0 = return Nothing
  | otherwise = liftM Just $ B.packCStringLen (buf, len)

watchFlag :: Watch -> CInt
watchFlag Watch   = 1
watchFlag NoWatch = 0

pathBufferSize :: Int
pathBufferSize = 65536

valueBufferSize :: Int
valueBufferSize = 1048576 -- 1M

stringVectorSize :: Int
stringVectorSize = 1024

aclsVectorSize :: Int
aclsVectorSize = 256

-- Implementation of exported functions:

defaultCreateMode :: CreateMode
defaultCreateMode = CreateMode { create_ephemeral = True
                               , create_sequence  = False
                               }


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


init :: String -> Maybe WatcherFunc -> Int -> IO ZHandle
init host watcher timeout = do
  zh <- withCString host (\csHost -> do
          zhPtr <- throwErrnoIfNull ("init: " ++ host) $
            zookeeper_init csHost nullFunPtr (fromIntegral timeout) nullPtr nullPtr 0
          newForeignPtr zookeeper_close_ptr zhPtr)

  -- allocate a 1MB buffer
  buf <- mallocBytes (fromIntegral valueBufferSize)

  zh' <- ZHandle zh <$> newMVar buf
  setWatcher zh' watcher
  return zh'


setWatcher :: ZHandle -> Maybe WatcherFunc -> IO ()
setWatcher zh Nothing =
  withForeignPtr (zh_ptr zh) (\zhPtr -> zoo_set_watcher zhPtr nullFunPtr)
setWatcher zh (Just watcher) = do
  watcherPtr <- wrapWatcher zh watcher
  withForeignPtr (zh_ptr zh) (\zhPtr -> zoo_set_watcher zhPtr watcherPtr)


close :: ZHandle -> IO ()
close zh = do
    finalizeForeignPtr $ zh_ptr zh
    free =<< readMVar (zh_value_buffer zh)


recvTimeout :: ZHandle -> IO Int
recvTimeout (ZHandle zh _) = fromIntegral <$> withForeignPtr zh zoo_recv_timeout


state :: ZHandle -> IO State
state (ZHandle zh _) = liftM zooState $ withForeignPtr zh zoo_state


isUnrecoverable :: ZHandle -> IO Bool
isUnrecoverable (ZHandle zh _) = checkErrorIs (#const ZINVALIDSTATE)
  "is_unrecoverable" (withForeignPtr zh is_unrecoverable)


setDebugLevel :: LogLevel -> IO ()
setDebugLevel = zoo_set_debug_level . zooLogLevel


create :: ZHandle -> String -> Maybe ByteString ->
          Acls -> CreateMode -> IO String
create (ZHandle zh _) path value acl flags =
  withForeignPtr zh (\zhPtr ->
    withCString path (\pathPtr ->
      withAclVector acl (\aclPtr ->
        withMaybeCStringLen value (\(valuePtr, valueLen) ->
          allocaBytes pathBufferSize (\buf -> do
            checkError ("create: " ++ path) $
              zoo_create zhPtr pathPtr valuePtr (fromIntegral valueLen)
                aclPtr (createModeInt flags) buf (fromIntegral pathBufferSize)
            peekCString buf)))))


delete :: ZHandle -> String -> Int -> IO ()
delete (ZHandle zh _) path version =
  checkError ("delete: " ++ path) $
    withForeignPtr zh (\zhPtr ->
      withCString path (\pathPtr ->
        zoo_delete zhPtr pathPtr (fromIntegral version)))


exists :: ZHandle -> String -> Watch -> IO (Maybe Stat)
exists (ZHandle zh _) path watch =
  withForeignPtr zh (\zhPtr ->
    withCString path (\pathPtr ->
      allocaBytes (#size struct Stat) (\statPtr -> do
        err <- checkErrorIs (#const ZNONODE) ("exists: " ++ path) $
                 zoo_exists zhPtr pathPtr (watchFlag watch) statPtr
        getStat err statPtr)))
  where getStat False ptr = liftM Just $ copyStat ptr
        getStat _ _       = return Nothing


get :: ZHandle -> String -> Watch -> IO (Maybe ByteString, Stat)
get zh path watch =
  withForeignPtr (zh_ptr zh) (\zhPtr ->
    withCString path (\pathPtr ->
      alloca (\bufLen ->
        withMVar (zh_value_buffer zh) (\buf ->
          allocaBytes (#size struct Stat) (\statPtr -> do
            poke bufLen (fromIntegral valueBufferSize)
            checkError ("get: " ++ path) $
              zoo_get zhPtr pathPtr (watchFlag watch) buf bufLen statPtr
            stat <- copyStat statPtr
            maybeBuf <- peek bufLen >>= packMaybeCStringLen buf . fromIntegral
            return (maybeBuf, stat))))))


getChildren :: ZHandle -> String -> Watch -> IO [String]
getChildren (ZHandle zh _) path watch =
  withForeignPtr zh (\zhPtr ->
    withCString path (\pathPtr ->
      allocaBytes (#size struct String_vector) (\vecPtr ->
        allocaBytes (stringVectorSize * (#size char*)) (\stringsPtr -> do
          (#poke struct String_vector, count) vecPtr stringVectorSize
          (#poke struct String_vector, data ) vecPtr stringsPtr
          checkError ("get_children: " ++ path) $
            zoo_get_children zhPtr pathPtr (watchFlag watch) vecPtr
          copyStringVec vecPtr))))


set :: ZHandle -> String -> Maybe ByteString -> Int -> IO ()
set (ZHandle zh _) path value version =
  withForeignPtr zh (\zhPtr ->
    withCString path (\pathPtr ->
      withMaybeCStringLen value (\(valuePtr, valueLen) ->
        checkError ("set: " ++ path) $
          zoo_set zhPtr pathPtr valuePtr (fromIntegral valueLen) (fromIntegral version))))


getAcl :: ZHandle -> String -> IO (Acls, Stat)
getAcl (ZHandle zh _) path =
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


setAcl :: ZHandle -> String -> Int -> Acls -> IO ()
setAcl (ZHandle zh _) path version acls =
  withForeignPtr zh (\zhPtr ->
    withCString path (\pathPtr ->
      withAclVector acls (\aclsPtr ->
        checkError ("set_acl: " ++ path) $
          zoo_set_acl zhPtr pathPtr (fromIntegral version) aclsPtr)))
