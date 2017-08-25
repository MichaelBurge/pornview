{-# LANGUAGE DeriveGeneric, FlexibleInstances, MultiParamTypeClasses, StandaloneDeriving, ViewPatterns, ImplicitParams, RankNTypes, OverloadedStrings, InstanceSigs, BangPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main where

-- Core data structures and operations generated from PV/Database.v
import qualified Database as DB

-- Standard Haskell libraries
import Data.Aeson
import Data.Aeson.Types
import GHC.Generics
import Data.Text as T hiding (foldl')
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TL
import Data.Text.Encoding as T (decodeUtf8)
import Prelude hiding (readFile, writeFile, decode)
import Data.ByteString.Lazy hiding (putStrLn, foldl')
import Data.List
import qualified Data.Map as M
import Control.Concurrent.STM
import Control.Concurrent.STM.TVar
import System.Directory
import System.Posix.Files
import Data.Maybe
import Control.Concurrent.STM
import Data.Monoid

import Network.Wai as W
import Network.Wai.Handler.Warp
import Network.HTTP.Types.Method
import Network.HTTP.Types.Status

deriving instance Generic DB.Bool
deriving instance Generic DB.Image
deriving instance Generic DB.ImageDb
deriving instance Generic DB.N
deriving instance Generic DB.Positive
deriving instance Generic DB.Tree0
deriving instance Generic DB.Z
deriving instance Generic elt => Generic (DB.Tree elt)

instance (Generic elt, FromJSON elt) => FromJSON (DB.Tree elt)
instance (Generic elt, ToJSON elt) => ToJSON (DB.Tree elt)
instance FromJSON DB.Bool
instance FromJSON DB.Image
instance FromJSON DB.ImageDb
instance FromJSON DB.Positive
instance FromJSON DB.Tree0
instance FromJSON DB.Z
instance ToJSON DB.Bool
instance ToJSON DB.Image
instance ToJSON DB.ImageDb
instance ToJSON DB.Positive
instance ToJSON DB.Tree0
instance ToJSON DB.Z

deriving instance Show DB.Image
instance Show DB.N where
  show x = show $ n_to_int x

instance FromJSON DB.N where
  parseJSON x = int_to_n <$> (parseJSON x :: Parser Int)

instance ToJSON DB.N where
  toJSON x = toJSON $ (n_to_int x :: Int)

pv_port = 1234
db_file = "images.db"
collection_dir = "images"

data ServerState = ServerState {
  state_db         :: TVar DB.ImageDb,
  state_categories :: TVar (M.Map String DB.N)
  }

type PageT a = (?state :: ServerState, ?req :: Request, ?respond :: Response -> IO ResponseReceived) => a -> IO ResponseReceived
type Page = PageT ()

main :: IO ()
main = do
  state <- initialize
  run pv_port $ \req respond -> let ?state = state; ?req = req ; ?respond = respond in do
    putStrLn (show req)
    case (pathInfo req, requestMethod req) of
      ([], "GET") -> pageIndex ()
      ("static" : xs, "GET") -> pageStatic $ T.unpack $ T.intercalate "/" xs
      ("images" : imageId : _, "GET") -> pageImage $ param_n imageId
      ("api" : "listCategories" : _, "GET") -> pageListCategories ()
      ("api" : "listImages" : _, "GET") -> pageListImages ()
      ("api" : "tagImage" : imageId : catName : _, "POST") -> pageTagImage (param_n imageId, catName)
      ("api" : "untagImage" : imageId : catName : _, "POST") -> pageUntagImage (param_n imageId, catName)
      _ -> respond (W.responseLBS status404 [] "???")

initialize :: IO ServerState
initialize = do
  db <- loadOrCreate db_file initDb :: IO DB.ImageDb
  ServerState <$> newTVarIO db <*> newTVarIO categories

loadOrCreate :: (FromJSON a, ToJSON a) => FilePath -> (IO a) -> IO a
loadOrCreate filename init = do
  exists <- doesFileExist filename
  if exists
    then fromJust <$> decode <$> readFile filename
    else do
      x <- init
      writeFile filename $ encode x
      return x

-- Database operations
initDb :: IO DB.ImageDb
initDb = do
  images <- readDirectory collection_dir
  return $ foldl' DB.create_image DB.newDb images

-- TODO: Categories should really be managed in Database.v
categories :: M.Map String DB.N
categories = M.fromList $ Prelude.map (\(x, y) -> (x, int_to_n y)) [
  ("Catgirls",    0),
  ("Catboys",     1),
  ("Floor Tiles", 2)
  ]

readDirectory :: String -> IO [DB.Image]
readDirectory dir = do
  filepaths <- Prelude.map (\x -> dir ++ "/" ++ x) <$> listDirectory dir
  mapM readFile filepaths
  where
    readFile :: FilePath -> IO DB.Image
    readFile filepath = do
      timestamp <- modificationTimeHiRes <$> getFileStatus filepath
      return $ DB.MkImage DB.N0 filepath (int_to_n 1)

int_to_n :: Integral a => a -> DB.N
int_to_n x = DB.of_nat $ fromIntegral x

n_to_int :: Integral a => DB.N -> a
n_to_int x = fromIntegral $ DB.to_nat0 x

param_n :: Text -> DB.N
param_n x = case reads $ T.unpack x of
  [(y, "")] -> int_to_n y
  _ -> error $ T.unpack $ "Non-integer param: " <> x

saveDb :: DB.ImageDb -> IO ()
saveDb db = writeFile db_file $ encode db

-- All endpoints

pageIndex :: Page
pageIndex _ = pageStatic "index.html"
  
pageStatic :: PageT FilePath
pageStatic filename = putStrLn filename >> (?respond $ W.responseFile status200 [] ("static/" ++ filename) Nothing)

pageListCategories :: Page
pageListCategories _ = do
  let cats = M.keys categories
  ?respond $ W.responseLBS status200 [] (encode cats)
      
pageListImages :: Page
pageListImages _ = do
  db <- readTVarIO $ state_db ?state
  putStrLn $ show $ queryString ?req
  let catIds = case Data.List.lookup "category" (queryString ?req) of
        Nothing -> []
        Just Nothing -> []
        Just (Just "") -> []
        Just (Just x) -> case M.lookup (T.unpack $ decodeUtf8 x) categories of
          Nothing -> []
          Just catId -> [catId]
  putStrLn $ show $ Prelude.map n_to_int catIds
  let images = DB.find_categories db catIds
  putStrLn $ show images
  ?respond $ W.responseLBS status200 [] (encode images)

pageTagImage :: PageT (DB.ImageId, Text)
pageTagImage (imageId, catName) = case M.lookup (T.unpack catName) categories of
  Nothing -> ?respond $ W.responseLBS status404 [] "{}"
  Just catId -> do
    atomically $ modifyTVar' (state_db ?state) $ \db ->
      DB.tag_image db imageId catId
    saveDb <$> readTVarIO (state_db ?state)
    ?respond $ W.responseLBS status200 [] "{}"
  
pageUntagImage :: PageT (DB.ImageId, Text)
pageUntagImage (imageId, catName) = case M.lookup (T.unpack catName) categories of
  Nothing -> ?respond $ W.responseLBS status404 [] "{}"
  Just catId -> do
    atomically $ modifyTVar' (state_db ?state) $ \db ->
      DB.untag_image db imageId catId
    saveDb <$> readTVarIO (state_db ?state)
    ?respond $ W.responseLBS status200 [] "{}"

pageImage :: PageT DB.ImageId
pageImage imgId = do
  db <- readTVarIO $ state_db ?state
  case DB.find_img db imgId of
    Nothing -> ?respond $ W.responseLBS status404 [] "Image not found"
    Just img -> ?respond $ W.responseFile status200 [] (DB.filename img) Nothing
