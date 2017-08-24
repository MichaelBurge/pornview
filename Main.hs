{-# LANGUAGE DeriveGeneric, FlexibleInstances, MultiParamTypeClasses, StandaloneDeriving, ViewPatterns, ImplicitParams, RankNTypes, OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main where

-- Core data structures and operations generated from PV/Database.v
import qualified Database as DB

-- Standard Haskell libraries
import Data.Aeson
import GHC.Generics
import Data.Csv
import Data.Text
import Prelude
import Data.ByteString.Lazy hiding (putStrLn)

import Network.Wai as W
import Network.Wai.Handler.Warp
import Network.HTTP.Types.Method
import Network.HTTP.Types.Status

deriving instance Generic DB.Ascii0
deriving instance Generic DB.Bool
deriving instance Generic DB.Image
deriving instance Generic DB.ImageDb
deriving instance Generic DB.N
deriving instance Generic DB.Positive
deriving instance Generic DB.String
deriving instance Generic DB.Tree0
deriving instance Generic DB.Z
deriving instance Generic elt => Generic (DB.Tree elt)

instance (Generic elt, FromJSON elt) => FromJSON (DB.Tree elt)
instance (Generic elt, ToJSON elt) => ToJSON (DB.Tree elt)
instance FromJSON DB.Ascii0
instance FromJSON DB.Bool
instance FromJSON DB.Image
instance FromJSON DB.ImageDb
instance FromJSON DB.N
instance FromJSON DB.Positive
instance FromJSON DB.String
instance FromJSON DB.Tree0
instance FromJSON DB.Z
instance ToJSON DB.Ascii0
instance ToJSON DB.Bool
instance ToJSON DB.Image
instance ToJSON DB.ImageDb
instance ToJSON DB.N
instance ToJSON DB.Positive
instance ToJSON DB.String
instance ToJSON DB.Tree0
instance ToJSON DB.Z

type PageT a = (?req :: Request, ?respond :: Response -> IO ResponseReceived) => a -> IO ResponseReceived
type Page = PageT ()

pv_port = 1234

main :: IO ()
main = run pv_port $ \req respond -> let ?req = req ; ?respond = respond in
  case (pathInfo req, requestMethod req) of
    ([], "GET") -> pageIndex ()
    -- (["static", filename], "GET") -> pageStatic
    _ -> putStrLn (show req) >> respond (W.responseLBS status404 [] "???")

pageIndex :: Page
pageIndex _ = pageStatic "index.html"
  
pageStatic :: PageT FilePath
pageStatic filename = ?respond $ W.responseFile status200 [] ("static/" ++ filename) Nothing
