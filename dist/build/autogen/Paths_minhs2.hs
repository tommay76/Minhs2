{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -fno-warn-implicit-prelude #-}
module Paths_minhs2 (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/tommay76/.cabal/bin"
libdir     = "/home/tommay76/.cabal/lib/x86_64-linux-ghc-8.0.2/minhs2-0.1.0.0"
dynlibdir  = "/home/tommay76/.cabal/lib/x86_64-linux-ghc-8.0.2"
datadir    = "/home/tommay76/.cabal/share/x86_64-linux-ghc-8.0.2/minhs2-0.1.0.0"
libexecdir = "/home/tommay76/.cabal/libexec"
sysconfdir = "/home/tommay76/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "minhs2_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "minhs2_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "minhs2_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "minhs2_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "minhs2_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "minhs2_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
