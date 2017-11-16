{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
-- | The Futhark basis library embedded embedded as strings read during
-- compilation of the Futhark compiler.  The advantage is that the
-- standard library can be accessed without reading it from disk, thus
-- saving users from include path headaches.
module Language.Futhark.Futlib (futlib) where

import Data.FileEmbed
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import System.FilePath

-- | Futlib embedded as 'T.Text' values, one for every file.
futlib :: [(FilePath, T.Text)]
futlib = map fixup futlib_bs
  where futlib_bs = $(embedDir "futlib")
        fixup (path, s) = ("/futlib" </> path, T.decodeUtf8 s)
