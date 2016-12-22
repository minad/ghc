{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE NoImplicitPrelude #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.OverloadedLists
-- Copyright   :  (c) The University of Glasgow 2002
-- License     :  see libraries/base/LICENSE
--
-- Maintainer  :  cvs-ghc@haskell.org
-- Stability   :  internal
-- Portability :  non-portable (GHC Extensions)
--
-- This trustworthy module reexports the `IsList` class which is used by the
-- OverloadedLists extension.  See the
-- <https://ghc.haskell.org/trac/ghc/wiki/OverloadedLists>
-- for more details.
--
-----------------------------------------------------------------------------

module GHC.OverloadedLists
       (
        -- * Overloaded lists
        IsList(..)
       ) where

import GHC.Exts
