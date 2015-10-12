{-# OPTIONS_GHC -Wall        #-}
{-# LANGUAGE OverloadedLists #-}

module T9951a where

f :: [a] -> ()
f x = case x of
  [] -> ()
  (_:_) -> ()

