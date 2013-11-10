-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides a simple monad to encapsulate error
-- messages within the 'Q' monad.

module Libraries.Template.ErrorMsgQ where

import Language.Haskell.TH

-- | Shortcut for 'Either String a'.
type ErrMsg a = Either String a

-- | Type for the monad encapsulating error messages.
data ErrMsgQ a = ErrMsgQ (Q (ErrMsg a))

instance Monad ErrMsgQ where
    return x = ErrMsgQ $ return $ return x
    (>>=) (ErrMsgQ x) f = ErrMsgQ $ do
              x' <- x
              case x' of 
                 Left s -> return (Left s)
                 Right r -> let (ErrMsgQ y) = f r in y


-- | Set an error message, to be thrown.
-- Usage:                 
--                  
-- > errorMsg "an error happened"                 
errorMsg :: String -> ErrMsgQ a
errorMsg s = ErrMsgQ (return (Left s))

-- | Make a 'Q' computation error-message aware.
embedQ :: Q a -> ErrMsgQ a
embedQ x = ErrMsgQ $ do x' <- x; return (return x')

-- | Throw the error that has been created, using the given string as
-- a prefix. Usage:
-- 
-- > extractQ "name of function: " $ do
-- >   <<commands that may thow an error>>
extractQ :: String -> ErrMsgQ a -> Q a
extractQ prefix (ErrMsgQ x) = 
  do
    x' <- x
    case x' of
      Left s -> error (prefix ++ s)
      Right x -> return x


