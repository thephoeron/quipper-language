-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE CPP #-}

-- | This module provides a thin portability layer for handling user
-- interrupts.
-- 
-- The reason is that in the standard Haskell library, this
-- functionality is only available in operating system specific
-- modules, namely "System.Posix.Signals" (for POSIX systems,
-- including Linux) and "GHC.ConsoleHandler" (for Windows).
-- 
-- Note that despite this compatibility layer, there are some
-- operating system specific quirks:
-- 
-- * In Windows, console events (such as Control-C) can only be
-- received by an application running in a Windows console. Certain
-- environments that look like consoles do not support console events,
-- such as xterm and rxvt windows, and Cygwin shells with @CYGWIN=tty@
-- set.
-- 
-- * In Windows, setting a handler for any one signal automatically
-- overrides the handlers for all signals (effectively ignoring them).
-- Also, if the 'Default' or 'Ignore' handler is specified, it
-- applies to all signals.  We do not currently provide a way to
-- specify handlers for multiple signals.

module Libraries.PortableSignals (
  Signal(..),
  Handler(Default,Ignore,Catch,CatchOnce),
  installHandler,
  with_handler
  ) where

#ifdef mingw32_HOST_OS
import qualified GHC.ConsoleHandler as OS
#else
import qualified System.Posix.Signals as OS
#endif
       
-- ----------------------------------------------------------------------
-- * Common interface

-- | A data type for signals. This can be extended as needed.
data Signal =
  Interrupt  -- ^ Control-C event.
  | Close    -- ^ TERM signal (POSIX) or Close event (Windows).

-- | A data type for handlers.
data Handler =
  Default                -- ^ Default action.
  | Ignore               -- ^ Ignore the signal.
  | Catch (IO ())        -- ^ Handle the signal in a new thread when the signal is received.
  | CatchOnce (IO ())    -- ^ Like 'Catch', but only handle the first such signal.
  | OSHandler OS.Handler -- ^ An operating system specific handler.

-- | Install a handler for the given signal. The old handler is
-- returned. 
installHandler :: Signal -> Handler -> IO Handler
#ifdef mingw32_HOST_OS
installHandler = installHandler_windows
#else
installHandler = installHandler_posix
#endif

-- | Run a block of code with a given signal handler. The previous
-- handler is restored when the block terminates.
with_handler :: Signal -> Handler -> IO a -> IO a
with_handler signal handler body = do
  oldhandler <- installHandler signal handler
  a <- body
  installHandler signal oldhandler
  return a

-- ----------------------------------------------------------------------
-- * Windows specific code

#ifdef mingw32_HOST_OS

-- | Check if the Windows 'ConsoleEvent' matches the given abstract
-- 'Signal'. We implement this as a relation, rather than a function,
-- to allow for more than one 'ConsoleEvent' to match the same
-- 'Signal', or for more than one 'Signal' to match the same
-- 'ConsoleEvent'.
signal_matches :: OS.ConsoleEvent -> Signal -> Bool
signal_matches OS.ControlC Interrupt = True
signal_matches OS.Close Close = True
signal_matches _ _ = False

-- | Windows implementation of 'installHandler'.
installHandler_windows :: Signal -> Handler -> IO Handler
installHandler_windows signal handler = do
  oldhandler <- OS.installHandler (oshandler handler)
  return (OSHandler oldhandler)
    where
      oshandler Default = OS.Default
      oshandler Ignore = OS.Ignore
      oshandler (Catch body) = OS.Catch $ \event -> do
        if signal_matches event signal
          then body 
          else return ()
      oshandler (CatchOnce body) = OS.Catch $ \event -> do
        if signal_matches event signal 
          then do
            -- uninstall the handler
            OS.installHandler OS.Default
            body
          else return ()
      oshandler (OSHandler h) = h
      
-- ----------------------------------------------------------------------
-- * POSIX specific code

#else

-- | Map an abstract 'Signal' to a POSIX specific 'OS.Signal'.
ossignal :: Signal -> OS.Signal
ossignal Interrupt = OS.keyboardSignal
ossignal Close = OS.softwareTermination

-- | Map a 'Handler' to a POSIX specific handler.
oshandler :: Handler -> OS.Handler
oshandler Default = OS.Default
oshandler Ignore = OS.Ignore
oshandler (Catch body) = OS.Catch body
oshandler (CatchOnce body) = OS.CatchOnce body
oshandler (OSHandler h) = h

-- | POSIX implementation of 'installHandler'.
installHandler_posix :: Signal -> Handler -> IO Handler
installHandler_posix signal handler = do
  oldhandler <- OS.installHandler (ossignal signal) (oshandler handler) Nothing
  return (OSHandler oldhandler)

#endif
