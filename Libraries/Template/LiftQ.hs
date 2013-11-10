-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module defines the state monad used in
-- 'Libraries.Template.Lifting' for Template Haskell 
-- term manipulation.
module Libraries.Template.LiftQ where

import qualified Language.Haskell.TH as TH
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List

import Language.Haskell.TH (Name)
import Control.Monad.State
import Data.Map (Map)
import Data.Set (Set)

import qualified Libraries.Template.ErrorMsgQ as Err
import Libraries.Template.ErrorMsgQ (ErrMsgQ)


-- | State of the monad.
data LiftState = LiftState {
  boundVar :: Map Name Int, -- ^ How many times each name is bound.
  prefix :: Maybe String,   -- ^ The template prefix .
  monadName :: Maybe String -- ^ The name of the monad.
}

-- | An empty state.
emptyLiftState :: LiftState
emptyLiftState = LiftState { 
  boundVar = Map.empty, 
  prefix = Nothing,
  monadName = Nothing
}

-- | Shortcut to @StateT LiftState ErrMsgQ@.
type LiftQState = StateT LiftState ErrMsgQ

-- | The monad.
data LiftQ a = LiftQ (LiftQState a)

instance Monad LiftQ where
  return x = LiftQ $ return x
  (>>=) (LiftQ x) f = LiftQ $ do
           x' <- x
           let (LiftQ y) = f x'
           y


-- | Retrieve the state from the monad.
getState :: LiftQ LiftState
getState = LiftQ $ mapStateT (\x -> do ((),s) <- x; return (s,s))
                             (return ())

-- | Set the state of the monad.
setState :: LiftState -> LiftQ ()
setState s = LiftQ $ mapStateT (\_ -> return ((),s))
                               ((return ()) :: LiftQState ())

-- * Various functions to go back and forth between monads.

-- | From 'ErrMsgQ' to 'LiftQ'.
embedErrMsgQ :: ErrMsgQ a -> LiftQ a
embedErrMsgQ q = LiftQ $ mapStateT (\x -> do ((),s) <- x; y <- q; return (y,s))
                                   (return ())

-- | From 'TH.Q' to 'LiftQ'.
embedQ :: TH.Q a -> LiftQ a
embedQ q = LiftQ $ mapStateT (\x -> do ((),s) <- x; y <- Err.embedQ q; return (y,s))
                             (return ())

-- | Get 'TH.Q' out of 'LiftQ'
extractQ :: String -> LiftQ a -> TH.Q a
extractQ s (LiftQ x) = Err.extractQ s $ evalStateT x emptyLiftState

-- | Set an error message.
errorMsg :: String -> LiftQ a
errorMsg s = embedErrMsgQ $ Err.errorMsg s


-- * Working with variable names.

-- | Increase the number of binds of a variable name.
addToBoundVar :: Name -> LiftQ ()
addToBoundVar n = do
   s <- getState
   let new_value = 
         if (Map.member n $ boundVar s)
         then 1 + ((boundVar s) Map.! n) 
         else 0
   setState $ s { boundVar = Map.insert n new_value $ boundVar s }

-- | Decrease the number of binds of a variable name.
removeFromBoundVar :: Name -> LiftQ ()
removeFromBoundVar n = do
   s <- getState
   if (not $ Map.member n $ boundVar s) 
     then errorMsg ((show n) ++ " is not a bound value")
     else let old_value = (boundVar s) Map.! n in
        if old_value == 0
        then setState $ s { boundVar = Map.delete n $ boundVar s }
        else setState $ s { boundVar = Map.insert n (old_value - 1) $ boundVar s }

-- | Run a computation with a particular name being bound.
withBoundVar :: Name -> LiftQ a -> LiftQ a
withBoundVar n comp = do
  addToBoundVar n
  a <- comp
  removeFromBoundVar n
  return a

-- | Run a computation with a particular list of names being bound.
withBoundVars :: [Name] -> LiftQ a -> LiftQ a
withBoundVars names comp = foldl (flip withBoundVar) comp names

-- | Say whether a given name is bound.
isBoundVar :: Name -> LiftQ Bool
isBoundVar n = do
  s <- getState
  return $ Map.member n $ boundVar s


-- * Other operations on monad state.

-- | Set the template prefix.
setPrefix :: String -> LiftQ ()
setPrefix p = do
   s <- getState
   case (prefix s) of
      Just p' -> errorMsg ("cannot set the prefix to " ++ 
                           (show p) ++ 
                           ": prefix already defined as " ++ 
                           p') 
      Nothing -> setState $ s { prefix = Just p }


-- | Get the template prefix.
getPrefix :: LiftQ String
getPrefix = do
   s <- getState
   case (prefix s) of
      Nothing -> errorMsg "undefined prefix"
      Just p -> return p

-- | Set the monad name.
setMonadName :: String -> LiftQ ()
setMonadName m = do
   s <- getState
   case (monadName s) of
      Just m' -> errorMsg ("cannot set the monad to " ++ 
                           (show m) ++ 
                           ": monad already defined as " ++ 
                           m') 
      Nothing -> setState $ s { monadName = Just m }

-- | Get the monad name.
getMonadName :: LiftQ String
getMonadName = do
   s <- getState
   case (monadName s) of
      Nothing -> errorMsg "undefined monad"
      Just m -> return m




-- * Functions dealing with variable names.

-- | Make a name out of a string.
mkName :: String -> Name
mkName s = TH.mkName s

-- | Make a name out of a string, monadic-style.
newName :: String -> LiftQ Name
newName st = embedQ $ TH.newName st




-- | Make any string into a string containing only @[0-9a-zA-Z_.]@.
-- For example, it replaces any occurrence of @\"+\"@ with
-- @\"symb_plus_\"@.
sanitizeString :: String -> String
sanitizeString name = 
  List.concat (List.map 
               (\c -> 
                 Map.findWithDefault c c 
                     (Map.map (\s -> "symb_" ++ s ++ "_")
                              unicodeNames))
               (List.map (\x -> [x]) name))
   where
   unicodeNames :: Map.Map String String
   unicodeNames = Map.fromList
    [("!","exclamation"),
     ("\"","doublequote"),
     ("#","sharp"),
     ("$","dollar"),
     ("%","percent"),
     ("&","ampersand"),
     ("'","quote"),
     ("(","oparent"),
     (")","cparent"),
     ("*","star"),
     ("+","plus"),
     (",","comma"),
     ("-","minus"),
     -- we keep dots
     ("/","slash"),
     (":","colon"),
     (";","semicolon"),
     ("<","oangle"),
     ("=","equal"),
     (">","cangle"),
     ("?","question"),
     ("@","at"),
     ("[","obracket"),
     ("\\","backslash"),
     ("]","cbracket"),
     ("^","caret"),
     -- we keep _
     ("`","graveaccent"),
     ("{","obrace"),
     ("|","vbar"),
     ("}","cbrace"),
     ("~","tilde")]


-- | Take a string and make it into a valid Haskell name starting with
-- @\"template_\"@.
templateString :: String -> LiftQ String
templateString s = do
  p <- getPrefix
  return (p ++ (sanitizeString s))

-- | Look for the corresponding "template" name.
lookForTemplate :: Name -> LiftQ (Maybe Name)
lookForTemplate n = do
  t_string <- templateString $ TH.nameBase n
  embedQ $ TH.lookupValueName t_string

-- | Make a the template version of a given name.
makeTemplateName :: Name -> LiftQ Name
makeTemplateName n = do
  t_string <- templateString $ TH.nameBase n
  return $ TH.mkName t_string


-- * Other functions.

-- | Print on the terminal a monadic, printable object.
prettyPrint :: TH.Ppr a => LiftQ a -> IO ()
prettyPrint x = (TH.runQ $ extractQ "prettyPrint: " x) >>= (putStrLn . TH.pprint)


-- | Project patterns out of a clause.
clauseGetPats :: TH.Clause -> [TH.Pat]
clauseGetPats (TH.Clause pats _ _) = pats


-- | Check that the list is a non-empty repetition of the same
-- element.
equalNEListElts :: Eq a => [a] -> Bool
equalNEListElts [] = True
equalNEListElts (h:list) = foldl (&&) True $ map (== h) list


-- | Returns the length of the patterns in a list of clauses. Throw an
-- error if the patterns do not have all the same size.
clausesLengthPats :: [TH.Clause] -> LiftQ Int
clausesLengthPats [] = errorMsg "empty clause"
clausesLengthPats clauses 
  | (equalNEListElts $ map length $ map clauseGetPats clauses) = 
    return $ length $ clauseGetPats $ head clauses    
clausesLengthPats _ = errorMsg "patterns in clause are not of equal size"

