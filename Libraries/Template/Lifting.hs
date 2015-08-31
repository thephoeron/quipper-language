-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}

-- | This module describes stripped-down Template Haskell abstract
-- syntax trees (ASTs) for a subset of Haskell.

module Libraries.Template.Lifting where

import Control.Monad.State

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.List as List

import Data.Maybe (catMaybes)

import qualified Data.Set as Set
import Data.Set (Set)

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH (Name)

-- Get the monad to build the lifting.
import Libraries.Template.LiftQ


-- * Abstract syntax trees of a simplified language

-- | There are no \"guarded bodies\". One net effect is to make the
-- \"where\" construct equivalent to a simple \"let\".
type Body = Exp

-- | Literals.
data Lit =
   CharL Char          -- ^ Characters.
 | IntegerL Integer    -- ^ Integers.
 | RationalL Rational  -- ^ Reals.
   deriving (Show)


-- | Patterns.
data Pat = 
    LitP Lit          -- ^ Literal.
  | VarP Name         -- ^ Variable name.
  | TupP [Pat]        -- ^ Tuple.
  | WildP             -- ^ Wildchar.
  | ListP [Pat]       -- ^ List as @[...]@.
  | ConP Name [Pat]   -- ^ Cons: @h:t@.
    deriving (Show)

-- | Match term construct.
data Match =
  Match Pat Body
  deriving (Show)

-- | First-level declaration.
data Dec = 
  ValD Name Body
  deriving (Show)

-- | Expression
data Exp = 
    VarE Name         -- ^ Variable name.
  | ConE Name         -- ^ Constant name.
  | LitE Lit          -- ^ Literal.
  | AppE Exp Exp      -- ^ Application.
  | LamE Name Exp     -- ^ Lambda abstraction.
  | TupE [Exp]        -- ^ Tuple.
  | CondE Exp Exp Exp -- ^ If-then-else.
  | LetE [Dec] Exp    -- ^ Let-construct.
  | CaseE Exp [Match] -- ^ Case distinction
  | ListE [Exp]       -- ^ List: @[...]@.
  | ReturnE           -- ^ hardcoded constant for @'return'@.
  | MAppE             -- ^ hardcoded constant for @'>>='@.
  deriving (Show)


-- $ Syntactic sugar to recover do-notation.

-- | Datatype to encode the notation @x <- expr@.
data BindS = BindS Name Exp

-- | A simple @do@: list of monadic @let@ followed by a computation.
doE :: [BindS] -> Exp -> Exp 
doE binds exp = foldr doOne exp binds
  where
    doOne :: BindS -> Exp -> Exp
    doOne (BindS n value) computation = AppE (AppE MAppE value) (LamE n computation)


-- * Variable substitution
    

-- | Get the set of variable names in a pattern.
getVarNames :: Pat -> Set Name
getVarNames (VarP n) = Set.singleton n
getVarNames (TupP pats) = Set.unions $ map getVarNames pats
getVarNames (ListP pats) = Set.unions $ map getVarNames pats
getVarNames _ = Set.empty

-- | Substitution in a @'Match'@.
substMatch :: Name -> Exp -> Match -> Match
substMatch n s (Match p e) | Set.member n (getVarNames p) = Match p e
                           | True                         = Match p (substExp n s e)


-- | Substitution in a @'Dec'@.
substDec :: Name -> Exp -> Dec -> Dec
substDec n s (ValD m e) | n == m = ValD m e
                        | True   = ValD m (substExp n s e)

-- | Substitution in an @'Exp'@.
substExp :: Name -> Exp -> Exp -> Exp
substExp n s (VarE m) | n == m = s
                      | True   = (VarE m)
substExp n s (ConE m) = ConE m
substExp n s (LitE l) = LitE l
substExp n s (AppE e1 e2) = AppE (substExp n s e1) (substExp n s e2)
substExp n s (LamE m exp) | n == m = LamE m exp
                          | True   = LamE m $ substExp n s exp
substExp n s (TupE exps) = TupE $ map (substExp n s) exps
substExp n s (CondE e1 e2 e3) = CondE (substExp n s e1) (substExp n s e2) (substExp n s e3)
substExp n s (LetE decs exp) = LetE (map (substDec n s) decs) (substExp n s exp)
substExp n s (CaseE exp matches) = CaseE (substExp n s exp) $ map (substMatch n s) matches
substExp n s (ListE exps) = ListE $ map (substExp n s) exps
substExp n s ReturnE = ReturnE
substExp n s MAppE   = MAppE


-- | Substitution of several variables in one go.
mapSubstExp :: (Map Name Exp) -> Exp -> Exp
mapSubstExp map exp = List.foldl (\exp (x,y) -> substExp x y exp) exp $ Map.toList map


-- * Downgrading Template Haskell to AST

-- | Downgrading TH literals to @'Exp'@.
litTHtoExpAST :: TH.Lit -> LiftQ Exp
litTHtoExpAST (TH.CharL c) = return $ LitE $ CharL c
litTHtoExpAST (TH.StringL s) = return $ ListE $ map (LitE . CharL) s
litTHtoExpAST (TH.IntegerL i) = return $ LitE $ IntegerL i	
litTHtoExpAST (TH.RationalL r) = return $ LitE $ RationalL r
litTHtoExpAST x = errorMsg ("lifting not handled for " ++ (show x))

-- | Downgrading TH literals to @'Pat'@.
litTHtoPatAST :: TH.Lit -> LiftQ Pat
litTHtoPatAST (TH.CharL c) = return $ LitP $ CharL c
litTHtoPatAST (TH.StringL s) = return $ ListP $ map (LitP . CharL) s
litTHtoPatAST (TH.IntegerL i) = return $ LitP $ IntegerL i	
litTHtoPatAST (TH.RationalL r) = return $ LitP $ RationalL r
litTHtoPatAST x = errorMsg ("lifting not handled for " ++ (show x))


-- | Take a list of patterns coming from a @where@ section and output
-- a list of fresh names for normalized @let@s. Also gives a mapping
-- for substituting inside the expressions. Assume all names in the
-- list of patterns are distinct.
normalizePatInExp :: [Pat] -> LiftQ ([Name], Map Name Exp)
normalizePatInExp pats = do
  fresh_names <- mapM newName $ replicate (length pats) "normalizePat"
  let sets_of_old_names = List.map getVarNames pats
  let old_to_fresh old_name =
        List.lookup True $ zip (List.map (Set.member old_name) sets_of_old_names) fresh_names
  let old_to_pat old_name =
        List.lookup True $ zip (List.map (Set.member old_name) sets_of_old_names) pats
  let list_of_old_names = List.concat $ List.map Set.toList sets_of_old_names
  let maybe_list_map = mapM
            (\x -> do
                fresh <- old_to_fresh x
                pat <-   old_to_pat x
                return (x, CaseE (VarE fresh) [Match pat (VarE x)]))
            list_of_old_names
  case maybe_list_map of
    Nothing -> errorMsg "error in patterns..."
    Just l -> return $ (fresh_names, Map.fromList l)
  

-- | Build a @let@-expression out of pieces.
whereToLet :: Exp -> [(Pat,Exp)] -> LiftQ Exp
whereToLet exp [] = return exp
whereToLet exp list = do
  (fresh_names, pmap) <- normalizePatInExp $ map fst list
  let decs'' = map (uncurry ValD) $ zip fresh_names $ map snd list
  let decs' = map (\(ValD n e) -> ValD n $ mapSubstExp pmap e) decs''
  return $ 
    LetE decs' $ 
         CaseE (TupE $ map VarE fresh_names) [Match (TupP $ map fst list) exp]

-- | Build a @'Match'@ out of a TH clause
clauseToMatch :: TH.Clause -> LiftQ Match
clauseToMatch (TH.Clause pats body decs) = do
  pats' <- mapM patTHtoAST pats 
  body' <- bodyTHtoAST body 
  decs' <- mapM decTHtoAST decs
  exp <- whereToLet body' decs'
  return $ Match (TupP pats') exp

-- | From a list of TH clauses, make a case-distinction wrapped in a
-- lambda abstraction.
clausesToLambda :: [TH.Clause] -> LiftQ Exp
clausesToLambda clauses = do
  -- get length of patterns
  pats_length <- clausesLengthPats clauses
  -- make a list of new names from the function name
  fresh_names <- mapM newName $ replicate pats_length "x"
  -- make matches out of the clauses.
  matches <- mapM clauseToMatch clauses
  -- return a simple function with a case-distinction
  return $ foldr LamE 
                 (CaseE (TupE $ map VarE fresh_names) matches)
                 fresh_names


-- | Downgrade expressions.
expTHtoAST :: TH.Exp -> LiftQ Exp

expTHtoAST (TH.VarE v) = return $ VarE v
expTHtoAST (TH.ConE n) = return $ ConE n
expTHtoAST (TH.LitE l) = litTHtoExpAST l

expTHtoAST (TH.AppE e1 e2) = do 
  e1' <- expTHtoAST e1
  e2' <- expTHtoAST e2
  return $ AppE e1' e2'

expTHtoAST (TH.InfixE (Just e1) e2 (Just e3)) = do
  e1' <- expTHtoAST e1
  e2' <- expTHtoAST e2
  e3' <- expTHtoAST e3
  return $ AppE (AppE e2' e1') e3'

expTHtoAST (TH.InfixE Nothing e2 (Just e3)) = do
  e2' <- expTHtoAST e2
  e3' <- expTHtoAST e3
  n <- newName "x"
  return $ LamE n $ AppE (AppE e2' (VarE n)) e3'

expTHtoAST (TH.InfixE (Just e1) e2 Nothing) = do
  e1' <- expTHtoAST e1
  e2' <- expTHtoAST e2
  return $ AppE e2' e1'

expTHtoAST (TH.InfixE Nothing e2 Nothing) = do
  e2' <- expTHtoAST e2
  return e2'

expTHtoAST (TH.LamE pats exp) = 
  clausesToLambda [TH.Clause pats (TH.NormalB exp) []]

expTHtoAST (TH.TupE exps) = do
  exps' <- mapM expTHtoAST exps
  return (TupE exps')

expTHtoAST (TH.CondE e1 e2 e3) = do
  e1' <- expTHtoAST e1
  e2' <- expTHtoAST e2
  e3' <- expTHtoAST e3
  return $ CondE e1' e2' e3'

expTHtoAST (TH.LetE decs exp) = do
  decs' <- mapM decTHtoAST decs
  exp' <- expTHtoAST exp
  whereToLet exp' decs' 

expTHtoAST (TH.CaseE exp matches) = do
  exp' <- expTHtoAST exp
  matches' <- mapM matchTHtoAST matches
  return $ CaseE exp' matches'
  
expTHtoAST (TH.ListE exps) = do
  exps' <- mapM expTHtoAST exps
  return $ ListE exps'
  

expTHtoAST (TH.SigE e _) = expTHtoAST e

expTHtoAST x = errorMsg ("lifting not handled for " ++ (show x))


-- | Downgrade match-constructs.
matchTHtoAST :: TH.Match -> LiftQ Match
matchTHtoAST (TH.Match pat body decs) = do
   pat' <- patTHtoAST pat
   body' <- bodyTHtoAST body
   decs' <- mapM decTHtoAST decs
   exp <- whereToLet body' decs'
   return $ Match pat' exp

-- | Downgrade bodies into expressions.
bodyTHtoAST :: TH.Body -> LiftQ Exp
bodyTHtoAST (TH.NormalB exp) = expTHtoAST exp
bodyTHtoAST (TH.GuardedB x) = errorMsg ("guarded body not allowed in lifting: " ++ (show x))

-- | Downgrade patterns.
patTHtoAST :: TH.Pat -> LiftQ Pat
patTHtoAST (TH.LitP l) = litTHtoPatAST l
patTHtoAST (TH.VarP n) = return $ VarP n
patTHtoAST (TH.TupP pats) = do pats' <- mapM patTHtoAST pats; return $ TupP pats'
patTHtoAST (TH.WildP) = return WildP
patTHtoAST (TH.ListP pats) = do pats' <- mapM patTHtoAST pats; return $ ListP pats'
patTHtoAST (TH.ConP n pats) = do pats' <- mapM patTHtoAST pats; return $ ConP n pats'
patTHtoAST (TH.InfixP p1 n p2) = do
  p1' <- patTHtoAST p1
  p2' <- patTHtoAST p2
  return $ ConP n [p1',p2']
patTHtoAST x = errorMsg ("non-implemented lifting: " ++ (show x))




-- | Downgrade first-level declarations.
firstLevelDecTHtoAST :: TH.Dec -> Maybe (LiftQ Dec)
firstLevelDecTHtoAST (TH.FunD name clauses) = Just $ do
  exp <- clausesToLambda clauses
  name' <- makeTemplateName name
  return $ ValD name' $ substExp name (VarE name') exp

firstLevelDecTHtoAST (TH.ValD (TH.VarP name) body decs) = Just $ do
  body' <- bodyTHtoAST body 
  decs' <- mapM decTHtoAST decs
  exp <- whereToLet body' decs' 
  name' <- makeTemplateName name
  return $ ValD name' $ substExp name (VarE name') exp

firstLevelDecTHtoAST (TH.ValD _ _ _) = Just $
  errorMsg ("only variables and functions can be lifted as first-level declarations")

firstLevelDecTHtoAST (TH.SigD _ _) = Nothing

firstLevelDecTHtoAST x = Just $ errorMsg ("non-implemented lifting: " ++ (show x))


-- | Downgrade any declarations (including the ones in @where@-constructs).
decTHtoAST :: TH.Dec -> LiftQ (Pat,Exp)

decTHtoAST (TH.FunD name clauses) = do
  exp <- clausesToLambda clauses
  return $ (VarP name, exp)

decTHtoAST (TH.ValD pat body decs) = do
  pat' <- patTHtoAST pat
  body' <- bodyTHtoAST body 
  decs' <- mapM decTHtoAST decs
  exp <- whereToLet body' decs'
  return $ (pat', exp)

decTHtoAST x = errorMsg ("non-implemented lifting: " ++ (show x))




-- * Upgrade AST to Template Haskell

-- | Abstract syntax tree of the type of the function 'return'.
typReturnE :: LiftQ TH.Type
typReturnE = do
  m_string <- getMonadName
  let m = TH.conT (mkName m_string)
  embedQ [t| forall x. x -> $(m) x |]

-- | Abstract syntax tree of the type of the function '>>='.
typMAppE :: LiftQ TH.Type
typMAppE = do
  m_string <- getMonadName
  let m = TH.conT (mkName m_string)
  embedQ [t| forall x y. $(m) x -> (x -> $(m) y) -> $(m) y |]


-- | Upgrade literals
litASTtoTH :: Lit -> TH.Lit
litASTtoTH (CharL c) = TH.CharL c
litASTtoTH (IntegerL i) = TH.IntegerL i
litASTtoTH (RationalL r) = TH.RationalL r

-- | Upgrade patterns.
patASTtoTH :: Pat -> TH.Pat
patASTtoTH (LitP l)      = TH.LitP $ litASTtoTH l
patASTtoTH (VarP n)      = TH.VarP n
patASTtoTH (TupP pats)   = TH.TupP $ map patASTtoTH pats
patASTtoTH WildP         = TH.WildP
patASTtoTH (ListP pats)  = TH.ListP $ map patASTtoTH pats
patASTtoTH (ConP n pats) = TH.ConP n $ map patASTtoTH pats

-- | Upgrade match-constructs.
matchASTtoTH :: Match -> LiftQ TH.Match
matchASTtoTH (Match p b) = do
  exp <- expASTtoTH b
  return $ TH.Match (patASTtoTH p) (TH.NormalB exp) []

-- | Upgrade declarations.
decASTtoTH :: Dec -> LiftQ TH.Dec

decASTtoTH (ValD n b) = do
  exp <- expASTtoTH b
  return $ TH.ValD (TH.VarP n) (TH.NormalB exp) []


-- | Upgrade expressions.
expASTtoTH :: Exp -> LiftQ TH.Exp

expASTtoTH (VarE n) = return $ TH.VarE n
expASTtoTH (ConE n) = return $ TH.ConE n
expASTtoTH (LitE l) = return $ TH.LitE $ litASTtoTH l

expASTtoTH (AppE e1 e2) = do
  e1' <- expASTtoTH e1
  e2' <- expASTtoTH e2
  return $ TH.AppE e1' e2'

expASTtoTH (LamE n e) = do
  e' <- expASTtoTH e
  return $ TH.LamE [TH.VarP n] e'

expASTtoTH (TupE exps) = do
  exps' <- mapM expASTtoTH exps
  return $ TH.TupE exps'

expASTtoTH (CondE e1 e2 e3) = do
  e1' <- expASTtoTH e1
  e2' <- expASTtoTH e2
  e3' <- expASTtoTH e3
  return $ TH.CondE e1' e2' e3'

expASTtoTH (LetE decs e) = do
  decs' <- mapM decASTtoTH decs
  e' <- expASTtoTH e
  return $ TH.LetE decs' e'

expASTtoTH (CaseE e matches) = do
  e' <- expASTtoTH e
  m' <- mapM matchASTtoTH matches
  return $ TH.CaseE e' m'

expASTtoTH (ListE exps) = do
  exps' <- mapM expASTtoTH exps
  return $ TH.ListE exps'

expASTtoTH ReturnE = do
  t <- typReturnE
  maybe_r <- embedQ $ TH.lookupValueName "return"
  case maybe_r of
    Just r -> return $ TH.SigE (TH.VarE r) t
    Nothing -> errorMsg "\'return\' undefined"
  
expASTtoTH MAppE = do
  t <- typMAppE
  maybe_a <- embedQ $ TH.lookupValueName ">>="
  case maybe_a of
    Just a -> return $ TH.SigE (TH.VarE a) t
    Nothing -> errorMsg "\'>>=\' undefined"




-- * Lifting AST terms (into AST terms)

-- | Variable referring to the lifting function for integers.
liftIntegerL :: Exp
liftIntegerL = VarE $ mkName "template_integer"

-- | Variable referring to the lifting function for reals.
liftRationalL :: Exp
liftRationalL = VarE $ mkName "template_rational"

-- | Lifting literals.
liftLitAST :: Lit -> LiftQ Exp
liftLitAST (CharL c) = return (AppE ReturnE (LitE $ CharL c))
liftLitAST (IntegerL i) = return $ AppE liftIntegerL (LitE $ IntegerL i)
liftLitAST (RationalL r) =  return $ AppE liftRationalL (LitE $ RationalL r)

-- | Lifting patterns.
liftPatAST :: Pat -> LiftQ Pat
liftPatAST pat = return pat

-- | Lifting match-constructs.
liftMatchAST :: Match -> LiftQ Match
liftMatchAST (Match pat exp) = do
  exp' <- liftExpAST exp
  return $ Match pat exp' 

-- | Lifting declarations.
liftDecAST :: Dec -> LiftQ Dec
liftDecAST (ValD name exp) = do
  exp' <- liftExpAST exp
  return $ ValD name exp'

-- | Lifting first-level declarations.
liftFirstLevelDecAST :: Dec -> LiftQ Dec
liftFirstLevelDecAST (ValD name exp) = withBoundVar name $ do
  exp' <- liftExpAST exp
  return $ ValD name exp'

-- | Lifting expressions.
liftExpAST :: Exp -> LiftQ Exp

liftExpAST (VarE x) = do
  template_name <- lookForTemplate x
  case template_name of
    Nothing -> do
      b <- isBoundVar x
      if b 
        then return $ VarE x
        else return $ AppE ReturnE $ VarE x
    Just t  -> return $ VarE t

liftExpAST (ConE n) = do
  template_name <- lookForTemplate n
  case template_name of
    Nothing -> do 
      t <- templateString $ TH.nameBase n
      errorMsg ("variable " ++ t ++ " undefined")
    Just t  -> return $ VarE t

liftExpAST (LitE l) = liftLitAST l

liftExpAST (AppE e1 e2) = do
  e1' <- liftExpAST e1
  e2' <- liftExpAST e2
  n1 <- newName "app1"
  n2 <- newName "app2"
  return $ doE [BindS n1 e1', BindS n2 e2'] $ AppE (VarE n1) (VarE n2)

liftExpAST (LamE n exp) = do
  exp' <- liftExpAST exp
  return $ AppE ReturnE $ LamE n exp'

liftExpAST (TupE exps) = do
  exps' <- mapM liftExpAST exps
  fresh_names <- mapM newName $ replicate (length exps) "tupe"
  return $ 
    doE (map (uncurry BindS) $ zip fresh_names exps')
        (AppE ReturnE $ TupE $ map VarE fresh_names)

liftExpAST (CondE e1 e2 e3) = do
  e1' <- liftExpAST e1
  e2' <- liftExpAST e2
  e3' <- liftExpAST e3
  return $ AppE (AppE (AppE (VarE (mkName "template_if")) (e1')) (e2')) (e3')


liftExpAST (LetE decs exp) = 
  let existing_names = map (\(ValD n _) -> n) decs
  in
   withBoundVars existing_names $ do
     decs' <- mapM liftDecAST decs
     exp' <- liftExpAST exp
     return $ 
       LetE decs' exp'


liftExpAST (CaseE exp matches) = do
  exp' <- liftExpAST exp
  matches' <- mapM liftMatchAST matches
  fresh_name <- newName "case"
  return $ doE [BindS fresh_name exp']
               $ CaseE (VarE fresh_name) matches'
  
liftExpAST (ListE exps) = do
  exps' <- mapM liftExpAST exps
  fresh_names <- mapM newName $ replicate (length exps) "liste"
  return $ 
    doE (map (uncurry BindS) $ zip fresh_names exps')
       $ AppE ReturnE $ ListE $ map VarE fresh_names

-- These two are not supposed to be there!
liftExpAST ReturnE = undefined
liftExpAST MAppE   = undefined


-- | make a declaration into a template-declaration (by renaming with
-- the template-prefix).
makeDecTemplate :: Dec -> LiftQ Dec
makeDecTemplate (ValD name exp) = do
  name' <- makeTemplateName name
  return $ ValD name' $ substExp name (VarE name') exp


-- * Various pretty printing functions


-- | pretty-printing Template Haskell declarations.
prettyPrintAST :: TH.Q [TH.Dec] -> IO ()
prettyPrintAST x = prettyPrint $ do
  x' <- embedQ x
  y <- sequence $ catMaybes $ map firstLevelDecTHtoAST x'
  mapM decASTtoTH y

-- | Pretty-printing Template Haskell expressions.
prettyPrintLiftExpTH :: TH.Q (TH.Exp) -> IO ()
prettyPrintLiftExpTH x = prettyPrint $ do
  x' <- embedQ x
  y <- expTHtoAST x'
  z <- liftExpAST y
  expASTtoTH z

-- | Pretty-printing expressions.
prettyPrintLiftExpAST :: LiftQ (Exp) -> IO ()
prettyPrintLiftExpAST x = prettyPrint $ do
  z <- x
  z' <- liftExpAST z
  expASTtoTH z'


-- * The main lifting functions.


-- | Lift a list of declarations. The first argument is the name of
-- the monad to lift into.
decToMonad :: String -> TH.Q [TH.Dec] -> TH.Q [TH.Dec]
decToMonad s x = extractQ "decToMonad: " $ do
  setMonadName s
  setPrefix "template_"
  dec <- embedQ x
  decAST <- sequence $ catMaybes $ map firstLevelDecTHtoAST dec
  liftedAST <- mapM liftFirstLevelDecAST decAST
  mapM decASTtoTH liftedAST

-- | Lift an expression. The first argument is the name of the monad
-- to lift into.
expToMonad :: String -> TH.Q TH.Exp -> TH.Q TH.Exp
expToMonad s x = extractQ "expToMonad: " $ do
  setMonadName s
  setPrefix "template_"
  dec <- embedQ x
  decAST <- expTHtoAST dec
  liftedAST <- liftExpAST decAST
  expASTtoTH liftedAST


