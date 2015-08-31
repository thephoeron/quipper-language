-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | This module provides functions for defining general-purpose
-- transformations on low-level circuits. The uses of this include:
-- 
-- * gate transformations, where a whole circuit is transformed by
-- replacing each kind of gate with another gate or circuit;
-- 
-- * error correcting codes, where a whole circuit is transformed
-- replacing each qubit by some fixed number of qubits, and each gate
-- by a circuit; and
-- 
-- * simulations, where a whole circuit is mapped to a semantic
-- function by specifying a semantic function for each gate.
-- 
-- The interface is designed to allow the programmer to specify new
-- transformers easily. To define a specific transformation, the
-- programmer has to specify only four pieces of information:
-- 
-- * A type /a/=⟦Qubit⟧, to serve as a semantic domain for qubits.
-- 
-- * A type /b/=⟦Bit⟧, to serve as a semantic domain for bits.
-- 
-- * A monad /m/. This is to allow translations to have side effects
-- if desired; one can use the identity monad otherwise.
-- 
-- * For every gate /G/, a corresponding semantic function ⟦/G/⟧.  The
-- type of this function depends on what kind of gate /G/ is. For example:
-- 
-- @
-- If /G/ :: Qubit -> Circ Qubit, then ⟦/G/⟧ :: /a/ -> /m/ /a/. 
-- If /G/ :: (Qubit, Bit) -> Circ (Bit, Bit), then ⟦/G/⟧ :: (/a/, /b/) -> /m/ (/b/, /b/).
-- @ 
-- 
-- The programmer provides this information by defining a function of
-- type 'Transformer' /m/ /a/ /b/. See <#Transformers> below.  Once a
-- particular transformer has been defined, it can then be applied to
-- entire circuits. For example, for a circuit with 1 inputs and 2
-- outputs:
-- 
-- @
-- If /C/ :: Qubit -> (Bit, Qubit), then ⟦/C/⟧ :: /a/ -> /m/ (/b/, /a/).
-- @

-- ----------------------------------------------------------------------
-- Grammar note for developers: a "transformer" does a
-- "transformation" by "transforming" gates. We use "transform" as a
-- verb, "transformation" to describe the process of transforming, and
-- "transformer" for the code that describes or does the transformation. 
-- 
-- I had initially used the words "iteration", "translation",
-- "transform", "transformation", "interpretation", and "semantics"
-- interchangeably, which was a huge linguistic mess.

module Quipper.Transformer where

-- import other Quipper stuff
import Quipper.Circuit
import Libraries.Auxiliary

-- import other stuff
import Control.Monad
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import Data.Typeable

-- ======================================================================
-- * An example transformer
-- 
-- $EXAMPLE
-- 
-- The following is a short but complete example of how to write and
-- use a simple transformer. As usual, we start by importing Quipper:
-- 
-- > import Quipper
-- 
-- We will write a transformer called @sample_transformer@, which maps
-- every swap gate to a sequence of three controlled-not gates, and
-- leaves all other gates unchanged. For convenience, Quipper
-- pre-defines an 'identity_transformer', which can be used as a
-- catch-all clause to take care of all the gates that don't need to
-- be rewritten.
-- 
-- > mytransformer :: Transformer Circ Qubit Bit
-- > mytransformer (T_QGate "swap" 2 0 _ ncf f) = f $
-- >   \[q0, q1] [] ctrls -> do
-- >     without_controls_if ncf $ do
-- >       with_controls ctrls $ do
-- >         qnot_at q0 `controlled` q1
-- >         qnot_at q1 `controlled` q0
-- >         qnot_at q0 `controlled` q1
-- >         return ([q0, q1], [], ctrls)
-- > mytransformer g = identity_transformer g
-- 
-- Note how Quipper syntax has been used to define the replacement
-- circuit, consisting of three controlled-not gates. Also, since the
-- original swap gate may have been controlled, we have added the
-- additional controls with a 'with_controls' operator.
-- 
-- To try this out, we define some random circuit using swap gates:
-- 
-- > mycirc a b c d = do
-- >   swap_at a b
-- >   hadamard_at b
-- >   swap_at b c `controlled` [a, d]
-- >   hadamard_at c
-- >   swap_at c d
-- 
-- To apply the transformer to this circuit, we use the generic
-- operator 'transform_generic':
-- 
-- > mycirc2 = transform_generic mytransformer mycirc
-- 
-- Finally, we use a @main@ function to display the original circuit
-- and then the transformed one:
-- 
-- > main = do
-- >   print_simple Preview mycirc
-- >   print_simple Preview mycirc2

-- ======================================================================
-- * Bindings

-- $bindings
-- 
-- We introduce the notion of a /binding/ as a low-level way to
-- describe functions of varying arities. A binding assigns a value to
-- a wire in a circuit (much like a \"valuation\" in logic or semantics
-- assigns values to variables). 
-- 
-- To iterate through a circuit, one will typically specify initial
-- bindings for the input wires. This encodes the input of the function
-- ⟦/C/⟧ mentioned in the introduction. The bindings are updated as
-- one passes through each gate. When the iteration is finished, the
-- final bindings assign a value to each output wire of the
-- circuit. This encodes the output of the function ⟦/C/⟧. Therefore,
-- the interpretation of a circuit is representable as a function from
-- bindings (of input wires) to bindings (of output wires), i.e., it
-- has the type ⟦/C/⟧ :: 'Bindings' /a/ /b/ -> 'Bindings' /a/ /b/.

-- | An /endpoint/ is either a /qubit/ or a /bit/. In a transformer,
-- we have ⟦Endpoint Qubit Bit⟧ = ⟦Qubit⟧ + ⟦Bit⟧. The type 'Endpoint'
-- /a/ /b/ is the same as 'Either' /a/ /b/, but we use more suggestive
-- field names.
data B_Endpoint a b =
  Endpoint_Qubit a
  | Endpoint_Bit b
    deriving (Eq, Ord, Typeable, Show)

-- | A binding is a map from a set of wires to the disjoint union of
-- /a/ and /b/.
type Bindings a b = Map Wire (B_Endpoint a b)

-- | Return the list of bound wires from a binding.
wires_of_bindings :: Bindings a b -> [Wire]
wires_of_bindings = Map.keys

-- | The empty binding.
bindings_empty :: Bindings a b
bindings_empty = Map.empty

-- | Bind a wire to a value, and add it to the given bindings.
bind :: Wire -> B_Endpoint a b -> Bindings a b -> Bindings a b
bind r x bindings = Map.insert r x bindings

-- | Bind a qubit wire to a value, and add it to the given bindings.
bind_qubit_wire :: Wire -> a -> Bindings a b -> Bindings a b
bind_qubit_wire r x bindings = bind r (Endpoint_Qubit x) bindings

-- | Bind a bit wire to a value, and add it to the given bindings.
bind_bit_wire :: Wire -> b -> Bindings a b -> Bindings a b
bind_bit_wire r x bindings = bind r (Endpoint_Bit x) bindings

-- | Retrieve the value of a wire from the given bindings. 
unbind :: Bindings a b -> Wire -> B_Endpoint a b
unbind bindings w = case Map.lookup w bindings of
       Nothing -> error ("unbind: wire (" ++ show w ++ ") not in bindings: " ++ show (wires_of_bindings bindings))
       Just a -> a

-- | Retrieve the value of a qubit wire from the given bindings.
-- Throws an error if the wire was bound to a classical bit.
unbind_qubit_wire :: Bindings a b -> Wire -> a
unbind_qubit_wire bindings w = 
  case unbind bindings w of
    Endpoint_Qubit x -> x
    Endpoint_Bit x -> error "Transformer error: expected a qubit, got a bit"

-- | Retrieve the value of a bit wire from the given bindings.
-- Throws an error if the wire was bound to a qubit.
unbind_bit_wire :: Bindings a b -> Wire -> b
unbind_bit_wire bindings w = 
  case unbind bindings w of
    Endpoint_Bit x -> x
    Endpoint_Qubit x -> error "Transformer error: expected a bit, got a qubit"

-- | Delete a wire from the given bindings.
bind_delete :: Wire -> Bindings a b -> Bindings a b
bind_delete r bindings = Map.delete r bindings

-- | Like 'bind', except bind a list of wires to a list of values. The
-- lists must be of the same length.
bind_list :: [Wire] -> [B_Endpoint a b] -> Bindings a b -> Bindings a b
bind_list ws xs bindings =
  foldr (\ (w, x) -> bind w x) bindings (zip ws xs)
    
-- | Like 'bind_qubit_wire', except bind a list of qubit wires to a list of
-- values. The lists must be of the same length.
bind_qubit_wire_list :: [Wire] -> [a] -> Bindings a b -> Bindings a b
bind_qubit_wire_list ws xs bindings =
  foldr (\ (w, x) -> bind_qubit_wire w x) bindings (zip ws xs)
    
-- | Like 'bind_bit_wire', except bind a list of bit wires to a list of
-- values. The lists must be of the same length.
bind_bit_wire_list :: [Wire] -> [b] -> Bindings a b -> Bindings a b
bind_bit_wire_list ws xs bindings =
  foldr (\ (w, x) -> bind_bit_wire w x) bindings (zip ws xs)
    
-- | Like 'unbind', except retrieve a list of values.
unbind_list :: Bindings a b -> [Wire] -> [B_Endpoint a b]
unbind_list bindings ws =
  map (unbind bindings) ws

-- | Like 'unbind_qubit_wire', except retrieve a list of values.
unbind_qubit_wire_list :: Bindings a b -> [Wire] -> [a]
unbind_qubit_wire_list bindings ws =
  map (unbind_qubit_wire bindings) ws
    
-- | Like 'unbind_bit_wire', except retrieve a list of values.
unbind_bit_wire_list :: Bindings a b -> [Wire] -> [b]
unbind_bit_wire_list bindings ws =
  map (unbind_bit_wire bindings) ws
    
-- | A list of signed values of type ⟦Endpoint⟧. This type is an
-- abbreviation defined for convenience.
type Ctrls a b = [Signed (B_Endpoint a b)]

-- | Given a list of signed wires (controls), and a list of signed
-- values, make a bindings from the wires to the values. Ignore the signs.
bind_controls :: Controls -> Ctrls a b -> Bindings a b -> Bindings a b
bind_controls controls xs bindings =
  bind_list (map from_signed controls) (map from_signed xs) bindings

-- | Like 'unbind', but retrieve binding for all wires in a list of
-- controls.
unbind_controls :: Bindings a b -> Controls -> Ctrls a b
unbind_controls bindings c =
  [Signed (unbind bindings w) b | Signed w b <- c ]

-- $transformers_anchor #Transformers#

-- ----------------------------------------------------------------------
-- * Transformers

-- $transformers
-- 
-- The types 'T_Gate' and 'Transformer' are at the heart of the
-- circuit transformer functionality. Their purpose is to give a
-- concise syntax in which to express semantic functions for gates. As
-- mentioned in the introduction, the programmer needs to specify two
-- type /a/ and /b/, a monad /m/, and a semantic function for each
-- gate.  With the T_Gate' and 'Transformer' types, the definition
-- takes the following form:
-- 
-- > my_transformer :: Transformer m a b
-- > my_transformer (T_Gate1 <parameters> f) = f $ <semantic function for gate 1>
-- > my_transformer (T_Gate2 <parameters> f) = f $ <semantic function for gate 2>
-- > my_transformer (T_Gate3 <parameters> f) = f $ <semantic function for gate 3>
-- > ...
-- 
-- The type 'T_Gate' is very higher-order, involving a function /f/
-- that consumes the semantic function for each gate. The reason for
-- this higher-orderness is that the semantic functions for different
-- gates may have different types. 
-- 
-- This higher-orderness makes the 'T_Gate' mechanism hard to read,
-- but easy to use. Effectively we only have to write lengthy and
-- messy code once and for all, rather than once for each transformer.
-- In particular, all the required low-level bindings and unbindings
-- can be handled by general-purpose code, and do not need to clutter
-- each transformer. 

-- | The type 'T_Gate' is used to define case distinctions over gates
-- in the definition of transformers. For each kind of gate /X/, it
-- contains a constructor of the form @(T_X f)@. Here, /X/ identifies
-- the gate, and /f/ is a higher-order function to pass the
-- translation of /X/ to.

-- Implementation note: in the future, perhaps we can also add two
-- variants of this type: one that is specialized to the "simple"
-- case, where the semantics functions are assumed not to modify the
-- controls; another that is specialized to m = Id. This would make
-- the definition of most circuit transformers look less cluttered. 

data T_Gate m a b x =
  T_QGate      String Int Int InverseFlag NoControlFlag (([a] -> [a] -> Ctrls a b -> m ([a], [a], Ctrls a b)) -> x)
  | T_QRot       String Int Int InverseFlag Timestep NoControlFlag (([a] -> [a] -> Ctrls a b -> m ([a], [a], Ctrls a b)) -> x)
  | T_GPhase     Double NoControlFlag (([B_Endpoint a b] -> Ctrls a b -> m (Ctrls a b)) -> x)
  | T_CNot       NoControlFlag ((b -> Ctrls a b -> m (b, Ctrls a b)) -> x)
  | T_CGate      String NoControlFlag (([b] -> m (b, [b])) -> x)
  | T_CGateInv   String NoControlFlag ((b -> [b] -> m [b]) -> x)
  | T_CSwap      NoControlFlag ((b -> b -> Ctrls a b -> m (b, b, Ctrls a b)) -> x)
  | T_QPrep      NoControlFlag ((b -> m a) -> x)
  | T_QUnprep    NoControlFlag ((a -> m b) -> x)
  | T_QInit      Bool NoControlFlag (m a -> x)
  | T_CInit      Bool NoControlFlag (m b -> x)
  | T_QTerm      Bool NoControlFlag ((a -> m ()) -> x)
  | T_CTerm      Bool NoControlFlag ((b -> m ()) -> x)
  | T_QMeas      ((a -> m b) -> x)
  | T_QDiscard   ((a -> m ()) -> x)
  | T_CDiscard   ((b -> m ()) -> x)
  | T_DTerm      Bool ((b -> m ()) -> x)
  | T_Subroutine BoxId InverseFlag NoControlFlag ControllableFlag [Wire] Arity [Wire] Arity RepeatFlag ((Namespace -> [B_Endpoint a b] -> Ctrls a b -> m ([B_Endpoint a b], Ctrls a b)) -> x)
  | T_Comment String InverseFlag (([(B_Endpoint a b, String)] -> m ()) -> x)

-- Make 'T_Gate' an instance of 'Show', to enable transformers to
-- produce better error messages about unimplemented gates etc.
instance Show (T_Gate m a b x) where
  show (T_QGate name n m inv ncf f) = "QGate[" ++ name ++ "," ++ show n ++ "," ++ show m ++ "]" ++ optional inv "*"
  show (T_QRot name n m inv t ncf f) = "QRot[" ++ name ++ "," ++ show t ++ "," ++ show n ++ "," ++ show m ++ "]" ++ optional inv "*"
  show (T_GPhase t ncf f) = "GPhase[" ++ show t ++ "]"
  show (T_CNot ncf f) = "CNot"
  show (T_CGate n ncf f) = "CGate[" ++ n ++ "]"
  show (T_CGateInv n ncf f) = "CGate[" ++ n ++ "]*"
  show (T_CSwap ncf f) = "CSwap"
  show (T_QPrep ncf f) = "QPrep"
  show (T_QUnprep ncf f) = "QUnprep"
  show (T_QInit b ncf f) = "QInit" ++ if b then "1" else "0"
  show (T_CInit b ncf f) = "CInit" ++ if b then "1" else "0"
  show (T_QTerm b ncf f) = "QTerm" ++ if b then "1" else "0"
  show (T_CTerm b ncf f) = "CTerm" ++ if b then "1" else "0"
  show (T_QMeas f) = "QMeas"
  show (T_QDiscard f) = "QDiscard"
  show (T_CDiscard f) = "CDiscard"
  show (T_DTerm b f) = "DTerm" ++ if b then "1" else "0"
  show (T_Subroutine n inv ncf scf ws a1 vs a2 rep f) = "Subroutine(x" ++ (show rep) ++ ")[" ++ show n ++ "]" ++ optional inv "*"
  show (T_Comment n inv f) = "Comment[" ++ n ++ "]" ++ optional inv "*"

-- | A circuit transformer is specified by defining a function of type
-- 'Transformer' /m/ /a/ /b/. This involves specifying a monad /m/,
-- semantic domains /a/=⟦Qubit⟧ and /b/=⟦Bit⟧, and a semantic function
-- for each gate, like this:
-- 
-- > my_transformer :: Transformer m a b
-- > my_transformer (T_Gate1 <parameters> f) = f $ <semantic function for gate 1>
-- > my_transformer (T_Gate2 <parameters> f) = f $ <semantic function for gate 2>
-- > my_transformer (T_Gate3 <parameters> f) = f $ <semantic function for gate 3>
-- > ...

-- Implementation note: the use of \"forall\" in this type is to allow
-- some freedom in the return type of the continuation 'f' in the
-- definition of 'T_Gate'. This makes it easier, for example, to
-- compose transformers with other transformers. The use of \"forall\"
-- implies that any module that uses the 'Transformer' type may have
-- to declare the @Rank2Types@ language extension. This was not
-- required in GHC 7.4, but seems to be required in GHC 7.6.
type Transformer m a b = forall x . T_Gate m a b x -> x

-- | A \"binding transformer\" is a function from bindings to
-- bindings. The semantics of any gate or circuit is ultimately a
-- binding transformer, for some types /a/, /b/ and some monad /m/. We
-- introduce an abbreviation for this type primarily as a convenience
-- for the definition of 'bind_gate', but also because this type can
-- be completely hidden from user code.
type BT m a b = Bindings a b -> m (Bindings a b)

-- | Turn a 'Gate' into a 'T_Gate'. This is the function that actually
-- handles the explicit bindings/unbindings required for the inputs
-- and outputs of each gate. Effectively it gives a way, for each
-- gate, of turning a semantic function into a binding transformer.
-- Additionally, this function is passed a Namespace, so that the
-- semantic function for T_Subroutine can use it.
bind_gate :: Monad m => Namespace -> Gate -> T_Gate m a b (BT m a b)
bind_gate namespace gate = case gate of
  QGate name inv ws vs c ncf -> T_QGate name n m inv ncf (list_binary ws vs c)
    where
      n = length ws
      m = length vs
  QRot name inv t ws vs c ncf -> T_QRot name n m inv t ncf (list_binary ws vs c)
    where
      n = length ws
      m = length vs
  GPhase t w c ncf         -> T_GPhase t ncf (phase_ary w c)
  CNot w c ncf             -> T_CNot ncf (cunary w c)  
  CGate n w vs ncf         -> T_CGate n ncf (cgate_ary w vs)
  CGateInv n w vs ncf      -> T_CGateInv n ncf (cgateinv_ary w vs)
  CSwap w v c ncf          -> T_CSwap ncf (binary_c w v c)
  QPrep w ncf              -> T_QPrep ncf (qprep_ary w)
  QUnprep w ncf            -> T_QUnprep ncf (qunprep_ary w)
  QInit b w ncf            -> T_QInit b ncf (qinit_ary w)
  CInit b w ncf            -> T_CInit b ncf (cinit_ary w)
  QTerm b w ncf            -> T_QTerm b ncf (qterm_ary w)
  CTerm b w ncf            -> T_CTerm b ncf (cterm_ary w)
  QMeas w                  -> T_QMeas (qunprep_ary w)
  QDiscard w               -> T_QDiscard (qterm_ary w)
  CDiscard w               -> T_CDiscard (cterm_ary w)
  DTerm b w                -> T_DTerm b (cterm_ary w)
  Subroutine n inv ws a1 vs a2 c ncf scf rep
    -> T_Subroutine n inv ncf scf ws a1 vs a2 rep
         (\f -> subroutine_ary ws vs c (f namespace))
  Comment s inv ws         -> T_Comment s inv (comment_ary ws)
  where
    unary :: Monad m => Wire -> Controls -> (a -> Ctrls a b -> m (a, Ctrls a b)) -> BT m a b
    unary w c f bindings = do
      let w' = unbind_qubit_wire bindings w
      let c' = unbind_controls bindings c
      (w'', c'') <- f w' c'
      let bindings1 = bind_qubit_wire w w'' bindings
      let bindings2 = bind_controls c c'' bindings1
      return bindings2
    
    binary :: Monad m => Wire -> Wire -> Controls -> (a -> a -> Ctrls a b -> m (a, a, Ctrls a b)) -> BT m a b
    binary w v c f bindings = do
      let w' = unbind_qubit_wire bindings w
      let v' = unbind_qubit_wire bindings v
      let c' = unbind_controls bindings c
      (w'', v'', c'') <- f w' v' c'
      let bindings1 = bind_qubit_wire w w'' bindings
      let bindings2 = bind_qubit_wire v v'' bindings1
      let bindings3 = bind_controls c c'' bindings2
      return bindings3
    
    binary_c :: Monad m => Wire -> Wire -> Controls -> (b -> b -> Ctrls a b -> m (b, b, Ctrls a b)) -> BT m a b
    binary_c w v c f bindings = do
      let w' = unbind_bit_wire bindings w
      let v' = unbind_bit_wire bindings v
      let c' = unbind_controls bindings c
      (w'', v'', c'') <- f w' v' c'
      let bindings1 = bind_bit_wire w w'' bindings
      let bindings2 = bind_bit_wire v v'' bindings1
      let bindings3 = bind_controls c c'' bindings2
      return bindings3
    
    list_unary :: Monad m => [Wire] -> Controls -> ([a] -> Ctrls a b -> m ([a], Ctrls a b)) -> BT m a b
    list_unary ws c f bindings = do
      let ws' = unbind_qubit_wire_list bindings ws
      let c' = unbind_controls bindings c
      (ws'', c'') <- f ws' c'
      let bindings1 = bind_qubit_wire_list ws ws'' bindings
      let bindings2 = bind_controls c c'' bindings1
      return bindings2

    list_binary :: Monad m => [Wire] -> [Wire] -> Controls -> ([a] -> [a] -> Ctrls a b -> m ([a], [a], Ctrls a b)) -> BT m a b
    list_binary ws vs c f bindings = do
      let ws' = unbind_qubit_wire_list bindings ws
      let vs' = unbind_qubit_wire_list bindings vs
      let c' = unbind_controls bindings c
      (ws'', vs'', c'') <- f ws' vs' c'
      let bindings1 = bind_qubit_wire_list ws ws'' bindings
      let bindings2 = bind_qubit_wire_list vs vs'' bindings1
      let bindings3 = bind_controls c c'' bindings2
      return bindings3

    qprep_ary :: Monad m => Wire -> (b -> m a) -> BT m a b
    qprep_ary w f bindings = do
      let w' = unbind_bit_wire bindings w
      w'' <- f w'
      let bindings1 = bind_qubit_wire w w'' bindings
      return bindings1
    
    qunprep_ary :: Monad m => Wire -> (a -> m b) -> BT m a b
    qunprep_ary w f bindings = do
      let w' = unbind_qubit_wire bindings w
      w'' <- f w'
      let bindings1 = bind_bit_wire w w'' bindings
      return bindings1
    
    cunary :: Monad m => Wire -> Controls -> (b -> Ctrls a b -> m (b, Ctrls a b)) -> BT m a b
    cunary w c f bindings = do
      let w' = unbind_bit_wire bindings w
      let c' = unbind_controls bindings c
      (w'', c'') <- f w' c'
      let bindings1 = bind_bit_wire w w'' bindings
      let bindings2 = bind_controls c c'' bindings1
      return bindings2
    
    qinit_ary :: Monad m => Wire -> m a -> BT m a b
    qinit_ary w f bindings = do
      w'' <- f
      let bindings1 = bind_qubit_wire w w'' bindings
      return bindings1
    
    cinit_ary :: Monad m => Wire -> m b -> BT m a b
    cinit_ary w f bindings = do
      w'' <- f
      let bindings1 = bind_bit_wire w w'' bindings
      return bindings1
    
    qterm_ary :: Monad m => Wire -> (a -> m ()) -> BT m a b
    qterm_ary w f bindings = do
      let w' = unbind_qubit_wire bindings w
      () <- f w'
      let bindings1 = bind_delete w bindings
      return bindings1
    
    cterm_ary :: Monad m => Wire -> (b -> m ()) -> BT m a b
    cterm_ary w f bindings = do
      let w' = unbind_bit_wire bindings w
      () <- f w'
      let bindings1 = bind_delete w bindings
      return bindings1
    
    cgate_ary :: Monad m => Wire -> [Wire] -> ([b] -> m (b, [b])) -> BT m a b
    cgate_ary w vs f bindings = do
      let vs' = unbind_bit_wire_list bindings vs
      (w'', vs'') <- f vs'
      let bindings1 = bind_bit_wire w w'' bindings
      let bindings2 = bind_bit_wire_list vs vs'' bindings1 
      return bindings2

    cgateinv_ary :: Monad m => Wire -> [Wire] -> (b -> [b] -> m [b]) -> BT m a b
    cgateinv_ary w vs f bindings = do
      let vs' = unbind_bit_wire_list bindings vs
      let w' = unbind_bit_wire bindings w
      vs'' <- f w' vs'
      let bindings1 = bind_bit_wire_list vs vs'' bindings
      return bindings1

    subroutine_ary :: Monad m => [Wire] -> [Wire] -> Controls
                   -> ([B_Endpoint a b] -> Ctrls a b -> m ([B_Endpoint a b], Ctrls a b))
                   -> BT m a b
    subroutine_ary ws vs c f bindings = do
      let c' = unbind_controls bindings c
      let ws' = unbind_list bindings ws
      (vs'',c'') <- f ws' c'
      let bindings1 = bind_list vs vs'' bindings 
      let bindings2 = bind_controls c c'' bindings1
      return bindings2
      
    phase_ary :: Monad m => [Wire] -> Controls -> ([B_Endpoint a b] -> Ctrls a b -> m (Ctrls a b)) -> BT m a b
    phase_ary w c f bindings = do
      let w' = map (unbind bindings) w
      let c' = unbind_controls bindings c
      c'' <- f w' c'
      let bindings1 = bind_controls c c'' bindings
      return bindings1

    comment_ary :: Monad m => [(Wire, String)] -> (([(B_Endpoint a b, String)] -> m ()) -> BT m a b)
    comment_ary ws f bindings = do
      let ws' = zip (unbind_list bindings $ map fst ws) (map snd ws)
      f ws'
      return bindings

-- ----------------------------------------------------------------------
-- * Applying transformers to circuits

-- | Apply a 'Transformer' ⟦-⟧ to a 'Circuit' /C/, and output the
-- semantic function ⟦/C/⟧ :: bindings -> bindings.
transform_circuit :: Monad m => Transformer m a b -> Circuit -> Bindings a b -> m (Bindings a b)
transform_circuit transformer c bindings =
  foldM apply bindings gs
  where
    (_,gs,_,_) = c
    apply bindings g = transformer (bind_gate namespace_empty g) bindings

-- | Like 'transform_circuit', but for boxed circuits.
--
-- The handling of subroutines will depend on the transformer. 
-- For \"gate transformation\" types of applications, one typically
-- would like to leave the boxed structure intact.
-- For \"simulation\" types of applications, one would generally
-- recurse through the boxed structure.
--
-- The difference is specified in the definition of the transformer
-- within the semantic function of the Subroutine gate, whether to
-- create another boxed gate or open the box.
transform_bcircuit_rec :: Monad m => Transformer m a b -> BCircuit -> Bindings a b -> m (Bindings a b)
transform_bcircuit_rec transformer (c,namespace) bindings = 
  foldM apply bindings gs
  where
    (_,gs,_,_) = c
    apply bindings g = transformer (bind_gate namespace g) bindings

-- | Same as 'transform_bcircuit_rec', but specialized to when /m/ is
-- the identity operation.
transform_bcircuit_id :: Transformer Id a b -> BCircuit -> Bindings a b -> Bindings a b
transform_bcircuit_id t c b = getId (transform_bcircuit_rec t c b)

-- | To transform Dynamic Boxed circuits, we require a Transformer to define the
-- behavior on static gates, but we also require functions for what to do when
-- a subroutine is defined, and for when a dynamic_lift operation occurs. This is
-- all wrapped in the DynamicTransformer data type.
data DynamicTransformer m a b = DT {
     transformer :: Transformer m a b,
     define_subroutine :: BoxId -> TypedSubroutine -> m (),     
     lifting_function :: b -> m Bool
  }	

-- | Like 'transform_bcircuit_rec', but for dynamic-boxed circuits.
--
-- \"Write\" operations can be thought of as gates, and so they are passed to 
-- the given transformer. The handling of \"Read\" operations is taken care of 
-- by the \"lifting_function\" of the DynamicTransformer. \"Subroutine\" operations 
-- call the 'define_subroutine' function of the DynamicTransformer.
transform_dbcircuit :: Monad m => DynamicTransformer m a b -> DBCircuit x -> Bindings a b -> m (x,Bindings a b)
transform_dbcircuit dt (a0,rw) bindings = evalStateT (inner_transform dt (a0,rw) bindings) namespace_empty where
  inner_transform :: Monad m => DynamicTransformer m a b -> DBCircuit x -> Bindings a b -> (StateT Namespace m) (x,Bindings a b)
  inner_transform dt (a0,rw) bindings = 
    case rw of
      (RW_Return (_,_,x)) -> return (x,bindings)
      (RW_Write gate rw') -> do
        namespace <- get
        bindings' <- lift $ (transformer dt) (bind_gate namespace gate) bindings
        inner_transform dt (a0,rw')  bindings'
      (RW_Read wire rw_cont) -> do
        let bit = unbind_bit_wire bindings wire
        bool <- lift $ (lifting_function dt) bit
        let rw' = rw_cont bool
        inner_transform dt (a0,rw') bindings
      (RW_Subroutine name subroutine rw') -> do
        lift $ (define_subroutine dt) name subroutine
        namespace <- get
        let namespace' = map_provide name subroutine namespace
        put namespace'
        inner_transform dt (a0,rw') bindings
