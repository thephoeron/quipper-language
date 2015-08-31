-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MonadComprehensions #-}

-- | This module contains the core of the classical circuit
-- optimization algorithm.
module QuipperLib.ClassicalOptim.Simplification where

import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Set.Monad as S  {- set-monad-0.1.0.0 -}
import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as IM {- containers-0.5.2.1 -}

import qualified Control.DeepSeq as Seq

import Control.Applicative (Applicative(..))
import Control.Monad (liftM, ap)

import qualified Libraries.Auxiliary as Q

import QuipperLib.ClassicalOptim.Circuit
import QuipperLib.ClassicalOptim.AlgExp

-- ----------------------------------------------------------------------
-- * Auxiliary definitions

-- | Internal definition of a trace, for debugging purposes. This is a
-- no-op, but can be replaced to turn on debugging.
trace :: String -> b -> b
trace a b = b

-- | Change a wire ID in a gate. The first two arguments are the old
-- and the new wire ID.
moveWire :: Wire -> Wire -> Gate -> Gate
moveWire from to NoOp = NoOp
moveWire from to (Init b w) = if (w == from) then error "moveWire" else (Init b w)
moveWire from to (Cnot w ctls) = Cnot w' ctls'
   where
   w' = if (from == w) then to else w
   ctls' = map moveCtls ctls
   moveCtls (w,b) = if (from == w) then (to,b) else (w,b)

-- | Flip the control on the given wire (from positive to negative or
-- vice versa).
flipCtl :: Wire -> Gate -> Gate
flipCtl _ NoOp = NoOp
flipCtl _ (Init b w) = Init b w
flipCtl w (Cnot w' ctls) = Cnot w' $ map (\(x,b) -> if (x == w) then (x,not b) else (x,b)) ctls

-- | Change a wire ID in a gate and flip the potential control.
moveWireFlip :: Wire -> Wire -> Gate -> Gate
moveWireFlip from to NoOp = NoOp
moveWireFlip from to (Init b w) = if (w == from) then error "moveWire" else (Init b w)
moveWireFlip from to (Cnot w ctls) = Cnot w' ctls'
   where
   w' = if (from == w) then to else w
   ctls' = map moveCtls ctls
   moveCtls (w,b) = if (from == w) then (to,b) else if (to == w) then (w,not b) else (w,b)

-- ----------------------------------------------------------------------
-- * Small, simple optimizations

-- | Suppress gates acting on garbage wires, i.e., wires that are not in the input set. 
suppress_garbage :: [Gate] -> IS.IntSet -> [Gate]

suppress_garbage ((Cnot w ctls):gs) used = 
  if (IS.member w used) then g:gs1 else gs2
  where
    g = Cnot w ctls
    gs1 = suppress_garbage gs $ IS.union (IS.insert w used) $ IS.fromList $ L.map fst ctls
    gs2 = suppress_garbage gs used

suppress_garbage (g:gs) used = g:(suppress_garbage gs used)

suppress_garbage [] _ = []


-- | Like 'suppress_garbage', but packaged in a manner that is friendly for composition.
suppressGarbageGates :: ([Gate],[Wire]) -> ([Gate],[Wire])

suppressGarbageGates (gs,out) = (reverse $ suppress_garbage (reverse gs) $ IS.fromList out, out)


-- ----------------------------------------------------------------------
-- * Compression of wire numbering

-- $ As the optimization process goes on, many /init/ gates will end
-- up being discarded. The function 'compressWires' compacts the wire
-- numbering scheme to make a smaller circuit.

-- | Get the set of all wires used by the circuit.
getAllWires :: [Gate] -> IS.IntSet
getAllWires gs = L.foldl' IS.union IS.empty $ L.map aux gs
  where
    aux (Cnot w ctls) = IS.insert w $ L.foldl' (flip IS.insert) IS.empty $ L.map fst ctls
    aux (Init _ w) = IS.singleton w
    aux NoOp = IS.empty

-- | Get the set of wires initialized by the circuit.
getInitWires :: [Gate] -> IS.IntSet
getInitWires gs = L.foldl' IS.union IS.empty $ map aux gs
  where
    aux (Cnot _ _) = IS.empty
    aux (Init _ w) = IS.singleton w
    aux NoOp = IS.empty

-- | Get the set of input wires, i.e., the ones that are used but not initialized.
getInputWires :: [Gate] -> IS.IntSet
getInputWires gs = IS.difference (getAllWires gs)  (getInitWires gs)

-- | Compress the wire numbering.
compressWires :: [Wire] -> ([Gate],[Wire]) -> ([Gate],[Wire])
compressWires inputwires (gs,output) =  (gs',out')
  where
    iws = getInitWires gs
    begin = if inputwires == []
            then 0
            else 1 + (head $ reverse $ L.sort inputwires)
    end = begin + (IS.size iws)
    listmap = zip ([0..begin-1] ++ (IS.toAscList iws)) [0 .. end]
    remap = M.fromList $ trace (show listmap) listmap
    out' = map (remap M.!) output
    gs' = map (rewire remap) gs
    
    rewire m (Cnot w ctls) = Cnot (m M.! w) $ map (\(x,b) -> (m M.! x, b)) ctls
    rewire m (Init b w) = Init b (m M.! w)
    rewire m NoOp = NoOp


-- ----------------------------------------------------------------------
-- * A useful data structure

-- $ When considering a particular point in a circuit (i.e., in a list
-- of gates), to decide whether a given wire is used or controlled
-- before or after, we keep a data-structure 'UsedWire'.

-- | The type of gate ID's.
type GateId = Int

-- | A set of gate ID's.
type GateIdSet = IS.IntSet

-- | A map from wires to pairs of 'GateId's. The left member gives the
-- ID of the first gate using the wire, and the right member gives the
-- ID of the last gate using the wire.
type UsedWire = IM.IntMap GateIdSet

-- | Get the minimum of a set of gate ID's.
gateIdFindMin :: GateIdSet -> Maybe GateId
gateIdFindMin g = if (IS.null g) then Nothing else Just (IS.findMin g)

-- | Get the maximum of a set of gate ID's.
gateIdFindMax :: GateIdSet -> Maybe GateId
gateIdFindMax g = if (IS.null g) then Nothing else Just (IS.findMax g)

-- | Get the pair corresponding to the given wire.
pairUsedWire :: UsedWire -> Wire -> GateIdSet
pairUsedWire m w = IM.findWithDefault IS.empty w m

-- | Get the first gate using the wire in the future.
firstUsedWire :: UsedWire -> Wire -> Maybe GateId
firstUsedWire = curry $ gateIdFindMin . (uncurry pairUsedWire)

-- | Get the last gate using the wire in the past. Return 0 if none.
lastUsedWire :: UsedWire -> Wire -> GateId
lastUsedWire w w'= 
  case (curry $ gateIdFindMax . (uncurry pairUsedWire)) w w' of
    Just w -> w
    Nothing -> 0

-- | 'nextUsedGate' /ws/ /g/ /g/' /w/: Look for the next gate in /ws/
-- corresponding to wire /w/, starting from /g/. Return /g/' if none.
nextUsedGate :: UsedWire -> GateId -> GateId -> Wire -> GateId
nextUsedGate ws g g' w =
  case (do gs <- IM.lookup w ws; IS.lookupGT g gs) of
    Just g  -> g
    Nothing -> g'

-- | For each wire, find the set of gates placing a control on it.
circuitControlWires :: GateId -> [Gate] -> UsedWire
circuitControlWires id gs = aux id IM.empty gs
  where
    aux _ m [] = m
    aux g m (Init _ _:gs) = aux (g+1) m gs
    aux g m ((Cnot _ ctls):gs) = aux (g+1) m' gs
      where
        wires = map fst ctls
        m' = L.foldl (\m'' w -> IM.alter (f g) w m'') m wires
        f g Nothing = Just $ IS.singleton g
        f g (Just s) = Just $ IS.insert g s
    aux g m (NoOp:_) = error "circuitControlWires cannot deal with NoOp"

-- | For each wire, find the set of gates acting on it with NOT.
circuitNotWires :: GateId -> [Gate] -> UsedWire
circuitNotWires id gs = aux id IM.empty gs
  where
    aux _ m [] = m
    aux g m (Init _ _:gs) = aux (g+1) m gs
    aux g m ((Cnot w _):gs) = aux (g+1) m' gs
      where
        m' = IM.alter (f g) w m
        f g Nothing = Just $ IS.singleton g
        f g (Just s) = Just $ IS.insert g s
    aux g m (_:gs) = aux (g+1) m gs

-- ----------------------------------------------------------------------
-- * Algebraic optimization method

-- $ To each wire in a circuit, we attach a set of formulas.  At each
-- iteration, the wire that gets modified is updated with its new
-- value, using all the possible values, possibly together with a
-- fresh variable.  At each iteration, we also strip away the
-- expressions that get too large. Here, the size of an algebraic
-- expression is measured by the 'exp_length' function.

-- | Calculate the size of an algebraic expression.
exp_length :: Exp -> Int
exp_length e = L.foldl' (+) 0 $ L.map (\x -> let y = IS.size x in seq y y) $ S.toList e

-- | Given a list of sets of expressions, form the conjunction of
-- every possible choice of one expression from each set. For example.
-- 
-- > exp_list_and [{a,b}, {c,d}, {e,f}] = 
-- >     [a∧c∧e, a∧c∧f, a∧d∧e, a∧d∧f, b∧c∧e, b∧c∧f, b∧d∧e, b∧d∧f].
exp_list_and :: [S.Set Exp] -> S.Set Exp
exp_list_and []  = S.singleton exp_true
exp_list_and [l] = l
exp_list_and (h:k:t) = exp_list_and ([exp_and x y | x <- h, y <- k]:t)

-- | Evaluate a control with respect to a state.
expEvalCtl :: (IM.IntMap (S.Set (Exp,Int))) -> (Wire,Bool) -> S.Set Exp
expEvalCtl m (w,True)  = S.map fst (m IM.! w)
expEvalCtl m (w,False) = S.map exp_not $ S.map fst $ (IM.!) m w

-- | Evaluate a gate with respect to a state.
expEvalGate :: (IM.IntMap (S.Set (Exp,Int))) -> Gate -> IM.IntMap (S.Set (Exp,Int))

expEvalGate m (Init False w) = IM.insert w (S.singleton (exp_false,0)) m
expEvalGate m (Init True  w) = IM.insert w (S.singleton (exp_true,1)) m
expEvalGate m NoOp = m

expEvalGate m (Cnot w ctls) = IM.insert w cnot m
  where
    ands = exp_list_and $ L.map (expEvalCtl m) ctls
    cnot = S.map (\x -> (x,exp_length x)) [exp_xor x y |
                                              x <- S.map fst $ (IM.!) m w,
                                              y <- ands ]

-- ----------------------------------------------------------------------
-- ** State of the optimization automaton

-- | The state of the automaton. This contains in particular the
-- current state, the past and future gates, and a fresh variable.
data ExpState = ExpState {
  gates_to_skip :: IM.IntMap Gate, -- ^ For use with 'stepSwapCirc'.
  allWiresInCirc :: IS.IntSet,     -- ^ All the wires in the circuit.
  gateId :: GateId,                -- ^ ID of the first gate in the future (starts at 1).
  usedControlWires :: UsedWire,    -- ^ Location of the controls.
  usedNotWires :: UsedWire,        -- ^ Location of the NOT gates.
  future :: [Gate],                -- ^ Gates left to explore.
  past :: [Gate],                  -- ^ Gates already explored.
  expMap :: IM.IntMap (S.Set (Exp,Int)), -- ^ Algebraic state of the wires. Also contains the size of the expression, so we don't have to recompute it each time.
  freshVar :: Integer,             -- ^ The next fresh wire.
  outWires :: [Wire],              -- ^ The output wires.
  sizeCirc :: Int                  -- ^ Size of the circuit.
  }


instance Seq.NFData Gate where
    rnf (Init a b) = a `seq` b `seq` ()
    rnf (Cnot w ctls) = ctls `Seq.deepseq` w `Seq.deepseq` ()
    rnf NoOp = ()

{-
instance Seq.NFData ExpState where
    rnf e = {-allWiresInCirc e `Seq.deepseq` gateId e `Seq.deepseq` usedControlWires e `Seq.deepseq` usedNotWires e `Seq.deepseq` future e `Seq.deepseq` past e `Seq.deepseq` expMap e `Seq.deepseq` freshVar e `Seq.deepseq` outWires e-} () `Seq.deepseq` ()
-}

-- | The initial state for a given set of parameters.
initExpState :: IS.IntSet -> [Wire] -> [Gate] -> ExpState
initExpState ws_in ws_out gs = ExpState {
  gates_to_skip = IM.empty,
  allWiresInCirc = getAllWires gs,
  gateId = 1,
  usedControlWires = circuitControlWires 1 gs,
  usedNotWires = circuitNotWires 1 gs,
  future = gs,
  past = [],
  expMap   = IM.fromList $ L.map (\x -> (x, S.singleton (exp_var x, 1))) $ IS.toAscList ws_in,
  freshVar = fromIntegral $ (+) 1 $ IS.findMax ws_in,
  outWires = ws_out,
  sizeCirc = length gs
  }

-- ----------------------------------------------------------------------
-- ** The state monad

-- | The state monad corresponding to 'ExpState'.
data EvalCirc a =  EvalCirc (ExpState -> (ExpState, a))

instance Monad EvalCirc where
  return x = EvalCirc (\y -> (y,x))
  (>>=) (EvalCirc c) f = EvalCirc (\s -> let (s',x) = c s in
                                 let (EvalCirc c') = f x in
                                 c' s')

instance Applicative EvalCirc where
  pure = return
  (<*>) = ap

instance Functor EvalCirc where
  fmap = liftM

-- ----------------------------------------------------------------------
-- ** Low-level access functions

-- | Construct an @'ExpState'@ out of an @'EvalCirc'@.
runEvalCirc :: IS.IntSet -> [Wire] -> [Gate] -> EvalCirc a -> ExpState
runEvalCirc ws_in ws_out gs (EvalCirc e) = fst $ e $ initExpState ws_in ws_out gs

-- | Retrieve the state.
getExpState :: EvalCirc ExpState
getExpState = EvalCirc (\s -> (s,s))

-- | Set the state.
setExpState :: ExpState -> EvalCirc ()
setExpState s = EvalCirc (\_ -> (s,()))

-- ----------------------------------------------------------------------
-- ** Higher-level access functions

-- | Create a fresh variable
newFreshVar :: EvalCirc Integer
newFreshVar = do
  s <- getExpState
  let v = freshVar s
  setExpState (s { freshVar = v + 1 }) 
  return v

-- | Pull a new gate to be analyzed out of the future.
pullNewGate :: EvalCirc (Maybe Gate)
pullNewGate = do
  s <- getExpState
  case (future s) of
    (h:t) -> do setExpState (s { future = t } )
                return (Just h)
    []    -> return Nothing

-- | Modify the future gates.
changeFuture :: [Gate] -> EvalCirc ()
changeFuture gs = do
  s <- getExpState
  setExpState (s { future = gs } )
  return ()

-- | Update the future using the given parameter function. Return two sets
-- of 'gateId's that got modified: the first set concerns the controls,
-- the second set the NOT gates.
updateFuture :: (Gate -> Gate) -> EvalCirc (IS.IntSet,IS.IntSet)
updateFuture f = do
  s <- getExpState
  let ((_,!gsModifCtls,!gsModifNots),new_future) = 
              L.mapAccumL (\(gid,gs,gs') g -> let g' = f g in
                                        ((
                                        gid+1
                                        ,
                                        if (ctlsOfGate g == ctlsOfGate g') 
                                        then gs
                                        else IS.insert gid gs
                                        ,
                                        if (wireOfGate g == wireOfGate g') 
                                        then gs'
                                        else IS.insert gid gs'
                                        ),
                                        g'))
                        (1 + (gateId s), IS.empty,IS.empty) (future s)
  changeFuture new_future
  
  return (gsModifCtls,gsModifNots)

-- | Store a gate in the past.
storeOldGate :: Gate -> EvalCirc ()
storeOldGate g = do
  s <- getExpState
  let p = past s
  seq g $ seq p $ setExpState (s { past = g:p } )
  return ()

-- | Increase the '@gateId@' (i.e., go forward).
incrGateId :: EvalCirc ()
incrGateId = do
  s <- getExpState
  setExpState (s { gateId = 1 + (gateId s) } )
  return ()

-- | Get the set of all wires.
getAllWiresInCirc :: EvalCirc IS.IntSet
getAllWiresInCirc = do
  s <- getExpState
  return (allWiresInCirc s)

-- | Set the set of all wires.
setAllWiresInCirc :: IS.IntSet -> EvalCirc ()
setAllWiresInCirc ws = do
  s <- getExpState
  ws `seq` setExpState (s {allWiresInCirc = ws})
  return ()

-- | Remove a gate from the set of all wires.
removeFromAllWiresInCirc :: Int -> EvalCirc ()
removeFromAllWiresInCirc w = do
  ws <- getAllWiresInCirc
  setAllWiresInCirc $ IS.delete w ws
  return ()

-- | Get the algebraic representation of the set of wires.
getExpMap :: EvalCirc (IM.IntMap (S.Set (Exp,Int)))
getExpMap = do
  s <- getExpState
  s `seq` return (expMap s)

-- | Set the algebraic representation of the state of wires.
setExpMap :: (IM.IntMap (S.Set (Exp,Int))) -> EvalCirc ()
setExpMap m = do
  s <- getExpState
  m `seq` setExpState (s { expMap = m } )
  return ()

-- | Update the database recording the controlled wires.
updateUsedControlWires :: (UsedWire -> UsedWire) -> EvalCirc ()
updateUsedControlWires f = do
  s <- getExpState
  let c = f $ usedControlWires s
  c `seq` setExpState (s { usedControlWires = c } )
  return ()

-- | Update the database recording the NOT gates.
updateUsedNotWires :: (UsedWire -> UsedWire) -> EvalCirc ()
updateUsedNotWires f = do
  s <- getExpState
  let c = f $ usedNotWires s
  c `seq` setExpState (s { usedNotWires = c } )
  return ()

-- | Update the list of output wires.
updateOutWires :: ([Wire] -> [Wire]) -> EvalCirc ()
updateOutWires f = do
  s <- getExpState
  let c = f $ outWires s
  c `seq` setExpState (s { outWires = c } )
  return ()

-- | Add a gate ID to the list of gates to skip.
addToSkipGates :: GateId -> Gate -> EvalCirc ()
addToSkipGates id g = do
  s <- getExpState
  let c = IM.insert id g (gates_to_skip s)
  c `seq` setExpState (s {gates_to_skip = c} )
  return ()

-- | Send a gate to the end of the future.
sendEndOfTime :: Gate -> EvalCirc ()
sendEndOfTime g = do
   s <- getExpState
   changeFuture ((future s) ++ [g])
   return ()

-- | Place a gate at the given gate ID in the future.
shiftGate :: Gate -> GateId -> EvalCirc ()
shiftGate g x = do
   s <- getExpState
   let (!head, !tail) = splitAt x (future s)
   let z = head ++ [g] ++ tail
   z `Seq.deepseq` changeFuture z
   return ()

-- ----------------------------------------------------------------------
-- ** Auxiliary functions

-- | @pairEqualExp m1 m2 ws@: returns a list of pairs of wires @(x,y)@
-- such that @m2 x = m1 x = m1 y@.
pairEqualExp :: (IM.IntMap [Exp]) -> (IM.IntMap [Exp]) -> [Wire] -> [(Wire,Wire)]
pairEqualExp m1 m2 ws = 
  L.map fst $ L.filter aux $ L.zip pair_ws (L.map value pair_ws)
  where
    all_pairs l = [(x,y) | x <- l, y <- l]
    pair_ws = all_pairs ws
    value (x,y) = (m2 IM.! x, m1 IM.! x, m1 IM.! y)
    aux ((_,_),(a,b,c)) = a == b && b == c

-- | From a set of expressions (annotated with sizes), prune the ones
-- whose size is larger than /n/.
pruneListExp :: Int -> S.Set (Exp,Int) -> S.Set (Exp,Int)
pruneListExp n l = S.filter (\x -> snd x <= n) l


-- ----------------------------------------------------------------------
-- ** The algebraic optimization automaton          
 
-- | Perform a set of filters acting on one gate at a time, looking
-- for:
-- 
--     * gates having no effect;
--
--     * orphan NOT-gates (i.e. NOT gates negating an out-wire) ;
-- 
--     * simple copy-cats (both positive and negative) ;
--
--     * hidden copy-cats.
--
-- Return 'False' when the end of the circuit is reached, 'True' otherwise. 
stepEvalCirc :: EvalCirc Bool
stepEvalCirc = do
  m_before <- getExpMap
  trace ("the state of the system is " ++ (show $ m_before)) $ return ()
  s <- getExpState
  if ((gateId s) `mod` 1000 == 0) then trace ("Timestamp... " ++ (show (gateId s))) (return ()) else return ()
  s <- getExpState
  trace ("outside wires " ++ (show $ outWires s)) $ return ()
  maybe_g <- pullNewGate
  trace ("pulled new gate " ++ (show maybe_g)) $ return ()
  s <- getExpState
  case maybe_g of

    Nothing -> return False
      
    Just g -> do -- analyze the gate
      m_before <- getExpMap
      let m_after = expEvalGate m_before g
      
      case g of
        
        NoOp -> error "stepEvalCirc cannot deal with NoOp"
        
        Init b w | not ((IM.member w $ usedNotWires s) || (IM.member w $ usedControlWires s) || L.elem w (outWires s))-> do 
          trace "got an orphan init, removing it" $ return ()
          storeOldGate NoOp -- store a placeholder for the gate
          incrGateId
          removeFromAllWiresInCirc w
          -- we could also clean expMap from the reference to w but I think it makes no gain
          return True
        
        Init _ _ -> do
          trace "got a regular init" $ return ()
          storeOldGate g
          setExpMap m_after
          incrGateId
          return True
        
        Cnot w _ | not $ S.null $ S.intersection (m_before IM.! w) (m_after IM.! w) -> do
          trace "got a cnot where no change happened..." $ return ()
          trace (show m_before) $ return ()
          trace (show m_after) $ return ()
          storeOldGate NoOp
          incrGateId
          return True

        Cnot w [] | not (L.elem w $ outWires s) -> do
          trace "got a not-gate that can be removed..." $ return ()
          s <- getExpState
          -- update future
          changeFuture $ L.map (flipCtl w) $ future s
          s <- getExpState
          trace (show $ future s) $ return ()
          storeOldGate NoOp
          incrGateId
          return True
        
        
        Cnot w ctls | otherwise -> do
          trace "got a general cnot" $ return ()
          trace ("state after the gate is " ++ (show m_after)) $ return ()
          
          allWs <- getAllWiresInCirc
          s <- getExpState
          let my_elem x = not (L.elem x $ outWires s)
          let all_ws = IS.toAscList $ IS.filter future_ctl $
                       IS.filter (\x -> my_elem x) $ -- not (L.elem x $ outWires s)) $
                       IS.filter (\x -> not $ S.null $ 
                                         S.intersection (m_after IM.! x)
                                                        (m_after IM.! w)) $
                       IS.filter (w /=) allWs -- IS.fromList $ L.map fst ctls 
                where
                  future_ctl x = 
                    (lastUsedWire (usedNotWires s) x) <= gateId s
                    &&
                    (lastUsedWire (usedNotWires s) w) <= gateId s

          let all_ws_neg = IS.toAscList $ IS.filter future_ctl $
                       IS.filter (\x -> not (L.elem x $ outWires s)) $
                       IS.filter (\x -> not $ S.null $ 
                                         S.intersection (m_after IM.! x)
                                                        (S.map (\(e,i) -> (exp_not e, i)) (m_after IM.! w))) $
                       IS.filter (w /=) $ IS.fromList $ L.map fst ctls
                where
                  future_ctl x = 
                    (lastUsedWire (usedNotWires s) x) <= gateId s
                    &&
                    (lastUsedWire (usedNotWires s) w) <= gateId s

          trace ("List of outside wires: " ++ (show $ outWires s)) (return ())
          trace ("List of available wires: " ++ (show all_ws)) (return ())
          trace ("List of available wires with neg: " ++ (show all_ws_neg)) (return ())
          
          
          case all_ws of
            
            [] -> do
              
              case all_ws_neg of
                [] -> do
                   
                   case g of
                     NoOp -> error "stepEvalCirc cannot deal with NoOp"

                     Init _ _ -> error "this is not supposed to arrive: a cnot became an init" -- setExpMap m_after
                     Cnot w ctls -> do
                       -- There is no "simple" copy-cat...
                       -- Let's try to find a hidden one.
                       
                       s <- getExpState

                       -- This helper function take a wire and look in
                       -- the past for the closest cnot acting on it
                       let getOlderCnot w = case (do set <- IM.lookup w (usedNotWires s); IS.lookupLT (gateId s) set) of
                            Nothing -> Nothing -- there is no previous not
                            Just g' ->         -- there is one not... let's check that it is a cnot
                             case ((past s) !! ((gateId s) - g' - 1)) of
                             Cnot _ [ctl] -> Just (g',ctl)
                             _ -> Nothing
                       
                       -- Helper acting on controls: only return
                       -- something if it is a single control.
                       let getOlderCnot_actOnCtls w1 [(w,b)] = do -- monad Maybe
                                   other_ctl <- getOlderCnot w1
                                   other_ctl `seq` return ((w,b),other_ctl)
                           getOlderCnot_actOnCtls _ _ = Nothing
                       
                       let retrieveHiddenCnot w1 ctls = do -- monad Maybe
                               -- if (L.elem w $ outWires s) then Nothing
                               -- else return ()
                               ((w2,b2),(g',(w3,b3))) <- getOlderCnot_actOnCtls w1 ctls
                               -- make sure w2 and w3 are distinct
                               if (w2 == w3) then Nothing else return ()
                               let m = m_after
                               -- check for the property w1 == w2 oplus w3
                               if (S.null $ S.intersection
                                      [exp_xor x y | (x,_) <- m IM.! w2, (y,_) <- m IM.! w3]
                                      [x | (x,_) <- m IM.! w1])
                               then Nothing
                               -- We have two CNOT candidates for hidden copy-cat.
                               else if ((not (L.elem w2 $ outWires s))
                                   &&
                                   (lastUsedWire (usedNotWires s) w2) <= gateId s
                                   &&
                                   (lastUsedWire (usedControlWires s) w2) <= gateId s)
                               then Just ((w2,b2),(w3,b3))
                               else if ((not (L.elem w3 $ outWires s))
                                        &&
                                        (lastUsedWire (usedNotWires s) w3) <= g'
                                        &&
                                        (lastUsedWire (usedControlWires s) w3) <= g')
                               then Just ((w3,b3),(w2,b2))
                               else Nothing
                       
                       case retrieveHiddenCnot w ctls of
                         Just ((w2,b2),(w3,b3)) -> -- we have a hidden cnot candidate. Great.
                            -- w2 is the wire that is not used with NOT in future
                            do
                            
                            trace "found one hidden copy-cat" $ return ()
                            updateOutWires $ map (\x -> if x == w then w2 else x) 
                            
                            (gsModifCtls,gsModifNots) <- updateFuture $ moveWire w w2
                            
                            trace ("moving " ++ (show w) ++ " to " ++ (show w2)) $ return ()
                            trace (show gsModifCtls) $ return ()
                            trace (show gsModifNots) $ return ()
                            
                            
                            s <- getExpState
                            trace ("before: usedNotWire = " ++ (show $ usedNotWires s)) $ return ()

                            updateUsedControlWires $ \c -> 
                                     IM.alter (\maybe_gs -> case maybe_gs of
                                                  Just gs -> Just $ IS.union gs gsModifCtls
                                                  Nothing -> Just gsModifCtls)  w2 $ 
                                     IM.update (\gs -> Just $ IS.difference gs gsModifCtls) w c
                            
                            updateUsedControlWires $ \c -> 
                                     IM.update (\gs -> Just $ IS.delete (gateId s) gs) w2 c
                            updateUsedControlWires $ \c -> 
                                     IM.alter (\maybe_gs -> case maybe_gs of
                                                  Just gs -> Just $ IS.insert (gateId s) gs
                                                  Nothing -> Just $ IS.singleton (gateId s)) w3 c
                            
                            updateUsedNotWires $ \c -> 
                                     IM.alter (\maybe_gs -> case maybe_gs of
                                                   Just gs -> Just $ IS.union gs gsModifNots
                                                   Nothing -> Just gsModifNots) w2 $ 
                                     IM.update (\gs -> Just $ IS.difference gs gsModifNots) w c
                            
                            updateUsedNotWires $ \c -> 
                                     IM.update (\gs -> Just $ IS.delete (gateId s) gs) w $
                                     IM.alter (\maybe_gs -> case maybe_gs of
                                                  Just gs -> Just $ IS.insert (gateId s) gs
                                                  Nothing -> Just $ IS.singleton (gateId s)) w2 c
                            
                            s <- getExpState
                            trace ("after: usedNotWire = " ++ (show $ usedNotWires s)) $ return ()

                            -- Update ExpMap
                            setExpMap $ IM.insert w (m_before IM.! w) $
                                        IM.insert w2 (m_after IM.! w) m_after
                            
                            storeOldGate $ Cnot w2 [(w3,True)]
                            incrGateId
                            return True
                            
                         _ -> -- No hidden Cnot, let's proceed...
                            do
                            let mw = m_after IM.! w
                            f <- if ((S.foldl' (\a (_,i) -> min a i) 3 mw) <= 1) 
                                 then return id 
                                 else do
                                      v <- newFreshVar
                                      return (S.insert (exp_var $ fromIntegral v, 1))
                            setExpMap $ IM.adjust (\a -> pruneListExp 3 a) w $ 
                                        IM.adjust f w m_after
          
                            storeOldGate g
                            incrGateId
                            return True

                -----------------
                -- Case of simple copy-cats
                (w':_) -> do
                   s <- getExpState
                   updateOutWires $ map (\x -> if x == w then w' else x)
                   
                   s <- getExpState
                   trace (show $ future s) $ return ()
                   (gsModifCtls,_) <- updateFuture $ moveWireFlip w w'
                   
                   -- update expMap: now, w is null and w' is not(old w)
                   expMap <- getExpMap
                   
                   setExpMap $ IM.insert w (m_before IM.! w) $
                               IM.insert w' (S.map (\(e,i) -> (exp_not e,i)) (expMap IM.! w')) expMap
                   
                   
                   
                   trace ("moving " ++ (show w) ++ " to " ++ (show w')) $ return ()
                   trace (show gsModifCtls) $ return ()
                   s <- getExpState
                   trace (show $ future s) $ return ()
                   
                   s <- getExpState
                   updateUsedControlWires $ \c -> 
                            IM.alter (\maybe_gs -> case maybe_gs of
                                     Just gs -> Just $ IS.union gs gsModifCtls
                                     Nothing -> Just gsModifCtls) w' $ 
                            IM.update (\gs -> Just $ IS.difference gs gsModifCtls) w c
                   updateUsedNotWires $ \c -> 
                            IM.update (\gs -> Just $ IS.delete (gateId s) gs) w c

                   storeOldGate (Cnot w' []) -- Set a flip on the w' wire 
                   
                   incrGateId
                   
                   return True
     
                
                   
            (w':_) -> do
              
              s <- getExpState
              updateOutWires $ map (\x -> if x == w then w' else x) 

              s <- getExpState
              trace (show $ future s) $ return ()
              trace ("usedNotWire = " ++ (show $ usedNotWires s)) $ return ()
              (gsModifCtls,_) <- updateFuture $ moveWire w w'
              
              trace ("moving " ++ (show w) ++ " to " ++ (show w')) $ return ()
              trace (show gsModifCtls) $ return ()
              s <- getExpState
              trace (show $ future s) $ return ()
              
              s <- getExpState
              updateUsedControlWires $ \c -> 
                       IM.alter (\maybe_gs -> case maybe_gs of
                                     Just gs -> Just $ IS.union gs gsModifCtls
                                     Nothing -> Just gsModifCtls
                                     ) w' $ 
                       IM.update (\gs -> Just $ IS.difference gs gsModifCtls) w c
              updateUsedNotWires $ \c -> 
                       IM.update (\gs -> Just $ IS.delete (gateId s) gs) w c
              
              storeOldGate NoOp -- replace g with NoOp so that gateId stays accurate
              incrGateId
              
              return True


-- | Shuffle the circuit by sending the CNOT gates as far as
-- possible (i.e., until they hit a control, or to the end).
-- Return 'False' when the end of the circuit is reached, 'True' otherwise. 
stepSwapCirc :: EvalCirc Bool
stepSwapCirc = do
  s <- getExpState
  
  case (IM.lookup (gateId s) (gates_to_skip s)) of
    
    Just g -> do 
      
      storeOldGate g
      incrGateId
      return True
    
    Nothing -> do
      
      maybe_g <- pullNewGate
      trace ("pulled new gate " ++ (show maybe_g)) $ return ()
      s <- getExpState
      if ((gateId s) `mod` 1000 == 0) then trace ("Timestamp (swap)... " ++ (show (gateId s))) {-(s `Seq.deepseq` (setExpState s))-} (return ())  else return ()
      case maybe_g of
      
        Nothing -> return False
        
        Just g@(Cnot w1 [(w2,b2)]) | IM.notMember (gateId s) (gates_to_skip s) -> do -- got a CNOT
        
          trace ("got a cnot to analyze " ++ (show $ gateId s) ++ " " ++ (show $ gates_to_skip s)) $ return ()
          
          let id = min (nextUsedGate (usedNotWires s) (gateId s) (1 + sizeCirc s) w2) $
                       (nextUsedGate (usedControlWires s) (gateId s) (1 + sizeCirc s) w1)
          
          trace ("found id = " ++ (show id)) $ return ()
          
          if ( id >  1 + gateId s ) --  && (id <= (sizeCirc s) )
            then do ------------- there is something to move!
              trace ("can be shifted to " ++ (show (id - 1))) $ return ()
              
              addToSkipGates (id - 1) g
              -- shiftGate g (id - 1 - (gateId s))
              
              s <- getExpState
              trace (show $ future s) $ return ()
              
              -- Remove references to (gateId s)
              
              updateUsedControlWires $ \c -> 
                       IM.update (\gs -> Just $ IS.delete (gateId s) gs) w2 c
              updateUsedNotWires $ \c -> 
                       IM.update (\gs -> Just $ IS.delete (gateId s) gs) w1 c
              
              -- Shift the ones between (gateId s) and id
              
              updateUsedNotWires $
                       IM.map $ IS.map $ \x -> if (x <= gateId s) || (x >= id) then x 
                                               else x - 1
              updateUsedControlWires $
                       IM.map $ IS.map $ \x -> if (x <= gateId s) || (x >= id) then x 
                                               else x - 1
              
              s <- getExpState
              let z = IM.mapKeys (\x -> if (x <= gateId s) || (x >= id) then x 
                                    else x - 1) (gates_to_skip s) in
                 z `seq` setExpState (s { gates_to_skip = z} )
      
              -- Set g in position (id - 1)
                    
              updateUsedControlWires $ \c -> 
                       IM.alter (\maybe_gs -> case maybe_gs of
                                    Just gs -> Just $ IS.insert (id - 1) gs
                                    Nothing -> Just $ IS.singleton (id - 1)) w2 c
              updateUsedNotWires $ \c -> 
                       IM.alter (\maybe_gs -> case maybe_gs of
                                     Just gs -> Just $ IS.insert (id - 1) gs
                                     Nothing -> Just $ IS.singleton (id - 1)) w1 c
              
              -- Make sure we skip (id - 1) later on.
              
              
          else do ------------- nothing to move...    
              trace "cannot be shifted" $ return ()
              storeOldGate g
              incrGateId
              
          return True
          
        Just g -> do
          trace ("got a random " ++ (show g)) $ return ()
          storeOldGate g
          incrGateId
          return True



-- | A more elementary version of @'stepSwapCirc'@: shuffle the
-- circuit by sending to the end all the NOT gates that can be sent
-- there. Return 'False' when the end of the circuit is reached,
-- 'True' otherwise.
stepSwapCirc_simple  :: EvalCirc Bool
stepSwapCirc_simple = do
  maybe_g <- pullNewGate
  trace ("pulled new gate " ++ (show maybe_g)) $ return ()
  s <- getExpState
  case maybe_g of

    Nothing -> return False
    
    Just g | (gateId s) == (length $ past s) + (length $ future s) -> do
        storeOldGate g
        return False 
          
    Just g@(Cnot w1 [(w2,b2)]) | 
        (lastUsedWire (usedNotWires s) w2) <= gateId s && 
        (lastUsedWire (usedNotWires s) w1) <= gateId s &&
        (lastUsedWire (usedControlWires s) w1) <= gateId s -> do -- got a CNOT

      trace "got a cnot that can be sent to the end" $ return ()
      
      sendEndOfTime g
      -- do not store gate, but increase gateId
      incrGateId
      return True
      
    Just g -> do
      storeOldGate g
      incrGateId
      return True

-- ----------------------------------------------------------------------
-- ** Some wrappers

-- | Run the monad until 'False' occurs.
runWhile :: Monad m => (a -> Bool) -> m a -> m ()
runWhile f c = do
  r <- c
  if f r then runWhile f c else return ()

-- | Strip the 'NoOp' gates from a list of gates.
stripNoOp :: [Gate] -> [Gate]
stripNoOp = L.filter (/= NoOp) 

-- | Wrapper around 'stepEvalCirc'.
alg_simplify :: ([Gate],[Wire]) -> ([Gate],[Wire])
alg_simplify (gs,out) = (stripNoOp gs',out')
  where
    gs' = (reverse $ past s) ++ (future s)
    out' = outWires s
    ws_in = getAllWires gs
    s = runEvalCirc ws_in out gs $ trace "Starting new circuit!" (runWhile id stepEvalCirc)

-- | Wrapper around 'stepSwapCirc'.
alg_swap :: ([Gate],[Wire]) -> ([Gate],[Wire])
alg_swap (gs,out) = (stripNoOp gs',out')
  where
    gs' = (reverse $ past s) ++ (future s)
    out' = outWires s
    ws_in = getAllWires gs
    s = runEvalCirc ws_in out gs $ trace "Starting new circuit!" (runWhile id stepSwapCirc)


-- | Wrapper around 'stepSwapCirc_simple'.
alg_swap_simple :: ([Gate],[Wire]) -> ([Gate],[Wire])
alg_swap_simple (gs,out) = (stripNoOp gs',out')
  where
    gs' = (reverse $ past s) ++ (future s)
    out' = outWires s
    ws_in = getAllWires gs
    s = runEvalCirc ws_in out gs $ trace "Starting new circuit!" (runWhile id stepSwapCirc_simple)

-- ----------------------------------------------------------------------
-- * Multi-pass optimization

-- | Auxiliary function. Simultaneously compute the maximum of the
-- lengths of two lists, and their point-wise equality.
is_equal_list :: Eq a => [a] -> [a] -> Int -> (Int,Bool)

is_equal_list [] [] n                      = (n,True)
is_equal_list (h1:t1) (h2:t2) n | h1 == h2 = is_equal_list t1 t2 (n+1)
is_equal_list t1 t2 n                        = (n + max (length t1) (length t2),False)

-- | Get the list of initialized wires from a circuit.
get_list_init :: [Gate] -> [Wire]
get_list_init ((Init _ w):gs) = w:(get_list_init gs)
get_list_init (g:gs) = get_list_init gs
get_list_init [] = []

-- | Do several passes of @'alg_simplify'@ until it reaches a fixed point.
simplRec' :: ([Gate],[Wire]) -> ([Gate],[Wire])
simplRec' (l,output) = trace (show (l,output)) $ 
   let (l',output') = alg_simplify (l, output) in
   let (n,b) = is_equal_list l l' 0 in
   if b then (l,output) 
   else trace (show n) simplRec' $ suppressGarbageGates (l',output')

-- | Do several passed of @'alg_swap'@ followed with @'simplRec'@
-- until it reaches a fixed point.
simplRec :: ([Gate],[Wire]) -> ([Gate],[Wire])
simplRec (l1,o1) = 
      let (l3,o3) = simplRec' $ alg_swap (l1,o1) in
      let (n,b) = is_equal_list l1 l3 0 in
      if b then (l3,o3) 
      else trace "Swapping!" $ simplRec $ (l3,o3)
