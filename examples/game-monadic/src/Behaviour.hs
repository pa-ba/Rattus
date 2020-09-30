{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS -fplugin=Rattus.Plugin #-}

module Behaviour where

import Rattus

import MStream as MStr
import Rattus.Stream (Str)

import Prelude hiding ((<*>),zip,map,zipWith)

import Control.Eff.Reader.Strict
import Control.Eff

data Input = Input {reset :: ! Bool, move :: ! Move, time :: !Float}
data Move = StartLeft | EndLeft | StartRight | EndRight | NoMove

{-# ANN module Rattus #-}

type Vel = (Float:* Float)
type Pos = (Float:* Float)

newtype PadPos = PadPos {unPadBox :: Float}

size_x', size_y' :: Int
size_x' = 500
size_y' = 500

size_x = fromIntegral size_x'
size_y = fromIntegral size_y'

-- | vector addtition
(.+.) :: Pos -> Pos -> Pos
(x1:*y1) .+. (x2:*y2) = (x1+x2:*y1+y2)

-- | scalar multiplication
(.*.) :: Float -> Pos -> Pos
s .*. (x:*y) = (s*x:*s*y)


type Normal = (Float:* Float)


-- | Objects may cause collissions. Given a position, an object checks
-- whether a collusion occurred and if so returns the normal vector of
-- the surface
type Object = Pos -> Maybe' Normal

-- | List of all static objects in the game (i.e. the walls and the
-- ceiling)
staticObjects :: List Object
staticObjects =
  (\(x:*_) -> if size_x/2-5 <= x then Just' (-1:*0) else Nothing') :!
  (\(_:*y) -> if size_y/2-5 <= y then Just' (0:* -1) else Nothing') :!
  (\(x:*_) -> if x <= -size_x/2+5 then Just' (1:*0) else Nothing') :! Nil
  


checkCollision :: List Object -> Pos -> Maybe' Normal
checkCollision objs p =
  listToMaybe' $ mapMaybe' (\f -> f p) (objs +++ staticObjects)


applyCollision :: Normal -> Vel -> Vel
applyCollision (nx:*ny) (vx:*vy)
  | nx > 0 && vx < 0 = (-vx:*vy)
  | nx < 0 && vx > 0 = (-vx:*vy)
  | ny > 0 && vy < 0 = (vx:* -vy)
  | ny < 0 && vy > 0 = (vx:* -vy)
  | otherwise = (vx:*vy)

velTrans :: List Object -> Pos -> Vel -> Float -> Vel
velTrans objs p v _ = (x:* y)
  where (x:*y) = maybe' v (`applyCollision` v) (checkCollision objs p)



movePadD :: Input -> Float -> Float
movePadD Input{move = StartRight} _ = 10
movePadD Input{move = StartLeft} _ = -10
movePadD Input{move = EndLeft} delta | delta < 0 = 0
movePadD Input{move = EndRight} delta | delta > 0 = 0
movePadD _ delta = if delta < 100 && delta > -100 then delta * 1.3 else delta


padStep :: '[Input] < r => (Float :* Float) -> Eff r (Float :* Float)
padStep (delta :* pos) = do
  inp <- ask
  let delta' = movePadD inp delta
  let pos' = min (max (-size_x/2+20) (pos + delta' * time inp)) (size_x/2-20)
  return (delta' :* pos')


padPos :: '[Input] < r => EStr r Float
padPos = mapPure (box snd') (MStr.unfold (box padStep) (0:* 0))


padObj :: Float -> Object
padObj p (x :* y) =
  if y <= -size_y/2+13 && y >= -size_y/2+5  && x >= p-20 && x <= p+20
  then Just' (0 :* 1)
  else Nothing'

ballPos :: '[PadPos, Input] < r => EStr r Pos
ballPos = mapPure (box fst') (MStr.unfold (box ballStep) ((0:*0):*(20:*50)))


ballStep :: '[PadPos, Input] < r => (Pos :* Vel) -> Eff r (Pos :* Vel)
ballStep (p :* v) = do
  PadPos pad <- ask
  inp <- ask
  let v' = velTrans (padObj pad :! Nil) p v (time inp)
  return (p .+. (time inp .*. v') :* v')


ballTrig :: '[Input, PadPos] < r => Eff r (Maybe' (EStr r Pos))
ballTrig = do
  inp <- ask
  return (if reset inp then Just' ballPos else Nothing')

pongM :: EStr '[Reader Input] (PadPos :* Pos)
pongM = runReaderStr ballPos' (MStr.mapPure (box PadPos) padPos)
  where ballPos' = MStr.switch (box ballTrig) ballPos


pong :: Str Input -> Str (PadPos :* Pos)
pong = runEffStr . runReaderStr' pongM
