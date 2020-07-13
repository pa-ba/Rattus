{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RebindableSyntax #-}
module Behaviour where


import GHC.Float
import Rattus
import Rattus.Yampa
import Rattus.Events hiding (map)
import Prelude hiding ((<*>),zip,map,scan,zipWith)
import Data.Maybe

data Input = Input {reset :: ! Bool, move :: ! Move}
data Move = StartLeft | EndLeft | StartRight | EndRight | NoMove deriving Eq

{-# ANN module Rattus #-}

ifThenElse True x _ = x
ifThenElse False _ y = y


type Vel = (Float:* Float)
type Pos = (Float:* Float)

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
type Object = Pos -> Maybe Normal

-- | List of all static objects in the game (i.e. the walls and the
-- ceiling)
staticObjects :: [Object]
staticObjects =
  [ \(x:*y) -> if size_x/2-5 <= x then Just (-1:*0) else Nothing
  , \(x:*y) -> if size_y/2-5 <= y then Just (0:* -1) else Nothing
  , \(x:*y) -> if x <= -size_x/2+5 then Just (1:*0) else Nothing
  ]


checkCollision :: [Object] -> Pos -> Maybe Normal
checkCollision objs p =
  listToMaybe $ mapMaybe (\f -> f p) (objs ++ staticObjects)


applyCollision :: Normal -> Vel -> Vel
applyCollision (nx:*ny) (vx:*vy)
  | nx > 0 && vx < 0 = (-vx:*vy)
  | nx < 0 && vx > 0 = (-vx:*vy)
  | ny > 0 && vy < 0 = (vx:* -vy)
  | ny < 0 && vy > 0 = (vx:* -vy)
  | otherwise = (vx:*vy)

velTrans :: [Object] -> Pos -> Vel -> Vel
velTrans objs p v = (x:* y)
  where (x:*y) = maybe v (`applyCollision` v) (checkCollision objs p)



movePadD :: Float -> Input -> Float -> Float
movePadD _ Input{move = StartRight} _ = 10
movePadD _ Input{move = StartLeft} _ = -10
movePadD pos Input{move = m} delta
  | ((m == EndLeft || pos <= (-size_x/2+20)) && delta < 0)
    || ((m == EndRight || pos >= (size_x/2-20)) && delta > 0) = 0
movePadD _ _ delta = if delta < 100 && delta > -100 then delta * 1.3 else delta


padPos :: SF Input Float
padPos = loopPre 0 run where
  run :: SF (Input, Float) (Float, O Float)
  run = proc (inp, vel) -> do
    pos <- integral 0 -< vel
    let vel' = movePadD pos inp vel
    returnA -< (pos, delay vel')
        


padObj :: Float -> Object
padObj p (x :* y) =
  if y <= -size_y/2+13 && y >= -size_y/2+5  && x >= p-20 && x <= p+20
  then Just (0 :* 1)
  else Nothing

ballPos :: SF (Float :* Input) Pos
ballPos = loopPre (20:*50) run where
  run :: SF ((Float :* Input), Vel) (Pos, O Vel)
  run  = proc ((pad :* inp),v) -> do
    p <- integral (0:*0) -< v
    let v' = velTrans [padObj pad] p v
    returnA -< (p, delay v')


pong :: SF Input (Pos :* Float)
pong = proc inp -> do
  pad <- padPos -< inp
  let ev = if reset inp then Just' ballPos else Nothing'
  ball <- rSwitch ballPos -< ((pad :* inp), ev)
  returnA -< (ball :* pad)
