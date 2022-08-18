{-# LANGUAGE TypeOperators #-}
module Main where

import Behaviour
import Rattus.ToHaskell
import Graphics.Gloss.Interface.Pure.Game
import Graphics.Gloss.Data.Color
import Rattus

noInput = Input False False NoMove 0

type World = (List (Float :* Float),Float,Trans Input (List Pos :* Float) ,Input)


initial :: World
initial = (Nil,0,runTransducer pong, noInput)

render :: World -> Picture
render (bs,pad,_,_) = 
  Pictures
  ([ (Color white (Polygon [(pad-20,-size_y/2+5),(pad+20,-size_y/2+5),
                           (pad+20,-size_y/2+10),(pad-20,-size_y/2+10)]))
  , Color white (Line [(-size_x/2,-size_y/2),(-size_x/2,size_y/2)
                      ,(size_x/2,size_y/2),(size_x/2,-size_y/2)])]
  ++ map' (\ (x :* y) -> translate x y
    (Color white (ThickCircle 3 6))) bs)

map' :: (a -> b) -> List a -> [b]
map' _ Nil = []
map' f (x :! xs) = f x : map' f xs

handleEvent :: Event -> World -> World
handleEvent e (bs,pad,s,_) = (bs,pad,s,inp)
  where inp =
          case e of
            (EventKey (SpecialKey KeyDelete) Down _ _) ->
              Input {addBall = False, removeBall = True, move = NoMove, time = 0}
            (EventKey (SpecialKey KeySpace) Down _ _) ->
              Input {addBall = True, removeBall = False, move = NoMove, time = 0}
            (EventKey (SpecialKey KeyLeft) Down _ _) ->
              Input {addBall = False, removeBall = False, move = StartLeft, time = 0}
            (EventKey (SpecialKey KeyLeft) Up _ _) ->
              Input {addBall = False, removeBall = False, move = EndLeft, time = 0}
            (EventKey (SpecialKey KeyRight) Down _ _) ->
              Input {addBall = False, removeBall = False, move = StartRight, time = 0}
            (EventKey (SpecialKey KeyRight) Up _ _) ->
              Input {addBall = False, removeBall = False, move = EndRight, time = 0}
            _ -> noInput

step :: Float -> World -> World
step f (_,_,Trans st,b) = (bs,pad,st',noInput)
  where ((bs:*pad),st') = st (b {time = 4*f})
  



main :: IO ()
main = play
       (InWindow "press [spacebar] to spawn ball; press [backspace] to remove ball" (size_x',size_y') (100,100))
       black
       60
       initial
       render
       handleEvent
       step
