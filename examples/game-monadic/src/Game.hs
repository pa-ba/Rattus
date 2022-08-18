{-# LANGUAGE TypeOperators #-}
module Main where

import Behaviour
import Rattus.ToHaskell
import Graphics.Gloss.Interface.Pure.Game
import Graphics.Gloss.Data.Color
import Rattus

noInput = Input False NoMove 0

type World = (Float,Float,Float,Trans Input (PadPos :* Pos) ,Input)


initial :: World
initial = (0,0,0,runTransducer pong, noInput)

render :: World -> Picture
render (x,y,pad,_,_) = 
  Pictures
  [ translate x y
    (Color white (ThickCircle 3 6))
    --(translate (-8) (0.5) (Color white (Scale 0.14 (-0.14) (Text "y"))))
  , (Color white (Polygon [(pad-20,-size_y/2+5),(pad+20,-size_y/2+5),
                           (pad+20,-size_y/2+10),(pad-20,-size_y/2+10)]))
  , Color white (Line [(-size_x/2,-size_y/2),(-size_x/2,size_y/2)
                      ,(size_x/2,size_y/2),(size_x/2,-size_y/2)])]

handleEvent :: Event -> World -> World
handleEvent e (x,y,pad,s,_) = (x,y,pad,s,inp)
  where inp =
          case e of
            (EventKey (SpecialKey KeySpace) Down _ _) ->
              Input {reset = True, move = NoMove, time = 0}
            (EventKey (SpecialKey KeyLeft) Down _ _) ->
              Input {reset = False, move = StartLeft, time = 0}
            (EventKey (SpecialKey KeyLeft) Up _ _) ->
              Input {reset = False, move = EndLeft, time = 0}
            (EventKey (SpecialKey KeyRight) Down _ _) ->
              Input {reset = False, move = StartRight, time = 0}
            (EventKey (SpecialKey KeyRight) Up _ _) ->
              Input {reset = False, move = EndRight, time = 0}
            _ -> noInput

step :: Float -> World -> World
step f (_,_,_,Trans st,b) = (x,y,pad,st',noInput)
  where ((PadPos pad:*(x:*y)),st') = st (b {time = 4*f})
  



main :: IO ()
main = play
       (InWindow "press [spacebar] to reset the game" (size_x',size_y') (100,100))
       black
       60
       initial
       render
       handleEvent
       step
