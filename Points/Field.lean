import Points.Pos
import Points.Player
import Points.Point

structure Field where
  scoreRed: Nat
  scoreBlack: Nat
  moves: List (Pos width height × Player)
  lastSurroundPlayer: Player
  points: Array Point -- TODO: Vector from Batteries

def emptyField {width height: Nat}: Field :=
  { scoreRed := 0
  , scoreBlack := 0
  , moves := []
  , lastSurroundPlayer := Player.red
  , points := mkArray (width * height) Point.EmptyPoint
  }
