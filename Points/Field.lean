import Points.Pos
import Points.Player
import Points.Point

variable {width height: Nat}

structure Field where
  scoreRed: Nat
  scoreBlack: Nat
  moves: List (Pos width height × Player)
  lastSurroundPlayer: Player
  points: Array Point -- TODO: use Vector from Batteries when it's available in release
  size_eq: points.size = width * height

def cell (field: @Field width height) (pos: Pos width height): Point :=
  field.points.get <| pos.toFin.cast field.size_eq.symm

def isPuttingAllowed (field: @Field width height) (pos: Pos width height): Bool :=
  (cell field pos).isPuttingAllowed

def isPlayer (field: @Field width height) (pos: Pos width height) (player: Player): Bool :=
  (cell field pos).isPlayer player

def isPlayersPoint (field: @Field width height) (pos: Pos width height) (player: Player): Bool :=
  (cell field pos).isPlayersPoint player

def isCapturedPoint (field: @Field width height) (pos: Pos width height) (player: Player): Bool :=
  (cell field pos).isCapturedPoint player

def emptyField: @Field width height :=
  { scoreRed := 0
  , scoreBlack := 0
  , moves := []
  , lastSurroundPlayer := Player.red
  , points := mkArray (width * height) Point.EmptyPoint
  , size_eq := Array.size_mkArray ..
  }
