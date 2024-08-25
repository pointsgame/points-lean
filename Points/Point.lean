import Points.Player

inductive Point where
  | EmptyPoint: Point
  | PlayerPoint: Player → Point
  | BasePoint: Player → Bool → Point
  | EmptyBasePoint: Player → Point
deriving BEq, Hashable, Repr, Inhabited

namespace Point

def isPuttingAllowed: Point → Bool
  | EmptyPoint => true
  | EmptyBasePoint _ => true
  | _ => false

def isPlayer (point: Point) (player: Player): Bool :=
  match point with
  | PlayerPoint p => p == player
  | BasePoint p _ => p == player
  | _ => false

def isPlayersPoint (point: Point) (player: Player): Bool :=
  point == PlayerPoint player

def isCapturedPoint (point: Point) (player: Player): Bool :=
  point == BasePoint player.next true
