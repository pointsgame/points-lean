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

def wave [Monad m] (startPos: Pos width height) (f: Pos width height → m Bool): m Unit := do
  let neighborhood (pos: Pos width height): List $ Pos width height :=
    [pos.n', pos.s', pos.w', pos.e'].filterMap (·.map (·.fst))
  unless ← f startPos do
    return
  let mut q := Std.Queue.empty
  q := q.enqueue startPos
  repeat
    if let Option.some ⟨next, rest⟩ := q.dequeue? then
      q := rest
      for pos in neighborhood next do
        if ← f pos then
          q := q.enqueue pos
    else
      break
  return

def wave' (startPos: Pos width height) (f: Pos width height → Bool): Lean.HashSet $ Pos width height :=
  let fState (pos: Pos width height): StateM (Lean.HashSet $ Pos width height) Bool := do
    let passed ← StateT.get
    if !passed.contains pos && f pos then
      StateT.set $ passed.insert pos
      return true
    else
      return false
  (StateT.run (wave startPos fState) Lean.HashSet.empty).snd
