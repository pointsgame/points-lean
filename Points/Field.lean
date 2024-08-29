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

namespace Field

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

def getInputPoints (field: @Field width height) (pos: Pos width height) (player: Player): List $ (Σ' chainPos, Pos.Adjacent pos chainPos) × (Σ' capturedPos, Pos.Adjacent pos capturedPos) :=
  let isDirectionPlayer (dir: (pos₁: Pos width height) → Option $ Σ' pos₂, Pos.Adjacent pos₁ pos₂): Bool :=
        (dir pos).elim false fun ⟨dirPos, _⟩ => field.isPlayer dirPos player
  let list₁ := if not $ isDirectionPlayer Pos.w' then
                 if isDirectionPlayer Pos.nw' then pos.nw'.toList.zip pos.w'.toList
                 else if isDirectionPlayer Pos.n' then pos.n'.toList.zip pos.w'.toList
                 else []
               else
                 []
  let list₂ := if not $ isDirectionPlayer Pos.s' then
                if isDirectionPlayer Pos.sw' then (pos.sw'.toList.zip pos.s'.toList) ++ list₁
                else if isDirectionPlayer Pos.w' then (pos.w'.toList.zip pos.s'.toList) ++ list₁
                else list₁
              else
                list₁
  let list₃ := if not $ isDirectionPlayer Pos.e' then
                if isDirectionPlayer Pos.se' then (pos.se'.toList.zip pos.e'.toList) ++ list₂
                else if isDirectionPlayer Pos.s' then (pos.s'.toList.zip pos.e'.toList) ++ list₂
                else list₂
              else
                list₂
  let list₄ := if not $ isDirectionPlayer Pos.n' then
                if isDirectionPlayer Pos.ne' then (pos.ne'.toList.zip pos.n'.toList) ++ list₃
                else if isDirectionPlayer Pos.e' then (pos.e'.toList.zip pos.n'.toList) ++ list₃
                else list₃
              else
                list₃
  list₄

def buildChain (field: @Field width height) (startPos nextPos: Pos width height) (adj: Pos.Adjacent startPos nextPos) (player: Player): Option $ List $ Pos width height := Id.run do
  let mut chain := [startPos]
  -- ⟨centerPos, pos, adj⟩
  let mut inv: Σ' pos₁ pos₂, Pos.Adjacent pos₁ pos₂ := ⟨startPos, nextPos, adj⟩
  repeat
    if chain.contains inv.2.1 then
      chain := chain.dropWhile (· != inv.2.1)
    else
      chain := inv.2.1 :: chain
    inv := ⟨inv.2.1, inv.1, Pos.adjacent_symm inv.2.2⟩
    let mut direction := Pos.rotate_not_adjacent $ Pos.direction inv.2.2
    repeat
      if let Option.some ⟨pos, adj⟩ := Pos.direction_to_pos direction inv.1 then
        if field.isPlayer pos player then
          inv := ⟨inv.1, pos, adj⟩
          break
      direction := Pos.rotate direction
    if inv.2.1 = startPos then
      break
  -- TODO: check square
  Option.some chain
