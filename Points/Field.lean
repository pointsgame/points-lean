import Points.Pos
import Points.Player
import Points.Point

variable {width height: Nat}

structure NonEmptyList (a: Type) where
  mk ::
  list: List a
  nonEmpty: list ≠ []

-- TODO: use Vector from Batteries when it's available in release
structure Vector (a: Type) (n: Nat) where
  mk ::
  array: Array a
  size_eq: array.size = n

namespace Vector
  def get (vector: Vector a n) (i: Fin n): a :=
    vector.array.get <| i.cast vector.size_eq.symm

  def set (vector: Vector a n) (i: Fin n) (x: a): Vector a n :=
    ⟨vector.array.set (Fin.cast vector.size_eq.symm i) x, by simp [vector.size_eq]⟩
end Vector

structure Field where
  scoreRed: Nat
  scoreBlack: Nat
  moves: List $ Pos width height × Player
  points: Vector Point $ width * height

namespace Field

def point (field: @Field width height) (pos: Pos width height): Point :=
  field.points.get pos.toFin

def isPuttingAllowed (field: @Field width height) (pos: Pos width height): Bool :=
  (field.point pos).isPuttingAllowed

def isPlayer (field: @Field width height) (pos: Pos width height) (player: Player): Bool :=
  (field.point pos).isPlayer player

def isPlayersPoint (field: @Field width height) (pos: Pos width height) (player: Player): Bool :=
  (field.point pos).isPlayersPoint player

def isCapturedPoint (field: @Field width height) (pos: Pos width height) (player: Player): Bool :=
  (field.point pos).isCapturedPoint player

def isEmptyBase (field: @Field width height) (pos: Pos width height) (player: Player): Bool :=
  field.point pos == Point.EmptyBasePoint player

def emptyField: @Field width height :=
  { scoreRed := 0
  , scoreBlack := 0
  , moves := []
  , points := Vector.mk (mkArray (width * height) Point.EmptyPoint) $ Array.size_mkArray ..
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

def skewProduct (pos₁: Pos width height) (pos₂: Pos width height): Int :=
  match pos₁, pos₂ with
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => Int.ofNat x₁ * Int.ofNat y₂ - Int.ofNat y₁ * Int.ofNat x₂

def buildChain (field: @Field width height) (startPos nextPos: Pos width height) (adj: Pos.Adjacent startPos nextPos) (player: Player): Option $ NonEmptyList $ Pos width height := Id.run do
  let mut chain := [startPos]
  -- ⟨centerPos, pos, adj⟩
  let mut inv: Σ' pos₁ pos₂, Pos.Adjacent pos₁ pos₂ := ⟨startPos, nextPos, adj⟩
  let mut square := skewProduct startPos nextPos
  repeat
    if chain.contains inv.2.1 then
      chain := chain.dropWhile (· != inv.2.1)
    else
      chain := inv.2.1 :: chain
    inv := ⟨inv.2.1, inv.1, Pos.adjacent_symm inv.2.2⟩
    let mut direction := Pos.rotate_not_adjacent $ Pos.direction inv.2.2
    repeat
      if let Option.some ⟨pos, adj⟩ := Pos.direction_to_pos direction inv.1 then
        if pos == startPos || field.isPlayer pos player then
          inv := ⟨inv.1, pos, adj⟩
          break
      direction := Pos.rotate direction
    square := square + skewProduct inv.1 inv.2.1
    if inv.2.1 = startPos then
      break
  if square < 0
  then
    if h: chain.length > 2
    then Option.some $ NonEmptyList.mk chain $ List.length_pos.mp $ Nat.zero_lt_of_lt h
    else Option.none
  else Option.none

inductive IntersectionState where
  | None: IntersectionState
  | Up: IntersectionState
  | Target: IntersectionState
  | Down: IntersectionState
deriving BEq, Hashable, Repr, Inhabited

def getIntersectionState (pos: Pos width height) (nextPos: Pos width height): IntersectionState :=
  if nextPos.fst <= pos.fst
  then match Int.ofNat nextPos.snd - Int.ofNat pos.snd with
       | 1 => IntersectionState.Up
       | 0 => IntersectionState.Target
       | -1 => IntersectionState.Down
       | _ => IntersectionState.None
  else IntersectionState.None

def posInsideRing (pos: Pos width height) (ring: NonEmptyList $ Pos width height): Bool := Id.run do
  let mut intersections := 0
  let mut state := IntersectionState.None
  for nextPos in ring.list do
    match getIntersectionState pos nextPos with
    | IntersectionState.None => state := IntersectionState.None
    | IntersectionState.Up => if state == IntersectionState.Down then
                                intersections := intersections + 1
                              state := IntersectionState.Up
    | IntersectionState.Down => if state == IntersectionState.Up then
                                  intersections := intersections + 1
                                state := IntersectionState.Down
    | IntersectionState.Target => ()
  if state == IntersectionState.Up || state == IntersectionState.Down then
    let mut beginState := IntersectionState.None
    for nextPos in ring.list do
      beginState := getIntersectionState pos nextPos
      if beginState != IntersectionState.Target then
        break
    if state == IntersectionState.Up && beginState == IntersectionState.Down ||
       state == IntersectionState.Down && beginState == IntersectionState.Up then
      intersections := intersections + 1
  intersections % 2 == 1

def getInsideRing (pos: Pos width height) (ring: NonEmptyList $ Pos width height): Lean.HashSet $ Pos width height :=
  let ringSet := Lean.HashSet.ofList ring.list
  wave' pos (!ringSet.contains ·)

def getEmptyBaseChain (field: @Field width height) (startPos: Pos width height) (player: Player): Option $ NonEmptyList $ Pos width height := Id.run do
  let mut pos := startPos
  repeat
    if let Option.some pos' := pos.w then
      pos := pos'.fst
    else
      break
    if field.isPlayer pos player then
      let inputPoints := field.getInputPoints pos player
      let chains := inputPoints.filterMap fun ⟨⟨chainPos, adj⟩, _⟩ => field.buildChain pos chainPos adj player
      if let Option.some chain := chains.find? (posInsideRing startPos) then
        return chain
  Option.none

def capture (player: Player) (point: Point): Point :=
  match point with
  | Point.EmptyPoint => Point.BasePoint player false
  | Point.PlayerPoint player' => if player' == player
                                 then Point.PlayerPoint player'
                                 else Point.BasePoint player true
  | Point.BasePoint player' enemy => if player' == player
                                     then Point.BasePoint player' enemy
                                     else if enemy
                                     then Point.PlayerPoint player
                                     else Point.BasePoint player false
  | Point.EmptyBasePoint _ => Point.BasePoint player false

def putPoint (field: @Field width height) (pos: Pos width height) (player: Player) (_: isPuttingAllowed field pos = true): @Field width height :=
  let point := field.point pos
  let newMoves := ⟨pos, player⟩ :: field.moves
  if point == Point.EmptyBasePoint player then
    { scoreRed := field.scoreRed
    , scoreBlack := field.scoreBlack
    , moves := newMoves
    , points := field.points.set pos.toFin $ Point.PlayerPoint player
    }
  else
    let enemyPlayer := player.next
    let inputPoints := field.getInputPoints pos player
    let captures: List $ _ × _ := inputPoints.filterMap fun ⟨⟨chainPos, chainAdj⟩, ⟨capturedPos, _⟩⟩ =>
      (field.buildChain pos chainPos chainAdj player).map fun chain => ⟨chain, (getInsideRing capturedPos chain).toList⟩
    let capturedCount := List.length ∘ List.filter fun pos' => field.isPlayersPoint pos' enemyPlayer
    let freedCount := List.length ∘ List.filter fun pos' => field.isCapturedPoint pos' player
    let ⟨emptyCaptures, realCaptures⟩ := captures.partition fun ⟨_, captured⟩ => capturedCount captured == 0
    let capturedTotal := Nat.sum $ realCaptures.map (capturedCount ·.snd)
    let freedTotal := Nat.sum $ realCaptures.map (freedCount ·.snd)
    let realCaptured := realCaptures >>= (·.snd)
    if point == Point.EmptyBasePoint enemyPlayer then
      let enemyEmptyBaseChain := field.getEmptyBaseChain pos enemyPlayer
      let enemyEmptyBase := (enemyEmptyBaseChain.elim Lean.HashSet.empty $ getInsideRing pos).toList.filter fun pos' => field.isEmptyBase pos' enemyPlayer
      if captures.isEmpty then
        { scoreRed := if player == Player.red then field.scoreRed else field.scoreRed + 1
        , scoreBlack := if player == Player.black then field.scoreBlack else field.scoreBlack + 1
        , moves := newMoves
        , points := let points₁ := field.points.set pos.toFin $ Point.PlayerPoint player
                    let points₂ := enemyEmptyBase.foldr (fun pos' points => points.set pos'.toFin $ Point.BasePoint enemyPlayer $ pos' == pos) points₁
                    points₂
        }
      else
        { scoreRed := if player == Player.red then field.scoreRed + capturedTotal else field.scoreRed - freedTotal
        , scoreBlack := if player == Player.black then field.scoreBlack + capturedTotal else field.scoreBlack - freedTotal
        , moves := newMoves
        , points := let points₁ := field.points.set (Pos.toFin pos) $ Point.PlayerPoint player
                    let points₂ := enemyEmptyBase.foldr (fun pos' points => points.set (Pos.toFin pos') Point.EmptyPoint) points₁
                    let points₃ := realCaptured.foldr (fun pos' points => points.set (Pos.toFin pos') $ capture player (field.point pos')) points₂
                    points₃
        }
    else
      let newEmptyBase := (emptyCaptures >>= (·.snd)).filter fun pos' => field.point pos' == Point.EmptyPoint
      { scoreRed := if player == Player.red then field.scoreRed + capturedTotal else field.scoreRed - freedTotal
      , scoreBlack := if player == Player.black then field.scoreBlack + capturedTotal else field.scoreBlack - freedTotal
      , moves := newMoves
      , points := let points₁ := field.points.set (Pos.toFin pos) $ Point.PlayerPoint player
                  let points₂ := newEmptyBase.foldr (fun pos' points => points.set (Pos.toFin pos') $ Point.EmptyBasePoint player) points₁
                  let points₃ := realCaptured.foldr (fun pos' points => points.set (Pos.toFin pos') $ capture player (field.point pos')) points₂
                  points₃
      }

instance: Repr $ @Field width height where
  reprPrec field _ := Id.run do
    let mut s := ""
    for y in Fin.list height do
      for x in Fin.list width do
        s := s.push $ match field.point ⟨x, y⟩ with
        | Point.PlayerPoint Player.red => 'X'
        | Point.PlayerPoint Player.black => 'O'
        | Point.BasePoint Player.red true => 'o'
        | Point.BasePoint Player.black true => 'x'
        | Point.BasePoint _ false => ','
        | _ => '.'
      s := s.push '\n'
    return s
