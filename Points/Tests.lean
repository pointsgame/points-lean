import LSpec
import Points.Pos
import Points.Player
import Points.Field
import Init.Data.Array.QSort

structure GenField where
  width: Nat
  height: Nat
  field: @Field width height
deriving Repr

def constructField (image: String): Option GenField :=
  match (image.split (· == '\n')).filter (· != "") with
  | [] => Option.none
  | lines@(h :: _) => Id.run do
    let width := h.length
    let height := lines.length
    let moves: List $ Char × Pos width height := do
      let ⟨line, y⟩ ← lines.zip (Fin.list height)
      let ⟨c, x⟩ ← line.toList.zip (Fin.list width)
      return ⟨c, ⟨x, y⟩⟩
    let moves := moves.filter fun ⟨c, _⟩ => c.toLower != c.toUpper
    let moves := moves.toArray.qsort (·.fst < ·.fst)
    let moves: Array (Pos width height × Player) := moves.map fun ⟨c, pos⟩ => ⟨pos, if c.isLower then Player.red else Player.black⟩
    let field := moves.foldlM (fun field ⟨pos, player⟩ => if h: field.isPuttingAllowed pos
                                                          then Option.some $ field.putPoint pos player h
                                                          else Option.none) $ @Field.emptyField width height
    field.map fun field => { width, height, field }

def simpleSurround := constructField "
.a.
cBa
.a.
"

def surroundEmptyTerritory := constructField "
.a.
a.a
.a.
"

def movePriority := constructField "
.aB.
aCaB
.aB.
"

def movePriorityBig := constructField "
.B..
BaB.
aCaB
.aB.
"

def onionSurroundings := constructField "
...c...
..cBc..
.cBaBc.
..cBc..
...c...
"

def deepOnionSurroundings := constructField "
...D...
..DcD..
.DcBcD.
DcBaBcD
.DcBcD.
..DcD..
...D...
"

def applyControlSurroundingInSameTurn := constructField "
.a.
aBa
.a.
"

def doubleSurround := constructField "
.a.a.
aAbAa
.a.a.
"

def doubleSurroundWithEmptyPart := constructField "
.b.b..
b.zAb.
.b.b..
"

def shouldNotLeaveEmptyInside := constructField "
.aaaa..
a....a.
a.b...a
.z.bC.a
a.b...a
a....a.
.aaaa..
"

def surroundInOppositeTurn := constructField "
.a.
aBa
.a.
"

def partlySurroundInOppositeTurn := constructField "
.a..
aBa.
.a.a
..a.
"

def holeInsideSurrounding := constructField "
....c....
...c.c...
..c...c..
.c..a..c.
c..a.a..c
.c..a..c.
..c...c..
...cBc...
....d....
"

def holeInsideSurroundingAfterOppositeTurnSurrounding := constructField "
....b....
...b.b...
..b...b..
.b..a..b.
b..a.a..b
.b..a..b.
..b...b..
...bCb...
....b....
"

def surroundingDoesNotExpand := constructField "
....a....
...a.a...
..a.a.a..
.a.a.a.a.
a.a.aBa.a
.a.a.a.a.
..a.a.a..
...a.a...
....a....
"

def twoSurroundingsWithCommonBorder := constructField "
.a..
aAa.
.bAa
..a.
"

def twoSurroundingsWithCommonDot := constructField "
.a.a.
aBcBa
.a.a.
"

def threeSurroundingsWithCommonBorders := constructField "
..a..
.aAa.
..bAa
.aAa.
..a..
"

def twoSurroundingsWithCommonDotOneBorderlineEmptyPlace := constructField "
..a..
.aBa.
..c.a
.aBa.
..a..
"

#lspec
  LSpec.test "simple surround" (simpleSurround.elim false fun field => field.field.scoreRed = 1 && field.field.scoreBlack == 0) $
  LSpec.test "surround empty territory" (surroundEmptyTerritory.elim false fun field => field.field.scoreRed == 0 && field.field.scoreBlack == 0) $
  LSpec.test "move priority" (movePriority.elim false fun field => field.field.scoreRed == 0 && field.field.scoreBlack == 1) $
  LSpec.test "move priority, big" (movePriorityBig.elim false fun field => field.field.scoreRed == 0 && field.field.scoreBlack == 2) $
  LSpec.test "onion surroundings" (onionSurroundings.elim false fun field => field.field.scoreRed == 4 && field.field.scoreBlack == 0) $
  LSpec.test "deep onion surroundings" (deepOnionSurroundings.elim false fun field => field.field.scoreRed == 0 && field.field.scoreBlack == 9)
  -- applyControlSurroundingInSameTurn
  -- doubleSurround
  -- doubleSurroundWithEmptyPart
  -- shouldNotLeaveEmptyInside
  -- surroundInOppositeTurn
  -- partlySurroundInOppositeTurn
  -- holeInsideSurrounding
  -- holeInsideSurroundingAfterOppositeTurnSurrounding
  -- surroundingDoesNotExpand
  -- twoSurroundingsWithCommonBorder
  -- twoSurroundingsWithCommonDot
  -- threeSurroundingsWithCommonBorders
  -- twoSurroundingsWithCommonDotOneBorderlineEmptyPlace
