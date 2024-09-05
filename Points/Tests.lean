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

def simpleSurroundImage := constructField "
.a.
cBa
.a.
"

-- #eval simpleSurroundImage
