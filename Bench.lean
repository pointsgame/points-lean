import Mathlib.Control.Random
import Mathlib.Algebra.Group.Prod
import Points.Pos
import Points.Player
import Points.Field
import Cli

open Cli

def allMoves (width height: Nat): List $ Pos width height := do
  let y ← Fin.list height
  let x ← Fin.list width
  return ⟨x, y⟩

def shuffle (array: Array a): Rand $ Array a := do
  let mut inv: Σ' arr: Array a, array.size = arr.size := ⟨array, rfl⟩
  for i in Fin.list array.size do
    let j ← (Random.randFin (n := array.size - 1)).map $ Fin.cast $ Nat.sub_one_add_one_eq_of_pos i.size_pos
    inv := ⟨inv.1.swap (Fin.cast inv.2 i) (Fin.cast inv.2 j), by simp [inv.2]⟩
  return inv.1

def randomGame (width height: Nat): Rand $ @Field width height := do
  let mut field := Field.emptyField
  let moves ← shuffle $ Array.mk $ allMoves width height
  for pos in moves do
    if h: field.isPuttingAllowed pos then
      field := field.putNextPoint pos h
  return field

structure Result where
  mk ::
  red: Nat
  black: Nat
deriving BEq, Hashable, Repr, Inhabited

def randomGamesResult (games width height: Nat): Rand Result := do
  let mut red := 0
  let mut black := 0
  for _ in [0:games.succ] do
    let field ← randomGame width height
    match field.winner with
    | Option.some Player.red => red := red + 1
    | Option.some Player.black => black := black + 1
    | Option.none => pure ()
  return { red, black }

def runBench (p: Parsed): IO UInt32 := do
  let exit := do p.printHelp
                 @IO.Process.exit Nat 0
  let width ← (p.flag? "width" >>= (·.as? Nat)).elim exit pure
  let height ← (p.flag? "height" >>= (·.as? Nat)).elim exit pure
  let games ← (p.flag? "games-number" >>= (·.as? Nat)).elim exit pure
  let seed ← (p.flag? "seed" >>= (·.as? Nat)).elim exit pure
  let result := IO.runRandWith seed $ randomGamesResult games width height
  IO.println s!"{result.red}:{result.black}"
  return 0

def benchCmd: Cmd := `[Cli|
  exampleCmd VIA runBench; ["0.0.1"]
  "Field benchmark."

  FLAGS:
    w, width: Nat; "Filed width."
    h, height: Nat; "Filed height."
    n, "games-number": Nat; "Games number."
    s, seed: Nat; "RNG seed."
]

def main: List String → IO UInt32 :=
  benchCmd.validate
