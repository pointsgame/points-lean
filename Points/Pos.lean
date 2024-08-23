/--
x goes right, y goes down
-/
def Pos (width height : Nat) : Type :=
  Fin width × Fin height

namespace Pos

def sucx (pos: Pos width height): Pos width.succ height :=
  ⟨pos.fst.succ, pos.snd⟩

def sucy (pos: Pos width height): Pos width height.succ :=
  ⟨pos.fst, pos.snd.succ⟩

inductive AdjacentRight: Pos width height → Pos width height → Type where
  | adj_right: {width height: Nat} → @AdjacentRight width.succ.succ height.succ ⟨0, 0⟩ ⟨1, 0⟩
  | adj_to_right: {width height: Nat} → {pos₁ pos₂: Pos width height} → @AdjacentRight width height pos₁ pos₂ → @AdjacentRight width.succ height (sucx pos₁) (sucx pos₂)
  | adj_to_bottom: {width height: Nat} → {pos₁ pos₂: Pos width height} → @AdjacentRight width height pos₁ pos₂ → @AdjacentRight width height.succ (sucy pos₁) (sucy pos₂)

inductive AdjacentBottom: Pos width height → Pos width height → Type where
  | adj_bottom: {width height: Nat} → @AdjacentBottom width.succ height.succ.succ ⟨0, 0⟩ ⟨0, 1⟩
  | adj_to_right: {width height: Nat} → {pos₁ pos₂: Pos width height} → @AdjacentBottom width height pos₁ pos₂ → @AdjacentBottom width.succ height (sucx pos₁) (sucx pos₂)
  | adj_to_bottom: {width height: Nat} → {pos₁ pos₂: Pos width height} → @AdjacentBottom width height pos₁ pos₂ → @AdjacentBottom width height.succ (sucy pos₁) (sucy pos₂)

inductive AdjacentBottomRight: Pos width height → Pos width height → Type where
  | adj_bottom_right: {width height: Nat} → @AdjacentBottomRight width.succ.succ height.succ.succ ⟨0, 0⟩ ⟨1, 1⟩
  | adj_to_right: {width height: Nat} → {pos₁ pos₂: Pos width height} → @AdjacentBottomRight width height pos₁ pos₂ → @AdjacentBottomRight width.succ height (sucx pos₁) (sucx pos₂)
  | adj_to_bottom: {width height: Nat} → {pos₁ pos₂: Pos width height} → @AdjacentBottomRight width height pos₁ pos₂ → @AdjacentBottomRight width height.succ (sucy pos₁) (sucy pos₂)

inductive AdjacentTopRight: Pos width height → Pos width height → Type where
  | adj_top_right: {width height: Nat} → @AdjacentTopRight width.succ.succ height.succ.succ ⟨0, 1⟩ ⟨1, 0⟩
  | adj_to_right: {width height: Nat} → {pos₁ pos₂: Pos width height} → @AdjacentTopRight width height pos₁ pos₂ → @AdjacentTopRight width.succ height (sucx pos₁) (sucx pos₂)
  | adj_to_bottom: {width height: Nat} → {pos₁ pos₂: Pos width height} → @AdjacentTopRight width height pos₁ pos₂ → @AdjacentTopRight width height.succ (sucy pos₁) (sucy pos₂)

noncomputable def AdjacentLeft (pos₁: Pos width height) (pos₂: Pos width height): Type :=
  AdjacentRight pos₂ pos₁

noncomputable def AdjacentTop (pos₁: Pos width height) (pos₂: Pos width height): Type :=
  AdjacentBottom pos₂ pos₁

noncomputable def AdjacentTopLeft (pos₁: Pos width height) (pos₂: Pos width height): Type :=
  AdjacentBottomRight pos₂ pos₁

noncomputable def AdjacentBottomLeft (pos₁: Pos width height) (pos₂: Pos width height): Type :=
  AdjacentTopRight pos₂ pos₁

def n (pos: Pos width height): Option (Pos width height) :=
  match pos with
  | ⟨_, ⟨0, _⟩⟩ => Option.none
  | ⟨x, ⟨Nat.succ y, h⟩⟩ => Option.some ⟨x, ⟨y, Nat.lt_of_succ_lt h⟩⟩

def s (pos: Pos width height): Option (Pos width height) :=
  match height, pos with
  | 1, ⟨_, ⟨0, _⟩⟩ => Option.none
  | Nat.succ (Nat.succ _), ⟨x, ⟨0, _⟩⟩ => Option.some ⟨x, 1⟩
  | Nat.succ _, ⟨x, ⟨Nat.succ y, h⟩⟩ => (Pos.s ⟨x, ⟨y, Nat.lt_of_succ_lt_succ h⟩⟩).map fun ⟨x₁, y₁⟩ => ⟨x₁, y₁.succ⟩

def w (pos: Pos width height): Option (Pos width height) :=
  match pos with
  | ⟨⟨0, _⟩, _⟩ => Option.none
  | ⟨⟨Nat.succ x, h⟩, y⟩ => Option.some ⟨⟨x, Nat.lt_of_succ_lt h⟩, y⟩

def e (pos: Pos width height): Option (Pos width height) :=
  match width, pos with
  | 1, ⟨⟨0, _⟩, _⟩ => Option.none
  | Nat.succ (Nat.succ _), ⟨⟨0, _⟩, y⟩ => Option.some ⟨1, y⟩
  | Nat.succ _, ⟨⟨Nat.succ x, h⟩, y⟩ => (Pos.s ⟨⟨x, Nat.lt_of_succ_lt_succ h⟩, y⟩).map fun ⟨x₁, y₁⟩ => ⟨x₁.succ, y₁⟩
