/--
x goes right, y goes down
-/
def Pos (width height : Nat) : Type :=
  Fin width × Fin height

namespace Pos

abbrev AdjacentRight (pos₁: Pos width height) (pos₂: Pos width height): Prop :=
  match pos₁, pos₂ with
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => x₁.succ = x₂.castSucc ∧ y₁ = y₂

abbrev AdjacentBottom (pos₁: Pos width height) (pos₂: Pos width height): Prop :=
  match pos₁, pos₂ with
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => x₁ = x₂ ∧ y₁.succ = y₂.castSucc

abbrev AdjacentBottomRight (pos₁: Pos width height) (pos₂: Pos width height): Prop :=
  match pos₁, pos₂ with
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => x₁.succ = x₂.castSucc ∧ y₁.succ = y₂.castSucc

abbrev AdjacentTopRight (pos₁: Pos width height) (pos₂: Pos width height): Prop :=
  match pos₁, pos₂ with
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => x₁.succ = x₂.castSucc ∧ y₁.castSucc = y₂.succ

abbrev AdjacentLeft (pos₁: Pos width height) (pos₂: Pos width height): Prop :=
  AdjacentRight pos₂ pos₁

abbrev AdjacentTop (pos₁: Pos width height) (pos₂: Pos width height): Prop :=
  AdjacentBottom pos₂ pos₁

abbrev AdjacentTopLeft (pos₁: Pos width height) (pos₂: Pos width height): Prop :=
  AdjacentBottomRight pos₂ pos₁

abbrev AdjacentBottomLeft (pos₁: Pos width height) (pos₂: Pos width height): Prop :=
  AdjacentTopRight pos₂ pos₁

def n (pos₁: Pos width height): Option $ Σ' pos₂: Pos width height, AdjacentTop pos₁ pos₂ :=
  match pos₁ with
  | ⟨_, ⟨0, _⟩⟩ => Option.none
  | ⟨x, ⟨Nat.succ y, h⟩⟩ => Option.some ⟨⟨x, ⟨y, Nat.lt_of_succ_lt h⟩⟩, by apply And.intro; rfl; rfl⟩

def s (pos₁: Pos width height): Option $ Σ' pos₂: Pos width height, AdjacentBottom pos₁ pos₂ :=
  let y := ↑pos₁.snd.succ
  if h: y < height
  then Option.some ⟨⟨pos₁.fst, ⟨y, h⟩⟩, by apply And.intro; rfl; rfl⟩
  else Option.none

def w (pos₁: Pos width height): Option $ Σ' pos₂: Pos width height, AdjacentLeft pos₁ pos₂ :=
  match pos₁ with
  | ⟨⟨0, _⟩, _⟩ => Option.none
  | ⟨⟨Nat.succ x, h⟩, y⟩ => Option.some ⟨⟨⟨x, Nat.lt_of_succ_lt h⟩, y⟩, by apply And.intro; rfl; rfl⟩

def e (pos₁: Pos width height): Option $ Σ' pos₂: Pos width height, AdjacentRight pos₁ pos₂ :=
  let x := ↑pos₁.fst.succ
  if h: x < width
  then Option.some ⟨⟨⟨x, h⟩, pos₁.snd⟩, by apply And.intro; rfl; rfl⟩
  else Option.none
