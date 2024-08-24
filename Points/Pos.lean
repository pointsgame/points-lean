/--
x goes right, y goes down
-/
def Pos (width height : Nat) : Type :=
  Fin width × Fin height

namespace Pos

abbrev AdjacentRight: Pos width height → Pos width height → Prop
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => x₁.succ = x₂.castSucc ∧ y₁ = y₂

abbrev AdjacentBottom: Pos width height → Pos width height → Prop
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => x₁ = x₂ ∧ y₁.succ = y₂.castSucc

abbrev AdjacentBottomRight: Pos width height → Pos width height → Prop
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => x₁.succ = x₂.castSucc ∧ y₁.succ = y₂.castSucc

abbrev AdjacentTopRight: Pos width height → Pos width height → Prop
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => x₁.succ = x₂.castSucc ∧ y₁.castSucc = y₂.succ

abbrev AdjacentLeft (pos₁: Pos width height) (pos₂: Pos width height): Prop :=
  AdjacentRight pos₂ pos₁

abbrev AdjacentTop (pos₁: Pos width height) (pos₂: Pos width height): Prop :=
  AdjacentBottom pos₂ pos₁

abbrev AdjacentTopLeft (pos₁: Pos width height) (pos₂: Pos width height): Prop :=
  AdjacentBottomRight pos₂ pos₁

abbrev AdjacentBottomLeft (pos₁: Pos width height) (pos₂: Pos width height): Prop :=
  AdjacentTopRight pos₂ pos₁

theorem adjacent_to_bottom_right {pos₁ pos₂ pos₃ : Pos width height} (adj_r: AdjacentRight pos₁ pos₂) (adj_b: AdjacentBottom pos₂ pos₃): AdjacentBottomRight pos₁ pos₃ := by
  apply And.intro
  exact adj_b.left ▸ adj_r.left
  exact adj_r.right ▸ adj_b.right

theorem adjacent_to_top_right {pos₁ pos₂ pos₃ : Pos width height} (adj_r: AdjacentRight pos₁ pos₂) (adj_t: AdjacentTop pos₂ pos₃): AdjacentTopRight pos₁ pos₃ := by
  apply And.intro
  exact adj_t.left ▸ adj_r.left
  exact adj_r.right ▸ Eq.symm adj_t.right

def n (pos₁: Pos width height): Option $ Σ' pos₂, AdjacentTop pos₁ pos₂ :=
  match pos₁ with
  | ⟨_, ⟨0, _⟩⟩ => Option.none
  | ⟨x, ⟨Nat.succ y, h⟩⟩ => Option.some ⟨⟨x, ⟨y, Nat.lt_of_succ_lt h⟩⟩, by apply And.intro; rfl; rfl⟩

def s (pos₁: Pos width height): Option $ Σ' pos₂, AdjacentBottom pos₁ pos₂ :=
  let y := ↑pos₁.snd.succ
  if h: y < height
  then Option.some ⟨⟨pos₁.fst, ⟨y, h⟩⟩, by apply And.intro; rfl; rfl⟩
  else Option.none

def w (pos₁: Pos width height): Option $ Σ' pos₂, AdjacentLeft pos₁ pos₂ :=
  match pos₁ with
  | ⟨⟨0, _⟩, _⟩ => Option.none
  | ⟨⟨Nat.succ x, h⟩, y⟩ => Option.some ⟨⟨⟨x, Nat.lt_of_succ_lt h⟩, y⟩, by apply And.intro; rfl; rfl⟩

def e (pos₁: Pos width height): Option $ Σ' pos₂, AdjacentRight pos₁ pos₂ :=
  let x := ↑pos₁.fst.succ
  if h: x < width
  then Option.some ⟨⟨⟨x, h⟩, pos₁.snd⟩, by apply And.intro; rfl; rfl⟩
  else Option.none
