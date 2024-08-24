/--
x goes right, y goes down
-/
def Pos (width height: Nat): Type :=
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

abbrev Adjacent (pos₁: Pos width height) (pos₂: Pos width height): Prop :=
  AdjacentRight pos₁ pos₂ ∨
  AdjacentLeft pos₁ pos₂ ∨
  AdjacentBottom pos₁ pos₂ ∨
  AdjacentTop pos₁ pos₂ ∨
  AdjacentBottomRight pos₁ pos₂ ∨
  AdjacentTopLeft pos₁ pos₂ ∨
  AdjacentTopRight pos₁ pos₂ ∨
  AdjacentBottomLeft pos₁ pos₂

theorem adjacent_to_bottom_right {pos₁ pos₂ pos₃: Pos width height} (adj_r: AdjacentRight pos₁ pos₂) (adj_b: AdjacentBottom pos₂ pos₃): AdjacentBottomRight pos₁ pos₃ := by
  apply And.intro
  exact adj_b.left ▸ adj_r.left
  exact adj_r.right ▸ adj_b.right

theorem adjacent_to_top_right {pos₁ pos₂ pos₃: Pos width height} (adj_r: AdjacentRight pos₁ pos₂) (adj_t: AdjacentTop pos₂ pos₃): AdjacentTopRight pos₁ pos₃ := by
  apply And.intro
  exact adj_t.left ▸ adj_r.left
  exact adj_r.right ▸ Eq.symm adj_t.right

instance {pos₁ pos₂: Pos width height}: Coe (AdjacentRight pos₁ pos₂) (Adjacent pos₁ pos₂) where
  coe := .inl

instance {pos₁ pos₂: Pos width height}: Coe (AdjacentLeft pos₁ pos₂) (Adjacent pos₁ pos₂) where
  coe := .inr ∘ .inl

instance {pos₁ pos₂: Pos width height}: Coe (AdjacentBottom pos₁ pos₂) (Adjacent pos₁ pos₂) where
  coe := .inr ∘ .inr ∘ .inl

instance {pos₁ pos₂: Pos width height}: Coe (AdjacentTop pos₁ pos₂) (Adjacent pos₁ pos₂) where
  coe := .inr ∘ .inr ∘ .inr ∘ .inl

instance {pos₁ pos₂: Pos width height}: Coe (AdjacentBottomRight pos₁ pos₂) (Adjacent pos₁ pos₂) where
  coe := .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inl

instance {pos₁ pos₂: Pos width height}: Coe (AdjacentTopLeft pos₁ pos₂) (Adjacent pos₁ pos₂) where
  coe := .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inl

instance {pos₁ pos₂: Pos width height}: Coe (AdjacentTopRight pos₁ pos₂) (Adjacent pos₁ pos₂) where
  coe := .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inl

instance {pos₁ pos₂: Pos width height}: Coe (AdjacentBottomLeft pos₁ pos₂) (Adjacent pos₁ pos₂) where
  coe := .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inr

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

def nw (pos₁: Pos width height): Option $ Σ' pos₂, AdjacentTopLeft pos₁ pos₂ := do
  let ⟨npos, adj₁⟩ ← n pos₁
  let ⟨nwpos, adj₂⟩ ← w npos
  return ⟨nwpos, adjacent_to_bottom_right adj₂ adj₁⟩

def ne (pos₁: Pos width height): Option $ Σ' pos₂, AdjacentTopRight pos₁ pos₂ := do
  let ⟨epos, adj₁⟩ ← e pos₁
  let ⟨nepos, adj₂⟩ ← n epos
  return ⟨nepos, adjacent_to_top_right adj₁ adj₂⟩

def sw (pos₁: Pos width height): Option $ Σ' pos₂, AdjacentBottomLeft pos₁ pos₂ := do
  let ⟨spos, adj₁⟩ ← s pos₁
  let ⟨swpos, adj₂⟩ ← w spos
  return ⟨swpos, adjacent_to_top_right adj₂ adj₁⟩

def se (pos₁: Pos width height): Option $ Σ' pos₂, AdjacentBottomRight pos₁ pos₂ := do
  let ⟨epos, adj₁⟩ ← e pos₁
  let ⟨sepos, adj₂⟩ ← s epos
  return ⟨sepos, adjacent_to_bottom_right adj₁ adj₂⟩
