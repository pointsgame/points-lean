import Mathlib.Logic.Equiv.Fin

/--
x goes right, y goes down
-/
abbrev Pos (width height: Nat): Type :=
  Fin width × Fin height

namespace Pos

def toFin (pos: Pos width height): Fin $ width * height :=
  finProdFinEquiv pos

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

theorem adjacent_symm {pos₁ pos₂: Pos width height}: Adjacent pos₁ pos₂ → Adjacent pos₂ pos₁
  | Or.inl adj => Or.inr $ Or.inl adj
  | Or.inr $ Or.inl adj => Or.inl adj
  | Or.inr $ Or.inr $ Or.inl adj => Or.inr $ Or.inr $ Or.inr $ Or.inl adj
  | Or.inr $ Or.inr $ Or.inr $ Or.inl adj => Or.inr $ Or.inr $ Or.inl adj
  | Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl adj => Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl adj
  | Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl adj => Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl adj
  | Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl adj => Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr adj
  | Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr adj => Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl adj

theorem adjacent_to_bottom_right {pos₁ pos₂ pos₃: Pos width height} (adj_r: AdjacentRight pos₁ pos₂) (adj_b: AdjacentBottom pos₂ pos₃): AdjacentBottomRight pos₁ pos₃ := by
  apply And.intro
  exact adj_b.left ▸ adj_r.left
  exact adj_r.right ▸ adj_b.right

theorem adjacent_to_top_right {pos₁ pos₂ pos₃: Pos width height} (adj_r: AdjacentRight pos₁ pos₂) (adj_t: AdjacentTop pos₂ pos₃): AdjacentTopRight pos₁ pos₃ := by
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

instance adjacent_top: Coe (AdjacentTop pos₁ pos₂) (Adjacent pos₁ pos₂) where
  coe := .inr ∘ .inr ∘ .inr ∘ .inl

def n' (pos₁: Pos width height): Option $ Σ' pos₂, Adjacent pos₁ pos₂ :=
  (n pos₁).map fun ⟨pos₂, adj⟩ => ⟨pos₂, ↑adj⟩

instance adjacent_bottom: Coe (AdjacentBottom pos₁ pos₂) (Adjacent pos₁ pos₂) where
  coe := .inr ∘ .inr ∘ .inl

def s' (pos₁: Pos width height): Option $ Σ' pos₂, Adjacent pos₁ pos₂ :=
  (s pos₁).map fun ⟨pos₂, adj⟩ => ⟨pos₂, ↑adj⟩

instance adjacent_left: Coe (AdjacentLeft pos₁ pos₂) (Adjacent pos₁ pos₂) where
  coe := .inr ∘ .inl

def w' (pos₁: Pos width height): Option $ Σ' pos₂, Adjacent pos₁ pos₂ :=
  (w pos₁).map fun ⟨pos₂, adj⟩ => ⟨pos₂, ↑adj⟩

instance adjacent_right: Coe (AdjacentRight pos₁ pos₂) (Adjacent pos₁ pos₂) where
  coe := .inl

def e' (pos₁: Pos width height): Option $ Σ' pos₂, Adjacent pos₁ pos₂ :=
  (e pos₁).map fun ⟨pos₂, adj⟩ => ⟨pos₂, ↑adj⟩

instance adjacent_top_left: Coe (AdjacentTopLeft pos₁ pos₂) (Adjacent pos₁ pos₂) where
   coe := .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inl

def nw' (pos₁: Pos width height): Option $ Σ' pos₂, Adjacent pos₁ pos₂ :=
  (nw pos₁).map fun ⟨pos₂, adj⟩ => ⟨pos₂, ↑adj⟩

instance adjacent_top_right: Coe (AdjacentTopRight pos₁ pos₂) (Adjacent pos₁ pos₂) where
   coe := .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inl

def ne' (pos₁: Pos width height): Option $ Σ' pos₂, Adjacent pos₁ pos₂ :=
  (ne pos₁).map fun ⟨pos₂, adj⟩ => ⟨pos₂, ↑adj⟩

instance adjacent_bottom_left: Coe (AdjacentBottomLeft pos₁ pos₂) (Adjacent pos₁ pos₂) where
  coe := .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inr

def sw' (pos₁: Pos width height): Option $ Σ' pos₂, Adjacent pos₁ pos₂ :=
  (sw pos₁).map fun ⟨pos₂, adj⟩ => ⟨pos₂, ↑adj⟩

instance adjacent_bottom_right: Coe (AdjacentBottomRight pos₁ pos₂) (Adjacent pos₁ pos₂) where
  coe := .inr ∘ .inr ∘ .inr ∘ .inr ∘ .inl

def se' (pos₁: Pos width height): Option $ Σ' pos₂, Adjacent pos₁ pos₂ :=
  (se pos₁).map fun ⟨pos₂, adj⟩ => ⟨pos₂, ↑adj⟩

inductive Direction where
  | dir_right: Direction
  | dir_bottom_right: Direction
  | dir_bottom: Direction
  | dir_bottom_left: Direction
  | dir_left: Direction
  | dir_top_left: Direction
  | dir_top: Direction
  | dir_top_right: Direction

open Direction

def inverse: Direction → Direction
  | dir_right => dir_left
  | dir_bottom_right => dir_top_left
  | dir_bottom => dir_top
  | dir_bottom_left => dir_top_right
  | dir_left => dir_right
  | dir_top_left => dir_bottom_right
  | dir_top => dir_bottom
  | dir_top_right => dir_bottom_left

def rotate: Direction → Direction
  | dir_right => dir_bottom_right
  | dir_bottom_right => dir_bottom
  | dir_bottom => dir_bottom_left
  | dir_bottom_left => dir_left
  | dir_left => dir_top_left
  | dir_top_left => dir_top
  | dir_top => dir_top_right
  | dir_top_right => dir_right

def rotate_not_adjacent: Direction → Direction
  | dir_right => dir_bottom_left
  | dir_bottom_right => dir_bottom_left
  | dir_bottom => dir_top_left
  | dir_bottom_left => dir_top_left
  | dir_left => dir_top_right
  | dir_top_left => dir_top_right
  | dir_top => dir_bottom_right
  | dir_top_right => dir_bottom_right

def direction {pos₁ pos₂: Pos width height} (adj: Adjacent pos₁ pos₂): Direction :=
  if h₁: AdjacentRight pos₁ pos₂ then
    dir_right
  else if h₂: AdjacentLeft pos₁ pos₂ then
    dir_left
  else if h₃: AdjacentBottom pos₁ pos₂ then
    dir_bottom
  else if h₄: AdjacentTop pos₁ pos₂ then
    dir_top
  else if h₅: AdjacentBottomRight pos₁ pos₂ then
    dir_bottom_right
  else if h₆: AdjacentTopLeft pos₁ pos₂ then
    dir_top_left
  else if h₇: AdjacentTopRight pos₁ pos₂ then
    dir_top_right
  else if h₈: AdjacentBottomLeft pos₁ pos₂ then
    dir_bottom_left
  else
    False.elim <| by
      apply Or.elim adj
      . exact (absurd · h₁)
      . intro h
        apply Or.elim h
        . exact (absurd · h₂)
        . intro h
          apply Or.elim h
          . exact (absurd · h₃)
          . intro h
            apply Or.elim h
            . exact (absurd · h₄)
            . intro h
              apply Or.elim h
              . exact (absurd · h₅)
              . intro h
                apply Or.elim h
                . exact (absurd · h₆)
                . intro h
                  apply Or.elim h
                  . exact (absurd · h₇)
                  . exact (absurd · h₈)

def direction_to_pos (dir: Direction): (pos₁: Pos width height) → Option $ Σ' pos₂, Adjacent pos₁ pos₂ :=
  match dir with
  | dir_right => e'
  | dir_bottom_right => se'
  | dir_bottom => s'
  | dir_bottom_left => sw'
  | dir_left => w'
  | dir_top_left => nw'
  | dir_top => n'
  | dir_top_right => ne'
