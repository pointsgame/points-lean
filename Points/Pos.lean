/--
x goes right, y goes down
-/
def Pos (width height : Nat) : Type :=
  Fin width × Fin height

namespace Pos

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
