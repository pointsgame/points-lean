inductive Player where
  | red : Player
  | black : Player
deriving BEq, Hashable, Repr, Inhabited

instance: ToString Player where
  toString (player : Player) : String :=
    match player with
    | Player.red => "Red"
    | Player.black => "Black"

def Player.next (player : Player) : Player :=
  match player with
  | Player.red => Player.black
  | Player.black => Player.red
