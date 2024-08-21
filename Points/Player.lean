inductive Player where
  | red : Player
  | black : Player

def next (player : Player) : Player :=
  match player with
  | Player.red => Player.black
  | Player.black => Player.red
