type piece = 
| X
| O

type pos = 
| Piece of piece
| Blank

type board = (pos * pos * pos) * (pos * pos * pos) * (pos * pos * pos)

type row_index = 
| Top
| Middle
| Bottom

type col_index = 
| Left
| Middle
| Right

type pos_index = row_index * col_index
val get_pos : board -> pos_index -> pos

let get_pos (board : board) ((row, col) : pos_index) : pos =
  let (r1, r2, r3) = board in
  let row_index = match row with
    | Top -> r1
    | Middle -> r2
    | Bottom -> r3
  in
  let (c1, c2, c3) = row_index in
    match col with
    | Left -> c1
    | Middle -> c2
    | Right -> c3
    ;;

let win p1 p2 p3 =
  