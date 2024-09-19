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
  match (p1, p2, p3) with
  | (Piece X, Piece X, Piece X) -> true
  | (Piece O, Piece O, Piece O) -> true
  | _ -> false
;;

let winner (board : board) : bool =
  let ((r1c1, r1c2, r1c3), (r2c1, r2c2, r2c3), (r3c1, r3c2, r3c3)) = board in

  let row1 = win r1c1 r1c2 r1c3 in
  let row2 = win r2c1 r2c2 r2c3 in
  let row3 = win r3c1 r3c2 r3c3 in

  let col1 = win r1c1 r2c1 r3c1 in
  let col2 = win r1c2 r2c2 r3c2 in
  let col3 = win r1c3 r2c3 r3c3 in

  let diag1 = win r1c1 r2c2 r3c3 in
  let diag2 = win r1c3 r2c2 r3c1 in

  row1 || row2 || row3 || col1 || col2 || col3 || diag1 || diag2
;;