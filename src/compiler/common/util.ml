let rec take k xs =
  match k with
  | 0 -> []
  | k -> match xs with
    | [] -> failwith "Util.take"
    | y::ys -> y :: take (k - 1) ys
