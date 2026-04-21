module H = Hashtbl

open Value

exception HeapError of string

type t = {
  store : (int, value) H.t;
  mutable next_address : int;
}

let create () = {
  store = H.create 1024;
  next_address = 1;
}

let alloc h v =
  let addr = h.next_address in
  h.next_address <- h.next_address + 1;
  H.replace h.store addr v;
  addr

let read h addr =
  match H.find_opt h.store addr with
  | Some v -> v
  | None -> raise @@ HeapError "Heap.read: nil pointer"

let write h addr v =
  H.replace h.store addr v
