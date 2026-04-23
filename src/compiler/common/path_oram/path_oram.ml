(* Path ORAM — OCaml implementation
   Based on: Meta's path_oram.rs and bucket.rs implementations *)
let () = Random.self_init ()

(* ------------------------------------------------------------------ *)
(* State                                                                *)
(* ------------------------------------------------------------------ *)

type state = {
  height                    : int;
  block_size                : int;
  z                         : int;
  mutable next_address      : int;

  memory                    : Bucket.bucket array;
  (** position.(a) = the leaf index that block `a` is currently assigned to. *)
  (* TODO: Make oblivious (Linear scan works) *)
  position                  : int array;
  (** Buffer of blocks that could not be evicted back into the tree during the last access. *)
  mutable stash             : Bucket.block list;
}

(* ------------------------------------------------------------------ *)
(* Tree helpers                                                         *)
(* ------------------------------------------------------------------ *)

let log2 n =
  let rec aux n acc = if n <= 1 then acc else aux (n lsr 1) (acc + 1) in
  aux n 0

(** The node at level [l] on the path from the root down to leaf [x]. *)
let path_node ~height x l = x lsr (height - l)

(** True if a block assigned to [leaf] may be stored at [node]. *)
let can_place ~height leaf node =
  let l = log2 node in
  (leaf lsr (height - l)) = node


(* ------------------------------------------------------------------ *)
(* Bucket I/O                                                           *)
(* ------------------------------------------------------------------ *)

(** Read all real blocks from the bucket at [node] into the stash,
    replacing the bucket contents with dummies. *)
let read_bucket oram node =
  let real_blocks = Bucket.drain_bucket oram.memory.(node) oram.block_size in
  oram.stash <- real_blocks @ oram.stash

(** Greedily evict up to Z eligible stash blocks into the bucket at [node].
    A block is eligible if its assigned leaf path passes through [node].
    Ineligible and excess blocks remain in the stash. *)
let write_bucket oram node =
  let eligible b =
    not (Bucket.is_dummy b) &&
    can_place ~height:oram.height b.Bucket.position node
  in
  let yes, no = List.partition eligible oram.stash in
  let rec take_drop n = function
    | [] -> ([], [])
    | x :: xs ->
      if n = 0 then ([], x :: xs)
      else let taken, left = take_drop (n - 1) xs in
           (x :: taken, left)
  in
  let to_write, leftover = take_drop oram.z yes in
  oram.stash <- no @ leftover;
  Bucket.fill_bucket oram.memory.(node) to_write oram.block_size

(* ------------------------------------------------------------------ *)
(* Access                                                               *)
(* ------------------------------------------------------------------ *)

(** Read or write logical block [address].
    - [`Read]        — return current value unchanged.
    - [`Write data]  — overwrite block with [data], return old value. *)
let access oram ~address ~op =
  let height     = oram.height in
  let first_leaf = 1 lsl height in
  let num_leaves = 1 lsl height in

  (* 1. Look up current leaf and immediately re-randomise the assignment. *)
  let x           = oram.position.(address) in
  let new_position = first_leaf + Random.int num_leaves in
  oram.position.(address) <- new_position;

  (* 2. Read entire root-to-leaf path into the stash.
        Every access reads the same amount of data — hides which block
        is being accessed from a network observer. *)
  for l = 0 to height do
    read_bucket oram (path_node ~height x l)
  done;

  (* 3. Find the target block in the stash. *)
  (* TODO: Is the Bytes.copy/Bytes.make branching an issue? *)
  (* - It is, instead we should allocate a dedicated dummy block to the stash and return it when we miss deref *)
  let current_data =
    match List.find_opt (fun b -> b.Bucket.address = address) oram.stash with
    | Some b -> Bytes.copy b.Bucket.value
    | None   -> Bytes.make oram.block_size '\x00'
  in

  (* 4. Apply the operation — compute the new value. *)
  let new_data = match op with
    | `Read       -> current_data
    | `Write data -> data
  in

  (* 5. Replace the stash entry with the updated block at its new position. *)
  oram.stash <-
    Bucket.make_block ~address ~position:new_position ~value:new_data ~block_size:oram.block_size
    :: List.filter (fun b -> b.Bucket.address <> address) oram.stash;

  (* 6. Write the path back, evicting stash blocks leaf-to-root so blocks
        land as deep as possible, keeping the stash small. *)
  for l = height downto 0 do
    write_bucket oram (path_node ~height x l)
  done;

  current_data



let read oram address =
  access oram ~address:address ~op:`Read

let write oram address data =
  ignore(access oram ~address:address ~op:(`Write data))

let create ~capacity ~block_size ~z =
  assert (capacity >= 4 && capacity land (capacity - 1) = 0);
  assert (z >= 2);
  let height     = log2 capacity - 1 in
  let first_leaf = 1 lsl height in
  let num_leaves = 1 lsl height in
  let memory     = Array.init capacity (fun _ -> Bucket.make_bucket ~z ~block_size) in
  let position   = Array.init capacity (fun _ -> first_leaf + Random.int num_leaves) in
  let state = { height; block_size; z; memory; position; next_address = 0; stash = [] } in
  write state 0 (Bytes.make block_size '\x00');
  (* ignore (access x ~address:0 ~op:(`Write (Bytes.make block_size '\x00'))); *)
  { height; block_size; z; memory; position; next_address = 1; stash = [] }

let alloc oram value =
  let address = oram.next_address in
  let block_size = oram.block_size in
  let value_bytes = Bytes.length value in
  
  let base_block = Bytes.make block_size '\x00' in
  Bytes.blit value 0 base_block 0 value_bytes;

  write oram address base_block;
  oram.next_address <- address + 1;
  address
