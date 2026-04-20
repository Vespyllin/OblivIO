(* Bucket — OCaml implementation
   Based on: Meta's bucket.rs implementation *)

(* ------------------------------------------------------------------ *)
(* Constants                                                            *)
(* ------------------------------------------------------------------ *)

let dummy_address  = Int.max_int
let dummy_position = 0

(* ------------------------------------------------------------------ *)
(* Block                                                                *)
(* ------------------------------------------------------------------ *)

(** A Path ORAM block. Dumminess is encoded by sentinel values rather
    than a separate constructor, matching the Rust implementation. *)
type block = {
  value    : bytes;
  address  : int;
  (** The leaf index this block is currently assigned to. *)
  position : int;
}

(** Create a dummy block of [block_size] bytes. *)
let dummy_block block_size = {
  value    = Bytes.make block_size '\x00';
  address  = dummy_address;
  position = dummy_position;
}

let is_dummy b = b.position = dummy_position

let make_block ~address ~position ~value ~block_size =
  let data = Bytes.make block_size '\x00' in
  let len  = min (Bytes.length value) block_size in
  Bytes.blit value 0 data 0 len;
  { address; position; value = data }

(* ------------------------------------------------------------------ *)
(* Bucket                                                               *)
(* ------------------------------------------------------------------ *)

(** A Path ORAM bucket holds exactly Z blocks, each either real or dummy.
    Always fully populated — dummies fill unused slots. *)
type bucket = {
  mutable blocks : block array;
}

(** Create an empty bucket of [z] dummy blocks. *)
let make_bucket ~z ~block_size =
  { blocks = Array.make z (dummy_block block_size) }

(** Read all real blocks out of a bucket, replacing them with dummies.
    Returns the list of real blocks found. *)
let drain_bucket bucket block_size =
  let real_blocks = ref [] in
  for i = 0 to Array.length bucket.blocks - 1 do
    let b = bucket.blocks.(i) in
    if not (is_dummy b) then
      real_blocks := b :: !real_blocks;
    bucket.blocks.(i) <- dummy_block block_size
  done;
  !real_blocks

(** Write a list of blocks into a bucket, filling remaining slots with dummies.
    Raises if more blocks than slots are provided. *)
let fill_bucket bucket blocks block_size =
  let z = Array.length bucket.blocks in
  assert (List.length blocks <= z);
  (* Reset to all dummies first. *)
  Array.fill bucket.blocks 0 z (dummy_block block_size);
  List.iteri (fun i b -> bucket.blocks.(i) <- b) blocks