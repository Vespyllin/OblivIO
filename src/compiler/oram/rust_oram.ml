type oram_state

external create : int -> int -> oram_state               = "caml_oram_create"
external read       : oram_state -> int -> bytes         = "caml_oram_read"
external write      : oram_state -> int -> bytes -> unit = "caml_oram_write"
external to_bytes   : oram_state -> bytes                = "caml_oram_to_bytes"
external from_bytes : bytes -> oram_state                = "caml_oram_from_bytes"