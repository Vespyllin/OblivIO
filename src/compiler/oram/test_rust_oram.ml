module RustOram = ORAM.Rust_oram

let () =
  Printf.printf "=== Rust ORAM FFI tests ===\n%!";

  let oram = RustOram.create 21 32 in
  Printf.printf "PASS: create\n%!";

  let data = Bytes.make 64 '\x00' in
  Bytes.set_int64_be data 0 (Int64.of_int 43);
  RustOram.write oram 0 data;
  Printf.printf "PASS: write\n%!";

  let result = RustOram.read oram 0 in
  let value = Int64.to_int (Bytes.get_int64_be result 0) in
  assert (value = 43);
  Printf.printf "PASS: read\n%!";

  for i = 0 to 9 do
    let b = Bytes.make 64 '\x00' in
    Bytes.set_int64_be b 0 (Int64.of_int (i * 10));
    RustOram.write oram i b
  done;
  for i = 0 to 9 do
    let r = RustOram.read oram i in
    let v = Int64.to_int (Bytes.get_int64_be r 0) in
    assert (v = i * 10)
  done;
  Printf.printf "PASS: multiple addresses\n%!";

  let b = Bytes.make 64 '\x00' in
  Bytes.set_int64_be b 0 (Int64.of_int 999);
  RustOram.write oram 5 b;
  let r = RustOram.read oram 5 in
  let v = Int64.to_int (Bytes.get_int64_be r 0) in
  assert (v = 999);
  Printf.printf "PASS: overwrite\n%!";

  for _ = 1 to 20 do
    let r = RustOram.read oram 3 in
    let v = Int64.to_int (Bytes.get_int64_be r 0) in
    assert (v = 30)
  done;
  Printf.printf "PASS: repeated reads stable\n%!";

  (* Test to_bytes / from_bytes *)
  let serialised = RustOram.to_bytes oram in
  Printf.printf "LEN %d\n%!" (Bytes.length serialised);
  let oram2 = RustOram.from_bytes serialised in
  let r = ORAM.Rust_oram.read oram2 5 in
  let v = Int64.to_int (Bytes.get_int64_be r 0) in
  assert (v = 999);
  Printf.printf "PASS: to_bytes/from_bytes\n%!";

  Printf.printf "All tests passed.\n%!"