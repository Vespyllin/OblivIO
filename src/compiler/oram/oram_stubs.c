#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <stdint.h>
#include <string.h>

/* Forward declarations matching Rust #[no_mangle] functions */
typedef struct OramWrapper OramWrapper;
OramWrapper* oram_create(uint64_t capacity, uint64_t block_size);
void         oram_read(OramWrapper* ptr, uint64_t addr, uint8_t* out);
void         oram_write(OramWrapper* ptr, uint64_t addr, const uint8_t* data, size_t len);
void         oram_free(OramWrapper* ptr);
uint8_t*     oram_to_bytes(OramWrapper* ptr, size_t* out_len);
OramWrapper* oram_from_bytes(const uint8_t* data, size_t len);
void         oram_free_bytes(uint8_t* ptr, size_t len);


/* GC finalizer — called when OCaml collects the value */
static void oram_finalize(value v) {
    OramWrapper* ptr = *((OramWrapper**)Data_custom_val(v));
    if (ptr) oram_free(ptr);
}

static struct custom_operations oram_ops = {
    "oram_wrapper",
    oram_finalize,
    custom_compare_default,
    custom_hash_default,
    custom_serialize_default,
    custom_deserialize_default,
    custom_compare_ext_default,
    custom_fixed_length_default
};

CAMLprim value caml_oram_create(value capacity, value block_size) {
    CAMLparam2(capacity, block_size);
    CAMLlocal1(result);
    OramWrapper* ptr = oram_create((uint64_t)Int_val(capacity), (uint64_t)Int_val(block_size));
    result = caml_alloc_custom(&oram_ops, sizeof(OramWrapper*), 0, 1);
    *((OramWrapper**)Data_custom_val(result)) = ptr;
    CAMLreturn(result);
}

CAMLprim value caml_oram_read(value state, value addr) {
    CAMLparam2(state, addr);
    CAMLlocal1(result);
    OramWrapper* ptr = *((OramWrapper**)Data_custom_val(state));
    result = caml_alloc_string(64);
    oram_read(ptr, (uint64_t)Int_val(addr), (uint8_t*)Bytes_val(result));
    CAMLreturn(result);
}

CAMLprim value caml_oram_write(value state, value addr, value data) {
    CAMLparam3(state, addr, data);
    OramWrapper* ptr = *((OramWrapper**)Data_custom_val(state));
    oram_write(ptr,
               (uint64_t)Int_val(addr),
               (const uint8_t*)Bytes_val(data),
               caml_string_length(data));
    CAMLreturn(Val_unit);
}

CAMLprim value caml_oram_to_bytes(value state) {
    CAMLparam1(state);
    CAMLlocal1(result);
    OramWrapper* ptr = *((OramWrapper**)Data_custom_val(state));
    size_t len = 0;
    uint8_t* bytes = oram_to_bytes(ptr, &len);
    result = caml_alloc_string(len);
    memcpy(Bytes_val(result), bytes, len);
    oram_free_bytes(bytes, len);
    CAMLreturn(result);
}

CAMLprim value caml_oram_from_bytes(value data) {
    CAMLparam1(data);
    CAMLlocal1(result);
    size_t len = caml_string_length(data);
    OramWrapper* ptr = oram_from_bytes((const uint8_t*)Bytes_val(data), len);
    result = caml_alloc_custom(&oram_ops, sizeof(OramWrapper*), 0, 1);
    *((OramWrapper**)Data_custom_val(result)) = ptr;
    CAMLreturn(result);
}