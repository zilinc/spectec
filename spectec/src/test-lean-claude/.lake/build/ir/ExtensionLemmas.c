// Lean compiler output
// Module: ExtensionLemmas
// Imports: public import Init public meta import Init public import «wasm2.0» public import HelperLemmas public import Subtyping public import TypingLemmas public import TypePreservationPure
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_test_x2dlean_x2dclaude_wasm2_x2e0(uint8_t builtin);
lean_object* initialize_test_x2dlean_x2dclaude_HelperLemmas(uint8_t builtin);
lean_object* initialize_test_x2dlean_x2dclaude_Subtyping(uint8_t builtin);
lean_object* initialize_test_x2dlean_x2dclaude_TypingLemmas(uint8_t builtin);
lean_object* initialize_test_x2dlean_x2dclaude_TypePreservationPure(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_test_x2dlean_x2dclaude_ExtensionLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_test_x2dlean_x2dclaude_wasm2_x2e0(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_test_x2dlean_x2dclaude_HelperLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_test_x2dlean_x2dclaude_Subtyping(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_test_x2dlean_x2dclaude_TypingLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_test_x2dlean_x2dclaude_TypePreservationPure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
