// Lean compiler output
// Module: TypePreservation
// Imports: public import Init public meta import Init public import «wasm2.0» public import HelperLemmas public import Subtyping public import TypingLemmas public import TypePreservationPure public import ExtensionLemmas
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
lean_object* lp_test_x2dlean_x2dclaude_fzero(lean_object*);
static const lean_ctor_object lp_test_x2dlean_x2dclaude_TLC_num__default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_test_x2dlean_x2dclaude_TLC_num__default___closed__0 = (const lean_object*)&lp_test_x2dlean_x2dclaude_TLC_num__default___closed__0_value;
static const lean_ctor_object lp_test_x2dlean_x2dclaude_TLC_num__default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_test_x2dlean_x2dclaude_TLC_num__default___closed__1 = (const lean_object*)&lp_test_x2dlean_x2dclaude_TLC_num__default___closed__1_value;
static lean_once_cell_t lp_test_x2dlean_x2dclaude_TLC_num__default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_test_x2dlean_x2dclaude_TLC_num__default___closed__2;
static lean_once_cell_t lp_test_x2dlean_x2dclaude_TLC_num__default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_test_x2dlean_x2dclaude_TLC_num__default___closed__3;
static lean_once_cell_t lp_test_x2dlean_x2dclaude_TLC_num__default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_test_x2dlean_x2dclaude_TLC_num__default___closed__4;
static lean_once_cell_t lp_test_x2dlean_x2dclaude_TLC_num__default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_test_x2dlean_x2dclaude_TLC_num__default___closed__5;
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_num__default(uint8_t);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_num__default___boxed(lean_object*);
static lean_object* _init_lp_test_x2dlean_x2dclaude_TLC_num__default___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_unsigned_to_nat(32u);
v___x_8_ = lp_test_x2dlean_x2dclaude_fzero(v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_lp_test_x2dlean_x2dclaude_TLC_num__default___closed__3(void){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_obj_once(&lp_test_x2dlean_x2dclaude_TLC_num__default___closed__2, &lp_test_x2dlean_x2dclaude_TLC_num__default___closed__2_once, _init_lp_test_x2dlean_x2dclaude_TLC_num__default___closed__2);
v___x_10_ = 0;
v___x_11_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_11_, 0, v___x_9_);
lean_ctor_set_uint8(v___x_11_, sizeof(void*)*1, v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_lp_test_x2dlean_x2dclaude_TLC_num__default___closed__4(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(64u);
v___x_13_ = lp_test_x2dlean_x2dclaude_fzero(v___x_12_);
return v___x_13_;
}
}
static lean_object* _init_lp_test_x2dlean_x2dclaude_TLC_num__default___closed__5(void){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&lp_test_x2dlean_x2dclaude_TLC_num__default___closed__4, &lp_test_x2dlean_x2dclaude_TLC_num__default___closed__4_once, _init_lp_test_x2dlean_x2dclaude_TLC_num__default___closed__4);
v___x_15_ = 1;
v___x_16_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_16_, 0, v___x_14_);
lean_ctor_set_uint8(v___x_16_, sizeof(void*)*1, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_num__default(uint8_t v_nt_17_){
_start:
{
switch(v_nt_17_)
{
case 0:
{
lean_object* v___x_18_; 
v___x_18_ = ((lean_object*)(lp_test_x2dlean_x2dclaude_TLC_num__default___closed__0));
return v___x_18_;
}
case 1:
{
lean_object* v___x_19_; 
v___x_19_ = ((lean_object*)(lp_test_x2dlean_x2dclaude_TLC_num__default___closed__1));
return v___x_19_;
}
case 2:
{
lean_object* v___x_20_; 
v___x_20_ = lean_obj_once(&lp_test_x2dlean_x2dclaude_TLC_num__default___closed__3, &lp_test_x2dlean_x2dclaude_TLC_num__default___closed__3_once, _init_lp_test_x2dlean_x2dclaude_TLC_num__default___closed__3);
return v___x_20_;
}
default: 
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&lp_test_x2dlean_x2dclaude_TLC_num__default___closed__5, &lp_test_x2dlean_x2dclaude_TLC_num__default___closed__5_once, _init_lp_test_x2dlean_x2dclaude_TLC_num__default___closed__5);
return v___x_21_;
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_num__default___boxed(lean_object* v_nt_22_){
_start:
{
uint8_t v_nt_boxed_23_; lean_object* v_res_24_; 
v_nt_boxed_23_ = lean_unbox(v_nt_22_);
v_res_24_ = lp_test_x2dlean_x2dclaude_TLC_num__default(v_nt_boxed_23_);
return v_res_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_test_x2dlean_x2dclaude_wasm2_x2e0(uint8_t builtin);
lean_object* initialize_test_x2dlean_x2dclaude_HelperLemmas(uint8_t builtin);
lean_object* initialize_test_x2dlean_x2dclaude_Subtyping(uint8_t builtin);
lean_object* initialize_test_x2dlean_x2dclaude_TypingLemmas(uint8_t builtin);
lean_object* initialize_test_x2dlean_x2dclaude_TypePreservationPure(uint8_t builtin);
lean_object* initialize_test_x2dlean_x2dclaude_ExtensionLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_test_x2dlean_x2dclaude_TypePreservation(uint8_t builtin) {
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
res = initialize_test_x2dlean_x2dclaude_ExtensionLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
