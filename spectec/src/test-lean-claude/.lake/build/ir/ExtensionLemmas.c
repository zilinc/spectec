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
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_ExtensionLemmas_0__fun__blocktype_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_ExtensionLemmas_0__fun__blocktype_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_ExtensionLemmas_0__fun__store_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_ExtensionLemmas_0__fun__store_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_ExtensionLemmas_0__fun__blocktype_match__1_splitter___redArg(lean_object* v_v__blocktype_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
_start:
{
if (lean_obj_tag(v_v__blocktype_1_) == 0)
{
lean_object* v_valtype__opt_5_; 
lean_dec(v_h__3_4_);
v_valtype__opt_5_ = lean_ctor_get(v_v__blocktype_1_, 0);
lean_inc(v_valtype__opt_5_);
lean_dec_ref_known(v_v__blocktype_1_, 1);
if (lean_obj_tag(v_valtype__opt_5_) == 0)
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_1(v_h__1_2_, v___x_6_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; lean_object* v___x_9_; 
lean_dec(v_h__1_2_);
v_val_8_ = lean_ctor_get(v_valtype__opt_5_, 0);
lean_inc(v_val_8_);
lean_dec_ref_known(v_valtype__opt_5_, 1);
v___x_9_ = lean_apply_1(v_h__2_3_, v_val_8_);
return v___x_9_;
}
}
else
{
lean_object* v_v__typeidx_10_; lean_object* v___x_11_; 
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v_v__typeidx_10_ = lean_ctor_get(v_v__blocktype_1_, 0);
lean_inc(v_v__typeidx_10_);
lean_dec_ref_known(v_v__blocktype_1_, 1);
v___x_11_ = lean_apply_1(v_h__3_4_, v_v__typeidx_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_ExtensionLemmas_0__fun__blocktype_match__1_splitter(lean_object* v_motive_12_, lean_object* v_v__blocktype_13_, lean_object* v_h__1_14_, lean_object* v_h__2_15_, lean_object* v_h__3_16_){
_start:
{
if (lean_obj_tag(v_v__blocktype_13_) == 0)
{
lean_object* v_valtype__opt_17_; 
lean_dec(v_h__3_16_);
v_valtype__opt_17_ = lean_ctor_get(v_v__blocktype_13_, 0);
lean_inc(v_valtype__opt_17_);
lean_dec_ref_known(v_v__blocktype_13_, 1);
if (lean_obj_tag(v_valtype__opt_17_) == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec(v_h__2_15_);
v___x_18_ = lean_box(0);
v___x_19_ = lean_apply_1(v_h__1_14_, v___x_18_);
return v___x_19_;
}
else
{
lean_object* v_val_20_; lean_object* v___x_21_; 
lean_dec(v_h__1_14_);
v_val_20_ = lean_ctor_get(v_valtype__opt_17_, 0);
lean_inc(v_val_20_);
lean_dec_ref_known(v_valtype__opt_17_, 1);
v___x_21_ = lean_apply_1(v_h__2_15_, v_val_20_);
return v___x_21_;
}
}
else
{
lean_object* v_v__typeidx_22_; lean_object* v___x_23_; 
lean_dec(v_h__2_15_);
lean_dec(v_h__1_14_);
v_v__typeidx_22_ = lean_ctor_get(v_v__blocktype_13_, 0);
lean_inc(v_v__typeidx_22_);
lean_dec_ref_known(v_v__blocktype_13_, 1);
v___x_23_ = lean_apply_1(v_h__3_16_, v_v__typeidx_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_ExtensionLemmas_0__fun__store_match__1_splitter___redArg(lean_object* v_v__state_24_, lean_object* v_h__1_25_){
_start:
{
lean_object* v_v__store_26_; lean_object* v_v__frame_27_; lean_object* v___x_28_; 
v_v__store_26_ = lean_ctor_get(v_v__state_24_, 0);
lean_inc_ref(v_v__store_26_);
v_v__frame_27_ = lean_ctor_get(v_v__state_24_, 1);
lean_inc_ref(v_v__frame_27_);
lean_dec_ref(v_v__state_24_);
v___x_28_ = lean_apply_2(v_h__1_25_, v_v__store_26_, v_v__frame_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_ExtensionLemmas_0__fun__store_match__1_splitter(lean_object* v_motive_29_, lean_object* v_v__state_30_, lean_object* v_h__1_31_){
_start:
{
lean_object* v_v__store_32_; lean_object* v_v__frame_33_; lean_object* v___x_34_; 
v_v__store_32_ = lean_ctor_get(v_v__state_30_, 0);
lean_inc_ref(v_v__store_32_);
v_v__frame_33_ = lean_ctor_get(v_v__state_30_, 1);
lean_inc_ref(v_v__frame_33_);
lean_dec_ref(v_v__state_30_);
v___x_34_ = lean_apply_2(v_h__1_31_, v_v__store_32_, v_v__frame_33_);
return v___x_34_;
}
}
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
