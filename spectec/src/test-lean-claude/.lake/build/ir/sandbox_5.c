// Lean compiler output
// Module: sandbox_5
// Imports: public import Init public meta import Init public import ExtendedDeriveDecEq
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_ctorIdx___redArg(lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_node_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_test_x2dlean_List_beq___at___00instBEqTree_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_test_x2dlean_instBEqTree_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_instBEqTree_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_List_beq___at___00instBEqTree_beq_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_test_x2dlean_instBEqTree___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_test_x2dlean_instBEqTree_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_test_x2dlean_instBEqTree___closed__0 = (const lean_object*)&lp_test_x2dlean_instBEqTree___closed__0_value;
LEAN_EXPORT const lean_object* lp_test_x2dlean_instBEqTree = (const lean_object*)&lp_test_x2dlean_instBEqTree___closed__0_value;
LEAN_EXPORT uint8_t lp_test_x2dlean_Tree___auxDecEq_1_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_test_x2dlean_Tree_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree___auxDecEq_1____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_test_x2dlean_instDecidableEqTree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_instDecidableEqTree___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_test_x2dlean_Tree___auxDecEq_1____real(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree___auxDecEq_1____real___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_test_x2dlean_Tree_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
lean_object* v_a_8_; lean_object* v___x_9_; 
v_a_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_a_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_a_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_ctorElim(lean_object* v_motive__1_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_test_x2dlean_Tree_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_ctorElim___boxed(lean_object* v_motive__1_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_test_x2dlean_Tree_ctorElim(v_motive__1_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_leaf_elim___redArg(lean_object* v_t_22_, lean_object* v_leaf_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_test_x2dlean_Tree_ctorElim___redArg(v_t_22_, v_leaf_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_leaf_elim(lean_object* v_motive__1_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_leaf_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lp_test_x2dlean_Tree_ctorElim___redArg(v_t_26_, v_leaf_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_node_elim___redArg(lean_object* v_t_30_, lean_object* v_node_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_test_x2dlean_Tree_ctorElim___redArg(v_t_30_, v_node_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_node_elim(lean_object* v_motive__1_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_node_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_test_x2dlean_Tree_ctorElim___redArg(v_t_34_, v_node_36_);
return v___x_37_;
}
}
LEAN_EXPORT uint8_t lp_test_x2dlean_List_beq___at___00instBEqTree_beq_spec__0(lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
if (lean_obj_tag(v_x_39_) == 0)
{
uint8_t v___x_40_; 
v___x_40_ = 1;
return v___x_40_;
}
else
{
uint8_t v___x_41_; 
v___x_41_ = 0;
return v___x_41_;
}
}
else
{
if (lean_obj_tag(v_x_39_) == 0)
{
uint8_t v___x_42_; 
v___x_42_ = 0;
return v___x_42_;
}
else
{
lean_object* v_head_43_; lean_object* v_tail_44_; lean_object* v_head_45_; lean_object* v_tail_46_; uint8_t v___x_47_; 
v_head_43_ = lean_ctor_get(v_x_38_, 0);
v_tail_44_ = lean_ctor_get(v_x_38_, 1);
v_head_45_ = lean_ctor_get(v_x_39_, 0);
v_tail_46_ = lean_ctor_get(v_x_39_, 1);
v___x_47_ = lp_test_x2dlean_instBEqTree_beq(v_head_43_, v_head_45_);
if (v___x_47_ == 0)
{
return v___x_47_;
}
else
{
v_x_38_ = v_tail_44_;
v_x_39_ = v_tail_46_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t lp_test_x2dlean_instBEqTree_beq(lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v_a_51_; lean_object* v_a_52_; uint8_t v___x_53_; 
v_a_51_ = lean_ctor_get(v_x_49_, 0);
v_a_52_ = lean_ctor_get(v_x_50_, 0);
v___x_53_ = lean_nat_dec_eq(v_a_51_, v_a_52_);
return v___x_53_;
}
else
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
}
}
else
{
if (lean_obj_tag(v_x_50_) == 1)
{
lean_object* v_a_55_; lean_object* v_a_56_; uint8_t v___x_57_; 
v_a_55_ = lean_ctor_get(v_x_49_, 0);
v_a_56_ = lean_ctor_get(v_x_50_, 0);
v___x_57_ = lp_test_x2dlean_List_beq___at___00instBEqTree_beq_spec__0(v_a_55_, v_a_56_);
return v___x_57_;
}
else
{
uint8_t v___x_58_; 
v___x_58_ = 0;
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_instBEqTree_beq___boxed(lean_object* v_x_59_, lean_object* v_x_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = lp_test_x2dlean_instBEqTree_beq(v_x_59_, v_x_60_);
lean_dec_ref(v_x_60_);
lean_dec_ref(v_x_59_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_List_beq___at___00instBEqTree_beq_spec__0___boxed(lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = lp_test_x2dlean_List_beq___at___00instBEqTree_beq_spec__0(v_x_63_, v_x_64_);
lean_dec(v_x_64_);
lean_dec(v_x_63_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT uint8_t lp_test_x2dlean_Tree___auxDecEq_1_(lean_object* v_a_69_, lean_object* v_b_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_71_ = l_List_ctorIdx___redArg(v_a_69_);
v___x_72_ = l_List_ctorIdx___redArg(v_b_70_);
v___x_73_ = lean_nat_dec_eq(v___x_71_, v___x_72_);
lean_dec(v___x_72_);
lean_dec(v___x_71_);
if (v___x_73_ == 0)
{
return v___x_73_;
}
else
{
if (lean_obj_tag(v_a_69_) == 0)
{
return v___x_73_;
}
else
{
lean_object* v_head_74_; lean_object* v_tail_75_; lean_object* v_head_76_; lean_object* v_tail_77_; uint8_t v_inst_78_; 
v_head_74_ = lean_ctor_get(v_a_69_, 0);
v_tail_75_ = lean_ctor_get(v_a_69_, 1);
v_head_76_ = lean_ctor_get(v_b_70_, 0);
v_tail_77_ = lean_ctor_get(v_b_70_, 1);
v_inst_78_ = lp_test_x2dlean_Tree_decEq(v_head_74_, v_head_76_);
if (v_inst_78_ == 0)
{
return v_inst_78_;
}
else
{
v_a_69_ = v_tail_75_;
v_b_70_ = v_tail_77_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t lp_test_x2dlean_Tree_decEq(lean_object* v_a_80_, lean_object* v_b_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_82_ = lp_test_x2dlean_Tree_ctorIdx(v_a_80_);
v___x_83_ = lp_test_x2dlean_Tree_ctorIdx(v_b_81_);
v___x_84_ = lean_nat_dec_eq(v___x_82_, v___x_83_);
lean_dec(v___x_83_);
lean_dec(v___x_82_);
if (v___x_84_ == 0)
{
return v___x_84_;
}
else
{
if (lean_obj_tag(v_a_80_) == 0)
{
lean_object* v_a_85_; lean_object* v_a_86_; uint8_t v___x_87_; 
v_a_85_ = lean_ctor_get(v_a_80_, 0);
v_a_86_ = lean_ctor_get(v_b_81_, 0);
v___x_87_ = lean_nat_dec_eq(v_a_85_, v_a_86_);
return v___x_87_;
}
else
{
lean_object* v_a_88_; lean_object* v_a_89_; uint8_t v_inst_90_; 
v_a_88_ = lean_ctor_get(v_a_80_, 0);
v_a_89_ = lean_ctor_get(v_b_81_, 0);
v_inst_90_ = lp_test_x2dlean_Tree___auxDecEq_1_(v_a_88_, v_a_89_);
return v_inst_90_;
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree_decEq___boxed(lean_object* v_a_91_, lean_object* v_b_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = lp_test_x2dlean_Tree_decEq(v_a_91_, v_b_92_);
lean_dec_ref(v_b_92_);
lean_dec_ref(v_a_91_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree___auxDecEq_1____boxed(lean_object* v_a_95_, lean_object* v_b_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = lp_test_x2dlean_Tree___auxDecEq_1_(v_a_95_, v_b_96_);
lean_dec(v_b_96_);
lean_dec(v_a_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT uint8_t lp_test_x2dlean_instDecidableEqTree(lean_object* v_a_99_, lean_object* v_b_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lp_test_x2dlean_Tree_decEq(v_a_99_, v_b_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_instDecidableEqTree___boxed(lean_object* v_a_102_, lean_object* v_b_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = lp_test_x2dlean_instDecidableEqTree(v_a_102_, v_b_103_);
lean_dec_ref(v_b_103_);
lean_dec_ref(v_a_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint8_t lp_test_x2dlean_Tree___auxDecEq_1____real(lean_object* v_a_106_, lean_object* v_b_107_){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_alloc_closure((void*)(lp_test_x2dlean_instDecidableEqTree___boxed), 2, 0);
v___x_109_ = l_instDecidableEqList___redArg(v___x_108_, v_a_106_, v_b_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_Tree___auxDecEq_1____real___boxed(lean_object* v_a_110_, lean_object* v_b_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = lp_test_x2dlean_Tree___auxDecEq_1____real(v_a_110_, v_b_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_test_x2dlean_ExtendedDeriveDecEq(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_test_x2dlean_sandbox__5(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_test_x2dlean_ExtendedDeriveDecEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
