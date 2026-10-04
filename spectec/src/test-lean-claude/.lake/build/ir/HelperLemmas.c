// Lean compiler output
// Module: HelperLemmas
// Imports: public import Init public meta import Init public import Mathlib.Tactic public import «wasm2.0»
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
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_test_x2dlean_x2dclaude_append__context(lean_object*, lean_object*);
lean_object* l_List_modifyTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_lookup__total___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_lookup__total___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_lookup__total(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_lookup__total___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object lp_test_x2dlean_x2dclaude_TLC_list__update___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_test_x2dlean_x2dclaude_TLC_list__update___redArg___closed__0 = (const lean_object*)&lp_test_x2dlean_x2dclaude_TLC_list__update___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__update___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__update(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__update__func___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__update__func(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__slice__update___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__slice__update___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__slice__update(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__slice__update___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_In2_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_In2_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_list__slice__update_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_list__slice__update_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_list__slice__update_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_list__slice__update_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_list__slice__update_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_list__slice__update_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_prepend__label(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_prepend__local(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_prepend__return(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_append__local(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_append__label(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_append__return(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_lookup__total___redArg(lean_object* v_inst_1_, lean_object* v_l_2_, lean_object* v_n_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_List_get_x21Internal___redArg(v_inst_1_, v_l_2_, v_n_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_lookup__total___redArg___boxed(lean_object* v_inst_5_, lean_object* v_l_6_, lean_object* v_n_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_test_x2dlean_x2dclaude_TLC_lookup__total___redArg(v_inst_5_, v_l_6_, v_n_7_);
lean_dec(v_l_6_);
lean_dec(v_inst_5_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_lookup__total(lean_object* v_00_u03b1_9_, lean_object* v_inst_10_, lean_object* v_l_11_, lean_object* v_n_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_List_get_x21Internal___redArg(v_inst_10_, v_l_11_, v_n_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_lookup__total___boxed(lean_object* v_00_u03b1_14_, lean_object* v_inst_15_, lean_object* v_l_16_, lean_object* v_n_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_test_x2dlean_x2dclaude_TLC_lookup__total(v_00_u03b1_14_, v_inst_15_, v_l_16_, v_n_17_);
lean_dec(v_l_16_);
lean_dec(v_inst_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__update___redArg(lean_object* v_l_21_, lean_object* v_n_22_, lean_object* v_y_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = ((lean_object*)(lp_test_x2dlean_x2dclaude_TLC_list__update___redArg___closed__0));
lean_inc(v_l_21_);
v___x_25_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(v_l_21_, v_y_23_, v_l_21_, v_n_22_, v___x_24_);
lean_dec(v_l_21_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__update(lean_object* v_00_u03b1_26_, lean_object* v_l_27_, lean_object* v_n_28_, lean_object* v_y_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = ((lean_object*)(lp_test_x2dlean_x2dclaude_TLC_list__update___redArg___closed__0));
lean_inc(v_l_27_);
v___x_31_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(v_l_27_, v_y_29_, v_l_27_, v_n_28_, v___x_30_);
lean_dec(v_l_27_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__update__func___redArg(lean_object* v_l_32_, lean_object* v_n_33_, lean_object* v_f_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_List_modifyTR___redArg(v_l_32_, v_n_33_, v_f_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__update__func(lean_object* v_00_u03b1_36_, lean_object* v_l_37_, lean_object* v_n_38_, lean_object* v_f_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_List_modifyTR___redArg(v_l_37_, v_n_38_, v_f_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__slice__update___redArg(lean_object* v_l_41_, lean_object* v_i_42_, lean_object* v_n_43_, lean_object* v_update__l_44_){
_start:
{
if (lean_obj_tag(v_l_41_) == 0)
{
lean_dec(v_update__l_44_);
return v_l_41_;
}
else
{
if (lean_obj_tag(v_update__l_44_) == 0)
{
return v_l_41_;
}
else
{
lean_object* v_head_45_; lean_object* v_tail_46_; lean_object* v_head_47_; lean_object* v_tail_48_; lean_object* v_zero_49_; uint8_t v_isZero_50_; 
v_head_45_ = lean_ctor_get(v_l_41_, 0);
v_tail_46_ = lean_ctor_get(v_l_41_, 1);
v_head_47_ = lean_ctor_get(v_update__l_44_, 0);
v_tail_48_ = lean_ctor_get(v_update__l_44_, 1);
v_zero_49_ = lean_unsigned_to_nat(0u);
v_isZero_50_ = lean_nat_dec_eq(v_i_42_, v_zero_49_);
if (v_isZero_50_ == 1)
{
lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_61_; 
lean_inc(v_tail_48_);
lean_inc(v_head_47_);
v_isSharedCheck_61_ = !lean_is_exclusive(v_update__l_44_);
if (v_isSharedCheck_61_ == 0)
{
lean_object* v_unused_62_; lean_object* v_unused_63_; 
v_unused_62_ = lean_ctor_get(v_update__l_44_, 1);
lean_dec(v_unused_62_);
v_unused_63_ = lean_ctor_get(v_update__l_44_, 0);
lean_dec(v_unused_63_);
v___x_52_ = v_update__l_44_;
v_isShared_53_ = v_isSharedCheck_61_;
goto v_resetjp_51_;
}
else
{
lean_dec(v_update__l_44_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_61_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
uint8_t v_isZero_54_; 
v_isZero_54_ = lean_nat_dec_eq(v_n_43_, v_zero_49_);
if (v_isZero_54_ == 1)
{
lean_del_object(v___x_52_);
lean_dec(v_tail_48_);
lean_dec(v_head_47_);
return v_l_41_;
}
else
{
lean_object* v_one_55_; lean_object* v_n_56_; lean_object* v___x_57_; lean_object* v___x_59_; 
lean_inc(v_tail_46_);
lean_dec_ref_known(v_l_41_, 2);
v_one_55_ = lean_unsigned_to_nat(1u);
v_n_56_ = lean_nat_sub(v_n_43_, v_one_55_);
v___x_57_ = lp_test_x2dlean_x2dclaude_TLC_list__slice__update___redArg(v_tail_46_, v_zero_49_, v_n_56_, v_tail_48_);
lean_dec(v_n_56_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 1, v___x_57_);
v___x_59_ = v___x_52_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_head_47_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v___x_57_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
else
{
uint8_t v___x_64_; 
v___x_64_ = lean_nat_dec_eq(v_n_43_, v_zero_49_);
if (v___x_64_ == 0)
{
lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_74_; 
lean_inc(v_tail_46_);
lean_inc(v_head_45_);
v_isSharedCheck_74_ = !lean_is_exclusive(v_l_41_);
if (v_isSharedCheck_74_ == 0)
{
lean_object* v_unused_75_; lean_object* v_unused_76_; 
v_unused_75_ = lean_ctor_get(v_l_41_, 1);
lean_dec(v_unused_75_);
v_unused_76_ = lean_ctor_get(v_l_41_, 0);
lean_dec(v_unused_76_);
v___x_66_ = v_l_41_;
v_isShared_67_ = v_isSharedCheck_74_;
goto v_resetjp_65_;
}
else
{
lean_dec(v_l_41_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_74_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v_one_68_; lean_object* v_n_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v_one_68_ = lean_unsigned_to_nat(1u);
v_n_69_ = lean_nat_sub(v_i_42_, v_one_68_);
v___x_70_ = lp_test_x2dlean_x2dclaude_TLC_list__slice__update___redArg(v_tail_46_, v_n_69_, v_n_43_, v_update__l_44_);
lean_dec(v_n_69_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_70_);
v___x_72_ = v___x_66_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_head_45_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
else
{
lean_dec_ref_known(v_update__l_44_, 2);
return v_l_41_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__slice__update___redArg___boxed(lean_object* v_l_77_, lean_object* v_i_78_, lean_object* v_n_79_, lean_object* v_update__l_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_test_x2dlean_x2dclaude_TLC_list__slice__update___redArg(v_l_77_, v_i_78_, v_n_79_, v_update__l_80_);
lean_dec(v_n_79_);
lean_dec(v_i_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__slice__update(lean_object* v_00_u03b1_82_, lean_object* v_l_83_, lean_object* v_i_84_, lean_object* v_n_85_, lean_object* v_update__l_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lp_test_x2dlean_x2dclaude_TLC_list__slice__update___redArg(v_l_83_, v_i_84_, v_n_85_, v_update__l_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__slice__update___boxed(lean_object* v_00_u03b1_88_, lean_object* v_l_89_, lean_object* v_i_90_, lean_object* v_n_91_, lean_object* v_update__l_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lp_test_x2dlean_x2dclaude_TLC_list__slice__update(v_00_u03b1_88_, v_l_89_, v_i_90_, v_n_91_, v_update__l_92_);
lean_dec(v_n_91_);
lean_dec(v_i_90_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_In2_match__1_splitter___redArg(lean_object* v_l_94_, lean_object* v_l_x27_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_, lean_object* v_h__3_98_, lean_object* v_h__4_99_){
_start:
{
if (lean_obj_tag(v_l_94_) == 0)
{
lean_dec(v_h__4_99_);
lean_dec(v_h__3_98_);
if (lean_obj_tag(v_l_x27_95_) == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_h__2_97_);
v___x_100_ = lean_box(0);
v___x_101_ = lean_apply_1(v_h__1_96_, v___x_100_);
return v___x_101_;
}
else
{
lean_object* v_head_102_; lean_object* v_tail_103_; lean_object* v___x_104_; 
lean_dec(v_h__1_96_);
v_head_102_ = lean_ctor_get(v_l_x27_95_, 0);
lean_inc(v_head_102_);
v_tail_103_ = lean_ctor_get(v_l_x27_95_, 1);
lean_inc(v_tail_103_);
lean_dec_ref_known(v_l_x27_95_, 2);
v___x_104_ = lean_apply_2(v_h__2_97_, v_head_102_, v_tail_103_);
return v___x_104_;
}
}
else
{
lean_dec(v_h__2_97_);
lean_dec(v_h__1_96_);
if (lean_obj_tag(v_l_x27_95_) == 0)
{
lean_object* v_head_105_; lean_object* v_tail_106_; lean_object* v___x_107_; 
lean_dec(v_h__4_99_);
v_head_105_ = lean_ctor_get(v_l_94_, 0);
lean_inc(v_head_105_);
v_tail_106_ = lean_ctor_get(v_l_94_, 1);
lean_inc(v_tail_106_);
lean_dec_ref_known(v_l_94_, 2);
v___x_107_ = lean_apply_2(v_h__3_98_, v_head_105_, v_tail_106_);
return v___x_107_;
}
else
{
lean_object* v_head_108_; lean_object* v_tail_109_; lean_object* v_head_110_; lean_object* v_tail_111_; lean_object* v___x_112_; 
lean_dec(v_h__3_98_);
v_head_108_ = lean_ctor_get(v_l_94_, 0);
lean_inc(v_head_108_);
v_tail_109_ = lean_ctor_get(v_l_94_, 1);
lean_inc(v_tail_109_);
lean_dec_ref_known(v_l_94_, 2);
v_head_110_ = lean_ctor_get(v_l_x27_95_, 0);
lean_inc(v_head_110_);
v_tail_111_ = lean_ctor_get(v_l_x27_95_, 1);
lean_inc(v_tail_111_);
lean_dec_ref_known(v_l_x27_95_, 2);
v___x_112_ = lean_apply_4(v_h__4_99_, v_head_108_, v_tail_109_, v_head_110_, v_tail_111_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_In2_match__1_splitter(lean_object* v_00_u03b1_113_, lean_object* v_00_u03b2_114_, lean_object* v_motive_115_, lean_object* v_l_116_, lean_object* v_l_x27_117_, lean_object* v_h__1_118_, lean_object* v_h__2_119_, lean_object* v_h__3_120_, lean_object* v_h__4_121_){
_start:
{
if (lean_obj_tag(v_l_116_) == 0)
{
lean_dec(v_h__4_121_);
lean_dec(v_h__3_120_);
if (lean_obj_tag(v_l_x27_117_) == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_h__2_119_);
v___x_122_ = lean_box(0);
v___x_123_ = lean_apply_1(v_h__1_118_, v___x_122_);
return v___x_123_;
}
else
{
lean_object* v_head_124_; lean_object* v_tail_125_; lean_object* v___x_126_; 
lean_dec(v_h__1_118_);
v_head_124_ = lean_ctor_get(v_l_x27_117_, 0);
lean_inc(v_head_124_);
v_tail_125_ = lean_ctor_get(v_l_x27_117_, 1);
lean_inc(v_tail_125_);
lean_dec_ref_known(v_l_x27_117_, 2);
v___x_126_ = lean_apply_2(v_h__2_119_, v_head_124_, v_tail_125_);
return v___x_126_;
}
}
else
{
lean_dec(v_h__2_119_);
lean_dec(v_h__1_118_);
if (lean_obj_tag(v_l_x27_117_) == 0)
{
lean_object* v_head_127_; lean_object* v_tail_128_; lean_object* v___x_129_; 
lean_dec(v_h__4_121_);
v_head_127_ = lean_ctor_get(v_l_116_, 0);
lean_inc(v_head_127_);
v_tail_128_ = lean_ctor_get(v_l_116_, 1);
lean_inc(v_tail_128_);
lean_dec_ref_known(v_l_116_, 2);
v___x_129_ = lean_apply_2(v_h__3_120_, v_head_127_, v_tail_128_);
return v___x_129_;
}
else
{
lean_object* v_head_130_; lean_object* v_tail_131_; lean_object* v_head_132_; lean_object* v_tail_133_; lean_object* v___x_134_; 
lean_dec(v_h__3_120_);
v_head_130_ = lean_ctor_get(v_l_116_, 0);
lean_inc(v_head_130_);
v_tail_131_ = lean_ctor_get(v_l_116_, 1);
lean_inc(v_tail_131_);
lean_dec_ref_known(v_l_116_, 2);
v_head_132_ = lean_ctor_get(v_l_x27_117_, 0);
lean_inc(v_head_132_);
v_tail_133_ = lean_ctor_get(v_l_x27_117_, 1);
lean_inc(v_tail_133_);
lean_dec_ref_known(v_l_x27_117_, 2);
v___x_134_ = lean_apply_4(v_h__4_121_, v_head_130_, v_tail_131_, v_head_132_, v_tail_133_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_list__slice__update_match__3_splitter___redArg(lean_object* v_l_135_, lean_object* v_update__l_136_, lean_object* v_h__1_137_, lean_object* v_h__2_138_, lean_object* v_h__3_139_){
_start:
{
if (lean_obj_tag(v_l_135_) == 0)
{
lean_object* v___x_140_; 
lean_dec(v_h__3_139_);
lean_dec(v_h__2_138_);
v___x_140_ = lean_apply_1(v_h__1_137_, v_update__l_136_);
return v___x_140_;
}
else
{
lean_dec(v_h__1_137_);
if (lean_obj_tag(v_update__l_136_) == 0)
{
lean_object* v___x_141_; 
lean_dec(v_h__3_139_);
v___x_141_ = lean_apply_2(v_h__2_138_, v_l_135_, lean_box(0));
return v___x_141_;
}
else
{
lean_object* v_head_142_; lean_object* v_tail_143_; lean_object* v_head_144_; lean_object* v_tail_145_; lean_object* v___x_146_; 
lean_dec(v_h__2_138_);
v_head_142_ = lean_ctor_get(v_l_135_, 0);
lean_inc(v_head_142_);
v_tail_143_ = lean_ctor_get(v_l_135_, 1);
lean_inc(v_tail_143_);
lean_dec_ref_known(v_l_135_, 2);
v_head_144_ = lean_ctor_get(v_update__l_136_, 0);
lean_inc(v_head_144_);
v_tail_145_ = lean_ctor_get(v_update__l_136_, 1);
lean_inc(v_tail_145_);
lean_dec_ref_known(v_update__l_136_, 2);
v___x_146_ = lean_apply_4(v_h__3_139_, v_head_142_, v_tail_143_, v_head_144_, v_tail_145_);
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_list__slice__update_match__3_splitter(lean_object* v_00_u03b1_147_, lean_object* v_motive_148_, lean_object* v_l_149_, lean_object* v_update__l_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_, lean_object* v_h__3_153_){
_start:
{
if (lean_obj_tag(v_l_149_) == 0)
{
lean_object* v___x_154_; 
lean_dec(v_h__3_153_);
lean_dec(v_h__2_152_);
v___x_154_ = lean_apply_1(v_h__1_151_, v_update__l_150_);
return v___x_154_;
}
else
{
lean_dec(v_h__1_151_);
if (lean_obj_tag(v_update__l_150_) == 0)
{
lean_object* v___x_155_; 
lean_dec(v_h__3_153_);
v___x_155_ = lean_apply_2(v_h__2_152_, v_l_149_, lean_box(0));
return v___x_155_;
}
else
{
lean_object* v_head_156_; lean_object* v_tail_157_; lean_object* v_head_158_; lean_object* v_tail_159_; lean_object* v___x_160_; 
lean_dec(v_h__2_152_);
v_head_156_ = lean_ctor_get(v_l_149_, 0);
lean_inc(v_head_156_);
v_tail_157_ = lean_ctor_get(v_l_149_, 1);
lean_inc(v_tail_157_);
lean_dec_ref_known(v_l_149_, 2);
v_head_158_ = lean_ctor_get(v_update__l_150_, 0);
lean_inc(v_head_158_);
v_tail_159_ = lean_ctor_get(v_update__l_150_, 1);
lean_inc(v_tail_159_);
lean_dec_ref_known(v_update__l_150_, 2);
v___x_160_ = lean_apply_4(v_h__3_153_, v_head_156_, v_tail_157_, v_head_158_, v_tail_159_);
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_list__slice__update_match__1_splitter___redArg(lean_object* v_i_161_, lean_object* v_n_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_, lean_object* v_h__3_165_, lean_object* v_h__4_166_){
_start:
{
lean_object* v_zero_167_; uint8_t v_isZero_168_; 
v_zero_167_ = lean_unsigned_to_nat(0u);
v_isZero_168_ = lean_nat_dec_eq(v_i_161_, v_zero_167_);
if (v_isZero_168_ == 1)
{
uint8_t v_isZero_169_; 
lean_dec(v_h__4_166_);
lean_dec(v_h__2_164_);
v_isZero_169_ = lean_nat_dec_eq(v_n_162_, v_zero_167_);
if (v_isZero_169_ == 1)
{
lean_object* v___x_170_; lean_object* v___x_171_; 
lean_dec(v_h__3_165_);
lean_dec(v_n_162_);
v___x_170_ = lean_box(0);
v___x_171_ = lean_apply_1(v_h__1_163_, v___x_170_);
return v___x_171_;
}
else
{
lean_object* v_one_172_; lean_object* v_n_173_; lean_object* v___x_174_; 
lean_dec(v_h__1_163_);
v_one_172_ = lean_unsigned_to_nat(1u);
v_n_173_ = lean_nat_sub(v_n_162_, v_one_172_);
lean_dec(v_n_162_);
v___x_174_ = lean_apply_1(v_h__3_165_, v_n_173_);
return v___x_174_;
}
}
else
{
lean_object* v_one_175_; lean_object* v_n_176_; uint8_t v___x_177_; 
lean_dec(v_h__3_165_);
lean_dec(v_h__1_163_);
v_one_175_ = lean_unsigned_to_nat(1u);
v_n_176_ = lean_nat_sub(v_i_161_, v_one_175_);
v___x_177_ = lean_nat_dec_eq(v_n_162_, v_zero_167_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
lean_dec(v_h__2_164_);
v___x_178_ = lean_apply_3(v_h__4_166_, v_n_176_, v_n_162_, lean_box(0));
return v___x_178_;
}
else
{
lean_object* v___x_179_; 
lean_dec(v_h__4_166_);
lean_dec(v_n_162_);
v___x_179_ = lean_apply_1(v_h__2_164_, v_n_176_);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_list__slice__update_match__1_splitter___redArg___boxed(lean_object* v_i_180_, lean_object* v_n_181_, lean_object* v_h__1_182_, lean_object* v_h__2_183_, lean_object* v_h__3_184_, lean_object* v_h__4_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_list__slice__update_match__1_splitter___redArg(v_i_180_, v_n_181_, v_h__1_182_, v_h__2_183_, v_h__3_184_, v_h__4_185_);
lean_dec(v_i_180_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_list__slice__update_match__1_splitter(lean_object* v_motive_187_, lean_object* v_i_188_, lean_object* v_n_189_, lean_object* v_h__1_190_, lean_object* v_h__2_191_, lean_object* v_h__3_192_, lean_object* v_h__4_193_){
_start:
{
lean_object* v_zero_194_; uint8_t v_isZero_195_; 
v_zero_194_ = lean_unsigned_to_nat(0u);
v_isZero_195_ = lean_nat_dec_eq(v_i_188_, v_zero_194_);
if (v_isZero_195_ == 1)
{
uint8_t v_isZero_196_; 
lean_dec(v_h__4_193_);
lean_dec(v_h__2_191_);
v_isZero_196_ = lean_nat_dec_eq(v_n_189_, v_zero_194_);
if (v_isZero_196_ == 1)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_h__3_192_);
lean_dec(v_n_189_);
v___x_197_ = lean_box(0);
v___x_198_ = lean_apply_1(v_h__1_190_, v___x_197_);
return v___x_198_;
}
else
{
lean_object* v_one_199_; lean_object* v_n_200_; lean_object* v___x_201_; 
lean_dec(v_h__1_190_);
v_one_199_ = lean_unsigned_to_nat(1u);
v_n_200_ = lean_nat_sub(v_n_189_, v_one_199_);
lean_dec(v_n_189_);
v___x_201_ = lean_apply_1(v_h__3_192_, v_n_200_);
return v___x_201_;
}
}
else
{
lean_object* v_one_202_; lean_object* v_n_203_; uint8_t v___x_204_; 
lean_dec(v_h__3_192_);
lean_dec(v_h__1_190_);
v_one_202_ = lean_unsigned_to_nat(1u);
v_n_203_ = lean_nat_sub(v_i_188_, v_one_202_);
v___x_204_ = lean_nat_dec_eq(v_n_189_, v_zero_194_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_dec(v_h__2_191_);
v___x_205_ = lean_apply_3(v_h__4_193_, v_n_203_, v_n_189_, lean_box(0));
return v___x_205_;
}
else
{
lean_object* v___x_206_; 
lean_dec(v_h__4_193_);
lean_dec(v_n_189_);
v___x_206_ = lean_apply_1(v_h__2_191_, v_n_203_);
return v___x_206_;
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_list__slice__update_match__1_splitter___boxed(lean_object* v_motive_207_, lean_object* v_i_208_, lean_object* v_n_209_, lean_object* v_h__1_210_, lean_object* v_h__2_211_, lean_object* v_h__3_212_, lean_object* v_h__4_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = lp_test_x2dlean_x2dclaude___private_HelperLemmas_0__TLC_list__slice__update_match__1_splitter(v_motive_207_, v_i_208_, v_n_209_, v_h__1_210_, v_h__2_211_, v_h__3_212_, v_h__4_213_);
lean_dec(v_i_208_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_prepend__label(lean_object* v_C_215_, lean_object* v_t_216_){
_start:
{
lean_object* v_TYPES_217_; lean_object* v_FUNCS_218_; lean_object* v_GLOBALS_219_; lean_object* v_TABLES_220_; lean_object* v_MEMS_221_; lean_object* v_ELEMS_222_; lean_object* v_DATAS_223_; lean_object* v_LOCALS_224_; lean_object* v_LABELS_225_; lean_object* v_RETURN_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_234_; 
v_TYPES_217_ = lean_ctor_get(v_C_215_, 0);
v_FUNCS_218_ = lean_ctor_get(v_C_215_, 1);
v_GLOBALS_219_ = lean_ctor_get(v_C_215_, 2);
v_TABLES_220_ = lean_ctor_get(v_C_215_, 3);
v_MEMS_221_ = lean_ctor_get(v_C_215_, 4);
v_ELEMS_222_ = lean_ctor_get(v_C_215_, 5);
v_DATAS_223_ = lean_ctor_get(v_C_215_, 6);
v_LOCALS_224_ = lean_ctor_get(v_C_215_, 7);
v_LABELS_225_ = lean_ctor_get(v_C_215_, 8);
v_RETURN_226_ = lean_ctor_get(v_C_215_, 9);
v_isSharedCheck_234_ = !lean_is_exclusive(v_C_215_);
if (v_isSharedCheck_234_ == 0)
{
v___x_228_ = v_C_215_;
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_RETURN_226_);
lean_inc(v_LABELS_225_);
lean_inc(v_LOCALS_224_);
lean_inc(v_DATAS_223_);
lean_inc(v_ELEMS_222_);
lean_inc(v_MEMS_221_);
lean_inc(v_TABLES_220_);
lean_inc(v_GLOBALS_219_);
lean_inc(v_FUNCS_218_);
lean_inc(v_TYPES_217_);
lean_dec(v_C_215_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_230_, 0, v_t_216_);
lean_ctor_set(v___x_230_, 1, v_LABELS_225_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 8, v___x_230_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_TYPES_217_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_FUNCS_218_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_GLOBALS_219_);
lean_ctor_set(v_reuseFailAlloc_233_, 3, v_TABLES_220_);
lean_ctor_set(v_reuseFailAlloc_233_, 4, v_MEMS_221_);
lean_ctor_set(v_reuseFailAlloc_233_, 5, v_ELEMS_222_);
lean_ctor_set(v_reuseFailAlloc_233_, 6, v_DATAS_223_);
lean_ctor_set(v_reuseFailAlloc_233_, 7, v_LOCALS_224_);
lean_ctor_set(v_reuseFailAlloc_233_, 8, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_233_, 9, v_RETURN_226_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_prepend__local(lean_object* v_C_235_, lean_object* v_t__lst_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_237_ = lean_box(0);
v___x_238_ = lean_box(0);
v___x_239_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
lean_ctor_set(v___x_239_, 2, v___x_237_);
lean_ctor_set(v___x_239_, 3, v___x_237_);
lean_ctor_set(v___x_239_, 4, v___x_237_);
lean_ctor_set(v___x_239_, 5, v___x_237_);
lean_ctor_set(v___x_239_, 6, v___x_237_);
lean_ctor_set(v___x_239_, 7, v_t__lst_236_);
lean_ctor_set(v___x_239_, 8, v___x_237_);
lean_ctor_set(v___x_239_, 9, v___x_238_);
v___x_240_ = lp_test_x2dlean_x2dclaude_append__context(v___x_239_, v_C_235_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_prepend__return(lean_object* v_C_241_, lean_object* v_t_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_243_ = lean_box(0);
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v_t_242_);
v___x_245_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
lean_ctor_set(v___x_245_, 2, v___x_243_);
lean_ctor_set(v___x_245_, 3, v___x_243_);
lean_ctor_set(v___x_245_, 4, v___x_243_);
lean_ctor_set(v___x_245_, 5, v___x_243_);
lean_ctor_set(v___x_245_, 6, v___x_243_);
lean_ctor_set(v___x_245_, 7, v___x_243_);
lean_ctor_set(v___x_245_, 8, v___x_243_);
lean_ctor_set(v___x_245_, 9, v___x_244_);
v___x_246_ = lp_test_x2dlean_x2dclaude_append__context(v___x_245_, v_C_241_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_append__local(lean_object* v_C_247_, lean_object* v_t__lst_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_249_ = lean_box(0);
v___x_250_ = lean_box(0);
v___x_251_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_249_);
lean_ctor_set(v___x_251_, 2, v___x_249_);
lean_ctor_set(v___x_251_, 3, v___x_249_);
lean_ctor_set(v___x_251_, 4, v___x_249_);
lean_ctor_set(v___x_251_, 5, v___x_249_);
lean_ctor_set(v___x_251_, 6, v___x_249_);
lean_ctor_set(v___x_251_, 7, v_t__lst_248_);
lean_ctor_set(v___x_251_, 8, v___x_249_);
lean_ctor_set(v___x_251_, 9, v___x_250_);
v___x_252_ = lp_test_x2dlean_x2dclaude_append__context(v_C_247_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_append__label(lean_object* v_C_253_, lean_object* v_t_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v_t_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_box(0);
v___x_258_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_258_, 0, v___x_255_);
lean_ctor_set(v___x_258_, 1, v___x_255_);
lean_ctor_set(v___x_258_, 2, v___x_255_);
lean_ctor_set(v___x_258_, 3, v___x_255_);
lean_ctor_set(v___x_258_, 4, v___x_255_);
lean_ctor_set(v___x_258_, 5, v___x_255_);
lean_ctor_set(v___x_258_, 6, v___x_255_);
lean_ctor_set(v___x_258_, 7, v___x_255_);
lean_ctor_set(v___x_258_, 8, v___x_256_);
lean_ctor_set(v___x_258_, 9, v___x_257_);
v___x_259_ = lp_test_x2dlean_x2dclaude_append__context(v_C_253_, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_append__return(lean_object* v_C_260_, lean_object* v_t_261_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_262_ = lean_box(0);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v_t_261_);
v___x_264_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
lean_ctor_set(v___x_264_, 2, v___x_262_);
lean_ctor_set(v___x_264_, 3, v___x_262_);
lean_ctor_set(v___x_264_, 4, v___x_262_);
lean_ctor_set(v___x_264_, 5, v___x_262_);
lean_ctor_set(v___x_264_, 6, v___x_262_);
lean_ctor_set(v___x_264_, 7, v___x_262_);
lean_ctor_set(v___x_264_, 8, v___x_262_);
lean_ctor_set(v___x_264_, 9, v___x_263_);
v___x_265_ = lp_test_x2dlean_x2dclaude_append__context(v_C_260_, v___x_264_);
return v___x_265_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
lean_object* initialize_test_x2dlean_x2dclaude_wasm2_x2e0(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_test_x2dlean_x2dclaude_HelperLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_test_x2dlean_x2dclaude_wasm2_x2e0(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
