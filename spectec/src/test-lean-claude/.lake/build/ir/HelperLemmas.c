// Lean compiler output
// Module: HelperLemmas
// Imports: public import Init public meta import Init public import «wasm2.0»
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
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_prepend__label(lean_object*, lean_object*);
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
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_45_ = ((lean_object*)(lp_test_x2dlean_x2dclaude_TLC_list__update___redArg___closed__0));
lean_inc(v_i_42_);
lean_inc(v_l_41_);
v___x_46_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_41_, v_l_41_, v_i_42_, v___x_45_);
v___x_47_ = l_List_appendTR___redArg(v___x_46_, v_update__l_44_);
v___x_48_ = lean_nat_add(v_i_42_, v_n_43_);
lean_dec(v_i_42_);
v___x_49_ = l_List_drop___redArg(v___x_48_, v_l_41_);
lean_dec(v_l_41_);
v___x_50_ = l_List_appendTR___redArg(v___x_47_, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__slice__update___redArg___boxed(lean_object* v_l_51_, lean_object* v_i_52_, lean_object* v_n_53_, lean_object* v_update__l_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_test_x2dlean_x2dclaude_TLC_list__slice__update___redArg(v_l_51_, v_i_52_, v_n_53_, v_update__l_54_);
lean_dec(v_n_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__slice__update(lean_object* v_00_u03b1_56_, lean_object* v_l_57_, lean_object* v_i_58_, lean_object* v_n_59_, lean_object* v_update__l_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lp_test_x2dlean_x2dclaude_TLC_list__slice__update___redArg(v_l_57_, v_i_58_, v_n_59_, v_update__l_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_list__slice__update___boxed(lean_object* v_00_u03b1_62_, lean_object* v_l_63_, lean_object* v_i_64_, lean_object* v_n_65_, lean_object* v_update__l_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_test_x2dlean_x2dclaude_TLC_list__slice__update(v_00_u03b1_62_, v_l_63_, v_i_64_, v_n_65_, v_update__l_66_);
lean_dec(v_n_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_x2dclaude_TLC_prepend__label(lean_object* v_C_68_, lean_object* v_t_69_){
_start:
{
lean_object* v_TYPES_70_; lean_object* v_FUNCS_71_; lean_object* v_GLOBALS_72_; lean_object* v_TABLES_73_; lean_object* v_MEMS_74_; lean_object* v_ELEMS_75_; lean_object* v_DATAS_76_; lean_object* v_LOCALS_77_; lean_object* v_LABELS_78_; lean_object* v_RETURN_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_87_; 
v_TYPES_70_ = lean_ctor_get(v_C_68_, 0);
v_FUNCS_71_ = lean_ctor_get(v_C_68_, 1);
v_GLOBALS_72_ = lean_ctor_get(v_C_68_, 2);
v_TABLES_73_ = lean_ctor_get(v_C_68_, 3);
v_MEMS_74_ = lean_ctor_get(v_C_68_, 4);
v_ELEMS_75_ = lean_ctor_get(v_C_68_, 5);
v_DATAS_76_ = lean_ctor_get(v_C_68_, 6);
v_LOCALS_77_ = lean_ctor_get(v_C_68_, 7);
v_LABELS_78_ = lean_ctor_get(v_C_68_, 8);
v_RETURN_79_ = lean_ctor_get(v_C_68_, 9);
v_isSharedCheck_87_ = !lean_is_exclusive(v_C_68_);
if (v_isSharedCheck_87_ == 0)
{
v___x_81_ = v_C_68_;
v_isShared_82_ = v_isSharedCheck_87_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_RETURN_79_);
lean_inc(v_LABELS_78_);
lean_inc(v_LOCALS_77_);
lean_inc(v_DATAS_76_);
lean_inc(v_ELEMS_75_);
lean_inc(v_MEMS_74_);
lean_inc(v_TABLES_73_);
lean_inc(v_GLOBALS_72_);
lean_inc(v_FUNCS_71_);
lean_inc(v_TYPES_70_);
lean_dec(v_C_68_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_87_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_83_, 0, v_t_69_);
lean_ctor_set(v___x_83_, 1, v_LABELS_78_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 8, v___x_83_);
v___x_85_ = v___x_81_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_TYPES_70_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_FUNCS_71_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v_GLOBALS_72_);
lean_ctor_set(v_reuseFailAlloc_86_, 3, v_TABLES_73_);
lean_ctor_set(v_reuseFailAlloc_86_, 4, v_MEMS_74_);
lean_ctor_set(v_reuseFailAlloc_86_, 5, v_ELEMS_75_);
lean_ctor_set(v_reuseFailAlloc_86_, 6, v_DATAS_76_);
lean_ctor_set(v_reuseFailAlloc_86_, 7, v_LOCALS_77_);
lean_ctor_set(v_reuseFailAlloc_86_, 8, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_86_, 9, v_RETURN_79_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
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
res = initialize_test_x2dlean_x2dclaude_wasm2_x2e0(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
