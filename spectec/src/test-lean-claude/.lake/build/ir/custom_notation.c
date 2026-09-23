// Lean compiler output
// Module: custom_notation
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_mkFunctype(lean_object*, lean_object*);
static const lean_string_object lp_test_x2dlean_term__F_x2d_x3e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_F->_"};
static const lean_object* lp_test_x2dlean_term__F_x2d_x3e___00__closed__0 = (const lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__0_value;
static const lean_ctor_object lp_test_x2dlean_term__F_x2d_x3e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 95, 63, 253, 122, 79, 242, 53)}};
static const lean_object* lp_test_x2dlean_term__F_x2d_x3e___00__closed__1 = (const lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__1_value;
static const lean_string_object lp_test_x2dlean_term__F_x2d_x3e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* lp_test_x2dlean_term__F_x2d_x3e___00__closed__2 = (const lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__2_value;
static const lean_ctor_object lp_test_x2dlean_term__F_x2d_x3e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* lp_test_x2dlean_term__F_x2d_x3e___00__closed__3 = (const lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__3_value;
static const lean_string_object lp_test_x2dlean_term__F_x2d_x3e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "f->"};
static const lean_object* lp_test_x2dlean_term__F_x2d_x3e___00__closed__4 = (const lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__4_value;
static const lean_ctor_object lp_test_x2dlean_term__F_x2d_x3e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__4_value)}};
static const lean_object* lp_test_x2dlean_term__F_x2d_x3e___00__closed__5 = (const lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__5_value;
static const lean_string_object lp_test_x2dlean_term__F_x2d_x3e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* lp_test_x2dlean_term__F_x2d_x3e___00__closed__6 = (const lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__6_value;
static const lean_ctor_object lp_test_x2dlean_term__F_x2d_x3e___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* lp_test_x2dlean_term__F_x2d_x3e___00__closed__7 = (const lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__7_value;
static const lean_ctor_object lp_test_x2dlean_term__F_x2d_x3e___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__7_value),((lean_object*)(((size_t)(68) << 1) | 1))}};
static const lean_object* lp_test_x2dlean_term__F_x2d_x3e___00__closed__8 = (const lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__8_value;
static const lean_ctor_object lp_test_x2dlean_term__F_x2d_x3e___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__3_value),((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__5_value),((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__8_value)}};
static const lean_object* lp_test_x2dlean_term__F_x2d_x3e___00__closed__9 = (const lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__9_value;
static const lean_ctor_object lp_test_x2dlean_term__F_x2d_x3e___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__1_value),((lean_object*)(((size_t)(67) << 1) | 1)),((lean_object*)(((size_t)(68) << 1) | 1)),((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__9_value)}};
static const lean_object* lp_test_x2dlean_term__F_x2d_x3e___00__closed__10 = (const lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__10_value;
LEAN_EXPORT const lean_object* lp_test_x2dlean_term__F_x2d_x3e__ = (const lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__10_value;
static const lean_string_object lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__0 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__0_value;
static const lean_string_object lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__1 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__1_value;
static const lean_string_object lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__2 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__2_value;
static const lean_string_object lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__3 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__3_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4_value_aux_0),((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4_value_aux_1),((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4_value_aux_2),((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4_value;
static const lean_string_object lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mkFunctype"};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__5 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__5_value;
static lean_once_cell_t lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__6;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(121, 126, 131, 184, 183, 185, 128, 193)}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__7 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__7_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__8 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__8_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__9 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__9_value;
static const lean_string_object lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__10 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__10_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__11 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__11_value;
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1___closed__0 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1___closed__0_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1___closed__1 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1___closed__1_value;
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_test_x2dlean_term__Sub_x3c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term_Sub<_"};
static const lean_object* lp_test_x2dlean_term__Sub_x3c___00__closed__0 = (const lean_object*)&lp_test_x2dlean_term__Sub_x3c___00__closed__0_value;
static const lean_ctor_object lp_test_x2dlean_term__Sub_x3c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_test_x2dlean_term__Sub_x3c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 29, 81, 28, 70, 52, 239, 117)}};
static const lean_object* lp_test_x2dlean_term__Sub_x3c___00__closed__1 = (const lean_object*)&lp_test_x2dlean_term__Sub_x3c___00__closed__1_value;
static const lean_string_object lp_test_x2dlean_term__Sub_x3c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "sub<"};
static const lean_object* lp_test_x2dlean_term__Sub_x3c___00__closed__2 = (const lean_object*)&lp_test_x2dlean_term__Sub_x3c___00__closed__2_value;
static const lean_ctor_object lp_test_x2dlean_term__Sub_x3c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__Sub_x3c___00__closed__2_value)}};
static const lean_object* lp_test_x2dlean_term__Sub_x3c___00__closed__3 = (const lean_object*)&lp_test_x2dlean_term__Sub_x3c___00__closed__3_value;
static const lean_ctor_object lp_test_x2dlean_term__Sub_x3c___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__7_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* lp_test_x2dlean_term__Sub_x3c___00__closed__4 = (const lean_object*)&lp_test_x2dlean_term__Sub_x3c___00__closed__4_value;
static const lean_ctor_object lp_test_x2dlean_term__Sub_x3c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__3_value),((lean_object*)&lp_test_x2dlean_term__Sub_x3c___00__closed__3_value),((lean_object*)&lp_test_x2dlean_term__Sub_x3c___00__closed__4_value)}};
static const lean_object* lp_test_x2dlean_term__Sub_x3c___00__closed__5 = (const lean_object*)&lp_test_x2dlean_term__Sub_x3c___00__closed__5_value;
static const lean_ctor_object lp_test_x2dlean_term__Sub_x3c___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__Sub_x3c___00__closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&lp_test_x2dlean_term__Sub_x3c___00__closed__5_value)}};
static const lean_object* lp_test_x2dlean_term__Sub_x3c___00__closed__6 = (const lean_object*)&lp_test_x2dlean_term__Sub_x3c___00__closed__6_value;
LEAN_EXPORT const lean_object* lp_test_x2dlean_term__Sub_x3c__ = (const lean_object*)&lp_test_x2dlean_term__Sub_x3c___00__closed__6_value;
static const lean_string_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Valtype_sub"};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__0 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__0_value;
static lean_once_cell_t lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__1;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 169, 62, 194, 47, 67, 198, 77)}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__2 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__2_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__3 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__3_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__2_value)}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__4 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__4_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__5 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__5_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__3_value),((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__5_value)}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__6 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__6_value;
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__Valtype__sub__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__Valtype__sub__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_test_x2dlean_term__Subs_x3c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term_Subs<_"};
static const lean_object* lp_test_x2dlean_term__Subs_x3c___00__closed__0 = (const lean_object*)&lp_test_x2dlean_term__Subs_x3c___00__closed__0_value;
static const lean_ctor_object lp_test_x2dlean_term__Subs_x3c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_test_x2dlean_term__Subs_x3c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 213, 136, 16, 17, 10, 17, 71)}};
static const lean_object* lp_test_x2dlean_term__Subs_x3c___00__closed__1 = (const lean_object*)&lp_test_x2dlean_term__Subs_x3c___00__closed__1_value;
static const lean_string_object lp_test_x2dlean_term__Subs_x3c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subs<"};
static const lean_object* lp_test_x2dlean_term__Subs_x3c___00__closed__2 = (const lean_object*)&lp_test_x2dlean_term__Subs_x3c___00__closed__2_value;
static const lean_ctor_object lp_test_x2dlean_term__Subs_x3c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__Subs_x3c___00__closed__2_value)}};
static const lean_object* lp_test_x2dlean_term__Subs_x3c___00__closed__3 = (const lean_object*)&lp_test_x2dlean_term__Subs_x3c___00__closed__3_value;
static const lean_ctor_object lp_test_x2dlean_term__Subs_x3c___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__7_value),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* lp_test_x2dlean_term__Subs_x3c___00__closed__4 = (const lean_object*)&lp_test_x2dlean_term__Subs_x3c___00__closed__4_value;
static const lean_ctor_object lp_test_x2dlean_term__Subs_x3c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__3_value),((lean_object*)&lp_test_x2dlean_term__Subs_x3c___00__closed__3_value),((lean_object*)&lp_test_x2dlean_term__Subs_x3c___00__closed__4_value)}};
static const lean_object* lp_test_x2dlean_term__Subs_x3c___00__closed__5 = (const lean_object*)&lp_test_x2dlean_term__Subs_x3c___00__closed__5_value;
static const lean_ctor_object lp_test_x2dlean_term__Subs_x3c___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__Subs_x3c___00__closed__1_value),((lean_object*)(((size_t)(40) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)&lp_test_x2dlean_term__Subs_x3c___00__closed__5_value)}};
static const lean_object* lp_test_x2dlean_term__Subs_x3c___00__closed__6 = (const lean_object*)&lp_test_x2dlean_term__Subs_x3c___00__closed__6_value;
LEAN_EXPORT const lean_object* lp_test_x2dlean_term__Subs_x3c__ = (const lean_object*)&lp_test_x2dlean_term__Subs_x3c___00__closed__6_value;
static const lean_string_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "resulttypeSub"};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__0 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__0_value;
static lean_once_cell_t lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__1;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 240, 165, 158, 161, 36, 65, 115)}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__2 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__2_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__3 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__3_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__4 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__4_value;
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__resulttypeSub__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__resulttypeSub__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_test_x2dlean_term__Ftsub_x3c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "term_Ftsub<_"};
static const lean_object* lp_test_x2dlean_term__Ftsub_x3c___00__closed__0 = (const lean_object*)&lp_test_x2dlean_term__Ftsub_x3c___00__closed__0_value;
static const lean_ctor_object lp_test_x2dlean_term__Ftsub_x3c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_test_x2dlean_term__Ftsub_x3c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 36, 50, 116, 53, 44, 57, 142)}};
static const lean_object* lp_test_x2dlean_term__Ftsub_x3c___00__closed__1 = (const lean_object*)&lp_test_x2dlean_term__Ftsub_x3c___00__closed__1_value;
static const lean_string_object lp_test_x2dlean_term__Ftsub_x3c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ftsub<"};
static const lean_object* lp_test_x2dlean_term__Ftsub_x3c___00__closed__2 = (const lean_object*)&lp_test_x2dlean_term__Ftsub_x3c___00__closed__2_value;
static const lean_ctor_object lp_test_x2dlean_term__Ftsub_x3c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__Ftsub_x3c___00__closed__2_value)}};
static const lean_object* lp_test_x2dlean_term__Ftsub_x3c___00__closed__3 = (const lean_object*)&lp_test_x2dlean_term__Ftsub_x3c___00__closed__3_value;
static const lean_ctor_object lp_test_x2dlean_term__Ftsub_x3c___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__7_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* lp_test_x2dlean_term__Ftsub_x3c___00__closed__4 = (const lean_object*)&lp_test_x2dlean_term__Ftsub_x3c___00__closed__4_value;
static const lean_ctor_object lp_test_x2dlean_term__Ftsub_x3c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__F_x2d_x3e___00__closed__3_value),((lean_object*)&lp_test_x2dlean_term__Ftsub_x3c___00__closed__3_value),((lean_object*)&lp_test_x2dlean_term__Ftsub_x3c___00__closed__4_value)}};
static const lean_object* lp_test_x2dlean_term__Ftsub_x3c___00__closed__5 = (const lean_object*)&lp_test_x2dlean_term__Ftsub_x3c___00__closed__5_value;
static const lean_ctor_object lp_test_x2dlean_term__Ftsub_x3c___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&lp_test_x2dlean_term__Ftsub_x3c___00__closed__1_value),((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&lp_test_x2dlean_term__Ftsub_x3c___00__closed__5_value)}};
static const lean_object* lp_test_x2dlean_term__Ftsub_x3c___00__closed__6 = (const lean_object*)&lp_test_x2dlean_term__Ftsub_x3c___00__closed__6_value;
LEAN_EXPORT const lean_object* lp_test_x2dlean_term__Ftsub_x3c__ = (const lean_object*)&lp_test_x2dlean_term__Ftsub_x3c___00__closed__6_value;
static const lean_string_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Functype_sub"};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__0 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__0_value;
static lean_once_cell_t lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__1;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 131, 143, 48, 170, 236, 247, 119)}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__2 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__2_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__3 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__3_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__2_value)}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__4 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__4_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__5 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__5_value;
static const lean_ctor_object lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__3_value),((lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__5_value)}};
static const lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__6 = (const lean_object*)&lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__6_value;
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__Functype__sub__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__Functype__sub__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_prepend__label(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_test_x2dlean_mkFunctype(lean_object* v_tf1_1_, lean_object* v_tf2_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_tf1_1_);
lean_ctor_set(v___x_3_, 1, v_tf2_2_);
return v___x_3_;
}
}
static lean_object* _init_lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__6(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__5));
v___x_40_ = l_String_toRawSubstring_x27(v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1(lean_object* v_x_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = ((lean_object*)(lp_test_x2dlean_term__F_x2d_x3e___00__closed__1));
lean_inc(v_x_52_);
v___x_56_ = l_Lean_Syntax_isOfKind(v_x_52_, v___x_55_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_x_52_);
v___x_57_ = lean_box(1);
v___x_58_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v_a_54_);
return v___x_58_;
}
else
{
lean_object* v_quotContext_59_; lean_object* v_currMacroScope_60_; lean_object* v_ref_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_quotContext_59_ = lean_ctor_get(v_a_53_, 1);
v_currMacroScope_60_ = lean_ctor_get(v_a_53_, 2);
v_ref_61_ = lean_ctor_get(v_a_53_, 5);
v___x_62_ = lean_unsigned_to_nat(0u);
v___x_63_ = l_Lean_Syntax_getArg(v_x_52_, v___x_62_);
v___x_64_ = lean_unsigned_to_nat(2u);
v___x_65_ = l_Lean_Syntax_getArg(v_x_52_, v___x_64_);
lean_dec(v_x_52_);
v___x_66_ = 0;
v___x_67_ = l_Lean_SourceInfo_fromRef(v_ref_61_, v___x_66_);
v___x_68_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4));
v___x_69_ = lean_obj_once(&lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__6, &lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__6_once, _init_lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__6);
v___x_70_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__7));
lean_inc(v_currMacroScope_60_);
lean_inc(v_quotContext_59_);
v___x_71_ = l_Lean_addMacroScope(v_quotContext_59_, v___x_70_, v_currMacroScope_60_);
v___x_72_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__9));
lean_inc_n(v___x_67_, 2);
v___x_73_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_73_, 0, v___x_67_);
lean_ctor_set(v___x_73_, 1, v___x_69_);
lean_ctor_set(v___x_73_, 2, v___x_71_);
lean_ctor_set(v___x_73_, 3, v___x_72_);
v___x_74_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__11));
v___x_75_ = l_Lean_Syntax_node2(v___x_67_, v___x_74_, v___x_63_, v___x_65_);
v___x_76_ = l_Lean_Syntax_node2(v___x_67_, v___x_68_, v___x_73_, v___x_75_);
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v_a_54_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___boxed(lean_object* v_x_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1(v_x_78_, v_a_79_, v_a_80_);
lean_dec_ref(v_a_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1(lean_object* v_x_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4));
lean_inc(v_x_85_);
v___x_89_ = l_Lean_Syntax_isOfKind(v_x_85_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec(v_x_85_);
v___x_90_ = lean_box(0);
v___x_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v_a_87_);
return v___x_91_;
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = l_Lean_Syntax_getArg(v_x_85_, v___x_92_);
v___x_94_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1___closed__1));
lean_inc(v___x_93_);
v___x_95_ = l_Lean_Syntax_isOfKind(v___x_93_, v___x_94_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v___x_93_);
lean_dec(v_x_85_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_a_87_);
return v___x_97_;
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_98_ = lean_unsigned_to_nat(1u);
v___x_99_ = l_Lean_Syntax_getArg(v_x_85_, v___x_98_);
lean_dec(v_x_85_);
v___x_100_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_99_);
v___x_101_ = l_Lean_Syntax_matchesNull(v___x_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec(v___x_99_);
lean_dec(v___x_93_);
v___x_102_ = lean_box(0);
v___x_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v_a_87_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_ref_106_; uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_104_ = l_Lean_Syntax_getArg(v___x_99_, v___x_92_);
v___x_105_ = l_Lean_Syntax_getArg(v___x_99_, v___x_98_);
lean_dec(v___x_99_);
v_ref_106_ = l_Lean_replaceRef(v___x_93_, v_a_86_);
lean_dec(v___x_93_);
v___x_107_ = 0;
v___x_108_ = l_Lean_SourceInfo_fromRef(v_ref_106_, v___x_107_);
lean_dec(v_ref_106_);
v___x_109_ = ((lean_object*)(lp_test_x2dlean_term__F_x2d_x3e___00__closed__1));
v___x_110_ = ((lean_object*)(lp_test_x2dlean_term__F_x2d_x3e___00__closed__4));
lean_inc(v___x_108_);
v___x_111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_108_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = l_Lean_Syntax_node3(v___x_108_, v___x_109_, v___x_104_, v___x_111_, v___x_105_);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v_a_87_);
return v___x_113_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1___boxed(lean_object* v_x_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1(v_x_114_, v_a_115_, v_a_116_);
lean_dec(v_a_115_);
return v_res_117_;
}
}
static lean_object* _init_lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__0));
v___x_139_ = l_String_toRawSubstring_x27(v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1(lean_object* v_x_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = ((lean_object*)(lp_test_x2dlean_term__Sub_x3c___00__closed__1));
lean_inc(v_x_153_);
v___x_157_ = l_Lean_Syntax_isOfKind(v_x_153_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec(v_x_153_);
v___x_158_ = lean_box(1);
v___x_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v_a_155_);
return v___x_159_;
}
else
{
lean_object* v_quotContext_160_; lean_object* v_currMacroScope_161_; lean_object* v_ref_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_quotContext_160_ = lean_ctor_get(v_a_154_, 1);
v_currMacroScope_161_ = lean_ctor_get(v_a_154_, 2);
v_ref_162_ = lean_ctor_get(v_a_154_, 5);
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = l_Lean_Syntax_getArg(v_x_153_, v___x_163_);
v___x_165_ = lean_unsigned_to_nat(2u);
v___x_166_ = l_Lean_Syntax_getArg(v_x_153_, v___x_165_);
lean_dec(v_x_153_);
v___x_167_ = 0;
v___x_168_ = l_Lean_SourceInfo_fromRef(v_ref_162_, v___x_167_);
v___x_169_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4));
v___x_170_ = lean_obj_once(&lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__1, &lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__1_once, _init_lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__1);
v___x_171_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__2));
lean_inc(v_currMacroScope_161_);
lean_inc(v_quotContext_160_);
v___x_172_ = l_Lean_addMacroScope(v_quotContext_160_, v___x_171_, v_currMacroScope_161_);
v___x_173_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___closed__6));
lean_inc_n(v___x_168_, 2);
v___x_174_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_174_, 0, v___x_168_);
lean_ctor_set(v___x_174_, 1, v___x_170_);
lean_ctor_set(v___x_174_, 2, v___x_172_);
lean_ctor_set(v___x_174_, 3, v___x_173_);
v___x_175_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__11));
v___x_176_ = l_Lean_Syntax_node2(v___x_168_, v___x_175_, v___x_164_, v___x_166_);
v___x_177_ = l_Lean_Syntax_node2(v___x_168_, v___x_169_, v___x_174_, v___x_176_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v_a_155_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1___boxed(lean_object* v_x_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = lp_test_x2dlean___aux__custom__notation______macroRules__term__Sub_x3c____1(v_x_179_, v_a_180_, v_a_181_);
lean_dec_ref(v_a_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__Valtype__sub__1(lean_object* v_x_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4));
lean_inc(v_x_183_);
v___x_187_ = l_Lean_Syntax_isOfKind(v_x_183_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v_x_183_);
v___x_188_ = lean_box(0);
v___x_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_a_185_);
return v___x_189_;
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = l_Lean_Syntax_getArg(v_x_183_, v___x_190_);
v___x_192_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1___closed__1));
lean_inc(v___x_191_);
v___x_193_ = l_Lean_Syntax_isOfKind(v___x_191_, v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v___x_191_);
lean_dec(v_x_183_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_a_185_);
return v___x_195_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = l_Lean_Syntax_getArg(v_x_183_, v___x_196_);
lean_dec(v_x_183_);
v___x_198_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_197_);
v___x_199_ = l_Lean_Syntax_matchesNull(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v___x_197_);
lean_dec(v___x_191_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v_a_185_);
return v___x_201_;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v_ref_204_; uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_202_ = l_Lean_Syntax_getArg(v___x_197_, v___x_190_);
v___x_203_ = l_Lean_Syntax_getArg(v___x_197_, v___x_196_);
lean_dec(v___x_197_);
v_ref_204_ = l_Lean_replaceRef(v___x_191_, v_a_184_);
lean_dec(v___x_191_);
v___x_205_ = 0;
v___x_206_ = l_Lean_SourceInfo_fromRef(v_ref_204_, v___x_205_);
lean_dec(v_ref_204_);
v___x_207_ = ((lean_object*)(lp_test_x2dlean_term__Sub_x3c___00__closed__1));
v___x_208_ = ((lean_object*)(lp_test_x2dlean_term__Sub_x3c___00__closed__2));
lean_inc(v___x_206_);
v___x_209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_206_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = l_Lean_Syntax_node3(v___x_206_, v___x_207_, v___x_202_, v___x_209_, v___x_203_);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v_a_185_);
return v___x_211_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__Valtype__sub__1___boxed(lean_object* v_x_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = lp_test_x2dlean___aux__custom__notation______unexpand__Valtype__sub__1(v_x_212_, v_a_213_, v_a_214_);
lean_dec(v_a_213_);
return v_res_215_;
}
}
static lean_object* _init_lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__0));
v___x_237_ = l_String_toRawSubstring_x27(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1(lean_object* v_x_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = ((lean_object*)(lp_test_x2dlean_term__Subs_x3c___00__closed__1));
lean_inc(v_x_246_);
v___x_250_ = l_Lean_Syntax_isOfKind(v_x_246_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v_x_246_);
v___x_251_ = lean_box(1);
v___x_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v_a_248_);
return v___x_252_;
}
else
{
lean_object* v_quotContext_253_; lean_object* v_currMacroScope_254_; lean_object* v_ref_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_quotContext_253_ = lean_ctor_get(v_a_247_, 1);
v_currMacroScope_254_ = lean_ctor_get(v_a_247_, 2);
v_ref_255_ = lean_ctor_get(v_a_247_, 5);
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = l_Lean_Syntax_getArg(v_x_246_, v___x_256_);
v___x_258_ = lean_unsigned_to_nat(2u);
v___x_259_ = l_Lean_Syntax_getArg(v_x_246_, v___x_258_);
lean_dec(v_x_246_);
v___x_260_ = 0;
v___x_261_ = l_Lean_SourceInfo_fromRef(v_ref_255_, v___x_260_);
v___x_262_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4));
v___x_263_ = lean_obj_once(&lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__1, &lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__1_once, _init_lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__1);
v___x_264_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__2));
lean_inc(v_currMacroScope_254_);
lean_inc(v_quotContext_253_);
v___x_265_ = l_Lean_addMacroScope(v_quotContext_253_, v___x_264_, v_currMacroScope_254_);
v___x_266_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___closed__4));
lean_inc_n(v___x_261_, 2);
v___x_267_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_267_, 0, v___x_261_);
lean_ctor_set(v___x_267_, 1, v___x_263_);
lean_ctor_set(v___x_267_, 2, v___x_265_);
lean_ctor_set(v___x_267_, 3, v___x_266_);
v___x_268_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__11));
v___x_269_ = l_Lean_Syntax_node2(v___x_261_, v___x_268_, v___x_257_, v___x_259_);
v___x_270_ = l_Lean_Syntax_node2(v___x_261_, v___x_262_, v___x_267_, v___x_269_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v_a_248_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1___boxed(lean_object* v_x_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = lp_test_x2dlean___aux__custom__notation______macroRules__term__Subs_x3c____1(v_x_272_, v_a_273_, v_a_274_);
lean_dec_ref(v_a_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__resulttypeSub__1(lean_object* v_x_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4));
lean_inc(v_x_276_);
v___x_280_ = l_Lean_Syntax_isOfKind(v_x_276_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec(v_x_276_);
v___x_281_ = lean_box(0);
v___x_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v_a_278_);
return v___x_282_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = l_Lean_Syntax_getArg(v_x_276_, v___x_283_);
v___x_285_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1___closed__1));
lean_inc(v___x_284_);
v___x_286_ = l_Lean_Syntax_isOfKind(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v___x_284_);
lean_dec(v_x_276_);
v___x_287_ = lean_box(0);
v___x_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v_a_278_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = l_Lean_Syntax_getArg(v_x_276_, v___x_289_);
lean_dec(v_x_276_);
v___x_291_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_290_);
v___x_292_ = l_Lean_Syntax_matchesNull(v___x_290_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec(v___x_290_);
lean_dec(v___x_284_);
v___x_293_ = lean_box(0);
v___x_294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v_a_278_);
return v___x_294_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v_ref_297_; uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_295_ = l_Lean_Syntax_getArg(v___x_290_, v___x_283_);
v___x_296_ = l_Lean_Syntax_getArg(v___x_290_, v___x_289_);
lean_dec(v___x_290_);
v_ref_297_ = l_Lean_replaceRef(v___x_284_, v_a_277_);
lean_dec(v___x_284_);
v___x_298_ = 0;
v___x_299_ = l_Lean_SourceInfo_fromRef(v_ref_297_, v___x_298_);
lean_dec(v_ref_297_);
v___x_300_ = ((lean_object*)(lp_test_x2dlean_term__Subs_x3c___00__closed__1));
v___x_301_ = ((lean_object*)(lp_test_x2dlean_term__Subs_x3c___00__closed__2));
lean_inc(v___x_299_);
v___x_302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_299_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = l_Lean_Syntax_node3(v___x_299_, v___x_300_, v___x_295_, v___x_302_, v___x_296_);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v_a_278_);
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__resulttypeSub__1___boxed(lean_object* v_x_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = lp_test_x2dlean___aux__custom__notation______unexpand__resulttypeSub__1(v_x_305_, v_a_306_, v_a_307_);
lean_dec(v_a_306_);
return v_res_308_;
}
}
static lean_object* _init_lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__0));
v___x_330_ = l_String_toRawSubstring_x27(v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1(lean_object* v_x_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = ((lean_object*)(lp_test_x2dlean_term__Ftsub_x3c___00__closed__1));
lean_inc(v_x_344_);
v___x_348_ = l_Lean_Syntax_isOfKind(v_x_344_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec(v_x_344_);
v___x_349_ = lean_box(1);
v___x_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v_a_346_);
return v___x_350_;
}
else
{
lean_object* v_quotContext_351_; lean_object* v_currMacroScope_352_; lean_object* v_ref_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_quotContext_351_ = lean_ctor_get(v_a_345_, 1);
v_currMacroScope_352_ = lean_ctor_get(v_a_345_, 2);
v_ref_353_ = lean_ctor_get(v_a_345_, 5);
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = l_Lean_Syntax_getArg(v_x_344_, v___x_354_);
v___x_356_ = lean_unsigned_to_nat(2u);
v___x_357_ = l_Lean_Syntax_getArg(v_x_344_, v___x_356_);
lean_dec(v_x_344_);
v___x_358_ = 0;
v___x_359_ = l_Lean_SourceInfo_fromRef(v_ref_353_, v___x_358_);
v___x_360_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4));
v___x_361_ = lean_obj_once(&lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__1, &lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__1_once, _init_lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__1);
v___x_362_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__2));
lean_inc(v_currMacroScope_352_);
lean_inc(v_quotContext_351_);
v___x_363_ = l_Lean_addMacroScope(v_quotContext_351_, v___x_362_, v_currMacroScope_352_);
v___x_364_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___closed__6));
lean_inc_n(v___x_359_, 2);
v___x_365_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_365_, 0, v___x_359_);
lean_ctor_set(v___x_365_, 1, v___x_361_);
lean_ctor_set(v___x_365_, 2, v___x_363_);
lean_ctor_set(v___x_365_, 3, v___x_364_);
v___x_366_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__11));
v___x_367_ = l_Lean_Syntax_node2(v___x_359_, v___x_366_, v___x_355_, v___x_357_);
v___x_368_ = l_Lean_Syntax_node2(v___x_359_, v___x_360_, v___x_365_, v___x_367_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v_a_346_);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1___boxed(lean_object* v_x_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = lp_test_x2dlean___aux__custom__notation______macroRules__term__Ftsub_x3c____1(v_x_370_, v_a_371_, v_a_372_);
lean_dec_ref(v_a_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__Functype__sub__1(lean_object* v_x_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_377_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______macroRules__term__F_x2d_x3e____1___closed__4));
lean_inc(v_x_374_);
v___x_378_ = l_Lean_Syntax_isOfKind(v_x_374_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec(v_x_374_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v_a_376_);
return v___x_380_;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = l_Lean_Syntax_getArg(v_x_374_, v___x_381_);
v___x_383_ = ((lean_object*)(lp_test_x2dlean___aux__custom__notation______unexpand__mkFunctype__1___closed__1));
lean_inc(v___x_382_);
v___x_384_ = l_Lean_Syntax_isOfKind(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v___x_382_);
lean_dec(v_x_374_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v_a_376_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = l_Lean_Syntax_getArg(v_x_374_, v___x_387_);
lean_dec(v_x_374_);
v___x_389_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_388_);
v___x_390_ = l_Lean_Syntax_matchesNull(v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec(v___x_388_);
lean_dec(v___x_382_);
v___x_391_ = lean_box(0);
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_a_376_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_ref_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_393_ = l_Lean_Syntax_getArg(v___x_388_, v___x_381_);
v___x_394_ = l_Lean_Syntax_getArg(v___x_388_, v___x_387_);
lean_dec(v___x_388_);
v_ref_395_ = l_Lean_replaceRef(v___x_382_, v_a_375_);
lean_dec(v___x_382_);
v___x_396_ = 0;
v___x_397_ = l_Lean_SourceInfo_fromRef(v_ref_395_, v___x_396_);
lean_dec(v_ref_395_);
v___x_398_ = ((lean_object*)(lp_test_x2dlean_term__Ftsub_x3c___00__closed__1));
v___x_399_ = ((lean_object*)(lp_test_x2dlean_term__Ftsub_x3c___00__closed__2));
lean_inc(v___x_397_);
v___x_400_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_397_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = l_Lean_Syntax_node3(v___x_397_, v___x_398_, v___x_393_, v___x_400_, v___x_394_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v_a_376_);
return v___x_402_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean___aux__custom__notation______unexpand__Functype__sub__1___boxed(lean_object* v_x_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = lp_test_x2dlean___aux__custom__notation______unexpand__Functype__sub__1(v_x_403_, v_a_404_, v_a_405_);
lean_dec(v_a_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* lp_test_x2dlean_prepend__label(lean_object* v_C_407_, lean_object* v_t_408_){
_start:
{
lean_object* v_TYPES_409_; lean_object* v_FUNCS_410_; lean_object* v_GLOBALS_411_; lean_object* v_TABLES_412_; lean_object* v_MEMS_413_; lean_object* v_ELEMS_414_; lean_object* v_DATAS_415_; lean_object* v_LOCALS_416_; lean_object* v_LABELS_417_; lean_object* v_RETURN_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_426_; 
v_TYPES_409_ = lean_ctor_get(v_C_407_, 0);
v_FUNCS_410_ = lean_ctor_get(v_C_407_, 1);
v_GLOBALS_411_ = lean_ctor_get(v_C_407_, 2);
v_TABLES_412_ = lean_ctor_get(v_C_407_, 3);
v_MEMS_413_ = lean_ctor_get(v_C_407_, 4);
v_ELEMS_414_ = lean_ctor_get(v_C_407_, 5);
v_DATAS_415_ = lean_ctor_get(v_C_407_, 6);
v_LOCALS_416_ = lean_ctor_get(v_C_407_, 7);
v_LABELS_417_ = lean_ctor_get(v_C_407_, 8);
v_RETURN_418_ = lean_ctor_get(v_C_407_, 9);
v_isSharedCheck_426_ = !lean_is_exclusive(v_C_407_);
if (v_isSharedCheck_426_ == 0)
{
v___x_420_ = v_C_407_;
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_RETURN_418_);
lean_inc(v_LABELS_417_);
lean_inc(v_LOCALS_416_);
lean_inc(v_DATAS_415_);
lean_inc(v_ELEMS_414_);
lean_inc(v_MEMS_413_);
lean_inc(v_TABLES_412_);
lean_inc(v_GLOBALS_411_);
lean_inc(v_FUNCS_410_);
lean_inc(v_TYPES_409_);
lean_dec(v_C_407_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_422_, 0, v_t_408_);
lean_ctor_set(v___x_422_, 1, v_LABELS_417_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 8, v___x_422_);
v___x_424_ = v___x_420_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_TYPES_409_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_FUNCS_410_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v_GLOBALS_411_);
lean_ctor_set(v_reuseFailAlloc_425_, 3, v_TABLES_412_);
lean_ctor_set(v_reuseFailAlloc_425_, 4, v_MEMS_413_);
lean_ctor_set(v_reuseFailAlloc_425_, 5, v_ELEMS_414_);
lean_ctor_set(v_reuseFailAlloc_425_, 6, v_DATAS_415_);
lean_ctor_set(v_reuseFailAlloc_425_, 7, v_LOCALS_416_);
lean_ctor_set(v_reuseFailAlloc_425_, 8, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_425_, 9, v_RETURN_418_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_test_x2dlean_wasm2_x2e0(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_test_x2dlean_custom__notation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_test_x2dlean_wasm2_x2e0(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
