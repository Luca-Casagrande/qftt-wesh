// Lean compiler output
// Module: AppendixC
// Imports: public import Init public import Mathlib
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
LEAN_EXPORT lean_object* lp_qftt_x2dwesh_L__op(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_qftt_x2dwesh_L__op___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_qftt_x2dwesh_L__op___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_1);
x_5 = lp_mathlib_Ring_toAddGroupWithOne___redArg(x_1);
x_6 = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(x_5);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_3);
x_11 = lean_unsigned_to_nat(2u);
lean_inc(x_9);
x_12 = lean_apply_2(x_9, x_11, x_10);
x_13 = lean_apply_1(x_2, x_4);
x_14 = lean_apply_2(x_9, x_11, x_13);
x_15 = lean_apply_2(x_8, x_12, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* lp_qftt_x2dwesh_L__op(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_qftt_x2dwesh_L__op___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_qftt_x2dwesh_AppendixC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
