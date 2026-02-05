// Lean compiler output
// Module: Section6_Part1
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
lean_object* lp_mathlib_NormedAddCommGroup_toENormedAddCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_TensorProduct_comm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_qftt_x2dwesh_QFTTWESH_Section6_Part1_G__xy___redArg(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_instCommSemiring;
LEAN_EXPORT lean_object* lp_qftt_x2dwesh_QFTTWESH_Section6_Part1_G__xy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_qftt_x2dwesh_QFTTWESH_Section6_Part1_G__xy___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lp_mathlib_Complex_instCommSemiring;
x_4 = lp_mathlib_NormedAddCommGroup_toENormedAddCommMonoid___redArg(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
x_7 = lp_mathlib_TensorProduct_comm___redArg(x_3, x_5, x_5, x_6, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_qftt_x2dwesh_QFTTWESH_Section6_Part1_G__xy(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_qftt_x2dwesh_QFTTWESH_Section6_Part1_G__xy___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_qftt_x2dwesh_Section6__Part1(uint8_t builtin) {
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
