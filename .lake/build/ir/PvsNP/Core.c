// Lean compiler output
// Module: PvsNP.Core
// Imports: Init Mathlib.Data.Real.Basic
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
LEAN_EXPORT lean_object* l_PvsNP_DualComplexity_of___elambda__2(lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_DualComplexity_of___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_DualComplexity_of(lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_SAT__CA_dummy___default;
LEAN_EXPORT lean_object* l_PvsNP_DualComplexity_of___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_DualComplexity_of___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_DualComplexity_of___elambda__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_DualComplexity_of___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_PvsNP_DualComplexity_of___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PvsNP_DualComplexity_of___elambda__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PvsNP_DualComplexity_of___elambda__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_PvsNP_DualComplexity_of___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PvsNP_DualComplexity_of___elambda__2___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PvsNP_DualComplexity_of___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_PvsNP_DualComplexity_of___elambda__2___rarg), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_alloc_closure((void*)(l_PvsNP_DualComplexity_of___elambda__1___rarg), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_PvsNP_DualComplexity_of(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PvsNP_DualComplexity_of___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_PvsNP_SAT__CA_dummy___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PvsNP_Core(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PvsNP_SAT__CA_dummy___default = _init_l_PvsNP_SAT__CA_dummy___default();
lean_mark_persistent(l_PvsNP_SAT__CA_dummy___default);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
