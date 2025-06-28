// Lean compiler output
// Module: PvsNP.RSFoundation
// Imports: Init Mathlib.Data.Real.Basic Mathlib.Data.Real.Sqrt Mathlib.Data.Nat.Defs Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Order.Filter.Basic Mathlib.Order.Filter.AtTopBot
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
LEAN_EXPORT lean_object* l_PvsNP_RSFoundation_l__P;
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_one;
LEAN_EXPORT lean_object* l_PvsNP_RSFoundation__u03c4_u2080;
LEAN_EXPORT lean_object* l_PvsNP_RSFoundation_ca__state__count;
static lean_object* _init_l_PvsNP_RSFoundation__u03c4_u2080() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
return x_1;
}
}
static lean_object* _init_l_PvsNP_RSFoundation_l__P() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
return x_1;
}
}
static lean_object* _init_l_PvsNP_RSFoundation_ca__state__count() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(16u);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Sqrt(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Defs(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Order_Filter_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Order_Filter_AtTopBot(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PvsNP_RSFoundation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Sqrt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Defs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Order_Filter_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Order_Filter_AtTopBot(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PvsNP_RSFoundation__u03c4_u2080 = _init_l_PvsNP_RSFoundation__u03c4_u2080();
lean_mark_persistent(l_PvsNP_RSFoundation__u03c4_u2080);
l_PvsNP_RSFoundation_l__P = _init_l_PvsNP_RSFoundation_l__P();
lean_mark_persistent(l_PvsNP_RSFoundation_l__P);
l_PvsNP_RSFoundation_ca__state__count = _init_l_PvsNP_RSFoundation_ca__state__count();
lean_mark_persistent(l_PvsNP_RSFoundation_ca__state__count);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
