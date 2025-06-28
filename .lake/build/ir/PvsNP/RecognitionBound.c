// Lean compiler output
// Module: PvsNP.RecognitionBound
// Imports: Init PvsNP.Core PvsNP.RSFoundation PvsNP.CellularAutomaton PvsNP.SATEncoding Mathlib.Data.Fintype.Card Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Analysis.SpecialFunctions.Pow.Real
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
LEAN_EXPORT uint8_t l_PvsNP_RecognitionBound_ca__with__balanced__parity(lean_object*, lean_object*);
uint8_t l_PvsNP_SATEncoding_encode__sat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_BalancedParityCode_mask___default(lean_object*);
LEAN_EXPORT uint8_t l_PvsNP_RecognitionBound_BalancedParityCode_mask___default___rarg(lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_encode__bit(lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_ca__with__balanced__parity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_encode__bit___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_encode__bit___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_encode__bit___rarg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_BalancedParityCode_mask___default___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_BalancedParityCode_mask___default___boxed(lean_object*);
LEAN_EXPORT uint8_t l_PvsNP_RecognitionBound_BalancedParityCode_mask___default___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_BalancedParityCode_mask___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PvsNP_RecognitionBound_BalancedParityCode_mask___default___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_BalancedParityCode_mask___default___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_PvsNP_RecognitionBound_BalancedParityCode_mask___default___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_BalancedParityCode_mask___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PvsNP_RecognitionBound_BalancedParityCode_mask___default(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_encode__bit___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (x_2 == 0)
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_apply_1(x_1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_3);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = lean_box(x_10);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
x_13 = lean_box(x_12);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_encode__bit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PvsNP_RecognitionBound_encode__bit___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_encode__bit___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_PvsNP_RecognitionBound_encode__bit___rarg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_encode__bit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PvsNP_RecognitionBound_encode__bit(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_PvsNP_RecognitionBound_ca__with__balanced__parity(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_PvsNP_SATEncoding_encode__sat(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_PvsNP_RecognitionBound_ca__with__balanced__parity___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PvsNP_RecognitionBound_ca__with__balanced__parity(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_PvsNP_Core(uint8_t builtin, lean_object*);
lean_object* initialize_PvsNP_RSFoundation(uint8_t builtin, lean_object*);
lean_object* initialize_PvsNP_CellularAutomaton(uint8_t builtin, lean_object*);
lean_object* initialize_PvsNP_SATEncoding(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Card(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PvsNP_RecognitionBound(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PvsNP_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PvsNP_RSFoundation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PvsNP_CellularAutomaton(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PvsNP_SATEncoding(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Card(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
