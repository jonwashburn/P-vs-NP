// Lean compiler output
// Module: PvsNP.SATEncoding
// Imports: Init Mathlib.Data.Real.Basic Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Analysis.SpecialFunctions.Pow.Real PvsNP.Core PvsNP.RSFoundation PvsNP.CellularAutomaton
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT uint8_t l_PvsNP_SATEncoding_encode__sat(lean_object*, lean_object*);
static lean_object* l_PvsNP_SATEncoding_place__clause___closed__1;
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_morton__decode_extract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_place__variable___boxed(lean_object*);
static lean_object* l_List_sum___at_PvsNP_SATEncoding_place__clause___spec__2___closed__1;
uint8_t l_List_any___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_morton__encode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_PvsNP_SATEncoding_place__clause___spec__4(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_PvsNP_SATEncoding_place__clause___spec__3___boxed(lean_object*, lean_object*);
uint8_t l___private_PvsNP_CellularAutomaton_0__PvsNP_CellularAutomaton_decEqPosition3D____x40_PvsNP_CellularAutomaton___hyg_341_(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_encode__sat___boxed(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
LEAN_EXPORT uint8_t l_PvsNP_SATEncoding_encode__sat___lambda__3(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_PvsNP_SATEncoding_place__clause___closed__2;
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_place__variable(lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_place__clause(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_PvsNP_SATEncoding_place__clause___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_encode__sat___lambda__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_morton__encode_interleave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_encode__sat___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_PvsNP_SATEncoding_place__clause___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_bindTR_go___at_PvsNP_SATEncoding_place__clause___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_morton__encode_interleave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_List_sum___at_PvsNP_SATEncoding_place__clause___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_encode__sat___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_PvsNP_SATEncoding_0__PvsNP_CellularAutomaton_ca__run_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_PvsNP_SATEncoding_encode__sat___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_PvsNP_SATEncoding_encode__sat___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_PvsNP_SATEncoding_0__PvsNP_CellularAutomaton_ca__run_match__1_splitter(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_foldl___at_Array_appendList___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_sum___at_PvsNP_SATEncoding_place__clause___spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_morton__decode(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_PvsNP_SATEncoding_place__clause___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_morton__encode___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_List_enumFrom___rarg(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_PvsNP_SATEncoding_place__clause___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_PvsNP_SATEncoding_0__PvsNP_CellularAutomaton_ca__run_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_place__clause___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_morton__encode_interleave(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = lean_nat_shiftr(x_1, x_9);
x_11 = lean_nat_land(x_10, x_8);
lean_dec(x_10);
x_12 = lean_nat_shiftr(x_2, x_9);
x_13 = lean_nat_land(x_12, x_8);
lean_dec(x_12);
x_14 = lean_nat_shiftr(x_3, x_9);
x_15 = lean_nat_land(x_14, x_8);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_shiftl(x_15, x_16);
lean_dec(x_15);
x_18 = lean_nat_shiftl(x_13, x_8);
lean_dec(x_13);
x_19 = lean_nat_lor(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_nat_lor(x_19, x_11);
lean_dec(x_11);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_shiftl(x_5, x_21);
lean_dec(x_5);
x_23 = lean_nat_lor(x_22, x_20);
lean_dec(x_20);
lean_dec(x_22);
x_4 = x_9;
x_5 = x_23;
goto _start;
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_morton__encode_interleave___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PvsNP_SATEncoding_morton__encode_interleave(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_morton__encode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(32u);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_PvsNP_SATEncoding_morton__encode_interleave(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_morton__encode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PvsNP_SATEncoding_morton__encode(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_morton__decode_extract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_land(x_1, x_8);
x_10 = lean_nat_shiftr(x_1, x_8);
x_11 = lean_nat_land(x_10, x_8);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_shiftr(x_1, x_12);
x_14 = lean_nat_land(x_13, x_8);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_shiftr(x_1, x_15);
lean_dec(x_1);
x_17 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_18 = lean_nat_shiftl(x_3, x_8);
lean_dec(x_3);
x_19 = lean_nat_lor(x_18, x_9);
lean_dec(x_9);
lean_dec(x_18);
x_20 = lean_nat_shiftl(x_4, x_8);
lean_dec(x_4);
x_21 = lean_nat_lor(x_20, x_11);
lean_dec(x_11);
lean_dec(x_20);
x_22 = lean_nat_shiftl(x_5, x_8);
lean_dec(x_5);
x_23 = lean_nat_lor(x_22, x_14);
lean_dec(x_14);
lean_dec(x_22);
x_1 = x_16;
x_2 = x_17;
x_3 = x_19;
x_4 = x_21;
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_morton__decode(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_PvsNP_SATEncoding_morton__decode_extract(x_1, x_2, x_3, x_3, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_4, 1, x_10);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_15 = x_11;
} else {
 lean_dec_ref(x_11);
 x_15 = lean_box(0);
}
if (lean_is_scalar(x_15)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_15;
}
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_place__variable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_PvsNP_SATEncoding_morton__encode_interleave(x_1, x_1, x_1, x_2, x_3);
x_5 = l_PvsNP_SATEncoding_morton__decode(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_nat_to_int(x_7);
x_11 = lean_nat_to_int(x_8);
x_12 = lean_nat_to_int(x_9);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_place__variable___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PvsNP_SATEncoding_place__variable(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_PvsNP_SATEncoding_place__clause___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_PvsNP_SATEncoding_place__clause___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_int_add(x_1, x_3);
lean_dec(x_1);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_List_sum___at_PvsNP_SATEncoding_place__clause___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_sum___at_PvsNP_SATEncoding_place__clause___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_List_sum___at_PvsNP_SATEncoding_place__clause___spec__2___closed__1;
x_3 = l_List_foldl___at_PvsNP_SATEncoding_place__clause___spec__3(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_PvsNP_SATEncoding_place__clause___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_PvsNP_SATEncoding_place__clause___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_PvsNP_SATEncoding_place__clause___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_1 = x_9;
x_2 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_bindTR_go___at_PvsNP_SATEncoding_place__clause___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(lean_box(0), x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_PvsNP_SATEncoding_place__clause___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_PvsNP_SATEncoding_place__clause___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_place__clause(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_nat_abs(x_3);
x_5 = l_PvsNP_SATEncoding_place__variable(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_nat_abs(x_6);
x_8 = l_PvsNP_SATEncoding_place__variable(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_nat_abs(x_9);
x_11 = l_PvsNP_SATEncoding_place__variable(x_10);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_15);
x_16 = l_List_mapTR_loop___at_PvsNP_SATEncoding_place__clause___spec__1(x_15, x_12);
x_17 = l_List_sum___at_PvsNP_SATEncoding_place__clause___spec__2(x_16);
lean_dec(x_16);
x_18 = l_PvsNP_SATEncoding_place__clause___closed__1;
x_19 = lean_int_ediv(x_17, x_18);
lean_dec(x_17);
lean_inc(x_15);
x_20 = l_List_mapTR_loop___at_PvsNP_SATEncoding_place__clause___spec__4(x_15, x_12);
x_21 = l_List_sum___at_PvsNP_SATEncoding_place__clause___spec__2(x_20);
lean_dec(x_20);
x_22 = lean_int_ediv(x_21, x_18);
lean_dec(x_21);
lean_inc(x_15);
x_23 = l_List_mapTR_loop___at_PvsNP_SATEncoding_place__clause___spec__5(x_15, x_12);
x_24 = l_List_sum___at_PvsNP_SATEncoding_place__clause___spec__2(x_23);
lean_dec(x_23);
x_25 = lean_int_ediv(x_24, x_18);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_List_mapTR_loop___at_PvsNP_SATEncoding_place__clause___spec__6(x_15, x_12);
x_28 = 6;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_12);
x_32 = l_PvsNP_SATEncoding_place__clause___closed__2;
x_33 = l_List_bindTR_go___at_PvsNP_SATEncoding_place__clause___spec__7(x_27, x_32);
x_34 = l_List_appendTR___rarg(x_31, x_33);
return x_34;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_PvsNP_SATEncoding_place__clause___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_PvsNP_SATEncoding_place__clause___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_sum___at_PvsNP_SATEncoding_place__clause___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_sum___at_PvsNP_SATEncoding_place__clause___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_place__clause___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PvsNP_SATEncoding_place__clause(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_PvsNP_SATEncoding_encode__sat___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_PvsNP_SATEncoding_place__variable(x_2);
x_4 = l___private_PvsNP_CellularAutomaton_0__PvsNP_CellularAutomaton_decEqPosition3D____x40_PvsNP_CellularAutomaton___hyg_341_(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_PvsNP_SATEncoding_encode__sat___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l___private_PvsNP_CellularAutomaton_0__PvsNP_CellularAutomaton_decEqPosition3D____x40_PvsNP_CellularAutomaton___hyg_341_(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_PvsNP_SATEncoding_encode__sat___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_PvsNP_SATEncoding_place__clause(x_4, x_3);
x_6 = lean_alloc_closure((void*)(l_PvsNP_SATEncoding_encode__sat___lambda__2___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_List_any___rarg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_PvsNP_SATEncoding_encode__sat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_List_range(x_3);
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_PvsNP_SATEncoding_encode__sat___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_List_any___rarg(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_enumFrom___rarg(x_8, x_7);
x_10 = lean_alloc_closure((void*)(l_PvsNP_SATEncoding_encode__sat___lambda__3___boxed), 2, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = l_List_any___rarg(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 6;
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = 1;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_encode__sat___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PvsNP_SATEncoding_encode__sat___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_encode__sat___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PvsNP_SATEncoding_encode__sat___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_encode__sat___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PvsNP_SATEncoding_encode__sat___lambda__3(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_PvsNP_SATEncoding_encode__sat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PvsNP_SATEncoding_encode__sat(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_PvsNP_SATEncoding_0__PvsNP_CellularAutomaton_ca__run_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_PvsNP_SATEncoding_0__PvsNP_CellularAutomaton_ca__run_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_PvsNP_SATEncoding_0__PvsNP_CellularAutomaton_ca__run_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_PvsNP_SATEncoding_0__PvsNP_CellularAutomaton_ca__run_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_PvsNP_SATEncoding_0__PvsNP_CellularAutomaton_ca__run_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(uint8_t builtin, lean_object*);
lean_object* initialize_PvsNP_Core(uint8_t builtin, lean_object*);
lean_object* initialize_PvsNP_RSFoundation(uint8_t builtin, lean_object*);
lean_object* initialize_PvsNP_CellularAutomaton(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PvsNP_SATEncoding(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(builtin, lean_io_mk_world());
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
l_List_sum___at_PvsNP_SATEncoding_place__clause___spec__2___closed__1 = _init_l_List_sum___at_PvsNP_SATEncoding_place__clause___spec__2___closed__1();
lean_mark_persistent(l_List_sum___at_PvsNP_SATEncoding_place__clause___spec__2___closed__1);
l_PvsNP_SATEncoding_place__clause___closed__1 = _init_l_PvsNP_SATEncoding_place__clause___closed__1();
lean_mark_persistent(l_PvsNP_SATEncoding_place__clause___closed__1);
l_PvsNP_SATEncoding_place__clause___closed__2 = _init_l_PvsNP_SATEncoding_place__clause___closed__2();
lean_mark_persistent(l_PvsNP_SATEncoding_place__clause___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
