// Lean compiler output
// Module: src.SimplexAlgorithm
// Imports: Init src.MainTheorem Mathlib.Analysis.Convex.Cone.Proper Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
static lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_stop__condition___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argmin___at_LinearProgram_Tableau_simplex__step___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_LinearOrderedSemifield_toSemifield___rarg(lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_argmax___at_LinearProgram_Tableau_simplex__step___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argmax___at_LinearProgram_Tableau_simplex__step___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___elambda__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__recur(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_all___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_score__vertex___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_score__vertex___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___elambda__2(lean_object*);
LEAN_EXPORT lean_object* l_List_argmin___at_LinearProgram_Tableau_simplex__step___spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_score__vertex___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__1(lean_object*, lean_object*);
lean_object* l_Function_update___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_score__vertex___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_score__vertex___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Semifield_toDivisionSemiring___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_LinearProgram_maximize___default;
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Vector_tail___rarg(lean_object*);
lean_object* l_Equiv_vectorEquivFin___elambda__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Pi_instZero___elambda__1___rarg(lean_object*, lean_object*);
lean_object* l_Pi_instNeg___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_score__vertex___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argmax___at_LinearProgram_Tableau_simplex__step___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
lean_object* l_Vector_ofFn___rarg(lean_object*, lean_object*);
lean_object* l_Pi_instAdd___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___rarg(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_LinearProgram_Tableau_simplex__step___rarg___closed__1;
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_score__vertex___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableLtToLTToPreorderToPartialOrder___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_score__vertex___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___elambda__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l_LinearProgram_Tableau_simplex__recur___rarg___closed__1;
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___elambda__1___boxed(lean_object*, lean_object*);
lean_object* l_List_tail___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_argmax___at_LinearProgram_Tableau_simplex__step___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_stop__condition___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_instDecidableLeToLEToPreorderToPartialOrder___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_score(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_score__vertex___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__recur___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Semifield_toCommGroupWithZero___rarg(lean_object*);
LEAN_EXPORT uint8_t l_LinearProgram_Tableau_stop__condition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_fin__range(lean_object*);
LEAN_EXPORT lean_object* l_List_argmin___at_LinearProgram_Tableau_simplex__step___spec__6(lean_object*, lean_object*);
uint8_t l_Fintype_decidableMemRangeFintype___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_score__vertex(lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step(lean_object*);
lean_object* l_Vector_head___rarg(lean_object*);
lean_object* l_LinearOrderedRing_toLinearOrder___rarg(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_LinearOrderedField_toLinearOrderedSemifield___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__4(lean_object*);
lean_object* l_Field_toDivisionRing___rarg(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_LinearOrderedField_toField___rarg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Matrix_rowOp__pivot___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_score__vertex___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_vertex___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1(lean_object*);
static uint8_t l_LinearProgram_Tableau_simplex__recur___rarg___closed__2;
LEAN_EXPORT lean_object* l_List_argmin___at_LinearProgram_Tableau_simplex__step___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1(lean_object*, lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___elambda__1(lean_object*, lean_object*);
lean_object* l_List_foldrTR___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__3(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_vertex(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_transpose___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_score__vertex___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_stop__condition(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_score___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t _init_l_LinearProgram_maximize___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_mod(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___elambda__2___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_1);
x_7 = l_LinearOrderedSemifield_toSemifield___rarg(x_6);
x_8 = l_Semifield_toCommGroupWithZero___rarg(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_nat_dec_eq(x_4, x_5);
if (x_11 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
else
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = lean_apply_1(x_3, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_LinearOrderedField_toField___rarg(x_1);
x_4 = l_Field_toDivisionRing___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_mod(x_8, x_7);
lean_dec(x_7);
x_10 = lean_nat_dec_eq(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_nat_sub(x_4, x_6);
x_13 = lean_apply_2(x_11, x_12, x_5);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___lambda__1___boxed), 2, 1);
lean_closure_set(x_15, 0, x_3);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Pi_instNeg___elambda__1___rarg(x_15, x_16, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_apply_1(x_18, x_5);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_mod(x_6, x_1);
x_8 = lean_nat_dec_eq(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
x_12 = lean_apply_1(x_9, x_11);
return x_12;
}
else
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_inc(x_4);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___lambda__2___boxed), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_nat_add(x_1, x_2);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_4);
x_13 = l_LinearOrderedSemifield_toSemifield___rarg(x_12);
lean_inc(x_13);
x_14 = l_Semifield_toCommGroupWithZero___rarg(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Semifield_toDivisionSemiring___rarg(x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___lambda__3___boxed), 2, 1);
lean_closure_set(x_20, 0, x_19);
lean_inc(x_11);
x_21 = lean_alloc_closure((void*)(l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1___rarg___boxed), 5, 3);
lean_closure_set(x_21, 0, x_4);
lean_closure_set(x_21, 1, x_11);
lean_closure_set(x_21, 2, x_20);
x_22 = l_Vector_ofFn___rarg(x_11, x_21);
x_23 = lean_alloc_closure((void*)(l_Matrix_transpose___rarg), 3, 1);
lean_closure_set(x_23, 0, x_6);
x_24 = l_Vector_ofFn___rarg(x_2, x_23);
x_25 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___lambda__4___boxed), 5, 3);
lean_closure_set(x_25, 0, x_11);
lean_closure_set(x_25, 1, x_5);
lean_closure_set(x_25, 2, x_16);
x_26 = l_Vector_ofFn___rarg(x_10, x_25);
x_27 = l_List_appendTR___rarg(x_24, x_26);
x_28 = l_List_appendTR___rarg(x_22, x_27);
x_29 = lean_alloc_closure((void*)(l_Equiv_vectorEquivFin___elambda__2___rarg___boxed), 2, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___elambda__2___rarg), 3, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___elambda__1___boxed), 4, 3);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_2);
lean_closure_set(x_31, 2, x_9);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_LinearProgram_simplex__tableau___elambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_LinearProgram_simplex__tableau___elambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LinearProgram_simplex__tableau___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_LinearProgram_simplex__tableau___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LinearProgram_simplex__tableau___lambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_LinearProgram_simplex__tableau___lambda__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Function_update___rarg(x_3, x_4, x_5, x_1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_simplex__step___elambda__1___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___elambda__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Matrix_rowOp__pivot___rarg(x_1, x_7, x_5, x_8, x_9, x_6, lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_simplex__step___elambda__2___rarg___boxed), 11, 0);
return x_2;
}
}
static lean_object* _init_l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decEq___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_1);
x_7 = l_List_reverse___rarg(x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_inc(x_12);
x_13 = l_List_finRange(x_12);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1___rarg___closed__1;
lean_inc(x_9);
x_16 = l_Fintype_decidableMemRangeFintype___rarg(x_13, x_15, x_14, x_9);
x_17 = l_instDecidableNot___rarg(x_16);
if (x_17 == 0)
{
lean_dec(x_12);
lean_free_object(x_5);
lean_dec(x_9);
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_19 = lean_nat_add(x_2, x_3);
x_20 = lean_nat_add(x_19, x_11);
lean_dec(x_19);
x_21 = lean_nat_dec_eq(x_9, x_20);
lean_dec(x_20);
x_22 = l_instDecidableNot___rarg(x_21);
if (x_22 == 0)
{
lean_dec(x_12);
lean_free_object(x_5);
lean_dec(x_9);
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = l_LinearOrderedRing_toLinearOrder___rarg(x_24);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_mod(x_27, x_12);
lean_dec(x_12);
lean_inc(x_9);
x_29 = lean_apply_2(x_26, x_28, x_9);
x_30 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_1);
x_31 = l_LinearOrderedSemifield_toSemifield___rarg(x_30);
x_32 = l_Semifield_toCommGroupWithZero___rarg(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_instDecidableLtToLTToPreorderToPartialOrder___rarg(x_25, x_29, x_34);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_free_object(x_5);
lean_dec(x_9);
x_5 = x_10;
goto _start;
}
else
{
lean_ctor_set(x_5, 1, x_6);
{
lean_object* _tmp_4 = x_10;
lean_object* _tmp_5 = x_5;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_5, 0);
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_5);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_2, x_41);
lean_inc(x_42);
x_43 = l_List_finRange(x_42);
x_44 = lean_ctor_get(x_4, 1);
lean_inc(x_44);
x_45 = l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1___rarg___closed__1;
lean_inc(x_39);
x_46 = l_Fintype_decidableMemRangeFintype___rarg(x_43, x_45, x_44, x_39);
x_47 = l_instDecidableNot___rarg(x_46);
if (x_47 == 0)
{
lean_dec(x_42);
lean_dec(x_39);
x_5 = x_40;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_nat_add(x_2, x_3);
x_50 = lean_nat_add(x_49, x_41);
lean_dec(x_49);
x_51 = lean_nat_dec_eq(x_39, x_50);
lean_dec(x_50);
x_52 = l_instDecidableNot___rarg(x_51);
if (x_52 == 0)
{
lean_dec(x_42);
lean_dec(x_39);
x_5 = x_40;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = l_LinearOrderedRing_toLinearOrder___rarg(x_54);
x_56 = lean_ctor_get(x_4, 0);
lean_inc(x_56);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_nat_mod(x_57, x_42);
lean_dec(x_42);
lean_inc(x_39);
x_59 = lean_apply_2(x_56, x_58, x_39);
x_60 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_1);
x_61 = l_LinearOrderedSemifield_toSemifield___rarg(x_60);
x_62 = l_Semifield_toCommGroupWithZero___rarg(x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_instDecidableLtToLTToPreorderToPartialOrder___rarg(x_55, x_59, x_64);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_dec(x_39);
x_5 = x_40;
goto _start;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_39);
lean_ctor_set(x_68, 1, x_6);
x_5 = x_40;
x_6 = x_68;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_inc(x_2);
x_8 = lean_apply_1(x_2, x_7);
lean_inc(x_5);
x_9 = lean_apply_1(x_2, x_5);
x_10 = l_LinearOrderedRing_toLinearOrder___rarg(x_1);
x_11 = l_instDecidableLtToLTToPreorderToPartialOrder___rarg(x_10, x_8, x_9);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_5);
return x_4;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
lean_ctor_set(x_4, 0, x_5);
return x_4;
}
else
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_5);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__3___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__3___rarg(x_3, x_4, x_5, x_6, x_8);
x_6 = x_10;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__4___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_argmax___at_LinearProgram_Tableau_simplex__step___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__4___rarg(x_1, x_2, x_3, x_4, x_7, x_8, x_5);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_argmax___at_LinearProgram_Tableau_simplex__step___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_argmax___at_LinearProgram_Tableau_simplex__step___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_10 = l_List_reverse___rarg(x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_5);
x_14 = l_LinearOrderedRing_toLinearOrder___rarg(x_5);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_15 = lean_apply_2(x_7, x_12, x_6);
x_16 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_1);
x_17 = l_LinearOrderedSemifield_toSemifield___rarg(x_16);
x_18 = l_Semifield_toCommGroupWithZero___rarg(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_instDecidableEq___rarg(x_14, x_15, x_20);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
x_23 = l_instDecidableNot___rarg(x_22);
if (x_23 == 0)
{
lean_free_object(x_8);
lean_dec(x_12);
x_8 = x_13;
goto _start;
}
else
{
lean_ctor_set(x_8, 1, x_9);
{
lean_object* _tmp_7 = x_13;
lean_object* _tmp_8 = x_8;
x_8 = _tmp_7;
x_9 = _tmp_8;
}
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
lean_inc(x_5);
x_28 = l_LinearOrderedRing_toLinearOrder___rarg(x_5);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_26);
x_29 = lean_apply_2(x_7, x_26, x_6);
x_30 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_1);
x_31 = l_LinearOrderedSemifield_toSemifield___rarg(x_30);
x_32 = l_Semifield_toCommGroupWithZero___rarg(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_instDecidableEq___rarg(x_28, x_29, x_34);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
x_37 = l_instDecidableNot___rarg(x_36);
if (x_37 == 0)
{
lean_dec(x_26);
x_8 = x_27;
goto _start;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_9);
x_8 = x_27;
x_9 = x_39;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__5___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_5);
x_8 = lean_apply_1(x_2, x_5);
x_9 = lean_apply_1(x_2, x_7);
x_10 = l_LinearOrderedRing_toLinearOrder___rarg(x_1);
x_11 = l_instDecidableLtToLTToPreorderToPartialOrder___rarg(x_10, x_8, x_9);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_5);
return x_4;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
lean_ctor_set(x_4, 0, x_5);
return x_4;
}
else
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_5);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__7___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__7___rarg(x_2, x_3, x_4, x_5, x_7);
x_5 = x_9;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__8___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_argmin___at_LinearProgram_Tableau_simplex__step___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__8___rarg(x_1, x_2, x_3, x_6, x_7, x_4);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_argmin___at_LinearProgram_Tableau_simplex__step___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_argmin___at_LinearProgram_Tableau_simplex__step___spec__6___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_mod(x_7, x_6);
lean_dec(x_6);
x_9 = lean_apply_2(x_4, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
lean_inc(x_3);
lean_inc(x_5);
x_9 = lean_apply_2(x_3, x_5, x_8);
x_10 = lean_apply_2(x_3, x_5, x_4);
x_11 = lean_apply_2(x_6, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_LinearProgram_Tableau_simplex__step___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqFin___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_5 = lean_nat_add(x_2, x_3);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_add(x_5, x_6);
x_8 = l_List_fin__range(x_7);
x_9 = lean_box(0);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1___rarg(x_1, x_2, x_3, x_4, x_8, x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_inc(x_2);
lean_inc(x_4);
x_12 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_simplex__step___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_2);
lean_inc(x_11);
x_13 = l_List_argmax___at_LinearProgram_Tableau_simplex__step___spec__2___rarg(x_2, x_3, x_11, x_12, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
x_17 = l_List_fin__range(x_16);
x_18 = l_List_tail___rarg(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_11);
x_21 = l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__5___rarg(x_1, x_2, x_3, x_4, x_11, x_14, x_19, x_18, x_9);
lean_inc(x_14);
lean_inc(x_19);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_simplex__step___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_19);
lean_closure_set(x_22, 3, x_14);
x_23 = l_List_argmin___at_LinearProgram_Tableau_simplex__step___spec__6___rarg(x_2, x_11, x_22, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_24);
lean_inc(x_16);
lean_inc(x_14);
x_25 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_simplex__step___elambda__2___rarg___boxed), 11, 9);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_4);
lean_closure_set(x_25, 4, x_7);
lean_closure_set(x_25, 5, x_14);
lean_closure_set(x_25, 6, x_16);
lean_closure_set(x_25, 7, x_19);
lean_closure_set(x_25, 8, x_24);
x_26 = l_LinearProgram_Tableau_simplex__step___rarg___closed__1;
x_27 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_simplex__step___elambda__1___rarg___boxed), 6, 5);
lean_closure_set(x_27, 0, x_14);
lean_closure_set(x_27, 1, x_16);
lean_closure_set(x_27, 2, x_26);
lean_closure_set(x_27, 3, x_20);
lean_closure_set(x_27, 4, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_simplex__step___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_LinearProgram_Tableau_simplex__step___elambda__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LinearProgram_Tableau_simplex__step___elambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___elambda__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_LinearProgram_Tableau_simplex__step___elambda__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_argmax___at_LinearProgram_Tableau_simplex__step___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_argmax___at_LinearProgram_Tableau_simplex__step___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_argmax___at_LinearProgram_Tableau_simplex__step___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_argmax___at_LinearProgram_Tableau_simplex__step___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__7___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_argAux___at_LinearProgram_Tableau_simplex__step___spec__7(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldl___at_LinearProgram_Tableau_simplex__step___spec__8___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_argmin___at_LinearProgram_Tableau_simplex__step___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_argmin___at_LinearProgram_Tableau_simplex__step___spec__6___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_argmin___at_LinearProgram_Tableau_simplex__step___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_argmin___at_LinearProgram_Tableau_simplex__step___spec__6(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_LinearProgram_Tableau_simplex__step___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__step___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_LinearProgram_Tableau_simplex__step___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_score__vertex___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_nat_add(x_1, x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
x_7 = lean_nat_mod(x_3, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_score__vertex___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_1(x_1, x_4);
return x_6;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_score__vertex___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Function_update___at_LinearProgram_Tableau_score__vertex___spec__3___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_1);
x_4 = l_LinearOrderedSemifield_toSemifield___rarg(x_3);
x_5 = l_Semifield_toCommGroupWithZero___rarg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l_Pi_instZero___elambda__1___rarg), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Function_update___at_LinearProgram_Tableau_score__vertex___spec__3___rarg(x_8, x_4, x_5, x_6);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_LinearOrderedField_toField___rarg(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_CommRing_toNonUnitalCommRing___rarg(x_4);
lean_dec(x_4);
x_6 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___rarg(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Pi_instAdd___elambda__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_LinearOrderedField_toField___rarg(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_CommRing_toNonUnitalCommRing___rarg(x_4);
lean_dec(x_4);
x_6 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___rarg(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__2), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__3___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l_Pi_instZero___elambda__1___rarg), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_List_foldrTR___rarg(x_6, x_8, x_4);
x_10 = lean_apply_1(x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_score__vertex___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Multiset_map___rarg(x_5, x_4);
x_8 = l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg(x_1, x_2, x_3, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_score__vertex___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_sum___at_LinearProgram_Tableau_score__vertex___spec__4___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_score__vertex___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_nat_add(x_1, x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_5);
x_11 = lean_apply_1(x_10, x_5);
x_12 = l_Nat_cast___at_LinearProgram_Tableau_score__vertex___spec__1(x_1, x_2, x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_apply_2(x_13, x_5, x_9);
x_15 = l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2___rarg(x_4, x_1, x_2, x_12, x_14, x_6);
lean_dec(x_14);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_score__vertex___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_score__vertex___rarg___lambda__1), 6, 4);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
lean_closure_set(x_5, 3, x_1);
x_6 = lean_nat_add(x_2, x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_6, x_7);
lean_dec(x_6);
x_9 = lean_nat_add(x_2, x_7);
x_10 = l_List_finRange(x_9);
x_11 = lean_alloc_closure((void*)(l_Finset_sum___at_LinearProgram_Tableau_score__vertex___spec__4___rarg___boxed), 6, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_10);
lean_closure_set(x_11, 4, x_5);
x_12 = l_Vector_ofFn___rarg(x_8, x_11);
lean_dec(x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_score__vertex(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_score__vertex___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_score__vertex___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_cast___at_LinearProgram_Tableau_score__vertex___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_score__vertex___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Function_update___at_LinearProgram_Tableau_score__vertex___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_score__vertex___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Function_update___at_LinearProgram_Tableau_score__vertex___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Pi_single___at_LinearProgram_Tableau_score__vertex___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___lambda__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Multiset_sum___at_LinearProgram_Tableau_score__vertex___spec__5___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_score__vertex___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Finset_sum___at_LinearProgram_Tableau_score__vertex___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_vertex___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_LinearProgram_Tableau_score__vertex___rarg(x_1, x_2, x_3, x_4);
x_6 = l_Vector_tail___rarg(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_vertex(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_vertex___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_score___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_LinearProgram_Tableau_score__vertex___rarg(x_1, x_2, x_3, x_4);
x_6 = l_Vector_head___rarg(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_score(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_score___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_stop__condition___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_LinearOrderedRing_toLinearOrder___rarg(x_3);
x_5 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_1);
lean_dec(x_1);
x_6 = l_LinearOrderedSemifield_toSemifield___rarg(x_5);
x_7 = l_Semifield_toCommGroupWithZero___rarg(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_instDecidableLeToLEToPreorderToPartialOrder___rarg(x_4, x_9, x_2);
return x_10;
}
}
LEAN_EXPORT uint8_t l_LinearProgram_Tableau_stop__condition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_5 = lean_nat_add(x_2, x_3);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_mod(x_11, x_10);
lean_dec(x_10);
x_13 = lean_apply_1(x_8, x_12);
x_14 = l_Vector_ofFn___rarg(x_7, x_13);
lean_dec(x_7);
x_15 = l_Vector_tail___rarg(x_14);
lean_dec(x_14);
x_16 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_stop__condition___rarg___lambda__1), 2, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_List_all___rarg(x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_stop__condition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_stop__condition___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_stop__condition___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_LinearProgram_Tableau_stop__condition___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint8_t _init_l_LinearProgram_Tableau_simplex__recur___rarg___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 0;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static uint8_t _init_l_LinearProgram_Tableau_simplex__recur___rarg___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 1;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__recur___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_4);
lean_inc(x_1);
x_5 = l_LinearProgram_Tableau_stop__condition___rarg(x_1, x_2, x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_LinearProgram_Tableau_simplex__recur___rarg___closed__1;
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_7; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_LinearProgram_Tableau_simplex__step___rarg(x_1, x_2, x_3, x_4);
x_4 = x_7;
goto _start;
}
}
else
{
uint8_t x_9; 
x_9 = l_LinearProgram_Tableau_simplex__recur___rarg___closed__2;
if (x_9 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_10; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_LinearProgram_Tableau_simplex__step___rarg(x_1, x_2, x_3, x_4);
x_4 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_simplex__recur(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_simplex__recur___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_src_MainTheorem(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Convex_Cone_Proper(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_FiniteDimensional(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_src_SimplexAlgorithm(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_src_MainTheorem(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Convex_Cone_Proper(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_FiniteDimensional(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_LinearProgram_maximize___default = _init_l_LinearProgram_maximize___default();
l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1___rarg___closed__1 = _init_l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1___rarg___closed__1();
lean_mark_persistent(l_List_filterTR_loop___at_LinearProgram_Tableau_simplex__step___spec__1___rarg___closed__1);
l_LinearProgram_Tableau_simplex__step___rarg___closed__1 = _init_l_LinearProgram_Tableau_simplex__step___rarg___closed__1();
lean_mark_persistent(l_LinearProgram_Tableau_simplex__step___rarg___closed__1);
l_LinearProgram_Tableau_simplex__recur___rarg___closed__1 = _init_l_LinearProgram_Tableau_simplex__recur___rarg___closed__1();
l_LinearProgram_Tableau_simplex__recur___rarg___closed__2 = _init_l_LinearProgram_Tableau_simplex__recur___rarg___closed__2();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
