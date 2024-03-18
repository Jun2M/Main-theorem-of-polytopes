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
LEAN_EXPORT lean_object* l_LinearProgram_result_fail___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_return___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_LinearOrderedSemifield_toSemifield___rarg(lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_initial__tableau___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_return___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__2___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Nat_fin__list__range(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__14___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_initial__tableau___elambda__1___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_all___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164_;
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_return___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___elambda__1___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_return___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_Simplex__inner___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Pi_addMonoid___rarg(lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__11;
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__2;
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_origin__feasible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_return___spec__1___lambda__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__20;
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__3___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Function_update___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argmax___at_LinearProgram_Tableau_Simplex__inner___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_initial__tableau___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__2___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_LinearProgram_minimize___default;
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__21;
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_initial__tableau___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_return___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_Simplex__inner___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_hasDecEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toDistrib___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_fail___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__1(lean_object*, lean_object*);
lean_object* l_Semifield_toDivisionSemiring___rarg(lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__3;
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_vertex___default(lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__19;
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_return___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* l_Vector_tail___rarg(lean_object*);
lean_object* l_Equiv_vectorEquivFin___elambda__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__4(lean_object*, lean_object*);
lean_object* l_Pi_instZero___elambda__1___rarg(lean_object*, lean_object*);
lean_object* l_Pi_instNeg___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Semiring_toNonAssocSemiring___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_initial__tableau___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argmax___at_LinearProgram_Tableau_Simplex__inner___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__4;
lean_object* l_Vector_ofFn___rarg(lean_object*, lean_object*);
lean_object* l_Pi_instAdd___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_return___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argmin___at_LinearProgram_Tableau_Simplex__inner___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__14;
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__5;
lean_object* l_Multiset_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_return___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_Simplex__inner___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_value___default___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_return___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableLtToLTToPreorderToPartialOrder___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__17;
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_return___spec__8___boxed(lean_object*);
lean_object* l_List_tail___rarg(lean_object*);
lean_object* l_instDecidableLeToLEToPreorderToPartialOrder___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__3___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_LinearProgram_origin__feasible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__12;
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_return___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_Simplex__inner___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__13(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_origin__feasible___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Semifield_toCommGroupWithZero___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___elambda__1___spec__1___rarg(lean_object*, lean_object*);
static lean_object* l_LinearProgram_Tableau_pivoting___closed__1;
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_vertex___default___rarg(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_fail___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_initial__tableau___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___elambda__1___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_initial__tableau___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_basic___default(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__6;
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Vector_head___rarg(lean_object*);
lean_object* l_LinearOrderedRing_toLinearOrder___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_return___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_value___default___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_return___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_Simplex__inner___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AddMonoid_toAddZeroClass___rarg(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__2___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_LinearOrderedField_toLinearOrderedSemifield___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Field_toDivisionRing___rarg(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_return(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_return___spec__1___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_initial__tableau___elambda__1___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_LinearOrderedField_toField___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_Simplex__inner___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_return___spec__1___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_fail___elambda__1___boxed(lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__16;
LEAN_EXPORT lean_object* l_LinearProgram_result_fail___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argmin___at_LinearProgram_Tableau_Simplex__inner___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__9;
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__18;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_return___spec__5(lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__7;
LEAN_EXPORT lean_object* l_LinearProgram_result_basic___default___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___lambda__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_value___default___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__15;
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_initial__tableau___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_initial__tableau___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__12(lean_object*);
static lean_object* l_LinearProgram_Tableau_Simplex__inner___closed__1;
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_simplex__tableau___elambda__1___spec__1(lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__8;
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_Simplex__inner___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_return___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_vertex___default___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_return___spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1(lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__13;
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__11___boxed(lean_object*, lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_fail(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_return___spec__1___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_value___default___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldrTR___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_Simplex__inner___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_initial__tableau___elambda__1___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__22;
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__15(lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__1;
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_return___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_initial__tableau___elambda__1___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default___elambda__1(lean_object*);
lean_object* l_Matrix_transpose___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_fail___elambda__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_187_;
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___elambda__1___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_result_value___default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_initial__tableau___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_initial__tableau___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__10;
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__15___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_initial__tableau___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t _init_l_LinearProgram_minimize___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticSeq", 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__1;
x_2 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__2;
x_3 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__3;
x_4 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticSeq1Indented", 18);
return x_1;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__1;
x_2 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__2;
x_3 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__3;
x_4 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticRfl", 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__1;
x_2 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__2;
x_3 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__3;
x_4 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__11;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rfl", 3);
return x_1;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__13;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__6;
x_2 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__14;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__12;
x_3 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__15;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__6;
x_2 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__16;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__10;
x_3 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__17;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__6;
x_2 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__18;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__8;
x_3 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__19;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__6;
x_2 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__20;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__5;
x_3 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__21;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_164_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__22;
return x_1;
}
}
static lean_object* _init_l___auto____x40_src_SimplexAlgorithm___hyg_187_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__22;
return x_1;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_basic___default(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_nat_add(x_1, x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_mod(x_7, x_6);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_basic___default___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_LinearProgram_result_basic___default(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_value___default___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Vector_head___rarg(x_1);
x_5 = lean_apply_1(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_value___default___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_LinearProgram_result_value___default___elambda__1___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_value___default(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_alloc_closure((void*)(l_LinearProgram_result_value___default___elambda__1___rarg___boxed), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_closure((void*)(l_LinearProgram_result_value___default___elambda__1___rarg___boxed), 3, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_value___default___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_LinearProgram_result_value___default___elambda__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_value___default___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LinearProgram_result_value___default___elambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Pi_instNeg___elambda__1___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_LinearProgram_result_score___default___elambda__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
if (x_4 == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_alloc_closure((void*)(l_LinearProgram_result_score___default___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_LinearProgram_result_score___default___elambda__1___rarg), 3, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_closure((void*)(l_LinearProgram_result_score___default___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_LinearProgram_result_score___default___elambda__1___rarg), 3, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_LinearProgram_result_score___default___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LinearProgram_result_score___default___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_LinearProgram_result_score___default___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_score___default___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_LinearProgram_result_score___default(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_vertex___default___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Vector_tail___rarg(x_4);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Vector_tail___rarg(x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_vertex___default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_LinearProgram_result_vertex___default___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_vertex___default___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LinearProgram_result_vertex___default(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_fail___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_fail___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_LinearProgram_result_fail___elambda__1___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_fail___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_nat_add(x_1, x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_mod(x_7, x_6);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_fail(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_LinearProgram_result_fail___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_alloc_closure((void*)(l_LinearProgram_result_fail___elambda__1___rarg), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set(x_9, 4, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_fail___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LinearProgram_result_fail___elambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_fail___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_LinearProgram_result_fail___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_result_fail___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_LinearProgram_result_fail(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_origin__feasible___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_LinearProgram_origin__feasible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Vector_ofFn___rarg(x_1, x_6);
x_8 = lean_alloc_closure((void*)(l_LinearProgram_origin__feasible___lambda__1), 2, 1);
lean_closure_set(x_8, 0, x_4);
x_9 = l_List_all___rarg(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_origin__feasible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_LinearProgram_origin__feasible(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Function_update___rarg(x_3, x_4, x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_pivoting___elambda__1___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_NonUnitalNonAssocSemiring_toDistrib___rarg(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_1);
x_8 = l_LinearOrderedSemifield_toSemifield___rarg(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Semiring_toNonAssocSemiring___rarg(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_2, x_3, x_6);
lean_inc(x_12);
x_14 = lean_apply_2(x_12, x_4, x_13);
x_15 = lean_apply_2(x_12, x_5, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_7, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_pivoting___elambda__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_1);
lean_inc(x_1);
x_11 = l_LinearOrderedField_toField___rarg(x_1);
x_12 = l_Field_toDivisionRing___rarg(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_7);
x_15 = lean_apply_2(x_4, x_7, x_3);
x_16 = lean_apply_1(x_14, x_15);
lean_inc(x_6);
x_17 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_pivoting___elambda__2___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_6);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_16);
x_18 = lean_apply_1(x_6, x_7);
x_19 = l_Pi_instAdd___elambda__1___rarg(x_10, x_17, x_18, x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_20 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_1);
lean_dec(x_1);
x_21 = l_LinearOrderedSemifield_toSemifield___rarg(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Semiring_toNonAssocSemiring___rarg(x_22);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_apply_2(x_6, x_2, x_8);
x_27 = lean_apply_2(x_25, x_5, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_pivoting___elambda__2___rarg), 8, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_6, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_pivoting___elambda__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_1);
lean_inc(x_1);
x_10 = l_LinearOrderedField_toField___rarg(x_1);
x_11 = l_Field_toDivisionRing___rarg(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_4);
lean_inc(x_6);
x_14 = lean_apply_2(x_4, x_6, x_3);
x_15 = lean_apply_1(x_13, x_14);
lean_inc(x_4);
x_16 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_pivoting___elambda__2___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_4);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_5);
lean_closure_set(x_16, 4, x_15);
x_17 = lean_apply_1(x_4, x_6);
x_18 = l_Pi_instAdd___elambda__1___rarg(x_9, x_16, x_17, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_3);
x_19 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_1);
lean_dec(x_1);
x_20 = l_LinearOrderedSemifield_toSemifield___rarg(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Semiring_toNonAssocSemiring___rarg(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_2(x_4, x_2, x_7);
x_26 = lean_apply_2(x_24, x_5, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_pivoting___elambda__3___rarg), 7, 0);
return x_4;
}
}
static lean_object* _init_l_LinearProgram_Tableau_pivoting___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decEq___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
x_11 = lean_apply_2(x_10, x_6, x_7);
x_12 = lean_apply_1(x_9, x_11);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_14 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_pivoting___elambda__3___rarg), 7, 5);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_10);
lean_closure_set(x_14, 4, x_12);
lean_inc(x_7);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_pivoting___elambda__2___rarg), 8, 6);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_6);
lean_closure_set(x_15, 2, x_7);
lean_closure_set(x_15, 3, x_10);
lean_closure_set(x_15, 4, x_12);
lean_closure_set(x_15, 5, x_13);
x_16 = lean_ctor_get(x_5, 2);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l_LinearProgram_Tableau_pivoting___closed__1;
x_18 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_pivoting___elambda__1___rarg___boxed), 5, 4);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_7);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_LinearProgram_Tableau_pivoting___elambda__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LinearProgram_Tableau_pivoting___elambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LinearProgram_Tableau_pivoting___elambda__2___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__2___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_LinearProgram_Tableau_pivoting___elambda__2___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_LinearProgram_Tableau_pivoting___elambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___elambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_LinearProgram_Tableau_pivoting___elambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_pivoting___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_LinearProgram_Tableau_pivoting(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___elambda__1___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___elambda__1___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_cast___at_LinearProgram_Tableau_return___elambda__1___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_return___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_nat_mod(x_8, x_7);
x_11 = lean_apply_1(x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_return___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_4, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_1, x_4, x_5);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_return___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Function_update___at_LinearProgram_Tableau_return___spec__2___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_return___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_return___spec__1___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Pi_single___at_LinearProgram_Tableau_return___spec__1___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_Pi_instZero___elambda__1___rarg), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_return___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_closure((void*)(l_Pi_single___at_LinearProgram_Tableau_return___spec__1___lambda__2___boxed), 2, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_alloc_closure((void*)(l_Pi_instZero___elambda__1___rarg), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l_Function_update___at_LinearProgram_Tableau_return___spec__2___rarg(x_10, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
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
return x_7;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Pi_addMonoid___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Pi_instAdd___elambda__1___rarg(x_6, x_2, x_3, x_4);
x_8 = lean_apply_1(x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Pi_addMonoid___rarg(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__3), 5, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__4___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_Pi_instZero___elambda__1___rarg), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_List_foldrTR___rarg(x_5, x_7, x_2);
x_9 = lean_apply_2(x_8, x_3, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_return___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = l_Multiset_map___rarg(x_6, x_5);
x_10 = l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg(x_4, x_9, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_return___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_sum___at_LinearProgram_Tableau_return___spec__5___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__3), 5, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__4___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_Pi_instZero___elambda__1___rarg), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_List_foldrTR___rarg(x_5, x_7, x_2);
x_9 = lean_apply_2(x_8, x_3, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_Tableau_return___spec__9___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_return___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = l_Multiset_map___rarg(x_6, x_5);
x_10 = l_Multiset_sum___at_LinearProgram_Tableau_return___spec__9___rarg(x_4, x_9, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_return___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_sum___at_LinearProgram_Tableau_return___spec__8___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_return___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_5);
x_9 = lean_apply_1(x_8, x_5);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, x_5);
x_12 = l_Pi_single___at_LinearProgram_Tableau_return___spec__1(x_2, x_3, lean_box(0), x_4, x_9, x_11, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_return___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_mod(x_11, x_10);
lean_dec(x_10);
x_13 = lean_nat_dec_eq(x_7, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_nat_add(x_2, x_1);
x_15 = lean_nat_add(x_14, x_9);
lean_dec(x_14);
x_16 = l_Nat_cast___at_LinearProgram_Tableau_return___spec__3(x_2, x_1, x_7);
lean_dec(x_7);
x_17 = l_Nat_cast___at_LinearProgram_Tableau_return___spec__4(x_2, x_1, x_2);
x_18 = l_Fin_add(x_15, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_19 = l_Finset_sum___at_LinearProgram_Tableau_return___spec__5___rarg(x_2, x_1, lean_box(0), x_4, x_5, x_6, x_18, x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Nat_cast___at_LinearProgram_Tableau_return___spec__7(x_2, x_1, x_7);
lean_dec(x_7);
x_21 = l_Finset_sum___at_LinearProgram_Tableau_return___spec__8___rarg(x_2, x_1, lean_box(0), x_4, x_5, x_6, x_20, x_8);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_return(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_return___lambda__1), 7, 4);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
lean_inc(x_10);
x_11 = l_List_finRange(x_10);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_return___lambda__2___boxed), 8, 6);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_8);
lean_inc(x_5);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_return___elambda__1___boxed), 8, 7);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, lean_box(0));
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_7);
lean_closure_set(x_13, 6, x_10);
x_14 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_15 = l_Vector_ofFn___rarg(x_14, x_12);
lean_dec(x_14);
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Vector_head___rarg(x_15);
lean_inc(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_20 = l_Vector_tail___rarg(x_15);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (x_19 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_alloc_closure((void*)(l_LinearProgram_result_score___default___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_22, 0, x_5);
x_23 = lean_alloc_closure((void*)(l_Pi_instNeg___elambda__1___rarg), 3, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_21);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_17);
lean_dec(x_5);
lean_inc(x_18);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_18);
lean_ctor_set(x_26, 4, x_21);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___elambda__1___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_cast___at_LinearProgram_Tableau_return___elambda__1___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___elambda__1___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_cast___at_LinearProgram_Tableau_return___elambda__1___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_return___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_LinearProgram_Tableau_return___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_return___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Function_update___at_LinearProgram_Tableau_return___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_return___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Function_update___at_LinearProgram_Tableau_return___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_return___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Pi_single___at_LinearProgram_Tableau_return___spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_return___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Pi_single___at_LinearProgram_Tableau_return___spec__1___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_cast___at_LinearProgram_Tableau_return___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_cast___at_LinearProgram_Tableau_return___spec__4(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___rarg___lambda__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Multiset_sum___at_LinearProgram_Tableau_return___spec__6(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_return___spec__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Finset_sum___at_LinearProgram_Tableau_return___spec__5(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_return___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_cast___at_LinearProgram_Tableau_return___spec__7(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_Tableau_return___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Multiset_sum___at_LinearProgram_Tableau_return___spec__9(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_Tableau_return___spec__8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Finset_sum___at_LinearProgram_Tableau_return___spec__8(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_return___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_LinearProgram_Tableau_return___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_return___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_LinearProgram_Tableau_return(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
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
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_mod(x_7, x_3);
x_9 = lean_nat_dec_eq(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_6, x_7);
if (x_10 == 0)
{
lean_dec(x_1);
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
x_14 = lean_apply_1(x_11, x_13);
return x_14;
}
}
else
{
lean_dec(x_1);
lean_inc(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___elambda__2___rarg___boxed), 6, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___elambda__3___rarg), 3, 0);
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
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_apply_1(x_15, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_alloc_closure((void*)(l_LinearProgram_result_score___default___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_17, 0, x_3);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_Pi_instNeg___elambda__1___rarg(x_17, x_18, x_5);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_4);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___lambda__1___boxed), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_nat_add(x_1, x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = lean_nat_add(x_1, x_8);
x_11 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_4);
x_12 = l_LinearOrderedSemifield_toSemifield___rarg(x_11);
lean_inc(x_12);
x_13 = l_Semifield_toCommGroupWithZero___rarg(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Semifield_toDivisionSemiring___rarg(x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___lambda__2___boxed), 2, 1);
lean_closure_set(x_19, 0, x_18);
lean_inc(x_10);
x_20 = lean_alloc_closure((void*)(l_Matrix_diagonal___at_LinearProgram_simplex__tableau___spec__1___rarg___boxed), 5, 3);
lean_closure_set(x_20, 0, x_4);
lean_closure_set(x_20, 1, x_10);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Vector_ofFn___rarg(x_10, x_20);
x_22 = lean_alloc_closure((void*)(l_Matrix_transpose___rarg), 3, 1);
lean_closure_set(x_22, 0, x_6);
x_23 = l_Vector_ofFn___rarg(x_2, x_22);
x_24 = l_List_appendTR___rarg(x_21, x_23);
x_25 = lean_alloc_closure((void*)(l_Equiv_vectorEquivFin___elambda__2___rarg___boxed), 2, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___elambda__3___rarg), 3, 1);
lean_closure_set(x_26, 0, x_25);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___elambda__2___rarg___boxed), 6, 4);
lean_closure_set(x_27, 0, x_5);
lean_closure_set(x_27, 1, x_1);
lean_closure_set(x_27, 2, x_10);
lean_closure_set(x_27, 3, x_15);
x_28 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___elambda__1___boxed), 4, 3);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_9);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
return x_29;
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
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_LinearProgram_simplex__tableau___elambda__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___elambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_LinearProgram_simplex__tableau___elambda__3(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_LinearProgram_simplex__tableau___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_simplex__tableau___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LinearProgram_simplex__tableau___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_initial__tableau___elambda__1___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_initial__tableau___elambda__1___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_cast___at_LinearProgram_initial__tableau___elambda__1___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_mod(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_mod(x_8, x_4);
x_10 = lean_nat_dec_eq(x_6, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_7, x_8);
if (x_11 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_6, x_12);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = l_LinearOrderedRing_toLinearOrder___rarg(x_14);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_apply_1(x_16, x_13);
lean_inc(x_17);
x_18 = l_instDecidableLtToLTToPreorderToPartialOrder___rarg(x_15, x_17, x_5);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_1);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_LinearOrderedField_toField___rarg(x_1);
x_21 = l_Field_toDivisionRing___rarg(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_apply_1(x_23, x_17);
return x_24;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_LinearProgram_initial__tableau___elambda__2___rarg___boxed), 7, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_LinearProgram_initial__tableau___elambda__3___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_initial__tableau___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_AddMonoid_toAddZeroClass___rarg(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_initial__tableau___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
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
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_initial__tableau___spec__2___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_List_foldrTR___rarg(x_8, x_9, x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_initial__tableau___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Multiset_sum___at_LinearProgram_initial__tableau___spec__2___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_initial__tableau___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Multiset_map___rarg(x_3, x_2);
x_5 = l_Multiset_sum___at_LinearProgram_initial__tableau___spec__2___rarg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_initial__tableau___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Finset_sum___at_LinearProgram_initial__tableau___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_initial__tableau___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_initial__tableau___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Matrix_diagonal___at_LinearProgram_initial__tableau___spec__3___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Field_toDivisionRing___rarg(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l_LinearOrderedRing_toLinearOrder___rarg(x_6);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_inc(x_5);
x_9 = lean_apply_1(x_8, x_5);
x_10 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_1);
lean_dec(x_1);
x_11 = l_LinearOrderedSemifield_toSemifield___rarg(x_10);
x_12 = l_Semifield_toCommGroupWithZero___rarg(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_instDecidableLtToLTToPreorderToPartialOrder___rarg(x_7, x_9, x_14);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_apply_2(x_17, x_5, x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_alloc_closure((void*)(l_LinearProgram_initial__tableau___lambda__1___boxed), 2, 1);
lean_closure_set(x_19, 0, x_4);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_apply_1(x_20, x_5);
x_22 = l_Pi_instNeg___elambda__1___rarg(x_19, x_21, x_3);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_1);
x_11 = lean_nat_sub(x_4, x_6);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = l_LinearOrderedRing_toLinearOrder___rarg(x_12);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_11);
x_15 = lean_apply_1(x_14, x_11);
x_16 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_2);
x_17 = l_LinearOrderedSemifield_toSemifield___rarg(x_16);
x_18 = l_Semifield_toCommGroupWithZero___rarg(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_instDecidableLtToLTToPreorderToPartialOrder___rarg(x_13, x_15, x_20);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_apply_2(x_23, x_11, x_5);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_alloc_closure((void*)(l_LinearProgram_result_score___default___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_25, 0, x_2);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_apply_1(x_26, x_11);
x_28 = l_Pi_instNeg___elambda__1___rarg(x_25, x_27, x_5);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_inc(x_2);
x_29 = l_LinearOrderedField_toField___rarg(x_2);
x_30 = l_List_finRange(x_1);
lean_inc(x_2);
x_31 = lean_alloc_closure((void*)(l_LinearProgram_initial__tableau___lambda__2), 5, 4);
lean_closure_set(x_31, 0, x_2);
lean_closure_set(x_31, 1, x_3);
lean_closure_set(x_31, 2, x_5);
lean_closure_set(x_31, 3, x_29);
x_32 = l_Finset_sum___at_LinearProgram_initial__tableau___spec__1___rarg(x_2, x_30, x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_LinearProgram_initial__tableau___lambda__3___boxed), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_nat_add(x_1, x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = lean_nat_add(x_1, x_8);
x_11 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_4);
x_12 = l_LinearOrderedSemifield_toSemifield___rarg(x_11);
lean_inc(x_12);
x_13 = l_Semifield_toCommGroupWithZero___rarg(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Semifield_toDivisionSemiring___rarg(x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_closure((void*)(l_LinearProgram_simplex__tableau___lambda__2___boxed), 2, 1);
lean_closure_set(x_19, 0, x_18);
lean_inc(x_10);
lean_inc(x_4);
x_20 = lean_alloc_closure((void*)(l_Matrix_diagonal___at_LinearProgram_initial__tableau___spec__3___rarg___boxed), 5, 3);
lean_closure_set(x_20, 0, x_4);
lean_closure_set(x_20, 1, x_10);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Vector_ofFn___rarg(x_10, x_20);
x_22 = lean_alloc_closure((void*)(l_Matrix_transpose___rarg), 3, 1);
lean_closure_set(x_22, 0, x_6);
x_23 = l_Vector_ofFn___rarg(x_2, x_22);
x_24 = l_List_appendTR___rarg(x_21, x_23);
x_25 = lean_alloc_closure((void*)(l_Equiv_vectorEquivFin___elambda__2___rarg___boxed), 2, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_LinearProgram_initial__tableau___elambda__3___rarg), 3, 1);
lean_closure_set(x_26, 0, x_25);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_LinearProgram_initial__tableau___elambda__2___rarg___boxed), 7, 5);
lean_closure_set(x_27, 0, x_4);
lean_closure_set(x_27, 1, x_5);
lean_closure_set(x_27, 2, x_1);
lean_closure_set(x_27, 3, x_10);
lean_closure_set(x_27, 4, x_15);
x_28 = lean_alloc_closure((void*)(l_LinearProgram_initial__tableau___elambda__1___boxed), 4, 3);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_9);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_initial__tableau___elambda__1___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_cast___at_LinearProgram_initial__tableau___elambda__1___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_initial__tableau___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_cast___at_LinearProgram_initial__tableau___elambda__1___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_LinearProgram_initial__tableau___elambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_LinearProgram_initial__tableau___elambda__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_LinearProgram_initial__tableau___elambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___elambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_LinearProgram_initial__tableau___elambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_LinearProgram_initial__tableau___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Multiset_sum___at_LinearProgram_initial__tableau___spec__2___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_LinearProgram_initial__tableau___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Finset_sum___at_LinearProgram_initial__tableau___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_initial__tableau___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Matrix_diagonal___at_LinearProgram_initial__tableau___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Matrix_diagonal___at_LinearProgram_initial__tableau___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Matrix_diagonal___at_LinearProgram_initial__tableau___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LinearProgram_initial__tableau___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_initial__tableau___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_LinearProgram_initial__tableau___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_Simplex__inner___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = l_List_reverse___rarg(x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_nat_add(x_1, x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_mod(x_16, x_15);
lean_dec(x_15);
x_18 = lean_nat_dec_lt(x_17, x_11);
lean_dec(x_17);
if (x_18 == 0)
{
lean_free_object(x_7);
lean_dec(x_11);
x_4 = lean_box(0);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
x_21 = l_LinearOrderedRing_toLinearOrder___rarg(x_20);
x_22 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_5);
x_23 = l_LinearOrderedSemifield_toSemifield___rarg(x_22);
x_24 = l_Semifield_toCommGroupWithZero___rarg(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
x_28 = lean_nat_add(x_3, x_14);
x_29 = lean_nat_mod(x_16, x_28);
lean_dec(x_28);
lean_inc(x_11);
x_30 = lean_apply_2(x_27, x_29, x_11);
x_31 = l_instDecidableLtToLTToPreorderToPartialOrder___rarg(x_21, x_26, x_30);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_free_object(x_7);
lean_dec(x_11);
x_4 = lean_box(0);
x_7 = x_12;
goto _start;
}
else
{
lean_ctor_set(x_7, 1, x_8);
{
lean_object* _tmp_3 = lean_box(0);
lean_object* _tmp_6 = x_12;
lean_object* _tmp_7 = x_7;
x_4 = _tmp_3;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_7, 0);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_7);
x_37 = lean_nat_add(x_1, x_2);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_37, x_38);
lean_dec(x_37);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_mod(x_40, x_39);
lean_dec(x_39);
x_42 = lean_nat_dec_lt(x_41, x_35);
lean_dec(x_41);
if (x_42 == 0)
{
lean_dec(x_35);
x_4 = lean_box(0);
x_7 = x_36;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_44 = lean_ctor_get(x_5, 0);
lean_inc(x_44);
x_45 = l_LinearOrderedRing_toLinearOrder___rarg(x_44);
x_46 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_5);
x_47 = l_LinearOrderedSemifield_toSemifield___rarg(x_46);
x_48 = l_Semifield_toCommGroupWithZero___rarg(x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_6, 0);
lean_inc(x_51);
x_52 = lean_nat_add(x_3, x_38);
x_53 = lean_nat_mod(x_40, x_52);
lean_dec(x_52);
lean_inc(x_35);
x_54 = lean_apply_2(x_51, x_53, x_35);
x_55 = l_instDecidableLtToLTToPreorderToPartialOrder___rarg(x_45, x_50, x_54);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_dec(x_35);
x_4 = lean_box(0);
x_7 = x_36;
goto _start;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_35);
lean_ctor_set(x_58, 1, x_8);
x_4 = lean_box(0);
x_7 = x_36;
x_8 = x_58;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__3___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_Simplex__inner___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__3___rarg(x_4, x_5, x_6, x_7, x_9);
x_3 = lean_box(0);
x_7 = x_11;
x_8 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_argmax___at_LinearProgram_Tableau_Simplex__inner___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = l_List_foldl___at_LinearProgram_Tableau_Simplex__inner___spec__4(x_1, x_2, lean_box(0), x_5, x_6, x_9, x_10, x_7);
lean_dec(x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_Simplex__inner___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = l_List_reverse___rarg(x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_mod(x_16, x_9);
x_18 = lean_nat_dec_lt(x_17, x_14);
lean_dec(x_17);
if (x_18 == 0)
{
lean_free_object(x_10);
lean_dec(x_14);
x_4 = lean_box(0);
x_10 = x_15;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_inc(x_7);
x_20 = l_LinearOrderedRing_toLinearOrder___rarg(x_7);
x_21 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_5);
x_22 = l_LinearOrderedSemifield_toSemifield___rarg(x_21);
x_23 = l_Semifield_toCommGroupWithZero___rarg(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
lean_inc(x_8);
lean_inc(x_14);
x_27 = lean_apply_2(x_26, x_14, x_8);
x_28 = l_instDecidableLtToLTToPreorderToPartialOrder___rarg(x_20, x_25, x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_free_object(x_10);
lean_dec(x_14);
x_4 = lean_box(0);
x_10 = x_15;
goto _start;
}
else
{
lean_ctor_set(x_10, 1, x_11);
{
lean_object* _tmp_3 = lean_box(0);
lean_object* _tmp_9 = x_15;
lean_object* _tmp_10 = x_10;
x_4 = _tmp_3;
x_10 = _tmp_9;
x_11 = _tmp_10;
}
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_mod(x_34, x_9);
x_36 = lean_nat_dec_lt(x_35, x_32);
lean_dec(x_35);
if (x_36 == 0)
{
lean_dec(x_32);
x_4 = lean_box(0);
x_10 = x_33;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_inc(x_7);
x_38 = l_LinearOrderedRing_toLinearOrder___rarg(x_7);
x_39 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_5);
x_40 = l_LinearOrderedSemifield_toSemifield___rarg(x_39);
x_41 = l_Semifield_toCommGroupWithZero___rarg(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_6, 0);
lean_inc(x_44);
lean_inc(x_8);
lean_inc(x_32);
x_45 = lean_apply_2(x_44, x_32, x_8);
x_46 = l_instDecidableLtToLTToPreorderToPartialOrder___rarg(x_38, x_43, x_45);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_dec(x_32);
x_4 = lean_box(0);
x_10 = x_33;
goto _start;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_32);
lean_ctor_set(x_49, 1, x_11);
x_4 = lean_box(0);
x_10 = x_33;
x_11 = x_49;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__7___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_Simplex__inner___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_10 = l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__7___rarg(x_3, x_4, x_5, x_6, x_8);
x_2 = lean_box(0);
x_6 = x_10;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_argmin___at_LinearProgram_Tableau_Simplex__inner___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = l_List_foldl___at_LinearProgram_Tableau_Simplex__inner___spec__8(x_1, lean_box(0), x_4, x_5, x_8, x_9, x_6);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__10___rarg___boxed), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_alloc_closure((void*)(l_Pi_single___at_LinearProgram_Tableau_return___spec__1___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_alloc_closure((void*)(l_Pi_instZero___elambda__1___rarg), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__10___rarg(x_10, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = lean_nat_mod(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__13___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Pi_single___at_LinearProgram_Tableau_return___spec__1___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_Pi_instZero___elambda__1___rarg), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__13___rarg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__12___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__14(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = lean_nat_mod(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__15(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = lean_nat_mod(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_8 = lean_apply_2(x_6, x_4, x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_apply_2(x_9, x_4, x_3);
x_11 = lean_apply_2(x_5, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_nat_dec_eq(x_9, x_1);
lean_dec(x_1);
x_12 = l_instDecidableNot___rarg(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
x_13 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_2);
x_14 = l_LinearOrderedSemifield_toSemifield___rarg(x_13);
x_15 = l_Semifield_toDivisionSemiring___rarg(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__9(x_3, x_4, lean_box(0), x_2, x_5, x_6, x_17, x_10);
lean_dec(x_17);
lean_dec(x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__11(x_8, x_9);
lean_dec(x_8);
x_21 = lean_apply_2(x_19, x_20, x_10);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; 
x_7 = lean_nat_dec_eq(x_5, x_1);
lean_dec(x_1);
x_8 = l_instDecidableNot___rarg(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_LinearOrderedField_toLinearOrderedSemifield___rarg(x_2);
x_10 = l_LinearOrderedSemifield_toSemifield___rarg(x_9);
x_11 = l_Semifield_toDivisionSemiring___rarg(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__12___rarg(x_2, x_14, x_13, x_6);
lean_dec(x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__14(x_4, x_5);
lean_dec(x_4);
x_18 = lean_apply_2(x_16, x_17, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; 
x_6 = lean_nat_dec_eq(x_5, x_1);
x_7 = l_instDecidableNot___rarg(x_6);
if (x_7 == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__15(x_4, x_5);
x_10 = lean_apply_1(x_8, x_9);
return x_10;
}
}
}
static lean_object* _init_l_LinearProgram_Tableau_Simplex__inner___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqFin___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_nat_add(x_1, x_2);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
x_11 = l_Nat_fin__list__range(x_10);
x_12 = lean_box(0);
lean_inc(x_7);
lean_inc(x_5);
x_13 = l_List_filterTR_loop___at_LinearProgram_Tableau_Simplex__inner___spec__1(x_1, x_2, x_3, lean_box(0), x_5, x_7, x_11, x_12);
x_14 = l_LinearProgram_Tableau_Simplex__inner___closed__1;
lean_inc(x_13);
x_15 = l_List_hasDecEq___rarg(x_14, x_13, x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_inc(x_3);
lean_inc(x_7);
x_17 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_Simplex__inner___lambda__1___boxed), 3, 2);
lean_closure_set(x_17, 0, x_7);
lean_closure_set(x_17, 1, x_3);
lean_inc(x_16);
lean_inc(x_5);
x_18 = l_List_argmax___at_LinearProgram_Tableau_Simplex__inner___spec__2(x_1, x_2, lean_box(0), x_5, x_16, x_17, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_nat_add(x_3, x_9);
x_21 = l_Nat_fin__list__range(x_20);
x_22 = l_List_tail___rarg(x_21);
lean_dec(x_21);
lean_inc(x_19);
lean_inc(x_16);
lean_inc(x_7);
x_23 = l_List_filterTR_loop___at_LinearProgram_Tableau_Simplex__inner___spec__5(x_1, x_2, x_3, lean_box(0), x_5, x_7, x_16, x_19, x_20, x_22, x_12);
lean_inc(x_23);
x_24 = l_List_hasDecEq___rarg(x_14, x_23, x_12);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_20);
lean_inc(x_19);
lean_inc(x_7);
lean_inc(x_5);
x_25 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_Simplex__inner___lambda__2), 4, 3);
lean_closure_set(x_25, 0, x_5);
lean_closure_set(x_25, 1, x_7);
lean_closure_set(x_25, 2, x_19);
lean_inc(x_5);
x_26 = l_List_argmin___at_LinearProgram_Tableau_Simplex__inner___spec__6(x_3, lean_box(0), x_5, x_16, x_25, x_23);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_5);
x_28 = l_LinearProgram_Tableau_pivoting(x_3, x_10, lean_box(0), x_5, x_7, x_27, x_19, lean_box(0));
lean_dec(x_10);
x_4 = lean_box(0);
x_7 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_23);
lean_dec(x_16);
lean_inc(x_3);
lean_inc(x_7);
lean_inc(x_19);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_20);
x_30 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_Simplex__inner___lambda__3___boxed), 10, 8);
lean_closure_set(x_30, 0, x_20);
lean_closure_set(x_30, 1, x_5);
lean_closure_set(x_30, 2, x_1);
lean_closure_set(x_30, 3, x_2);
lean_closure_set(x_30, 4, x_10);
lean_closure_set(x_30, 5, x_19);
lean_closure_set(x_30, 6, x_7);
lean_closure_set(x_30, 7, x_3);
lean_inc(x_3);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_20);
x_31 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_Simplex__inner___lambda__4___boxed), 6, 4);
lean_closure_set(x_31, 0, x_20);
lean_closure_set(x_31, 1, x_5);
lean_closure_set(x_31, 2, x_7);
lean_closure_set(x_31, 3, x_3);
lean_inc(x_19);
lean_inc(x_20);
x_32 = lean_alloc_closure((void*)(l_LinearProgram_Tableau_Simplex__inner___lambda__5___boxed), 5, 4);
lean_closure_set(x_32, 0, x_20);
lean_closure_set(x_32, 1, x_19);
lean_closure_set(x_32, 2, x_7);
lean_closure_set(x_32, 3, x_3);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
lean_inc(x_5);
lean_inc(x_20);
x_34 = l_LinearProgram_Tableau_pivoting(x_20, x_10, lean_box(0), x_5, x_33, x_20, x_19, lean_box(0));
lean_dec(x_10);
x_35 = l_LinearProgram_Tableau_return(x_20, x_1, x_2, lean_box(0), x_5, x_6, x_34);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_13);
lean_dec(x_10);
x_36 = l_LinearProgram_Tableau_return(x_3, x_1, x_2, lean_box(0), x_5, x_6, x_7);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_Simplex__inner___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_filterTR_loop___at_LinearProgram_Tableau_Simplex__inner___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_Simplex__inner___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldl___at_LinearProgram_Tableau_Simplex__inner___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_argmax___at_LinearProgram_Tableau_Simplex__inner___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_argmax___at_LinearProgram_Tableau_Simplex__inner___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_LinearProgram_Tableau_Simplex__inner___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_filterTR_loop___at_LinearProgram_Tableau_Simplex__inner___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__7___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_argAux___at_LinearProgram_Tableau_Simplex__inner___spec__7(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_LinearProgram_Tableau_Simplex__inner___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_foldl___at_LinearProgram_Tableau_Simplex__inner___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_argmin___at_LinearProgram_Tableau_Simplex__inner___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_argmin___at_LinearProgram_Tableau_Simplex__inner___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__10___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__10(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__11(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Function_update___at_LinearProgram_Tableau_Simplex__inner___spec__13___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Pi_single___at_LinearProgram_Tableau_Simplex__inner___spec__12___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__14___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__14(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__15___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_cast___at_LinearProgram_Tableau_Simplex__inner___spec__15(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_LinearProgram_Tableau_Simplex__inner___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_LinearProgram_Tableau_Simplex__inner___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_LinearProgram_Tableau_Simplex__inner___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_LinearProgram_Tableau_Simplex__inner___lambda__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex__inner___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_LinearProgram_Tableau_Simplex__inner(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LinearProgram_Tableau_Simplex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_LinearProgram_simplex__tableau(x_1, x_2, lean_box(0), x_4, x_5);
lean_inc(x_1);
x_7 = l_LinearProgram_Tableau_Simplex__inner(x_1, x_2, x_1, lean_box(0), x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
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
l_LinearProgram_minimize___default = _init_l_LinearProgram_minimize___default();
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__1 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__1();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__1);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__2 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__2();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__2);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__3 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__3();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__3);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__4 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__4();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__4);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__5 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__5();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__5);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__6 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__6();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__6);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__7 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__7();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__7);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__8 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__8();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__8);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__9 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__9();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__9);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__10 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__10();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__10);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__11 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__11();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__11);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__12 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__12();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__12);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__13 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__13();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__13);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__14 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__14();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__14);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__15 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__15();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__15);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__16 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__16();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__16);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__17 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__17();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__17);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__18 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__18();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__18);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__19 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__19();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__19);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__20 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__20();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__20);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__21 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__21();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__21);
l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__22 = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__22();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164____closed__22);
l___auto____x40_src_SimplexAlgorithm___hyg_164_ = _init_l___auto____x40_src_SimplexAlgorithm___hyg_164_();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_164_);
l___auto____x40_src_SimplexAlgorithm___hyg_187_ = _init_l___auto____x40_src_SimplexAlgorithm___hyg_187_();
lean_mark_persistent(l___auto____x40_src_SimplexAlgorithm___hyg_187_);
l_LinearProgram_Tableau_pivoting___closed__1 = _init_l_LinearProgram_Tableau_pivoting___closed__1();
lean_mark_persistent(l_LinearProgram_Tableau_pivoting___closed__1);
l_LinearProgram_Tableau_Simplex__inner___closed__1 = _init_l_LinearProgram_Tableau_Simplex__inner___closed__1();
lean_mark_persistent(l_LinearProgram_Tableau_Simplex__inner___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
