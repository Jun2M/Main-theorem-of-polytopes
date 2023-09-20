import «Chapter2»
import Mathlib.LinearAlgebra.StdBasis


variable {d : ℕ+}

noncomputable def stdbasisℝd : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  Pi.basisFun ℝ (Fin d)

noncomputable def pointDual (p : {p : EuclideanSpace ℝ (Fin d) // p ≠ 0}) : Halfspace d :=
  Halfspace.mk' ⟨ (InnerProductSpace.toDual ℝ _ p), (fun h => p.2 <| (LinearIsometryEquiv.map_eq_zero_iff _).mp h) ⟩ 1

noncomputable def polarDual (X : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) := 
  ⋂₀ (Halfspace.S '' (pointDual '' (Subtype.val ⁻¹' X)))

-- Equivalence of ℝ^d and its dual
-- InnerProductSpace.toDual
