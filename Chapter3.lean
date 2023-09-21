import «Chapter2»
import Mathlib.LinearAlgebra.StdBasis


variable {d : ℕ+}

-- noncomputable def stdbasisℝd : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
--   Pi.basisFun ℝ (Fin d)

-- Given non-zero vector p, define the halfspace of vectors x such that inner p x ≤ 1
noncomputable def pointDual (p : {p : EuclideanSpace ℝ (Fin d) // p ≠ 0}) : Halfspace d :=
  Halfspace.mk1 ⟨ (InnerProductSpace.toDual ℝ _ ((norm p.1)⁻¹ • p.1)), (by
  simp only [ne_eq, map_smulₛₗ, map_inv₀, IsROrC.conj_to_real]
  have : norm ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin ↑d))) ↑p) = norm p.1 := by simp
  rw [← this]
  apply norm_smul_inv_norm
  rw [ne_eq, AddEquivClass.map_eq_zero_iff]
  exact p.2) ⟩ (norm p.1)⁻¹

lemma pointDual.α (p : {p : EuclideanSpace ℝ (Fin d) // p ≠ 0}) : (pointDual p).α = (norm p.1)⁻¹ := by rfl

lemma pointDual.h (p : {p : EuclideanSpace ℝ (Fin d) // p ≠ 0}) : 
  (pointDual p).S = (InnerProductSpace.toDual ℝ _ ((norm p.1)⁻¹ • p.1)) ⁻¹' {x | x ≤ (norm p.1)⁻¹} := by rfl

lemma pointDual_origin (p : {p : EuclideanSpace ℝ (Fin d) // p ≠ 0}) : 
  (0 : EuclideanSpace ℝ (Fin d)) ∈ (pointDual p).S := by
  rw [pointDual.h, map_smulₛₗ, map_inv₀, IsROrC.conj_to_real, Set.preimage_setOf_eq, 
    Set.mem_setOf_eq, map_zero, ← one_div]
  apply le_of_lt
  rw [div_pos_iff]
  left
  exact ⟨ zero_lt_one, by rw [norm_pos_iff]; exact p.2 ⟩
  done

lemma mem_pointDual (p : {p : EuclideanSpace ℝ (Fin d) // p ≠ 0}) : 
  ∀ x, x ∈ (pointDual p).S ↔ inner p.1 x ≤ (1:ℝ) := by
  intro x
  rw [pointDual.h, Set.mem_preimage, InnerProductSpace.toDual_apply, Set.mem_setOf, 
    inner_smul_left, IsROrC.conj_to_real, ← mul_le_mul_left (by rw [norm_pos_iff]; exact p.2 : 0 < norm p.1), 
    ← mul_assoc, mul_inv_cancel (norm_ne_zero_iff.mpr p.2), one_mul]
  done

noncomputable def polarDual (X : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) := 
  ⋂₀ ((·.S) '' (pointDual '' (Subtype.val ⁻¹' X)))

lemma polarDual_closed (X : Set (EuclideanSpace ℝ (Fin d))) : IsClosed (polarDual X) := by
  apply isClosed_sInter
  intro Hi_s h
  rw [Set.mem_image] at h
  rcases h with ⟨ Hi_, _, rfl ⟩
  exact Halfspace_closed _

lemma polarDual_convex (X : Set (EuclideanSpace ℝ (Fin d))) : Convex ℝ (polarDual X) := by
  apply convex_sInter
  intro Hi_s h
  rw [Set.mem_image] at h
  rcases h with ⟨ Hi_, _, rfl ⟩
  exact Halfspace_convex _

lemma polarDual_origin (X : Set (EuclideanSpace ℝ (Fin d))) : 
  (0 : EuclideanSpace ℝ (Fin d)) ∈ polarDual X := by
  intro Hi_s h
  rw [Set.mem_image] at h
  rcases h with ⟨ Hi_, h, rfl ⟩
  rw [Set.mem_image] at h
  rcases h with ⟨ p, _, rfl ⟩
  exact pointDual_origin p

lemma mem_polarDual {X : Set (EuclideanSpace ℝ (Fin d))} {v : EuclideanSpace ℝ (Fin d)}:
  v ∈ polarDual X ↔ ∀ x ∈ X, inner x v ≤ (1:ℝ) := by
  unfold polarDual
  rw [Set.mem_sInter]

  constructor
  · -- 1.
    intro h x hx
    cases' (em (x = 0)) with hx0 hx0
    · 
      rw [hx0, inner_zero_left]
      exact zero_le_one
    
    specialize h (pointDual ⟨ x, hx0 ⟩).S ?_
    · 
      apply Set.mem_image_of_mem
      apply Set.mem_image_of_mem
      rw [Set.mem_preimage]
      exact hx

    rw [mem_pointDual] at h
    exact h
    done
  · -- 2.
    intro h Hi_s hHi_s
    rw [Set.mem_image] at hHi_s
    rcases hHi_s with ⟨ Hi_, hHi_, rfl ⟩
    rw [Set.mem_image] at hHi_
    rcases hHi_ with ⟨ p, hp, rfl ⟩
    specialize h p.1 hp
    rw [mem_pointDual]
    exact h
    done
  done


-- lemma doublePolarDual_self {X : Set (EuclideanSpace ℝ (Fin d))} (hXcpt : IsCompact X)
--   (hXcl : IsClosed X) (hXcv : Convex ℝ X) (hX0 : 0 ∈ X) : polarDual (polarDual X) = X := by

--   done

-- Equivalence of ℝ^d and its dual
-- InnerProductSpace.toDual
