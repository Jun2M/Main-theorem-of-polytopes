import «src».Hyperplane
import Mathlib.Analysis.Convex.KreinMilman


variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open PolarFunctional

noncomputable def pointDualLin (p : {p : E // p ≠ 0}) : {f : (NormedSpace.Dual ℝ E) // norm f = 1} :=
  ⟨ (InnerProductSpace.toDual ℝ _ ((norm p.1)⁻¹ • p.1)), (by
  simp only [ne_eq, map_smulₛₗ, map_inv₀, IsROrC.conj_to_real]
  have : norm ((InnerProductSpace.toDual ℝ E) ↑p) = norm p.1 := by simp
  rw [← this]
  apply norm_smul_inv_norm
  rw [ne_eq, AddEquivClass.map_eq_zero_iff]
  exact p.2) ⟩

-- Given non-zero vector p, define the halfspace s.t. ∀ x, inner p x ≤ 1
noncomputable def pointDual (p : {p : E // p ≠ 0}) : PolarFunctional E :=
  PolarFunctional.mk (pointDualLin p) (norm p.1)⁻¹

lemma pointDual_f (p : {p : E // p ≠ 0}) :
  (pointDual p).f = (InnerProductSpace.toDual ℝ _ ((norm p.1)⁻¹ • p.1)) := by rfl

lemma pointDual_α (p : {p : E // p ≠ 0}) : (pointDual p).α = (norm p.1)⁻¹ := by rfl

lemma pointDual_le_halfspace_def (p : {p : E // p ≠ 0}) :
  (pointDual p).le_halfspace = (InnerProductSpace.toDual ℝ _ ((norm p.1)⁻¹ • p.1)) ⁻¹' {x | x ≤ (norm p.1)⁻¹} := by rfl

lemma pointDual_origin_mem (p : {p : E // p ≠ 0}) :
  (0 : E) ∈ (pointDual p).le_halfspace := by
  rw [pointDual_le_halfspace_def, map_smulₛₗ, map_inv₀, IsROrC.conj_to_real, Set.preimage_setOf_eq,
    Set.mem_setOf_eq, map_zero, ← one_div, div_nonneg_iff]
  left
  exact ⟨ zero_le_one, norm_nonneg _ ⟩
  done

lemma pointDual_mem_iff (p : {p : E // p ≠ 0}) (x : E):
  x ∈ (pointDual p).le_halfspace ↔ inner p.1 x ≤ (1:ℝ) := by
  rw [pointDual_le_halfspace_def, Set.mem_preimage, InnerProductSpace.toDual_apply, Set.mem_setOf,
    inner_smul_left, IsROrC.conj_to_real,
    ← mul_le_mul_left (by rw [norm_pos_iff]; exact p.2 : 0 < norm p.1),
    ← mul_assoc, mul_inv_cancel (norm_ne_zero_iff.mpr p.2), one_mul]
  done

lemma pointDual_comm (p q : {p : E // p ≠ 0}) :
  p.1 ∈ (pointDual q).le_halfspace ↔ q.1 ∈ (pointDual p).le_halfspace := by
  rw [pointDual_mem_iff, pointDual_mem_iff, real_inner_comm]
  done


noncomputable def polarDual (X : Set E) : Set E :=
  ⋂₀ (le_halfspace '' (pointDual '' (Subtype.val ⁻¹' X)))

lemma polarDual_closed (X : Set E) : IsClosed (polarDual X) := by
  apply isClosed_sInter
  intro Hi_s h
  rw [Set.mem_image] at h
  rcases h with ⟨ Hi_, _, rfl ⟩
  exact le_halfspace_closed _

lemma polarDual_convex (X : Set E) : Convex ℝ (polarDual X) := by
  apply convex_sInter
  intro Hi_s h
  rw [Set.mem_image] at h
  rcases h with ⟨ Hi_, _, rfl ⟩
  exact le_halfspace_convex _

lemma polarDual_origin_mem (X : Set E) :
  (0 : E) ∈ polarDual X := by
  intro Hi_s h
  rw [Set.mem_image] at h
  rcases h with ⟨ Hi_, h, rfl ⟩
  rw [Set.mem_image] at h
  rcases h with ⟨ p, _, rfl ⟩
  exact pointDual_origin_mem p

lemma polarDual_mem_iff {X : Set E} {v : E}:
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

    specialize h (le_halfspace <| pointDual ⟨ x, hx0 ⟩) ?_
    ·
      apply Set.mem_image_of_mem
      apply Set.mem_image_of_mem
      rw [Set.mem_preimage]
      exact hx

    rw [pointDual_mem_iff] at h
    exact h
    done
  · -- 2.
    intro h Hi_s hHi_s
    rw [Set.mem_image] at hHi_s
    rcases hHi_s with ⟨ Hi_, hHi_, rfl ⟩
    rw [Set.mem_image] at hHi_
    rcases hHi_ with ⟨ p, hp, rfl ⟩
    specialize h p.1 hp
    rw [pointDual_mem_iff]
    exact h
    done
  done

lemma polarDual_mem_iff' {X : Set E} {v : E}:
  v ∈ polarDual X ↔ ∀ x ∈ X, inner v x ≤ (1:ℝ) := by
  simp_rw [polarDual_mem_iff, real_inner_comm]
  done

lemma polarDual_comm_half (X Y : Set E) :
  X ⊆ polarDual Y → Y ⊆ polarDual X := by
  rw [Set.subset_def, Set.subset_def]
  intro h y hy
  rw [polarDual_mem_iff]
  intro x hx
  rw [real_inner_comm]
  specialize h x hx
  rw [polarDual_mem_iff] at h
  exact h y hy
  done

lemma polarDual_comm (X Y : Set E) :
  X ⊆ polarDual Y ↔ Y ⊆ polarDual X := by
  constructor <;>
  exact fun h => polarDual_comm_half _ _ h
  done

lemma doublePolarDual_self {X : Set E}
  (hXcl : IsClosed X) (hXcv : Convex ℝ X) (hX0 : 0 ∈ X) : polarDual (polarDual X) = X := by
  refine subset_antisymm ?_ (by rw [polarDual_comm])
  intro x hx
  simp only [polarDual_mem_iff] at hx
  contrapose! hx
  rcases geometric_hahn_banach_point_closed hXcv hXcl hx with ⟨ f, α, h, hX ⟩
  use (α⁻¹) • (InnerProductSpace.toDual ℝ E).symm f

  have hEqfxDivα : ∀ x, ⟪α⁻¹ • (LinearIsometryEquiv.symm (InnerProductSpace.toDual ℝ E)) f, x⟫_ℝ = f x / α := by
    intro x
    rw [real_inner_smul_left, InnerProductSpace.toDual_symm_apply]
    ring
    done

  have hαneg : α < 0 := (ContinuousLinearMap.map_zero f) ▸ (hX 0 hX0)

  constructor <;> intros <;> (try apply le_of_lt)
  · -- 1. ∀ z ∈ X, ⟪z, α⁻¹ • (LinearIsometryEquiv.symm (InnerProductSpace.toDual ℝ E)) f⟫_ℝ ≤ 1
    rw [real_inner_comm, hEqfxDivα, div_lt_iff_of_neg hαneg, one_mul]
    exact hX _ (by assumption)
  · -- 2. 1 < ⟪α⁻¹ • (LinearIsometryEquiv.symm (InnerProductSpace.toDual ℝ E)) f, x⟫_ℝ
    rw [hEqfxDivα, lt_div_iff_of_neg hαneg, one_mul]
    exact h
  done


lemma polarDual_empty : polarDual (∅ : Set E) = Set.univ := by
  rw [polarDual, Set.preimage_empty, Set.image_empty, Set.image_empty, Set.sInter_empty]
  done

lemma polarDual_zero : polarDual ({0} : Set E) = Set.univ := by
  rw [polarDual]
  have : (@Subtype.val E fun p => p ≠ 0) ⁻¹' {0} = ∅ := by
    rw [Set.preimage_singleton_eq_empty]
    simp only [ne_eq, Subtype.range_coe_subtype, Set.mem_setOf_eq, not_true, not_false_eq_true]
    done
  rw [this, Set.image_empty, Set.image_empty, Set.sInter_empty]
  done

lemma zero_mem_interior_polarDual_iff_compact [FiniteDimensional ℝ E] {X : Set E}
  (hXcl : IsClosed X) : 0 ∈ interior (polarDual X) ↔ IsCompact X := by
  suffices (X \ {0}).Nonempty → (0 ∈ interior (polarDual X) ↔ IsCompact X) by
    cases' (em (X \ {0}).Nonempty) with hXnonempty hXempty
    ·
      exact this hXnonempty
    ·
      rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty,
        Set.subset_singleton_iff_eq] at hXempty
      cases' hXempty with hXempty hX0
      ·
        rw [hXempty, polarDual_empty, interior_univ]
        exact ⟨ fun _ => isCompact_empty, fun _ => trivial ⟩
      ·
        rw [hX0, polarDual_zero, interior_univ]
        exact ⟨ fun _ => isCompact_singleton, fun _ => trivial ⟩
      done

  intro hXnonempty
  rw [Metric.isCompact_iff_isClosed_bounded, isBounded_iff_forall_norm_le]
  constructor
  · -- 1.
    intro h
    have : IsOpen (interior (polarDual X)) := isOpen_interior
    rw [Metric.isOpen_iff] at this
    rcases this 0 h with ⟨ ε, hε, hball ⟩; clear this h
    refine ⟨ hXcl, 2/ε, fun x hx => ?_ ⟩

    cases' em (x = 0) with hx0 hx0
    ·
      rw [hx0, norm_zero]
      exact div_nonneg zero_le_two (le_of_lt hε)
      done

    have := subset_trans hball (interior_subset) ; clear hball
    rw [polarDual_comm] at this
    specialize this hx
    simp only [polarDual_mem_iff, Metric.mem_ball, dist_zero_right] at this
    let u : E := (ε/2/(norm x)) • x

    have hu : ‖u‖ < ε := by
      rw [norm_smul, norm_div, Real.norm_eq_abs, norm_norm,
        div_mul_cancel _ (norm_ne_zero_iff.mpr hx0), abs_of_pos (half_pos hε)]
      exact half_lt_self hε

    specialize this u hu
    rwa [real_inner_smul_left, real_inner_self_eq_norm_mul_norm, ←mul_assoc,
    div_mul_cancel _ (norm_ne_zero_iff.mpr hx0), ← le_div_iff' (div_pos hε zero_lt_two),
      one_div_div] at this

  · -- 2.
    rw [interior_eq_compl_closure_compl, Set.mem_compl_iff, Metric.mem_closure_iff,
      dist_zero_left]
    push_neg
    intro h
    rcases h with ⟨ _, M, hM ⟩
    use 1/M
    refine ⟨ ?_, ?_ ⟩
    ·
      rw [gt_iff_lt, one_div, inv_pos]
      refine lt_of_lt_of_le (norm_pos_iff.mpr hXnonempty.some_mem.2) ?_
      exact hM hXnonempty.some hXnonempty.some_mem.1
    ·
      intro b hb
      rw [Set.mem_compl_iff, polarDual_mem_iff] at hb
      push_neg at hb
      rcases hb with ⟨ y, hy, hb ⟩
      specialize hM y hy
      have hnorminner: |inner y b| ≤ ‖y‖ * ‖b‖ := by
        exact abs_real_inner_le_norm y b
      rw [abs_of_pos (lt_trans zero_lt_one hb)] at hnorminner
      have : (1:ℝ) ≤ ‖y‖ * ‖b‖ := le_trans (le_of_lt hb) hnorminner
      have hynezero: y ≠ 0 := by
        rintro rfl
        rw [norm_zero, zero_mul] at this
        exact not_lt_of_le this zero_lt_one
      rw [← norm_pos_iff] at hynezero
      apply le_trans (div_le_div ((le_of_lt <| lt_trans zero_lt_one hb)) (le_of_lt hb) hynezero hM)
      apply div_le_of_nonneg_of_le_mul (le_of_lt hynezero)
      apply (mul_nonneg_iff_of_pos_left hynezero).mp (le_trans (zero_le_one) this)
      rw [mul_comm]
      exact hnorminner
      done
