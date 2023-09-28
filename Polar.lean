import Pre
import Hyperplane
import Mathlib.Analysis.Convex.KreinMilman


variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] 

noncomputable def pointDualLin (p : {p : E // p ≠ 0}) : {f : (NormedSpace.Dual ℝ E) // norm f = 1} :=
  ⟨ (InnerProductSpace.toDual ℝ _ ((norm p.1)⁻¹ • p.1)), (by
  simp only [ne_eq, map_smulₛₗ, map_inv₀, IsROrC.conj_to_real]
  have : norm ((InnerProductSpace.toDual ℝ E) ↑p) = norm p.1 := by simp
  rw [← this]
  apply norm_smul_inv_norm
  rw [ne_eq, AddEquivClass.map_eq_zero_iff]
  exact p.2) ⟩

-- Given non-zero vector p, define the halfspace of vectors x such that inner p x ≤ 1
noncomputable def pointDual (p : {p : E // p ≠ 0}) : Halfspace E :=
  Halfspace.mk (pointDualLin p) (norm p.1)⁻¹

lemma pointDual.α (p : {p : E // p ≠ 0}) : (pointDual p).α = (norm p.1)⁻¹ := by rfl

lemma pointDual.h (p : {p : E // p ≠ 0}) : 
  (pointDual p) = (InnerProductSpace.toDual ℝ _ ((norm p.1)⁻¹ • p.1)) ⁻¹' {x | x ≤ (norm p.1)⁻¹} := by rfl

lemma pointDual_origin (p : {p : E // p ≠ 0}) : 
  (0 : E) ∈ (SetLike.coe <| pointDual p) := by
  rw [pointDual.h, map_smulₛₗ, map_inv₀, IsROrC.conj_to_real, Set.preimage_setOf_eq, 
    Set.mem_setOf_eq, map_zero, ← one_div]
  apply le_of_lt
  rw [div_pos_iff]
  left
  exact ⟨ zero_lt_one, by rw [norm_pos_iff]; exact p.2 ⟩
  done

lemma mem_pointDual (p : {p : E // p ≠ 0}) (x : E): 
  x ∈ (SetLike.coe <| pointDual p) ↔ inner p.1 x ≤ (1:ℝ) := by
  rw [pointDual.h, Set.mem_preimage, InnerProductSpace.toDual_apply, Set.mem_setOf, 
    inner_smul_left, IsROrC.conj_to_real, ← mul_le_mul_left (by rw [norm_pos_iff]; exact p.2 : 0 < norm p.1), 
    ← mul_assoc, mul_inv_cancel (norm_ne_zero_iff.mpr p.2), one_mul]
  done

lemma pointDual_comm (p q : {p : E // p ≠ 0}) : 
  p.1 ∈ (SetLike.coe <| pointDual q) ↔ q.1 ∈ (SetLike.coe <| pointDual p) := by
  rw [mem_pointDual, mem_pointDual, real_inner_comm]
  done


noncomputable def polarDual (X : Set E) : Set E := 
  ⋂₀ (SetLike.coe '' (pointDual '' (Subtype.val ⁻¹' X)))

lemma polarDual_closed (X : Set E) : IsClosed (polarDual X) := by
  apply isClosed_sInter
  intro Hi_s h
  rw [Set.mem_image] at h
  rcases h with ⟨ Hi_, _, rfl ⟩
  exact Halfspace_closed _

lemma polarDual_convex (X : Set E) : Convex ℝ (polarDual X) := by
  apply convex_sInter
  intro Hi_s h
  rw [Set.mem_image] at h
  rcases h with ⟨ Hi_, _, rfl ⟩
  exact Halfspace_convex _

lemma polarDual_origin (X : Set E) : 
  (0 : E) ∈ polarDual X := by
  intro Hi_s h
  rw [Set.mem_image] at h
  rcases h with ⟨ Hi_, h, rfl ⟩
  rw [Set.mem_image] at h
  rcases h with ⟨ p, _, rfl ⟩
  exact pointDual_origin p

lemma mem_polarDual {X : Set E} {v : E}:
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
    
    specialize h (SetLike.coe <| pointDual ⟨ x, hx0 ⟩) ?_
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

lemma mem_polarDual' {X : Set E} {v : E}:
  v ∈ polarDual X ↔ ∀ x ∈ X, inner v x ≤ (1:ℝ) := by
  rw [mem_polarDual]
  constructor <;>
  ·
    intro h x hx
    rw [real_inner_comm]
    exact h x hx
  done

lemma polarDual_comm_half (X Y : Set E) : 
  X ⊆ polarDual Y → Y ⊆ polarDual X := by
  rw [Set.subset_def, Set.subset_def]
  intro h y hy
  rw [mem_polarDual]
  intro x hx
  rw [real_inner_comm]
  specialize h x hx
  rw [mem_polarDual] at h
  specialize h y hy
  exact h
  done

lemma polarDual_comm (X Y : Set E) :
  X ⊆ polarDual Y ↔ Y ⊆ polarDual X := by
  constructor <;> exact fun h => polarDual_comm_half _ _ h
  done

lemma doublePolarDual_self {X : Set E} 
  (hXcl : IsClosed X) (hXcv : Convex ℝ X) (hX0 : 0 ∈ X) : polarDual (polarDual X) = X := by
  apply subset_antisymm
  · -- 1.
    intro x hx
    contrapose! hx
    rw [mem_polarDual]
    push_neg
    rcases geometric_hahn_banach_point_closed hXcv hXcl hx with ⟨ f, α, h, hX ⟩

    have hαneg := (neg_pos.mpr ((ContinuousLinearMap.map_zero f) ▸ (hX 0 hX0)))
    use (α⁻¹) • (InnerProductSpace.toDual ℝ E).symm f
    rw [mem_polarDual']
    constructor <;> intros <;> (try apply le_of_lt) <;> rw [real_inner_smul_left, 
      InnerProductSpace.toDual_symm_apply, ←neg_lt_neg_iff, ←neg_mul, mul_comm, neg_inv, ← division_def]
    · -- 1.
      rw [lt_div_iff hαneg, neg_one_mul, neg_neg]
      exact hX (by assumption) (by assumption)
    · -- 2.
      rw [div_lt_iff hαneg, neg_one_mul, neg_neg]
      exact h
  · -- 2.
    rw [polarDual_comm]
    done
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

lemma compact_polarDual_iff [FiniteDimensional ℝ E] {X : Set E} (hXcl : IsClosed X) :
  0 ∈ interior (polarDual X) ↔ IsCompact X := by
  cases' (em (X \ {0}).Nonempty) with hXnonempty hXempty
  · 
    constructor <;> rw [Metric.isCompact_iff_isClosed_bounded, bounded_iff_forall_norm_le]
    · -- 1.
      intro h
      have := @isOpen_interior _ _ (polarDual X)
      rw [Metric.isOpen_iff] at this
      rcases this 0 h with ⟨ ε, hε, hball ⟩; clear this h
      refine ⟨ hXcl, 2/ε, fun x hx => ?_ ⟩

      cases' em (x = 0) with hx0 hx0
      · 
        rw [hx0, norm_zero]
        exact div_nonneg zero_le_two (le_of_lt hε)
        done
      let u : E := (ε/2/(norm x)) • x
      have hnormu : ‖u‖ = ε/2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (half_pos hε) (norm_pos_iff.mpr hx0)), 
        div_mul_cancel _ (norm_ne_zero_iff.mpr hx0)]
        done
      have hu : u ∈ Metric.ball (0:E) ε := by
        rw [Metric.mem_ball, dist_zero_right, hnormu]
        exact half_lt_self hε

      have h := interior_subset <| hball hu
      rw [mem_polarDual] at h
      specialize h x hx
      rw [real_inner_smul_right, real_inner_self_eq_norm_mul_norm, ←mul_assoc, 
        div_mul_cancel _ (norm_ne_zero_iff.mpr hx0), mul_comm, ← div_le_div_right (div_pos hε zero_lt_two), 
        mul_div_cancel _ (Ne.symm <| ne_of_lt (div_pos hε zero_lt_two)), one_div_div] at h
      exact h
    · -- 2.
      rw [interior_eq_compl_closure_compl, Set.mem_compl_iff, Metric.mem_closure_iff, dist_zero_left] 
      push_neg 
      intro h
      rcases h with ⟨ _, M, hM ⟩
      use 1/M
      refine ⟨ ?_, ?_ ⟩  
      · 
        rw [gt_iff_lt, one_div]
        exact inv_pos.mpr <| lt_of_lt_of_le (norm_pos_iff.mpr hXnonempty.some_mem.2) (hM hXnonempty.some hXnonempty.some_mem.1)
      · 
        intro b hb
        rw [Set.mem_compl_iff, mem_polarDual] at hb
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
        apply le_trans (div_le_div (le_of_lt <| lt_trans zero_lt_one hb) (le_of_lt hb) hynezero hM)
        apply div_le_of_nonneg_of_le_mul (le_of_lt hynezero) 
        apply (zero_le_mul_left hynezero).mp (le_trans (zero_le_one) this)
        rw [mul_comm]
        exact hnorminner
        done
  · 
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty, Set.subset_singleton_iff_eq] at hXempty
    cases' hXempty with hXempty hX0
    · 
      rw [hXempty, polarDual_empty, interior_univ]
      exact ⟨ fun _ => isCompact_empty, fun _ => trivial ⟩
    · 
      rw [hX0, polarDual_zero, interior_univ]
      exact ⟨ fun _ => isCompact_singleton, fun _ => trivial ⟩
    done

lemma polarDual_compact_if [FiniteDimensional ℝ E] {X : Set E} (hXcl : IsClosed X) (hXcv : Convex ℝ X) :
  0 ∈ interior X → IsCompact (polarDual X) := by
  intro h
  rw [← doublePolarDual_self hXcl hXcv (interior_subset h), compact_polarDual_iff (polarDual_closed _)] at h
  exact h
  done


def orthoHyperplane (x : {x : E // x ≠ 0}) : Set (Halfspace E) := 
  { Halfspace.mk (pointDualLin x) 0, Halfspace.mk (pointDualLin ⟨ -x.1, by rw [neg_ne_zero]; exact x.2 ⟩) 0 }

lemma orthoHyperplane.Finite (x : {x : E // x ≠ 0}) : (orthoHyperplane x).Finite := by
  unfold orthoHyperplane
  simp only [Set.mem_singleton_iff, Halfspace.mk.injEq, and_true, Set.finite_singleton, Set.Finite.insert]

lemma orthoHyperplane_mem (x : {x : E // x ≠ 0}) : ∀ (y : E), y ∈ cutSpace (orthoHyperplane x) ↔ inner x.1 y = (0:ℝ) := by
  intro y
  rw [mem_cutSpace]
  constructor
  · -- 1.
    intro h
    have h1 := h (Halfspace.mk (pointDualLin x) 0)
    simp only [pointDualLin, ne_eq, map_inv₀, IsROrC.conj_to_real, orthoHyperplane, Set.mem_singleton_iff,
      Halfspace.mk.injEq, and_true, Set.mem_insert_iff, true_or, forall_true_left, InnerProductSpace.toDual_apply, 
      inner_smul_left] at h1  
    
    have h2 := h (Halfspace.mk (pointDualLin ⟨ -x.1, by rw [neg_ne_zero]; exact x.2 ⟩) 0)
    simp only [pointDualLin, ne_eq, norm_neg, smul_neg, map_inv₀, IsROrC.conj_to_real, orthoHyperplane, 
      Set.mem_singleton_iff, Halfspace.mk.injEq, Subtype.mk.injEq, and_true, Set.mem_insert_iff,
      or_true, forall_true_left, InnerProductSpace.toDual_apply, inner_neg_left, inner_smul_left] at h2 
    rw [neg_le, neg_zero] at h2
    have := le_antisymm h1 h2
    rw [mul_eq_zero] at this
    cases' this with h3 h4
    · 
      rw [inv_eq_zero, norm_eq_zero] at h3
      exfalso
      exact x.2 h3
    ·
      exact h4 
  · -- 2.
    intro h H hH
    unfold orthoHyperplane at hH
    simp only [ne_eq, Set.mem_singleton_iff, Halfspace.mk.injEq, and_true, Set.mem_insert_iff] at hH 
    cases' hH with H H <;>
    simp only [H, pointDualLin, norm_neg, smul_neg, map_inv₀, IsROrC.conj_to_real, InnerProductSpace.toDual_apply, 
        inner_neg_left, inner_smul_left, neg_le, neg_zero, h, mul_zero, le_refl]
  done

lemma cutSpace_sUnion_orthoHyperplane (X : Set {x : E // x ≠ 0}) : ∀ (y : E), y ∈ cutSpace (⋃₀ (orthoHyperplane '' X)) ↔ ∀ (i : ↑(orthoHyperplane '' X)), y ∈ cutSpace ↑i := by
  intro y
  unfold cutSpace
  rw [Set.sUnion_eq_iUnion, Set.image_iUnion, Set.sInter_iUnion, Set.mem_iInter]

lemma orthoHyperplanes_mem (X : Set {x : E // x ≠ 0}) : ∀ (y : E), y ∈ cutSpace (⋃₀ (orthoHyperplane '' X)) ↔ ∀ x ∈ X, inner x.1 y = (0:ℝ) := by
  intro y
  rw [cutSpace_sUnion_orthoHyperplane]
  constructor
  · -- 1.
    intro h
    intro x hx
    simp at h
    specialize h (orthoHyperplane x) x.1 x.2 hx rfl
    exact (orthoHyperplane_mem x y).mp h
  · -- 2.
    intro h
    simp
    rintro a x1 x2 hx rfl
    rw [orthoHyperplane_mem]
    exact h _ hx
  done

