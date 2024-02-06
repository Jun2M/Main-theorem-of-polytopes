import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.InnerProductSpace.Dual
import «src».Pre


open Pointwise


-- Type for halfspaces of E
-- For completeness, it is define with a linear map with norm 1 and a real number bound
structure PolarFunctional (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  f : {f : (NormedSpace.Dual ℝ E) // norm f = 1}
  α : ℝ

variable {E P : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [AddTorsor E P]

noncomputable instance NegUnitSphereDual : Neg {f : (NormedSpace.Dual ℝ E) // norm f = 1} :=
  ⟨λ f => ⟨-f.1, by simp [f.2]⟩⟩

lemma unitSphereDual_neg : ∀ f : {f : (NormedSpace.Dual ℝ E) // norm f = 1}, (-f).1 = -f.1 := fun f => by
  change (⟨-f.1, _ ⟩: {f : (NormedSpace.Dual ℝ E) // norm f = 1}).1 = -f.1
  simp
  done

lemma unitSphereDual_surj : ∀ f : {f : (NormedSpace.Dual ℝ E) // norm f = 1},
  Function.Surjective f.val := by
  intro f
  apply LinearMap.surjective_of_ne_zero
  intro h
  rw [← ContinuousLinearMap.coe_zero, ContinuousLinearMap.coe_inj] at h
  have := h ▸ f.2
  simp only [norm_zero, zero_ne_one] at this
  done

namespace PolarFunctional

def hyperplane (H : PolarFunctional E) : Set E := H.f.1 ⁻¹' {H.α}

lemma hyperplane_mem_iff (H : PolarFunctional E) :
  ∀ x, x ∈ H.hyperplane ↔ H.f.1 x = H.α := by
  intro x
  rw [hyperplane, Set.mem_preimage, Set.mem_singleton_iff]
  done

lemma hyperplane_convex (H : PolarFunctional E) :
  Convex ℝ H.hyperplane := by
  exact @convex_hyperplane ℝ E ℝ _ _ _ _ _ _ H.f.1 (LinearMap.isLinear H.f.1) H.α
  done

lemma hyperplane_affineClosed (H : PolarFunctional E) :
  ∀ s : Fin n → E, Set.range s ⊆ H.hyperplane
    → ∀ a : Fin n → ℝ, Finset.univ.sum a = 1 →
    Finset.affineCombination ℝ Finset.univ s a ∈ H.hyperplane := by
  intro s hs a ha
  simp_rw [Set.range_subset_iff, hyperplane_mem_iff] at hs
  rw [Finset.affineCombination_eq_linear_combination _ _ _ ha, hyperplane_mem_iff, map_sum]
  simp_rw [map_smul, hs, smul_eq_mul, ← Finset.sum_mul, ha, one_mul]
  done




def le_halfspace (H : PolarFunctional E) : Set E := H.f.1 ⁻¹' {x | x ≤ H.α}


theorem le_halfspace_inj [CompleteSpace E] : Function.Injective (@le_halfspace E _ _) := by
    intro H1 H2 (h : H1.le_halfspace = H2.le_halfspace)
    cases' H1 with f1 α1
    cases' H2 with f2 α2
    simp only [le_halfspace] at h

    let p1 := (InnerProductSpace.toDual ℝ E).symm f1.1
    have hp1norm : norm p1 = 1 := (LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ _).symm f1.1) ▸ f1.2
    have hf1 : f1.1 = (InnerProductSpace.toDual ℝ E) p1 := by simp
    have hf1p1 : f1.1 p1 = 1 := by rw [hf1, InnerProductSpace.toDual_apply, real_inner_self_eq_norm_sq, hp1norm, sq, one_mul]

    have hfeq : f1 = f2 := by
      rw [Subtype.ext_iff]
      refine LinearIsometryEquiv.injective (InnerProductSpace.toDual ℝ E).symm ?_
      contrapose! h

      let p2 := (InnerProductSpace.toDual ℝ E).symm f2.1
      have hp2norm : norm p2 = 1 := (LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ _).symm f2.1) ▸ f2.2
      have hf2 : f2.1 = (InnerProductSpace.toDual ℝ E) p2 := by simp only [ContinuousLinearMap.strongUniformity_topology_eq,
        LinearIsometryEquiv.apply_symm_apply]

      change p1 ≠ p2 at h
      have hinnerlt1 : ⟪p1, p2⟫_ℝ < 1 := (inner_lt_one_iff_real_of_norm_one hp1norm hp2norm).mpr h
      let v := p1 - p2
      let v' := (norm v)⁻¹ • v

      have hDiffNormPos : 0 < ‖p1 - p2‖⁻¹ := inv_pos.mpr <| norm_pos_iff.mpr <| sub_ne_zero_of_ne h

      have hv'1 : 0 < f1.1 v' := by
        rw [hf1, InnerProductSpace.toDual_apply, real_inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq,
          hp1norm, sq, one_mul, mul_pos_iff]
        left
        exact ⟨ hDiffNormPos, by linarith ⟩

      have hv'2 : f2.1 v' < 0 := by
        rw [hf2, InnerProductSpace.toDual_apply, real_inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq,
          hp2norm, sq, one_mul, mul_neg_iff]
        left
        exact ⟨ hDiffNormPos, sub_neg.mpr ((real_inner_comm p1 p2) ▸ hinnerlt1) ⟩

      have hv'1out : ∃ M1 : ℝ, ∀ m > M1, (m • v') ∉ f1.1 ⁻¹' {x | x ≤ α1} := by
        use α1 / f1.1 v'
        intro m hm hmem
        rw [Set.mem_preimage, Set.mem_setOf, ContinuousLinearMap.map_smul, smul_eq_mul, ← le_div_iff hv'1] at hmem
        exact not_lt_of_le hmem hm

      have hv'2in : ∃ M2 : ℝ, ∀ m > M2, (m • v') ∈ f2.1 ⁻¹' {x | x ≤ α2} := by
        use α2 / f2.1 v'
        intro m hm
        rw [Set.mem_preimage, Set.mem_setOf, ContinuousLinearMap.map_smul, smul_eq_mul]
        have : m * f2.1 v' ≤ α2 / f2.1 v' * f2.1 v' := by
          rw [← neg_le_neg_iff, ← mul_neg, ← mul_neg, mul_le_mul_right (neg_pos_of_neg hv'2)]
          exact le_of_lt hm

        apply le_trans this
        rw [div_mul_cancel _ (ne_of_lt hv'2)]
        done

      rcases hv'1out with ⟨ M1, hM1 ⟩
      rcases hv'2in with ⟨ M2, hM2 ⟩

      have : M1 < 1 + max M1 M2 := by
        have := le_max_left M1 M2
        linarith
        done

      have : M2 < 1 + max M1 M2 := by
        have := le_max_right M1 M2
        linarith
        done

      rw [← Set.symmDiff_nonempty, Set.nonempty_def]
      use (1 + max M1 M2) • v'
      rw [Set.mem_symmDiff]
      right
      exact ⟨ hM2 (1 + max M1 M2) (by assumption), hM1 (1 + max M1 M2) (by assumption) ⟩

    congr
    contrapose! h
    rw [← Set.symmDiff_nonempty, Set.nonempty_def]
    use (max α1 α2) • p1
    rw [Set.mem_symmDiff]
    rcases (max_choice α1 α2) with hmax1 | hmax2
    ·
      left
      rw [hmax1, Set.mem_preimage, Set.mem_setOf, ContinuousLinearMap.map_smul, smul_eq_mul,
        Set.mem_preimage, Set.mem_setOf, ContinuousLinearMap.map_smul, smul_eq_mul, ← hfeq, hf1p1, mul_one]
      rw [max_eq_left_iff] at hmax1
      exact ⟨ le_refl _, not_le_of_gt <| lt_of_le_of_ne hmax1 h.symm ⟩
    ·
      right
      rw [hmax2, Set.mem_preimage, Set.mem_setOf, ContinuousLinearMap.map_smul, smul_eq_mul,
        Set.mem_preimage, Set.mem_setOf, ContinuousLinearMap.map_smul, smul_eq_mul, ← hfeq, hf1p1, mul_one]
      rw [max_eq_right_iff] at hmax2
      exact ⟨ le_refl _, not_le_of_gt <| lt_of_le_of_ne hmax2 h ⟩
    done

lemma le_halfspace_eq_iff [CompleteSpace E] (H1 H2 : PolarFunctional E) :
  H1.le_halfspace = H2.le_halfspace ↔ H1 = H2 := by
  exact ⟨ λ h => le_halfspace_inj h, λ h => h ▸ rfl ⟩

lemma le_halfspace_def (H : PolarFunctional E) : H.le_halfspace = H.f.1 ⁻¹' {x |  x ≤ H.α} := rfl

lemma le_halfspace_mem_iff (H : PolarFunctional E) : ∀ x, x ∈ H.le_halfspace  ↔ H.f.1 x ≤ H.α := by
  intro x
  rw [H.le_halfspace_def]
  rfl

lemma le_halfspace_convex (H : PolarFunctional E) : Convex ℝ (H.le_halfspace) := by
  rw [H.le_halfspace_def]
  exact convex_halfspace_le (LinearMap.isLinear H.f.1.1) H.α

lemma le_halfspace_closed (H : PolarFunctional E) : IsClosed (H.le_halfspace) := by
  rw [H.le_halfspace_def]
  exact IsClosed.preimage (H.f.1.cont) isClosed_Iic

lemma le_halfspace_span_top (H : PolarFunctional E) : affineSpan ℝ (H.le_halfspace) = ⊤ := by
  -- affine span of a ball(simplex, in general) is entire
  apply affineSpan_eq_top_of_nonempty_interior
  apply Set.Nonempty.mono (?_ : H.f.1 ⁻¹' (Metric.ball (H.α -1) (1/2)) ⊆ (interior ((convexHull ℝ) H.le_halfspace)))
  · -- preimage of ball is not empty as f is surjective
    cases' unitSphereDual_surj H.f (H.α -1) with x hx
    use x
    rw [Set.mem_preimage, Metric.mem_ball, dist_sub_eq_dist_add_right, hx, sub_add_cancel, dist_self]
    linarith
    done
  -- this open set is subset of the halfspace
  rw [IsOpen.subset_interior_iff (IsOpen.preimage (?_) Metric.isOpen_ball)]
  apply subset_trans ?_ (subset_convexHull ℝ (H.le_halfspace))
  intro x hx
  rw [Set.mem_preimage, Real.ball_eq_Ioo, Set.mem_Ioo] at hx
  rw [le_halfspace_mem_iff H]
  linarith
  exact H.f.1.cont
  done

noncomputable def translation (H : PolarFunctional E) (x : E) : PolarFunctional E :=
  PolarFunctional.mk H.f (H.α + H.f.1 x)

lemma translation_le_halfspace (H : PolarFunctional E) (x : E):
  (H.translation x).le_halfspace = (· + x) '' (H.le_halfspace) := by
  ext y
  rw [translation, le_halfspace_mem_iff, Set.image_add_right, Set.mem_preimage, ← sub_eq_add_neg,
    le_halfspace_mem_iff, ContinuousLinearMap.map_sub, sub_le_iff_le_add]
  done

lemma translation_le_halfspace_mem_iff (H : PolarFunctional E) (x : E) :
  ∀ y, y ∈ (H.translation x).le_halfspace ↔ y - x ∈ H.le_halfspace := by
  intro y
  rw [translation_le_halfspace, Set.image_add_right, Set.mem_preimage, sub_eq_add_neg]
  done

lemma translation_inj [CompleteSpace E] (x : E) :
  Function.Injective (·.translation x : PolarFunctional E → PolarFunctional E ) := by
  intro H1 H2 h
  rw [← le_halfspace_eq_iff] at h ⊢
  rwa [translation_le_halfspace, translation_le_halfspace,
    Set.image_eq_image] at h
  intro x y hxy
  rwa [add_left_inj] at hxy
  done


lemma frontier_le_Halfspace_eq_Hyperplane [CompleteSpace E] {H : PolarFunctional E} :
  frontier (H.le_halfspace) = H.hyperplane := by
  rw [H.le_halfspace_def, ContinuousLinearMap.frontier_preimage _ (unitSphereDual_surj H.f),
    ← Set.Iic, frontier_Iic' (Set.nonempty_Ioi)]
  rfl
  done

noncomputable def extend {p : Subspace ℝ E} [CompleteSpace p] (H' : PolarFunctional p) :
  PolarFunctional E := by
  choose f hf using Real.exists_extension_norm_eq p H'.f.1
  exact ⟨ ⟨ f, hf.2 ▸ H'.f.2 ⟩, H'.α ⟩

lemma extend_f1 {p : Subspace ℝ E} [CompleteSpace p] (H' : PolarFunctional p) :
  ∀ (x : { x // x ∈ p }), (extend H').f.1 x = H'.f.1 x  := by
  have := Classical.choose_spec (Real.exists_extension_norm_eq p H'.f.1)
  exact this.1

lemma extend_f2 {p : Subspace ℝ E} [CompleteSpace p] (H' : PolarFunctional p) :
  ‖(extend H').f.1‖ = ‖H'.f.1‖ := by
  have := Classical.choose_spec (Real.exists_extension_norm_eq p H'.f.1)
  exact this.2

lemma extend_α {p : Subspace ℝ E} [CompleteSpace p] (H' : PolarFunctional p) :
  (extend H').α = H'.α := by rfl

lemma extend_le_halfspace_inter_subspace_eq_le_halfspace {p : Subspace ℝ E} [CompleteSpace p]
  (H' : PolarFunctional p) :
  (extend H').le_halfspace ∩ p = (Subtype.val '' H'.le_halfspace)  := by
  apply subset_antisymm <;> intro x <;> rw [Set.mem_inter_iff, Set.mem_image, le_halfspace_mem_iff]
  ·
    rintro ⟨ hxH', hxp ⟩
    refine ⟨ ⟨ x, hxp ⟩, ?_, rfl ⟩
    rw [le_halfspace_mem_iff, ← (extend_f1 H' ⟨ x, hxp ⟩)]
    exact hxH'
  ·
    rintro ⟨ ⟨ x', hx'p ⟩, hx'H', rfl ⟩
    refine ⟨ ?_, hx'p ⟩
    rw [le_halfspace_mem_iff, ← (extend_f1 H' ⟨ x', hx'p ⟩)] at hx'H'
    exact hx'H'
  done

end PolarFunctional
