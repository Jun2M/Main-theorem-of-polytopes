import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.KreinMilman
-- import Pre


variable {d : ℕ+}


theorem Set.Finite.isOpen_sInter {s : Set (Set α)} (hs : s.Finite) [TopologicalSpace α] :
  (∀ t ∈ s, IsOpen t) → IsOpen (⋂₀ s) :=
  Finite.induction_on hs (fun _ => by rw [sInter_empty]; exact isOpen_univ) fun _ _ ih h => by
    simp only [sInter_insert, ball_insert_iff] at h ⊢
    exact h.1.inter (ih h.2)

lemma interior_eq_compl_closure_compl [TopologicalSpace α] {s : Set α} : interior s = (closure sᶜ)ᶜ := by
  rw [← compl_compl s, compl_compl sᶜ, interior_compl]
  done

-- Type for linear dual of EuclideanSpace ℝ (Fin d) with norm 1
def unitSphereDual (d : ℕ+) : Type := {f : (NormedSpace.Dual ℝ (EuclideanSpace ℝ (Fin d))) // norm f = 1}

lemma EquivUnitSphere : {p : EuclideanSpace ℝ (Fin d) // norm p = 1} ≃ₜ 
  {f : (NormedSpace.Dual ℝ (EuclideanSpace ℝ (Fin d))) // norm f = 1} where
  toFun := λ p => ⟨(InnerProductSpace.toDual _ _ p), ((LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ _) p.1) ▸ p.2)⟩
  invFun := λ f => ⟨ (InnerProductSpace.toDual _ _).invFun f.1, (by simp; exact f.2)⟩
  left_inv := λ p => by simp
  right_inv := λ f => by simp

lemma unitSphereDual_surj : ∀ f : {f : (NormedSpace.Dual ℝ (EuclideanSpace ℝ (Fin d))) // norm f = 1},
  Function.Surjective f.val := by
  intro f 
  apply LinearMap.surjective_of_ne_zero
  intro h
  rw [← ContinuousLinearMap.coe_zero] at h
  norm_cast at h
  let a := (h ▸ f.2)
  simp only [norm_zero, zero_ne_one] at a 
  done
  
lemma unitSphereDual_cont : ∀ f : unitSphereDual d, Continuous f.val := fun f => f.1.cont

-- Type for halfspaces of EuclideanSpace ℝ (Fin d)
-- For completeness, it is define with a linear map with norm 1 and a real number bound
structure Halfspace (d : ℕ+) where
  f : {f : (NormedSpace.Dual ℝ (EuclideanSpace ℝ (Fin d))) // norm f = 1}
  α : ℝ

def Halfspace.S (H_ : Halfspace d) : Set (EuclideanSpace ℝ (Fin d)) := H_.f.1 ⁻¹' {x | x ≤ H_.α}

instance Halfspace.SetLike (d : ℕ+) : SetLike (Halfspace d) (EuclideanSpace ℝ (Fin d)) where
  coe := Halfspace.S
  coe_injective' := by
    intro H1 H2 h
    cases' H1 with f1 α1
    cases' H2 with f2 α2
    simp only [Halfspace.S] at h

    let p1 := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin ↑d))).symm f1.1
    have hp1norm : norm p1 = 1 := (LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ _).symm f1.1) ▸ f1.2
    have hf1 : f1.1 = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin ↑d))) p1 := by simp
    have hf1p1 : f1.1 p1 = 1 := by rw [hf1, InnerProductSpace.toDual_apply, real_inner_self_eq_norm_sq, hp1norm, sq, one_mul]

    have hfeq : f1 = f2 := by
      ext
      apply LinearIsometryEquiv.injective (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin ↑d))).symm
      contrapose! h

      let p2 := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin ↑d))).symm f2.1
      have hp2norm : norm p2 = 1 := (LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ _).symm f2.1) ▸ f2.2
      have hf2 : f2.1 = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin ↑d))) p2 := by simp

      change p1 ≠ p2 at h
      have hinnerlt1:= (inner_lt_one_iff_real_of_norm_one hp1norm hp2norm).mpr h
      let v := p1 - p2
      let v' := (norm v)⁻¹ • v
      have hvnonzero : v ≠ 0 := sub_ne_zero_of_ne h
      
      have hv'1 : 0 < f1.1 v' := by
        rw [hf1, InnerProductSpace.toDual_apply, real_inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq, 
          hp1norm, sq, one_mul, mul_pos_iff]
        left
        exact ⟨ inv_pos.mpr <| norm_pos_iff.mpr hvnonzero, by linarith ⟩ 
      have hv'2 : f2.1 v' < 0 := by
        rw [hf2, InnerProductSpace.toDual_apply, real_inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq, 
          hp2norm, sq, one_mul, mul_neg_iff]
        left
        exact ⟨ inv_pos.mpr <| norm_pos_iff.mpr hvnonzero, sub_neg.mpr ((real_inner_comm p1 p2) ▸ hinnerlt1) ⟩
      
      have hv'1out : ∃ M1 : ℝ, ∀ m > M1, (m • v') ∉ f1 ⁻¹' {x | x ≤ α1} := by
        use α1 / f1.1 v'
        intro m hm hmem
        rw [Set.mem_preimage, Set.mem_setOf, ContinuousLinearMap.map_smul, smul_eq_mul, ← le_div_iff hv'1] at hmem
        exact not_lt_of_le hmem hm
      have hv'2in : ∃ M2 : ℝ, ∀ m > M2, (m • v') ∈ f2 ⁻¹' {x | x ≤ α2} := by
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

def Halfspace.h (H_ : Halfspace d) : ↑H_ = H_.f.1 ⁻¹' {x |  x ≤ H_.α} := rfl

lemma Halfspace_mem (H_ : Halfspace d) : ∀ x, x ∈ (SetLike.coe H_) ↔ H_.f.1 x ≤ H_.α := by
  intro x
  rw [H_.h]
  rfl

lemma Halfspace_convex (H_ : Halfspace d) : Convex ℝ (SetLike.coe H_) := by
  rw [H_.h]
  exact convex_halfspace_le (LinearMap.isLinear H_.f.1.1) H_.α

lemma Halfspace_closed (H_ : Halfspace d) : IsClosed (SetLike.coe H_) := by
  rw [H_.h]
  exact IsClosed.preimage (H_.f.1.cont) isClosed_Iic

lemma Halfspace_span (H_ : Halfspace d) : affineSpan ℝ (SetLike.coe H_) = ⊤ := by
  -- affine span of a ball(simplex, in general) is entire
  apply affineSpan_eq_top_of_nonempty_interior
  apply Set.Nonempty.mono (?_ : H_.f.1 ⁻¹' (Metric.ball (H_.α -1) (1/2)) ⊆ (interior ((convexHull ℝ) H_.S)))
  · -- preimage of ball is not empty as f is surjective
    cases' unitSphereDual_surj H_.f (H_.α -1) with x hx
    use x
    rw [Set.mem_preimage, Metric.mem_ball, dist_sub_eq_dist_add_right, hx, sub_add_cancel, dist_self]
    linarith
    done
  -- this open set is subset of the halfspace
  rw [IsOpen.subset_interior_iff (IsOpen.preimage (unitSphereDual_cont H_.f) Metric.isOpen_ball)]
  apply subset_trans ?_ (subset_convexHull ℝ (SetLike.coe H_))
  intro x hx
  rw [Set.mem_preimage, Real.ball_eq_Ioo, Set.mem_Ioo] at hx
  rw [Halfspace_mem H_]
  linarith
  done

noncomputable def Halfspace_translation (x : EuclideanSpace ℝ (Fin d)) (H_ : Halfspace d) : Halfspace d := 
  Halfspace.mk H_.f (H_.α + (H_.f.1 x))

lemma Halfspace_translation.h (H_ : Halfspace d) (x : EuclideanSpace ℝ (Fin d)) : 
  (Halfspace_translation x H_) = (fun v => v + x) '' H_ := by
  unfold Halfspace_translation
  rw [Halfspace.h, Halfspace.h]
  simp only [Set.preimage_setOf_eq, Set.image_add_right, map_add, map_neg, add_neg_le_iff_le_add]
  done  

lemma Halfspace_translation.injective (x : EuclideanSpace ℝ (Fin d)) : 
  Function.Injective (Halfspace_translation x) := by
  intro H1 H2 h
  rw [SetLike.ext_iff]
  intro y
  rw [SetLike.ext_iff] at h
  specialize h (y + x)
  
  rw [← SetLike.mem_coe, ← SetLike.mem_coe] at h
  rw [Halfspace_translation.h, Halfspace_translation.h, Set.mem_image, Set.mem_image] at h
  constructor <;> intro H
  · -- 1.
    rcases (h.mp (by exact ⟨ y, H, rfl ⟩ : ∃ x_1, x_1 ∈ H1 ∧ x_1 + x = y + x)) with ⟨ x_1, hx_1, hx_1x ⟩
    simp at hx_1x
    exact hx_1x ▸ hx_1
  · -- 2.
    rcases (h.mpr (by exact ⟨ y, H, rfl ⟩ : ∃ x_1, x_1 ∈ H2 ∧ x_1 + x = y + x)) with ⟨ x_1, hx_1, hx_1x ⟩
    simp at hx_1x
    exact hx_1x ▸ hx_1
  done

lemma frontierHalfspace_Hyperplane {Hi_ : Halfspace d} : 
  frontier Hi_ = {x : EuclideanSpace ℝ (Fin d) | Hi_.f.1 x = Hi_.α } := by
  have := ContinuousLinearMap.frontier_preimage Hi_.f.1 (unitSphereDual_surj Hi_.f) (Set.Iic Hi_.α)
  simp only [ne_eq, LinearMap.coe_toContinuousLinearMap', Set.nonempty_Ioi, frontier_Iic'] at this 
  change frontier ( Hi_.f.1 ⁻¹' {x | x ≤ Hi_.α}) = Hi_.f.1 ⁻¹' {Hi_.α} at this
  rw [Hi_.h, this] ; clear this
  unfold Set.preimage
  simp only [ne_eq, Set.mem_singleton_iff]
  done

lemma Hyperplane_convex (Hi_ : Halfspace d) : 
  Convex ℝ {x : EuclideanSpace ℝ (Fin d) | Hi_.f.1 x = Hi_.α } := by
  exact @convex_hyperplane ℝ (EuclideanSpace ℝ (Fin d)) ℝ _ _ _ _ _ _ Hi_.f.1 (LinearMap.isLinear Hi_.f.1) Hi_.α
  done

lemma Hyperplane_affineClosed (Hi_ : Halfspace d) :
  ∀ s : Fin n → (EuclideanSpace ℝ (Fin d)), Set.range s ⊆ {x : EuclideanSpace ℝ (Fin d) | Hi_.f.1 x = Hi_.α }
    → ∀ a : Fin n → ℝ, Finset.univ.sum a = 1 →  
    Finset.affineCombination ℝ Finset.univ s a ∈ {x : EuclideanSpace ℝ (Fin d) | Hi_.f.1 x = Hi_.α } := by
  intro s hs a ha
  rw [Finset.affineCombination_eq_linear_combination _ _ _ ha, Set.mem_setOf, ContinuousLinearMap.map_sum]
  have hg : (fun i => Hi_.f.1 (a i • s i)) = fun i => a i * Hi_.α := by
    ext i
    rw [Set.range_subset_iff] at hs
    specialize hs i
    rw [Set.mem_setOf] at hs
    rw [ContinuousLinearMap.map_smulₛₗ, smul_eq_mul, RingHom.id_apply, hs]
    done
  rw [hg, ←Finset.sum_mul, ha, one_mul]
  done

-- theorem2_21 = geometric_hahn_banach_open_point?

def IsFace (F X : Set (EuclideanSpace ℝ (Fin d))) : Prop := 
  Convex ℝ F ∧ IsClosed F ∧ IsExtreme ℝ X F

def IsProperFace (F X : Set (EuclideanSpace ℝ (Fin d))) : Prop := 
  F ≠ X ∧ F.Nonempty ∧ IsFace F X

lemma lemma2_27 {F X : Set (EuclideanSpace ℝ (Fin d))} (hXcl : IsClosed X) (hXCV : Convex ℝ X)
  (hF : IsProperFace F X) : F ⊆ intrinsicFrontier ℝ X := by
  rcases hF with ⟨hFX, hF0, hFCV, hFCl, hFs, hFEx⟩ ; clear hFCl hXCV hF0 hFCV
  intro y hyF
  have hyX : y ∈ X := Set.mem_of_subset_of_mem hFs hyF
  have hFss := (ssubset_of_subset_of_ne hFs hFX) ; clear hFs hFX
  rcases (Set.nonempty_diff.mpr (HasSSubset.SSubset.not_subset hFss)) with ⟨x, hxX, hxF⟩ ;clear hFss

  let y'n : ℕ → EuclideanSpace ℝ (Fin d) := λ n => AffineMap.lineMap x y (1 + 1/(n+1):ℝ)
  let Sn : ℕ → Set (EuclideanSpace ℝ (Fin d)) := λ n => segment ℝ x (y'n n)
  
  have h1 : ∀ n, 0 < 1 / ((@Nat.cast ℝ _ n) + 1:ℝ) := 
    fun n:ℕ => (div_pos zero_lt_one (Nat.cast_add_one_pos n))

  have hxy : x ≠ y := λ h => hxF (h ▸ hyF)

  have hySn : ∀ n, y ∈ Sn n := by
    intro n
    change y ∈ segment ℝ x (AffineMap.lineMap x y (1 + 1/(n+1):ℝ))
    rw [segment_eq_image_lineMap]
    use 1/(1 + 1/(n+1):ℝ)
    rw [Set.mem_Icc]
    constructor
    · -- 1. tedious inequalities
      suffices h2 : 0 < 1 / (1 + 1 / (↑n + 1:ℝ)) ∧ 1 / (1 + 1 / (↑n + 1:ℝ)) ≤ 1 from ⟨ le_of_lt h2.1, h2.2 ⟩
      rw [← one_le_inv_iff, one_div, inv_inv, le_add_iff_nonneg_right, one_div, inv_nonneg]
      exact le_of_lt (Nat.cast_add_one_pos n)
    · -- 2.
      rw [AffineMap.coe_lineMap, AffineMap.coe_lineMap]
      simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel, ne_eq]
      rw [one_div, smul_smul, inv_mul_cancel, one_smul, sub_add_cancel]
      exact (ne_of_lt (add_pos_of_nonneg_of_pos (by linarith) (h1 n))).symm

  have hy'naff : ∀ n, y'n n ∈ affineSpan ℝ X := by
    intro n
    apply AffineMap.lineMap_mem <;> apply subset_affineSpan <;> assumption

  let y''n : ℕ → affineSpan ℝ X := λ n => ⟨y'n n, hy'naff n⟩

  rw [← closure_diff_intrinsicInterior, Set.mem_diff _, IsClosed.closure_eq hXcl, mem_intrinsicInterior] ; clear hXcl
  refine ⟨ hyX, ?_ ⟩
  rintro ⟨ y1, hy1, hy1y ⟩
  revert hy1
  rw [imp_false, ←Set.mem_compl_iff, ←closure_compl]

  -- Finally using seq y'n to show y is a limit point of Xᶜ 
  rw [mem_closure_iff_seq_limit]
  use y''n
  constructor
  · -- 1. if y'n is in X then (as y is in a face) y'n & x are in F, contradiction
    intro n hn
    refine hxF (hFEx hxX hn hyF ?_ ).1 ; clear hFEx hxX 
    apply mem_openSegment_of_ne_left_right hxy
    · -- y = y'n?
      intro hyy'n
      change (AffineMap.lineMap x y) (1 + 1 / (↑n + 1:ℝ)) = y at hyy'n
      rw [AffineMap.lineMap_apply x y (1 + 1 / (↑n + 1:ℝ))] at hyy'n
      have hyy'n1 : (1 + 1 / (↑n + 1:ℝ)) • (y -ᵥ x) +ᵥ x -ᵥ x = y -ᵥ x := by rw [hyy'n]
      rw [vadd_vsub_assoc, vsub_self, add_zero] at hyy'n1 ; clear hyy'n
      have hyy'n2 : (1 + 1 / (↑n + 1:ℝ)) • (y -ᵥ x) - (1:ℝ) • (y -ᵥ x) = 0 := 
        by rw [hyy'n1, one_smul, sub_self]
      rw [← sub_smul (1 + 1 / (↑n + 1:ℝ)) 1 (y -ᵥ x), add_comm, add_sub_assoc, sub_self, 
        add_zero, smul_eq_zero] at hyy'n2 ; clear hyy'n1
      cases' hyy'n2 with h h
      · 
        exact (ne_of_lt (h1 n)).symm (by assumption)
      ·
        rw [vsub_eq_zero_iff_eq] at h
        exact hxF (h ▸ hyF)
    exact hySn n
  clear hyF hxF hySn Sn hFEx hxX
    
  · -- 2. good ol' epsilon delta argument
    rw [Metric.tendsto_atTop]
    intro ε hε
    use max 1 ⌈dist x y / ε⌉₊
    intro n hn
    rw [ge_iff_le, max_le_iff] at hn

    -- boring inequality manipulations
    have hεn : dist x y / n ≤ ε := by
      clear y''n hy'naff y'n hyX hy1y y1 h1 F X
      rw [Nat.ceil_le, div_le_iff hε, ← div_le_iff' ] at hn
      exact hn.2
      norm_cast
      linarith
      done
    apply lt_of_lt_of_le ?_ hεn

    rw [Subtype.dist_eq, hy1y, dist_lineMap_right, sub_add_cancel', div_eq_inv_mul, mul_one, norm_neg, 
      norm_inv, Real.norm_eq_abs, div_eq_inv_mul, mul_lt_mul_right (dist_pos.mpr hxy), inv_lt_inv]
    <;> norm_cast
    simp only [lt_add_iff_pos_right]
    simp only [add_pos_iff, or_true]
    linarith
    done
  done 

  lemma extremepointIsFace {X : Set (EuclideanSpace ℝ (Fin d))}
    (x : EuclideanSpace ℝ (Fin d)) (hxEx : x ∈ Set.extremePoints ℝ X) : IsFace {x} X :=
    ⟨ convex_singleton _, isClosed_singleton, mem_extremePoints_iff_extreme_singleton.mp hxEx ⟩

-- Theorem 2.34 = closure_convexHull_extremePoints