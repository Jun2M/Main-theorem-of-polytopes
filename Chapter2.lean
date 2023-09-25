import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.KreinMilman
-- import Pre


open Pointwise


lemma Set.translation.Finite {α : Type} [Add α] {S : Set α} (hS : S.Finite) (x : α) : 
  (S + ({x} : Set α)).Finite := by 
  rw [Set.add_singleton]
  exact Set.Finite.image _ hS

lemma Set.mem_translation {α : Type} [AddGroup α] (S : Set α) (s : α) (x : α) : 
  s ∈ S + {x} ↔ s + -x ∈ S := by
  rw [Set.add_singleton, Set.image_add_right, Set.mem_preimage]
  done

lemma Set.neg_add_cancel_right' {α : Type} [AddGroup α] (S : Set α) (x : α) : 
  S + {-x} + {x} = S := by
  ext y
  simp only [add_singleton, image_add_right, neg_neg, mem_preimage, neg_add_cancel_right]
  done

theorem Set.Finite.isOpen_sInter {s : Set (Set α)} (hs : s.Finite) [TopologicalSpace α] :
  (∀ t ∈ s, IsOpen t) → IsOpen (⋂₀ s) :=
  Finite.induction_on hs (fun _ => by rw [sInter_empty]; exact isOpen_univ) fun _ _ ih h => by
    simp only [sInter_insert, ball_insert_iff] at h ⊢
    exact h.1.inter (ih h.2)

lemma interior_eq_compl_closure_compl [TopologicalSpace α] {s : Set α} : interior s = (closure sᶜ)ᶜ := by
  rw [← compl_compl s, compl_compl sᶜ, interior_compl]
  done

-- Type for halfspaces of E
-- For completeness, it is define with a linear map with norm 1 and a real number bound
structure Halfspace (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  f : {f : (NormedSpace.Dual ℝ E) // norm f = 1}
  α : ℝ

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] 

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

def Halfspace.S (H_ : Halfspace E) : Set E := H_.f.1 ⁻¹' {x | x ≤ H_.α}

variable [CompleteSpace E]

instance Halfspace.SetLike : SetLike (Halfspace E) E where
  coe := Halfspace.S
  coe_injective' := by
    intro H1 H2 h
    cases' H1 with f1 α1
    cases' H2 with f2 α2
    simp only [Halfspace.S] at h

    let p1 := (InnerProductSpace.toDual ℝ E).symm f1.1
    have hp1norm : norm p1 = 1 := (LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ _).symm f1.1) ▸ f1.2
    have hf1 : f1.1 = (InnerProductSpace.toDual ℝ E) p1 := by simp
    have hf1p1 : f1.1 p1 = 1 := by rw [hf1, InnerProductSpace.toDual_apply, real_inner_self_eq_norm_sq, hp1norm, sq, one_mul]

    have hfeq : f1 = f2 := by
      ext
      apply LinearIsometryEquiv.injective (InnerProductSpace.toDual ℝ E).symm
      contrapose! h

      let p2 := (InnerProductSpace.toDual ℝ E).symm f2.1
      have hp2norm : norm p2 = 1 := (LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ _).symm f2.1) ▸ f2.2
      have hf2 : f2.1 = (InnerProductSpace.toDual ℝ E) p2 := by simp

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

def Halfspace.h (H_ : Halfspace E) : ↑H_ = H_.f.1 ⁻¹' {x |  x ≤ H_.α} := rfl

lemma Halfspace_mem (H_ : Halfspace E) : ∀ x, x ∈ (SetLike.coe H_) ↔ H_.f.1 x ≤ H_.α := by
  intro x
  rw [H_.h]
  rfl

lemma Halfspace_convex (H_ : Halfspace E) : Convex ℝ (SetLike.coe H_) := by
  rw [H_.h]
  exact convex_halfspace_le (LinearMap.isLinear H_.f.1.1) H_.α

lemma Halfspace_closed (H_ : Halfspace E) : IsClosed (SetLike.coe H_) := by
  rw [H_.h]
  exact IsClosed.preimage (H_.f.1.cont) isClosed_Iic

lemma Halfspace_span (H_ : Halfspace E) : affineSpan ℝ (SetLike.coe H_) = ⊤ := by
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
  rw [IsOpen.subset_interior_iff (IsOpen.preimage (?_) Metric.isOpen_ball)]
  apply subset_trans ?_ (subset_convexHull ℝ (SetLike.coe H_))
  intro x hx
  rw [Set.mem_preimage, Real.ball_eq_Ioo, Set.mem_Ioo] at hx
  rw [Halfspace_mem H_]
  linarith
  exact H_.f.1.cont
  done

noncomputable def Halfspace_translation (x : E) (H_ : Halfspace E) : Halfspace E := 
  Halfspace.mk H_.f (H_.α + (H_.f.1 x))

lemma Halfspace_translation.S (x : E) (H_ : Halfspace E) : 
  ↑(Halfspace_translation x H_) = (· + x) '' ↑H_ := by
  ext y
  rw [Halfspace_translation, Halfspace_mem, Set.image_add_right, Set.mem_preimage, ← sub_eq_add_neg, 
    Halfspace_mem, ContinuousLinearMap.map_sub, sub_le_iff_le_add]
  done

lemma mem_Halfspace_translation (x : E) (H_ : Halfspace E) : 
  ∀ y, y ∈ (SetLike.coe <| Halfspace_translation x H_) ↔ y - x ∈ SetLike.coe H_ := by
  intro y
  rw [Halfspace_translation.S, Set.image_add_right, Set.mem_preimage, sub_eq_add_neg]
  done 

lemma Halfspace_translation.injective (x : E) : 
  Function.Injective (Halfspace_translation x · : Halfspace E → Halfspace E ) := by
  intro H1 H2 h
  rw [SetLike.ext_iff]
  intro y
  rw [SetLike.ext_iff] at h
  specialize h (y + x)
  rw [← SetLike.mem_coe, ← SetLike.mem_coe, mem_Halfspace_translation, mem_Halfspace_translation, add_sub_cancel] at h
  exact h

lemma frontierHalfspace_Hyperplane {Hi_ : Halfspace E} : 
  frontier Hi_ = {x : E | Hi_.f.1 x = Hi_.α } := by
  have := ContinuousLinearMap.frontier_preimage Hi_.f.1 (unitSphereDual_surj Hi_.f) (Set.Iic Hi_.α)
  simp only [ne_eq, LinearMap.coe_toContinuousLinearMap', Set.nonempty_Ioi, frontier_Iic'] at this 
  change frontier ( Hi_.f.1 ⁻¹' {x | x ≤ Hi_.α}) = Hi_.f.1 ⁻¹' {Hi_.α} at this
  rw [Hi_.h, this] ; clear this
  unfold Set.preimage
  simp only [ne_eq, Set.mem_singleton_iff]
  done

lemma Hyperplane_convex (Hi_ : Halfspace E) : 
  Convex ℝ {x : E | Hi_.f.1 x = Hi_.α } := by
  exact @convex_hyperplane ℝ E ℝ _ _ _ _ _ _ Hi_.f.1 (LinearMap.isLinear Hi_.f.1) Hi_.α
  done

lemma Hyperplane_affineClosed (Hi_ : Halfspace E) :
  ∀ s : Fin n → E, Set.range s ⊆ {x : E | Hi_.f.1 x = Hi_.α }
    → ∀ a : Fin n → ℝ, Finset.univ.sum a = 1 →  
    Finset.affineCombination ℝ Finset.univ s a ∈ {x : E | Hi_.f.1 x = Hi_.α } := by
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

def IsFace (F X : Set E) : Prop := 
  Convex ℝ F ∧ IsClosed F ∧ IsExtreme ℝ X F

def IsProperFace (F X : Set E) : Prop := 
  F ≠ X ∧ F.Nonempty ∧ IsFace F X

lemma lemma2_27 {F X : Set E} [FiniteDimensional ℝ E] (hXcl : IsClosed X) (hXCV : Convex ℝ X)
  (hF : IsProperFace F X) : F ⊆ intrinsicFrontier ℝ X := by
  rcases hF with ⟨hFX, hF0, hFCV, hFCl, hFs, hFEx⟩ ; clear hFCl hXCV hF0 hFCV
  intro y hyF
  have hyX : y ∈ X := Set.mem_of_subset_of_mem hFs hyF
  have hFss := (ssubset_of_subset_of_ne hFs hFX) ; clear hFs hFX
  rcases (Set.nonempty_diff.mpr (HasSSubset.SSubset.not_subset hFss)) with ⟨x, hxX, hxF⟩ ;clear hFss

  let y'n : ℕ → E := λ n => AffineMap.lineMap x y (1 + 1/(n+1):ℝ)
  let Sn : ℕ → Set E := λ n => segment ℝ x (y'n n)
  
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

  lemma extremepointIsFace {X : Set E}
    (x : E) (hxEx : x ∈ Set.extremePoints ℝ X) : IsFace {x} X :=
    ⟨ convex_singleton _, isClosed_singleton, mem_extremePoints_iff_extreme_singleton.mp hxEx ⟩

-- Theorem 2.34 = closure_convexHull_extremePoints