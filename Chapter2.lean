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

-- instance EuclideanSpace.instDecidableEqEuclideanSpace : DecidableEq (EuclideanSpace ℝ (Fin d)) := by
--   exact @DFinsupp.instDecidableEqDFinsupp (Fin d) (λ i => ℝ) _ _ _

-- Type for linear dual of EuclideanSpace ℝ (Fin d) with norm 1
def unitSphereDual (d : ℕ+) : Type := {f : (NormedSpace.Dual ℝ (EuclideanSpace ℝ (Fin d))) // norm f = 1}

lemma EquivUnitSphere : {p : EuclideanSpace ℝ (Fin d) // norm p = 1} ≃ₜ 
  {f : (NormedSpace.Dual ℝ (EuclideanSpace ℝ (Fin d))) // norm f = 1} where
  toFun := λ p => ⟨(InnerProductSpace.toDual _ _ p), ((LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ _) p.1) ▸ p.2)⟩
  invFun := λ f => ⟨ (InnerProductSpace.toDual _ _).invFun f.1, (by simp; exact f.2)⟩
  left_inv := λ p => by simp
  right_inv := λ f => by simp

lemma unitSphereDual_surj : ∀ f : unitSphereDual d, Function.Surjective f.val := by
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
  f : unitSphereDual d
  α : ℝ
  S : Set (EuclideanSpace ℝ (Fin d)) := f.1 ⁻¹' {x | x ≤ α}
  h : S = f.1 ⁻¹' {x | x ≤ α}

def Halfspace.mk1 (f : unitSphereDual d) (α : ℝ) : Halfspace d := 
  ⟨ f, α, f.1 ⁻¹' {x | x ≤ α}, rfl⟩

lemma Halfspace_mem (H_ : Halfspace d) : ∀ x, x ∈ H_.S ↔ H_.f.1 x ≤ H_.α := by
  intro x
  rw [H_.h]
  exact Iff.rfl

lemma Halfspace_convex (H_ : Halfspace d) : Convex ℝ H_.S := by
  rw [H_.h]
  exact convex_halfspace_le (LinearMap.isLinear H_.f.1.1) H_.α

lemma Halfspace_closed (H_ : Halfspace d) : IsClosed H_.S := by
  rw [H_.h]
  exact IsClosed.preimage (H_.f.1.cont) isClosed_Iic

lemma Halfspace_span (H_ : Halfspace d) : affineSpan ℝ H_.S = ⊤ := by
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
  apply subset_trans ?_ (subset_convexHull ℝ H_.S)
  intro x hx
  rw [Set.mem_preimage, Real.ball_eq_Ioo, Set.mem_Ioo] at hx
  rw [Halfspace_mem H_]
  linarith
  done

lemma frontierHalfspace_Hyperplane {Hi_ : Halfspace d} : 
  frontier Hi_.S = {x : EuclideanSpace ℝ (Fin d) | Hi_.f.1 x = Hi_.α } := by
  have := ContinuousLinearMap.frontier_preimage Hi_.f.1 (unitSphereDual_surj Hi_.f) (Set.Iic Hi_.α)
  simp only [ne_eq, LinearMap.coe_toContinuousLinearMap', Set.nonempty_Ioi, frontier_Iic'] at this 
  change frontier (Hi_.f.1 ⁻¹' {x | x ≤ Hi_.α}) = Hi_.f.1 ⁻¹' {Hi_.α} at this
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