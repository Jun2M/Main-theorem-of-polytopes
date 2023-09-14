import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Convex.Independent


variable {d : ℕ+}

-- lemma LineMapChangeofBasis  {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} 
--   [Field k] [AddCommGroup V1] [Module k V1] [AddTorsor V1 P1] (p₀ : P1) (p₁ : P1) :
--   ∀ a : k, Set.range (@AffineMap.lineMap k V1 P1 _ _ _ _ p₀ p₁) = 
--   Set.range (@AffineMap.lineMap k V1 P1 _ _ _ _ p₀ (AffineMap.lineMap p₀ p₁ a)) := by
--   intro a
--   apply le_antisymm <;>
--   simp only [Set.le_eq_subset] <;>
--   rw [Set.range_subset_range_iff_exists_comp]
--   · 
--     use (·/a)
--     ext x
--     rw [Function.comp]
--     done
--   · 
--     done
--   sorry
--   done

-- lemma openSegment_intrinsicInterior_of_segment {x y : EuclideanSpace ℝ (Fin d)} (hxy : x ≠ y) :
--   openSegment ℝ x y ⊆ intrinsicInterior ℝ (segment ℝ x y) := by
--   rw [intrinsicInterior, segment_eq_image_lineMap]
--   intro z hz
--   rw [Set.mem_image]
--   have h : z ∈ affineSpan ℝ ((AffineMap.lineMap x y) '' Set.Icc (0:ℝ) 1) := sorry
--   use ⟨ z, h ⟩
--   constructor
--   · -- 1.
--     apply preimage_interior_subset_interior_preimage continuous_subtype_val
--     rw [Set.mem_preimage]
--     done
--   · -- 2.
--     sorry
--     done
--   done

-- Type for nonzero linear dual of EuclideanSpace ℝ (Fin d)
def nontrivialdual (d : ℕ+) : Type := {f : (Module.Dual ℝ (EuclideanSpace ℝ (Fin d))) // f ≠ 0}

lemma nontrivialdual_surj : ∀ f : nontrivialdual d, Function.Surjective f.val := by
  intros f x
  have h1 := f.2
  have h : ∃ v, f.1 v ≠ 0 := by
    contrapose! h1
    change ∀ v, f.1 v = (0 : Module.Dual ℝ (EuclideanSpace ℝ (Fin d))) v at h1
    ext v
    exact h1 v

  rcases h with ⟨v, hv⟩
  use (x/f.1 v) • v 
  rw [LinearMap.map_smulₛₗ, RingHom.id_apply, smul_eq_mul, div_mul_cancel x hv]
  done

lemma nontrivialdual_cont : ∀ f : nontrivialdual d, Continuous f.val := 
  fun f => LinearMap.continuous_of_finiteDimensional f.val

-- Type for halfspaces of EuclideanSpace ℝ (Fin d)
structure Halfspace (d : ℕ+) where
  f : nontrivialdual d
  α : ℝ
  S : Set (EuclideanSpace ℝ (Fin d)) := f.1 ⁻¹' {x | x ≤ α}
  h : S = f.1 ⁻¹' {x | x ≤ α}

lemma Halfspace_mem (H_ : Halfspace d) : ∀ x, x ∈ H_.S ↔ H_.f.1 x ≤ H_.α := by
  intro x
  rw [H_.h]
  exact Iff.rfl

lemma Halfspace_convex (H_ : Halfspace d) : Convex ℝ H_.S := by
  rw [H_.h]
  exact convex_halfspace_le (LinearMap.isLinear H_.f.1) H_.α

lemma Halfspace_closed (H_ : Halfspace d) : IsClosed H_.S := by
  rw [H_.h]
  exact IsClosed.preimage (LinearMap.continuous_of_finiteDimensional H_.f.1) isClosed_Iic

lemma Halfspace_span (H_ : Halfspace d) : affineSpan ℝ H_.S = ⊤ := by
  -- affine span of a ball(simplex, in general) is entire
  apply affineSpan_eq_top_of_nonempty_interior
  apply Set.Nonempty.mono (?_ : H_.f.1 ⁻¹' (Metric.ball (H_.α -1) (1/2)) ⊆ (interior ((convexHull ℝ) H_.S)))
  · -- preimage of ball is not empty as f is surjective
    cases' nontrivialdual_surj H_.f (H_.α -1) with x hx
    use x
    rw [Set.mem_preimage, Metric.mem_ball, dist_sub_eq_dist_add_right, hx, sub_add_cancel, dist_self]
    linarith
    done
  -- this open set is subset of the halfspace
  rw [IsOpen.subset_interior_iff (IsOpen.preimage (nontrivialdual_cont H_.f) Metric.isOpen_ball)]
  apply subset_trans ?_ (subset_convexHull ℝ H_.S)
  intro x hx
  rw [Set.mem_preimage, Real.ball_eq_Ioo, Set.mem_Ioo] at hx
  rw [Halfspace_mem H_]
  linarith
  done

  -- Metric.mem_closure_iff  
  -- 1. get basis for hyperplane
  -- 2. get a point in interior of Hi_
  -- 3. combine them to get a basis for entire space
  -- done

-- lemma HalfspaceIntrinsicFrontier (H_ : Halfspace d) : intrinsicFrontier ℝ H_.S = frontier H_.S := by
--   rw [intrinsicFrontier]
--   sorry
--   done

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

