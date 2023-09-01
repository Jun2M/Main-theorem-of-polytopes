import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.InnerProductSpace.EuclideanDist


variable {d : ℕ}

/-
Let 𝑋 be a closed convex subset of ℝ^𝑑. Then:
• 𝑋 is a 𝑉-polytope if it is the convex hull of a finite point set.
• 𝑋 is an 𝐻-polytope if it is the intersection of finitely many half spaces.

Theorem : Every 𝑉-polytope is an 𝐻-polytope, and every compact 𝐻-polytope is a 𝑉-polytope.
-/

def nontrivialdual (d : ℕ) : Type := {f : (Module.Dual ℝ (EuclideanSpace ℝ (Fin d))) // f ≠ 0}

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

structure Halfspace (d : ℕ) where
  f : nontrivialdual d
  α : ℝ
  S : Set (EuclideanSpace ℝ (Fin d)) := f.1 ⁻¹' {x | x ≤ α}
  h : S = f.1 ⁻¹' {x | x ≤ α}

lemma Halfspace_convex (H_ : Halfspace d) : Convex ℝ H_.S := by
  rw [H_.h]
  exact convex_halfspace_le (LinearMap.isLinear H_.f.1) H_.α

def RelativeInterior (X : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) := by
  apply (·.val) '' (@interior (affineSpan ℝ X) _ _) 
  exact setOf (λ x => x.val ∈ X)

def RelativeFrontier (X : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) := by
  apply (·.val) '' (@frontier (affineSpan ℝ X) _ _) 
  exact setOf (λ x => x.val ∈ X)

def IsFace (F X : Set (EuclideanSpace ℝ (Fin d))) : Prop := 
  Convex ℝ F ∧ IsClosed F ∧ IsExtreme ℝ X F

def IsProperFace (F X : Set (EuclideanSpace ℝ (Fin d))) : Prop := 
  F ≠ X ∧ F.Nonempty ∧ IsFace F X

lemma lemma2_27 {F X : Set (EuclideanSpace ℝ (Fin d))} (hXcl : IsClosed X) (hXCV : Convex ℝ X)
  (hF : IsProperFace F X) : F ⊆ RelativeFrontier X := by
  rcases hF with ⟨hFX, hF0, hFCV, hFCl, hFs, hFEx⟩
  unfold RelativeFrontier
  rcases hF0 with ⟨y, hyF⟩
  have hyX : y ∈ X := Set.mem_of_subset_of_mem hFs hyF
  have hFss := (ssubset_of_subset_of_ne hFs hFX) ; clear hFs hFX
  rcases (Set.nonempty_diff.mpr (HasSSubset.SSubset.not_subset hFss)) with ⟨x, hxX, hxF⟩

  let y'n : ℕ → EuclideanSpace ℝ (Fin d) := λ n => AffineMap.lineMap x y (1 + 1/(n+1):ℝ)
  let Sn : ℕ → Set (EuclideanSpace ℝ (Fin d)) := λ n => segment ℝ x (y'n n)
  
  have h1 : ∀ n, 0 < 1 / ((@Nat.cast ℝ _ n) + 1:ℝ) := 
    fun n:ℕ => (div_pos zero_lt_one (Nat.cast_add_one_pos n))

  have hySn : ∀ n, y ∈ Sn n := by
    intro n
    change y ∈ segment ℝ x (AffineMap.lineMap x y (1 + 1/(n+1):ℝ))
    rw [segment_eq_image_lineMap]
    use 1/(1 + 1/(n+1):ℝ)
    rw [Set.mem_Icc]
    constructor
    · -- 1. tedious inequalities
      sorry
    · -- 2.
      rw [AffineMap.coe_lineMap, AffineMap.coe_lineMap]
      simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel, ne_eq]
      rw [one_div, smul_smul, inv_mul_cancel, one_smul, sub_add_cancel]
      have : 0 < 1 + 1 / (↑n + 1:ℝ) := add_pos_of_nonneg_of_pos (by linarith) (h1 n)
      exact (ne_of_lt this).symm

  have hy'naff : ∀ n, y'n n ∈ affineSpan ℝ X := by
    intro n
    apply affineSpan_mono ℝ
    rw [Set.insert_subset_iff]
    exact ⟨hxX, Set.singleton_subset_iff.mpr hyX⟩
    exact AffineMap.lineMap_mem_affineSpan_pair (1 + 1/(n+1):ℝ) x y
    done

  have hSnaff : ∀ n, Sn n ⊆ affineSpan ℝ X := by -- By definition 𝑆𝑛 ⊆ aff 𝑋
    intro n ; clear hXcl hXCV hFCl hFEx hFss hxF hFCV hyF
    exact Convex.segment_subset (AffineSubspace.convex (affineSpan ℝ X)) 
      (mem_affineSpan ℝ hxX) (hy'naff n)
  
  have hy'nXc : ∀ n, y'n n ∉ X := by
    intro n hn
    refine hxF (hFEx hxX hn hyF ?_ ).1 
    apply mem_openSegment_of_ne_left_right
    · 
      rintro rfl
      exact hxF hyF
    · 
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
    done
    
    -- intro _ a ha ; clear hXcl hXCV hFCl hFEx hFss hxF hFCV hyF
    -- rcases ((Set.mem_image _ _ _).mp ha) with ⟨r, _, rfl⟩ ; clear ha Sn
    -- apply Set.mem_of_subset_of_mem _ (AffineMap.lineMap_mem_affineSpan_pair r x y)
    -- apply affineSpan_mono ℝ
    -- rw [Set.insert_subset_iff]
    -- exact ⟨hxX, Set.singleton_subset_iff.mpr hyX⟩
  
  -- have hy'nXc : ∀ n, y'n n ∉ X := by
  --   intro n hn 
  --   have hy'nSn : Sn n = segment ℝ x (y'n n) := by
  --     rw [segment_eq_image_lineMap] ; clear hXcl hXCV hFCl hFEx hFss hxF hFCV hyF hyX hxX hSnaff
  --     ext z
  --     constructor
  --     · -- 1.
  --       rintro ⟨r, hr, rfl⟩
  --       use r / (1 + 1 / (↑n + 1))
  --       constructor
  --       · -- 1.
  --         rw [Set.mem_Icc] ; clear Sn hn y'n x y F X  
  --         rw [Set.mem_Icc] at hr
  --         rcases hr with ⟨hr1, hr2⟩
  --         constructor
  --         · -- 1.
  --           have := le_trans hr1 hr2
  --           rw [div_nonneg_iff]
  --           left
  --           exact ⟨ by assumption, by assumption ⟩
  --         · -- 2.
  --           rw [div_le_one]
  --           assumption
  --           have : 0 < 1/(n + 1 :ℝ) := div_pos zero_lt_one (Nat.cast_add_one_pos n)
  --           linarith
  --           done
  --         done
  --       · -- 2.
          
  --         done
  --       done
  --     · -- 2.
  --       sorry
  --       done
  --     -- aesop
  --     done



    done

  done 




def Vpolytope {S : Set (EuclideanSpace ℝ (Fin d))} (_ : S.Finite) : 
  Set (EuclideanSpace ℝ (Fin d)) := convexHull ℝ S

def Hpolytope {H_ : Set (Halfspace d)} (_ : H_.Finite) : Set (EuclideanSpace ℝ (Fin d)) :=
  ⋂₀ ((·.S) '' H_)

lemma Convex_Vpolytope {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Finite) : 
  Convex ℝ (Vpolytope hS) := convex_convexHull ℝ S

lemma Closed_Vpolytope {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Finite) : 
  IsClosed (Vpolytope hS) := Set.Finite.isClosed_convexHull hS

lemma Compact_Vpolytope {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Finite) : 
  IsCompact (Vpolytope hS) := Set.Finite.isCompact_convexHull hS

lemma Convex_Hpolytope {H_ : Set (Halfspace d)} (hH_ : H_.Finite) : Convex ℝ (Hpolytope hH_) := by
  apply convex_sInter
  rintro _ ⟨ Hi_, _, rfl ⟩
  simp only [ne_eq, Set.preimage_setOf_eq]
  exact Halfspace_convex Hi_

lemma Closed_Hpolytope {H : Set (Halfspace d)} (hH_ : H.Finite) : IsClosed (Hpolytope hH_) := by
  apply isClosed_sInter
  rintro _ ⟨ Hi_, _, rfl ⟩
  change IsClosed Hi_.S
  rw [Hi_.h]
  apply IsClosed.preimage (LinearMap.continuous_of_finiteDimensional Hi_.f.1)
  exact isClosed_Iic

lemma frontierHalfspace_Hyperplane {Hi_ : Halfspace d} : 
  frontier Hi_.S = {x : EuclideanSpace ℝ (Fin d) | Hi_.f.1 x = Hi_.α } := by
  have := ContinuousLinearMap.frontier_preimage (LinearMap.toContinuousLinearMap Hi_.f.1) (nontrivialdual_surj Hi_.f) (Set.Iic Hi_.α)
  simp only [ne_eq, LinearMap.coe_toContinuousLinearMap', Set.nonempty_Ioi, frontier_Iic'] at this 
  change frontier (Hi_.f.1 ⁻¹' {x | x ≤ Hi_.α}) = Hi_.f.1 ⁻¹' {Hi_.α} at this
  rw [Hi_.h, this] ; clear this
  unfold Set.preimage
  simp only [ne_eq, Set.mem_singleton_iff]
  done

-- /-
-- Lemma4.5. Let 𝑋 bean 𝐻-polytope in ℝ^𝑑 and 𝑥 ∈ 𝑋 . Let 𝐼 ⊆ {1,...,𝑛} be such that 𝑥 ∈ 𝐻𝑖 iff
-- 𝑖 ∈ 𝐼 .Then 𝑥 is an extreme point of 𝑋 if and only if ∩ 𝑖∈𝐼 𝐻𝑖 ={𝑥}.
-- Proof. If 𝑖 ∈ 𝐼 ,then ℓ𝑖(𝑥) = 𝛼𝑖, so if 𝑢 is any vector so that 𝑥±𝑢 ∈ 𝑋, we must have
-- ℓ𝑖(𝑥)+ℓ𝑖(𝑢)≤𝛼𝑖 and ℓ𝑖(𝑥)−ℓ𝑖(𝑢)≤𝛼𝑖
-- fromwhichitfollowsthatℓ𝑖(𝑢) = 0. If [𝑥1,𝑥2] ⊆ 𝑋 isasegmentwith𝑥itsrelativeinterior,we
-- cantake𝑢 = 𝜀(𝑥2 −𝑥1)with𝜀 > 0 smallenoughtoconcludethat[𝑥1,𝑥2] ⊆ 𝐻 𝑖. Since𝑖 ∈ 𝐼 was
-- arbitrary,weconcludethat,infact,
-- [𝑥1,𝑥2]⊆⋂𝑖∈𝐼
-- 𝐻𝑖
-- Ifther.h.s. is{𝑥},wehaveshownthat𝑥isextreme.
-- Otherwise,wecanfind𝑦 ∈ ∩ 𝑖∈𝐼𝐻𝑖 differentfrom𝑋. Set𝑢 = 𝑦−𝑥 . Certainlythesegment
-- [𝑥−𝜀𝑢,𝑥+𝜀𝑢] ⊆ 𝐻𝑖 ⊆ 𝐻 −𝑖 forall𝜀 > 0 and𝑖 ∈ 𝐼 . For𝑗 ∈ 𝐼 𝑐,wehaveℓ𝑗(𝑥) < 𝛼𝑗. Since𝐼𝑐 is
-- finite,forasmallenough𝜀 > 0 ,thesegment[𝑥−𝜀𝑢,𝑥+𝜀𝑢]remainsdisjointfromeachof the
-- 𝐻𝑗,andhencein𝑋.Thisshowsthat𝑥isnotextreme.
-- -/

lemma ExtremePointsofHpolytope {H_ : Set (Halfspace d)} (hH_ : H_.Finite) (I : EuclideanSpace ℝ (Fin d) → Set (Halfspace d)) 
  (hI : ∀ x, I x ⊆ H_ ∧ ∀ Hi_, Hi_ ∈ I x ↔ x ∈ Hi_.S) :
  ∀ x ∈ Hpolytope hH_, x ∈ Set.extremePoints ℝ (Hpolytope hH_) ↔ ⋂₀ ((frontier ·.S) '' I x) = {x} := by
  rintro x hx
  by_cases ∃ u, x + u ∈ Hpolytope hH_ ∧ x - u ∈ Hpolytope hH_ 
  · rcases h with ⟨u, hxu, hxu'⟩
    unfold Hpolytope at hxu hxu'
    rw [Set.mem_sInter] at hxu hxu'
    
    sorry
  · sorry
  done


