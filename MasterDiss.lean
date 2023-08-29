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


