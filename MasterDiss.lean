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

def Halfspace (d : ℕ) : Type := {H : Set (EuclideanSpace ℝ (Fin d)) // ∃ (f : nontrivialdual d) (α : ℝ), H = f.1 ⁻¹' {x | x ≤ α}}

lemma Halfspace_convex (H : Halfspace d) : Convex ℝ H.1 := by
  rcases H with ⟨H, ⟨f, α, rfl⟩⟩
  exact convex_halfspace_le (LinearMap.isLinear f.1) α

def Vpolytope {S : Set (EuclideanSpace ℝ (Fin d))} (_ : S.Finite) : Set (EuclideanSpace ℝ (Fin d)) := convexHull ℝ S

def Hpolytope {H : Set (@Halfspace d)} (_ : H.Finite) : Set (EuclideanSpace ℝ (Fin d)) :=
  ⋂₀ ((fun x => x.1) '' H)

lemma Convex_Vpolytope {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Finite) : Convex ℝ (Vpolytope hS) := convex_convexHull ℝ S

lemma Closed_Vpolytope {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Finite) : IsClosed (Vpolytope hS) := 
  Set.Finite.isClosed_convexHull hS

lemma Compact_Vpolytope {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Finite) : IsCompact (Vpolytope hS) := 
  Set.Finite.isCompact_convexHull hS

lemma Convex_Hpolytope {H : Set (Halfspace d)} (hH : H.Finite) : Convex ℝ (Hpolytope hH) := by
  apply convex_sInter
  rintro Hiset ⟨ Hi, _, rfl ⟩
  simp only [ne_eq, Set.preimage_setOf_eq]
  exact Halfspace_convex Hi

lemma Closed_Hpolytope {H : Set (Halfspace d)} (hH : H.Finite) : IsClosed (Hpolytope hH) := 
  by
    apply isClosed_sInter
    rintro Hiset ⟨ Hi, _, rfl ⟩
    change IsClosed Hi.1
    rcases Hi.2 with ⟨ f, x, h1⟩
    rw [h1]
    apply IsClosed.preimage (LinearMap.continuous_of_finiteDimensional f.1)
    exact isClosed_Iic

lemma frontierHalfspace_Hyperplane {Hi : Halfspace d} : 
  frontier Hi.1 = {x : EuclideanSpace ℝ (Fin d) | Hi.2.1.1 x = f.2.2} := by
  unfold Halfspace
  have := ContinuousLinearMap.frontier_preimage (LinearMap.toContinuousLinearMap f.1)
  rw [LinearMap.coe_toContinuousLinearMap f.1] at this  
  rw [← not_iff_not]
  simp [Set.mem_compl_eq, Set.mem_set_of_eq]
  done

-- /-
-- Lemma4.5. Let𝑋bean𝐻-polytopeinℝ𝑑 and𝑥 ∈ 𝑋 . Let𝐼 ⊆ {1,...,𝑛}besuchthat𝑥 ∈ 𝐻 𝑖 iff
-- 𝑖 ∈𝐼 .Then𝑥isanextremepointof𝑋ifandonlyif∩𝑖∈𝐼𝐻𝑖 ={𝑥}.
-- Proof. If𝑖 ∈𝐼 ,thenℓ𝑖(𝑥)=𝛼𝑖,soif𝑢isanyvectorsothat𝑥±𝑢∈𝑋,wemusthave
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

lemma ExtremePointsofHpolytope {H : Set (((EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ) × ℝ)} (hH : H.Finite) 
  (I : Set (((EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ) × ℝ)) (hI : I ⊆ H ∧ ∀ f, f ∈ I ↔ x ∈ Halfspace f) :
  ∀ x ∈ Hpolytope hH, x ∈ Set.extremePoints ℝ (Hpolytope hH) ↔ 
  ⋂₀ ((fun f => {x : EuclideanSpace ℝ (Fin d) | f.1 x ≤ f.2}) '' I) = {x} := by
  rintro x hx
  constructor
  · intro h
    

  done

-- def IsVpolytope {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (hX : Convex ℝ X) [IsClosed X] : Prop :=
--   ∃ (S : Set (EuclideanSpace ℝ (Fin d))), S.Finite ∧ X = convexHull ℝ S

-- def IsHpolytope {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (hX : Convex ℝ X) [IsClosed X] : Prop :=
--   ∃ (S : Set (((EuclideanSpace ℝ (Fin d)) → ℝ) × ℝ)), S.Finite ∧ 
--     (∀ f : ((EuclideanSpace ℝ (Fin d)) → ℝ) × ℝ, f ∈ S → IsLinearMap ℝ f.1) ∧ 
--     X = ⋂₀ ((fun f => {x : EuclideanSpace ℝ (Fin d) | f.1 x ≤ f.2}) '' S)

-- lemma IsVpolytopeIsCompact {d : ℕ} {X : Set (EuclideanSpace ℝ (Fin d))} (hX : Convex ℝ X) [IsClosed X] (h : IsVpolytope X hX) 
--   : IsCompact X := by
--   rcases h with ⟨S, ⟨hS, rfl⟩⟩
--   exact Set.Finite.isCompact_convexHull hS
--   done

-- theorem Set.Finite.isCompact_convexHull1 {s : Set E} (hs : s.Finite) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [TopologicalAddGroup E]
--   [ContinuousSMul ℝ E] :
--     IsCompact (convexHull ℝ s) := by
--   rw [hs.convexHull_eq_image]
--   apply (@isCompact_stdSimplex _ hs.fintype).image
--   haveI := hs.fintype
--   apply LinearMap.continuous_on_pi
--   done

-- /-
-- Lemma4.5. Let𝑋bean𝐻-polytopeinℝ𝑑 and𝑥 ∈ 𝑋 . Let𝐼 ⊆ {1,...,𝑛}besuchthat𝑥 ∈ 𝐻 𝑖 iff
-- 𝑖 ∈𝐼 .Then𝑥isanextremepointof𝑋ifandonlyif∩𝑖∈𝐼𝐻𝑖 ={𝑥}.
-- Proof. If𝑖 ∈𝐼 ,thenℓ𝑖(𝑥)=𝛼𝑖,soif𝑢isanyvectorsothat𝑥±𝑢∈𝑋,wemusthave
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

-- lemma ExtremePointsofHpolytope {d : ℕ} {X : Set (EuclideanSpace ℝ (Fin d))} (hX : Convex ℝ X) [IsClosed X] (hX : IsHpolytope X hX) :
--   ∀ x ∈ X, x ∈ Set.extremePoints ℝ X ↔ x = x := by 
--   sorry
--   done

