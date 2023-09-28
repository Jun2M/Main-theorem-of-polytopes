import «Polar»


variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
open Pointwise


def Vpolytope {S : Set E} (_ : S.Finite): Set E :=
  convexHull ℝ S

lemma Convex_Vpolytope {S : Set E} (hS : S.Finite) : 
  Convex ℝ (Vpolytope hS) := convex_convexHull ℝ S

lemma Closed_Vpolytope {S : Set E} (hS : S.Finite) : 
  IsClosed (Vpolytope hS) := by exact Set.Finite.isClosed_convexHull hS
  
lemma Compact_Vpolytope {S : Set E} (hS : S.Finite) : 
  IsCompact (Vpolytope hS) := Set.Finite.isCompact_convexHull hS


def Hpolytope {H_ : Set (Halfspace E)} (_ : H_.Finite) : Set E :=
  ⋂₀ (SetLike.coe '' H_)

lemma Convex_Hpolytope {H_ : Set (Halfspace E)} (hH_ : H_.Finite) : Convex ℝ (Hpolytope hH_) := by
  apply convex_sInter
  rintro _ ⟨ Hi_, _, rfl ⟩
  exact Halfspace_convex Hi_

lemma Closed_Hpolytope {H : Set (Halfspace E)} (hH_ : H.Finite) : IsClosed (Hpolytope hH_) := by
  apply isClosed_sInter
  rintro _ ⟨ Hi_, _, rfl ⟩
  change IsClosed Hi_
  rw [Hi_.h]
  apply IsClosed.preimage (Hi_.f.1.cont)
  exact isClosed_Iic

lemma Hpolytope_same {H_ : Set (Halfspace E)} (hH_1 hH_2: H_.Finite) : 
  Hpolytope hH_1 = Hpolytope hH_2 := by
  unfold Hpolytope
  rfl

lemma mem_Hpolytope {H_ : Set (Halfspace E)} (hH_ : H_.Finite) (x : E) : 
  x ∈ Hpolytope hH_ ↔ ∀ Hi, Hi ∈ H_ → Hi.f.1 x ≤ Hi.α := by
  constructor <;> intro h
  · -- 1.
    intro Hi HiH
    unfold Hpolytope at h
    rw [Set.mem_sInter] at h
    specialize h Hi ⟨ Hi, HiH, rfl ⟩
    rw [Halfspace_mem] at h
    exact h
    done
  · -- 2.
    unfold Hpolytope
    rw [Set.mem_sInter]
    rintro _ ⟨ Hi_, hHi_, rfl ⟩
    specialize h Hi_ hHi_
    rw [Halfspace_mem]
    exact h
    done
    
lemma empty_Hpolytope (h : ∃ x : E, x ≠ 0) : ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite), Hpolytope hH_ = ∅ := by
  rcases h with ⟨ x, hx ⟩
  let xhat := (norm x)⁻¹ • x
  let fval : NormedSpace.Dual ℝ E := InnerProductSpace.toDualMap ℝ _ xhat
  let f : {f : (NormedSpace.Dual ℝ E) // norm f = 1} := ⟨ fval , (by
    change norm (innerSL ℝ ((norm x)⁻¹ • x)) = 1
    have := @norm_smul_inv_norm ℝ _ E _ _ x hx
    rw [IsROrC.ofReal_real_eq_id, id_eq] at this 
    rw [innerSL_apply_norm, this]
    done
  ) ⟩
  refine ⟨ {Halfspace.mk f (-1), Halfspace.mk (-f) (-1)} , 
    (by simp only [Set.mem_singleton_iff, Halfspace.mk.injEq, Set.finite_singleton, Set.Finite.insert]) , ?_ ⟩
  
  ext x
  rw [Set.mem_empty_iff_false, iff_false, mem_Hpolytope]
  intro h
  have h1 := h (Halfspace.mk f (-1)) (by simp)
  have h2 := h (Halfspace.mk (-f) (-1)) (by simp)
  rw [unitSphereDual_neg, ContinuousLinearMap.neg_apply, neg_le, neg_neg] at h2
  change f.1 x ≤ -1 at h1
  linarith
  done

lemma hyperplane_Hpolytope : ∀ (f : {f : (NormedSpace.Dual ℝ E) // norm f = 1}) (c : ℝ), 
  ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite), Hpolytope hH_ = {x | f.1 x = c} := by
  intro f c
  refine ⟨ {Halfspace.mk f c, Halfspace.mk (-f) (-c)}, 
    (by simp only [Set.mem_singleton_iff, Halfspace.mk.injEq, Set.finite_singleton, Set.Finite.insert]) , ?_ ⟩

  ext x
  rw [mem_Hpolytope, Set.mem_setOf]
  constructor
  · -- 1.
    intro h
    have h1 := h (Halfspace.mk f c) (by simp)
    have h2 := h (Halfspace.mk (-f) (-c)) (by simp)
    rw [unitSphereDual_neg, ContinuousLinearMap.neg_apply, neg_le, neg_neg] at h2
    change f.1 x ≤ c at h1
    exact le_antisymm h1 h2
  · -- 2.
    intro h Hi hHi
    simp only [Set.mem_singleton_iff, Halfspace.mk.injEq, Set.mem_insert_iff] at hHi 
    rcases hHi with rfl | rfl
    · 
      exact le_of_eq h
    · 
      rw [unitSphereDual_neg, ContinuousLinearMap.neg_apply, neg_le, neg_neg]
      exact le_of_eq h.symm
  done

lemma inter_Hpolytope (H_1 H_2 : Set (Halfspace E)) (hH_1 : H_1.Finite) (hH_2 : H_2.Finite) : 
  Hpolytope (Set.Finite.union hH_1 hH_2) = Hpolytope hH_1 ∩ Hpolytope hH_2 := by
  ext x
  rw [mem_Hpolytope, Set.mem_inter_iff, mem_Hpolytope, mem_Hpolytope]
  constructor
  · -- 1
    intro h
    constructor <;> intro Hi_ hH_ <;> exact h Hi_ (by simp only [Set.mem_union, hH_, true_or, or_true])
  · -- 2
    intro h Hi hHi
    rw [Set.mem_union] at hHi 
    rcases hHi with hHi | hHi
    · -- 2.1
      exact h.1 Hi hHi
    · -- 2.2
      exact h.2 Hi hHi 
  done