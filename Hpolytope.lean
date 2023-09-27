import «Polar»


variable {E P : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] 
  [PseudoMetricSpace P] [NormedAddTorsor E P] 
open Pointwise


def Vpolytope {S : Set P} (_ : S.Finite) (x : P) : Set P :=
  convexHull ℝ (S -ᵥ {x}) +ᵥ {x}

-- convex_convexHull ℝ S
-- Set.Finite.isClosed_convexHull hS
-- Set.Finite.isCompact_convexHull hS

lemma IsClosed_Vpolytope {S : Set P} (hS : S.Finite) (x : P) : 
  IsClosed (Vpolytope hS x) := by
  unfold Vpolytope
  apply IsClosed.vadd_right_of_isCompact ?_ isCompact_singleton
  apply Set.Finite.isClosed_convexHull 
  exact Set.detranslation.Finite hS x

lemma IsCompact_Vpolytope {S : Set P} (hS : S.Finite) (x : P) : 
  IsCompact (Vpolytope hS x) := by
  unfold Vpolytope
  rw [Set.vadd_singleton]
  apply IsCompact.image ?_ (Set.translation.continuous x)
  apply Set.Finite.isCompact_convexHull 
  exact Set.detranslation.Finite hS x

def Hpolytope {H_ : Set (Halfspace E)} (_ : H_.Finite) (x : P) : Set P :=
  (cutSpace H_) +ᵥ {x}

-- lemma Convex_Hpolytope {H_ : Set (Halfspace E)} (hH_ : H_.Finite) (x : P) :
--   Convex ℝ (Hpolytope hH_ x) := by
--   apply convex_sInter
--   rintro _ ⟨ Hi_, _, rfl ⟩
--   exact Halfspace_convex Hi_

lemma Closed_Hpolytope {H : Set (Halfspace E)} (hH_ : H.Finite) (x : P) : 
  IsClosed (Hpolytope hH_ x) := by
  apply IsClosed.vadd_right_of_isCompact ?_ isCompact_singleton
  apply isClosed_sInter
  rintro _ ⟨ Hi_, _, rfl ⟩
  change IsClosed Hi_
  rw [Hi_.h]
  apply IsClosed.preimage (Hi_.f.1.cont)
  exact isClosed_Iic

lemma mem_Hpolytope {H_ : Set (Halfspace E)} (hH_ : H_.Finite) (x y : P) : 
  y ∈ Hpolytope hH_ x ↔ ∀ Hi, Hi ∈ H_ → Hi.f.1 (y -ᵥ x) ≤ Hi.α := by
  rw [Hpolytope, cutSpace, Set.mem_translation, Set.mem_sInter]
  refine ⟨ fun h Hi HiH => (Halfspace_mem Hi (y -ᵥ x)).mp (h Hi ⟨ Hi, HiH, rfl ⟩), ?_ ⟩
  rintro h _ ⟨ Hi_, hHi_, rfl ⟩
  exact (Halfspace_mem _ _).mp (h Hi_ hHi_)
    
lemma empty_Hpolytope (x : P) (h : ∃ point : E, point ≠ 0) : ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite), Hpolytope hH_ x = ∅ := by
  rcases h with ⟨ point, hpoint ⟩
  let pointhat := (norm point)⁻¹ • point
  let fval : NormedSpace.Dual ℝ E := InnerProductSpace.toDualMap ℝ _ pointhat
  let f : {f : (NormedSpace.Dual ℝ E) // norm f = 1} := ⟨ fval , (by
    change norm (innerSL ℝ ((norm point)⁻¹ • point)) = 1
    have := @norm_smul_inv_norm ℝ _ E _ _ point hpoint
    rw [IsROrC.ofReal_real_eq_id, id_eq] at this 
    rw [innerSL_apply_norm, this]
    done
  ) ⟩
  refine ⟨ {Halfspace.mk f (-1), Halfspace.mk (-f) (-1)} , 
    (by simp only [Set.mem_singleton_iff, Halfspace.mk.injEq, Set.finite_singleton, Set.Finite.insert]) , ?_ ⟩
  
  ext y
  rw [Set.mem_empty_iff_false, iff_false, mem_Hpolytope]
  intro h
  have h1 := h (Halfspace.mk f (-1)) (by simp)
  have h2 := h (Halfspace.mk (-f) (-1)) (by simp)
  rw [unitSphereDual_neg, ContinuousLinearMap.neg_apply, neg_le, neg_neg] at h2
  change f.1 (y -ᵥ x) ≤ -1 at h1
  linarith
  done

lemma hyperplane_Hpolytope (x : P) : ∀ (f : {f : (NormedSpace.Dual ℝ E) // norm f = 1}) (c : ℝ), 
  ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite), Hpolytope hH_ x = { y : E | f.1 y = c} +ᵥ {x} := by
  intro f c
  refine ⟨ {Halfspace.mk f c, Halfspace.mk (-f) (-c)}, 
    (by simp only [Set.mem_singleton_iff, Halfspace.mk.injEq, Set.finite_singleton, Set.Finite.insert]) , ?_ ⟩

  ext y
  rw [mem_Hpolytope, Set.mem_translation, Set.mem_setOf]
  constructor
  · -- 1.
    intro h
    have h1 := h (Halfspace.mk f c) (by simp)
    have h2 := h (Halfspace.mk (-f) (-c)) (by simp)
    rw [unitSphereDual_neg, ContinuousLinearMap.neg_apply, neg_le, neg_neg] at h2
    change f.1 (y -ᵥ x) ≤ c at h1
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

lemma inter_Hpolytope (x : P) (H_1 H_2 : Set (Halfspace E)) (hH_1 : H_1.Finite) (hH_2 : H_2.Finite) : 
  Hpolytope (Set.Finite.union hH_1 hH_2) x = Hpolytope hH_1 x ∩ Hpolytope hH_2 x := by
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