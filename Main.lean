import «Chapter2»
import «Chapter3» 


variable {d : ℕ+}
open Pointwise

/-
Let 𝑋 be a closed convex subset of ℝ^𝑑. Then:
• 𝑋 is a 𝑉-polytope if it is the convex hull of a finite point set.
• 𝑋 is an 𝐻-polytope if it is the intersection of finitely many half spaces.

Theorem : Every 𝑉-polytope is an 𝐻-polytope, and every compact 𝐻-polytope is a 𝑉-polytope.
-/

def Vpolytope {S : Set (EuclideanSpace ℝ (Fin d))} (_ : S.Finite) : 
  Set (EuclideanSpace ℝ (Fin d)) := convexHull ℝ S

def Hpolytope {H_ : Set (Halfspace d)} (_ : H_.Finite) : Set (EuclideanSpace ℝ (Fin d)) :=
  ⋂₀ (SetLike.coe '' H_)

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
  change IsClosed Hi_
  rw [Hi_.h]
  apply IsClosed.preimage (Hi_.f.1.cont)
  exact isClosed_Iic

lemma mem_Hpolytope {H_ : Set (Halfspace d)} (hH_ : H_.Finite) (x : EuclideanSpace ℝ (Fin d)) : 
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
    
lemma empty_Hpolytope : ∃ (H_ : Set (Halfspace d)) (hH_ : H_.Finite), Hpolytope hH_ = ∅ := by
  let ihat : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single 0 1
  let fval := InnerProductSpace.toDualMap ℝ _ ihat
  let f : unitSphereDual d := ⟨ fval , (by
    change norm (innerSL ℝ ihat) = 1
    rw [innerSL_apply_norm, EuclideanSpace.norm_single, norm_one]
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

lemma hyperplane_Hpolytope : ∀ (f : unitSphereDual d) (c : ℝ), 
  ∃ (H_ : Set (Halfspace d)) (hH_ : H_.Finite), Hpolytope hH_ = {x | f.1 x = c} := by
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

lemma inter_Hpolytope (H_1 H_2 : Set (Halfspace d)) (hH_1 : H_1.Finite) (hH_2 : H_2.Finite) : 
  ∃ (H_ : Set (Halfspace d)) (hH_ : H_.Finite), Hpolytope hH_ = Hpolytope hH_1 ∩ Hpolytope hH_2 := by
  refine ⟨ H_1 ∪ H_2 , Set.Finite.union hH_1 hH_2, ?_ ⟩
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

lemma Vpolytope_translation {d : ℕ+} {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Finite) 
  (x : EuclideanSpace ℝ (Fin d)) : 
  Vpolytope (Set.translation.Finite hS x) = (Vpolytope hS) + {x}:= by
  rw [Vpolytope, convexHull_add, convexHull_singleton]
  rfl
  done

lemma Hpolytope_translation {d : ℕ+} {H_ : Set (Halfspace d)} (hH_ : H_.Finite) 
  (x : EuclideanSpace ℝ (Fin d)) : 
  Hpolytope (Set.Finite.image (Halfspace_translation x) hH_) = (@Hpolytope d H_ hH_) + {x}:= by
  rw [Hpolytope, Hpolytope, Set.sInter_image, Set.sInter_image]
  ext y
  rw [Set.mem_iInter, Set.add_singleton]
  simp only [Set.mem_iInter, SetLike.mem_coe, Set.image_add_right, Set.mem_preimage]
  constructor
  · -- 1.
    intro h Hi_ hHi_
    specialize h (Halfspace_translation x Hi_) (Set.mem_image_of_mem _ hHi_)
    rw [← SetLike.mem_coe, mem_Halfspace_translation] at h
    exact h
  · -- 2.
    intro h Hi_ hHi_
    specialize h (Halfspace_translation (-x) Hi_) (?_)
    rw [Set.mem_image] at hHi_
    rcases hHi_ with ⟨ Hi_', hHi_', rfl ⟩
    have : Halfspace_translation (-x) (Halfspace_translation x Hi_') = Hi_':= by
      rw [SetLike.ext_iff]
      intro z
      rw [← SetLike.mem_coe, ← SetLike.mem_coe, mem_Halfspace_translation, mem_Halfspace_translation, 
        sub_neg_eq_add, add_sub_cancel]
      done
    rw [this]
    assumption
    rw [← SetLike.mem_coe, mem_Halfspace_translation, add_sub_cancel, SetLike.mem_coe] at h
    exact h
  done


-- As a ball around x is convex, it must contain a segment with x in its interior
lemma hxSegBallInterSeg : ∀ (x1 x2 : EuclideanSpace ℝ (Fin d)) (ε : ℝ), x ∈ openSegment ℝ x1 x2 ∧ ¬ (x1 = x ∧ x2 = x) → 
  0 < ε → ∃ x1' x2', x ∈ openSegment ℝ x1' x2' ∧ segment ℝ x1' x2' ⊆ openSegment ℝ x1 x2 ∩ Metric.ball x ε ∧ 
    ¬ (x1' = x ∧ x2' = x) := by 
  rintro x1 x2 ε ⟨ hxseg, hne ⟩ hε 
  push_neg at hne
  have hxseg' := hxseg
  rw [openSegment_eq_image', Set.mem_image] at hxseg
  rcases hxseg with ⟨ t, ht, htt ⟩ 
  let v := x2 - x1
  let t1 := (-(min t (ε/norm v)/2))
  let t2 := ((min (1-t) (ε/norm v))/2)
  use t1 • v + x 
  use t2 • v + x

  have hx12 : x1 ≠ x2 := by
    intro h
    rw [←h, openSegment_same] at hxseg'
    exact (h.symm ▸ hne) (Set.eq_of_mem_singleton hxseg').symm (Set.eq_of_mem_singleton hxseg').symm

  have ht1pos: 0 < min t (ε / ‖x2 - x1‖) := lt_min ht.1 <| div_pos hε <| norm_sub_pos_iff.mpr (Ne.symm hx12)

  have ht2pos: 0 < min (1 - t) (ε / ‖x2 - x1‖) := 
    lt_min (by linarith [ht.2]) <| div_pos hε <| norm_sub_pos_iff.mpr (Ne.symm hx12)

  have ht1 : t1 < 0 := neg_lt_zero.mpr <| half_pos ht1pos
  have ht2 : 0 < t2 := half_pos ht2pos
  have ht12 : 0 < t2 - t1 := sub_pos.mpr <| lt_trans ht1 ht2

  constructor
  · -- x in the segment
    rw [openSegment_eq_image', Set.mem_image]
    refine ⟨ (-t1/(t2 - t1)), ?_, ?_ ⟩
    · 
      constructor
      · -- 1.
        rw [div_pos_iff]
        left
        exact ⟨ neg_pos_of_neg ht1, ht12 ⟩
      · -- 2.
        rw [div_lt_one_iff]
        left
        exact ⟨ ht12, neg_lt_sub_iff_lt_add.mpr <| lt_add_of_le_of_pos (le_refl _) ht2 ⟩
      done
    · 
      rw [smul_sub (-t1 / (t2 - t1)), smul_add (-t1 / (t2 - t1)), smul_smul, smul_add, smul_smul, 
        add_sub_add_comm, sub_self, add_zero, ←sub_smul, ←mul_sub, div_mul_cancel _ ?_, add_comm, 
        ← add_assoc, ← add_smul, neg_add_self, zero_smul, zero_add]
      exact Ne.symm (ne_of_lt ht12)
  

  -- intersection of convex is convex
  -- convex of 1d is segment

  constructor
  · -- 1. main proof
    rw [Set.subset_inter_iff]
    constructor
    · -- 1. smaller segment is in the segment
      have := @convex_openSegment ℝ _ _ _ _ x1 x2
      rw [convex_iff_segment_subset] at this
      apply this <;> clear this <;> rw [←htt] <;> 
      rw [@add_comm _ _ x1, ←add_assoc, ← add_smul, @add_comm _ _ _ t, openSegment_eq_image']
      · -- 1. first bound of the smaller segment is in the segment (boring ineq manipulation)
        exact ⟨ t + t1, 
          ⟨ lt_of_le_of_lt' (by linarith [min_le_left t (ε/norm v)] : t -t/2 ≤ t -(min t (ε /norm v)/2)) 
            (by linarith [ht.1]), lt_trans (add_lt_of_neg_right t ht1) ht.2 ⟩, 
          by simp only [ge_iff_le] ;rw [add_comm, @add_comm _ _ t t1, sub_eq_neg_add] ⟩
      · -- 2. second bound of the smaller segment is in the segment
        refine ⟨ t + t2,
          ⟨ lt_trans ht.1 (by linarith [ht2pos] : t < t + (min (1 - t) (ε / ‖x2 - x1‖) / 2)), ?_ ⟩,
          by simp only [ge_iff_le] ;rw [add_comm] ⟩
        exact lt_of_lt_of_le' (by linarith [ht.2]) (by linarith [min_le_left (1 - t) ((ε / ‖x2 - x1‖))] 
          : t + min (1 - t) (ε / ‖x2 - x1‖) / 2 ≤ t + ((1 - t) / 2))
      done
    · -- 2. smaller segment is in the ball
      clear ht hxseg' hne
      rw [← half_lt_self_iff] at hε
      apply (convex_iff_segment_subset.mp <| convex_ball x ε ) <;> rw [Metric.mem_ball] <;> norm_num <;>
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), ← min_div_div_right (by linarith), 
        Monotone.map_min fun _ _ => (mul_le_mul_right (norm_sub_pos_iff.mpr (Ne.symm hx12))).mpr] <;>
      apply min_lt_of_right_lt <;>
      rw [@div_mul_comm _ _ _ 2, mul_comm, 
        div_mul_div_cancel _ (Ne.symm (ne_of_lt (norm_sub_pos_iff.mpr (Ne.symm hx12))))] <;>
      exact hε
    done
  · -- 2. the smaller segment is not a singleton
    push_neg
    intro h1
    rcases (em (x1 = x)) with (rfl | _) <;> norm_num <;> intro h <;> rw [sub_eq_zero] at h <;> 
    cases' h with h h <;> try exact (ne_of_lt ht2pos) h.symm 
    all_goals {exact hx12 h.symm}
    done
  done


def Hpolytope.I (H_ : Set (Halfspace d)) (x : EuclideanSpace ℝ (Fin d)) : Set (Halfspace d) :=
  { Hi_ ∈ H_ | x ∈ (frontier <| SetLike.coe Hi_) }

lemma Hpolytope.I_mem {H_ : Set (Halfspace d)} (x : EuclideanSpace ℝ (Fin d)) : 
  ∀ Hi_, Hi_ ∈ Hpolytope.I H_ x ↔ Hi_ ∈ H_ ∧ x ∈ (frontier <| SetLike.coe Hi_) := by
  rintro Hi_ 
  unfold I
  rw [Set.mem_setOf]
  done

lemma Hpolytope.I_sub {H_ : Set (Halfspace d)} (x : EuclideanSpace ℝ (Fin d)) : 
  Hpolytope.I H_ x ⊆ H_ := by
  unfold Hpolytope.I
  simp only [Set.sep_subset]
  done

lemma ExtremePointsofHpolytope {H_ : Set (Halfspace d)} (hH_ : H_.Finite) :
  ∀ x ∈ Hpolytope hH_, x ∈ Set.extremePoints ℝ (Hpolytope hH_) ↔ 
  ⋂₀ ((frontier <| SetLike.coe ·) '' Hpolytope.I H_ x) = {x} := by
  rintro x hxH
  constructor
  · -- 1.
    intro hxEx
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨ fun HiS ⟨ Hi_, hHi_, h ⟩ => h ▸ hHi_.2, ?_ ⟩

    contrapose! hxEx
    rcases hxEx with ⟨ y, hy, hyx ⟩
    
    -- some useful results
    have hxyy : x ∈ openSegment ℝ ((2:ℝ) • x - y) y := by
      clear hyx hy hxH hH_ 
      rw [openSegment_eq_image, Set.mem_image]
      refine ⟨ 1/2, by norm_num, ?_ ⟩
      rw [(by norm_num : (1:ℝ) - 1 / 2 = 1 / 2), smul_sub, sub_add_cancel, smul_smul, 
        div_mul_cancel _ (by linarith), one_smul]
      done

    -- v is in halfspaces not in I by being inside a suitably small ball around x
    have hmemballmemIc : ∃ ε, ε > 0 ∧ ∀ v, v ∈ Metric.ball x ε → ∀ Hi_, Hi_ ∈ H_ \ Hpolytope.I H_ x → 
      v ∈ SetLike.coe Hi_ := by
      -- For all Hi ∉ I x, x is in the interior of Hi then we can fit a ball around x within Hi
      have hball : ∃ ε, ε > 0 ∧ Metric.ball x ε ⊆ ⋂₀ ((interior <| SetLike.coe ·) '' (H_ \ Hpolytope.I H_ x)) := by
        unfold Hpolytope at hxH
        have hxIcinterior : x ∈ ⋂₀ ((interior <| SetLike.coe ·) '' (H_ \ Hpolytope.I H_ x)) := by
          rintro HiS ⟨ Hi_, hHi_, rfl ⟩ 
          rw [Set.mem_diff, Hpolytope.I_mem, IsClosed.frontier_eq <| Halfspace_closed Hi_, 
            Set.mem_diff] at hHi_
          push_neg at hHi_
          exact hHi_.2 hHi_.1 <| hxH Hi_ ⟨ Hi_, hHi_.1, rfl ⟩
        
        have hIcinteriorOpen : IsOpen (⋂₀ ((interior <| SetLike.coe ·) '' (H_ \ Hpolytope.I H_ x))) := by
          apply Set.Finite.isOpen_sInter (Set.Finite.image _ (Set.Finite.diff hH_ _))
          exact fun _ ⟨ Hi_, _, h ⟩ => h ▸ isOpen_interior

        rw [Metric.isOpen_iff] at hIcinteriorOpen
        exact hIcinteriorOpen x hxIcinterior
      
      rcases hball with ⟨ ε, hε, hball ⟩
      refine ⟨ ε, hε, fun v hv Hi_ hHi_ => ?_ ⟩
      apply interior_subset
      exact (Set.mem_sInter.mp <| hball hv) (interior <| SetLike.coe Hi_) ⟨ Hi_, hHi_, rfl ⟩

    -- v is in halfspaces in I by being in the segment
    have hmemsegmemI : ∀ v, v ∈ segment ℝ ((2:ℝ) • x - y) y → ∀ Hi_, Hi_ ∈ Hpolytope.I H_ x → v ∈ SetLike.coe Hi_ := by
      rintro v hv Hi_ hHi_
      -- x & y are in the hyperplane
      rw [Set.mem_sInter] at hy
      specialize hy (frontier <| SetLike.coe Hi_) ⟨ Hi_, hHi_, rfl ⟩
      have hHi_2 := hHi_.2
      rw [frontierHalfspace_Hyperplane] at hy hHi_2

      -- v ∈ segment ℝ ((2:ℝ) • x - y) y ⊆ frontier Hi_ ⊆ Hi_
      apply IsClosed.frontier_subset <| Halfspace_closed Hi_
      rw [frontierHalfspace_Hyperplane]
      apply Set.mem_of_mem_of_subset hv
      apply (convex_iff_segment_subset.mp <| Hyperplane_convex Hi_) _ hy

      -- segment is in the hyperplane as hyperplane is closed under affine combination
      have h21 : Finset.sum Finset.univ ![(2:ℝ), -1] = 1 := by 
        rw [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        linarith
        done
      
      have h2x_y := Hyperplane_affineClosed Hi_ ![x, y] (by 
        rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty];
        exact Set.union_subset (Set.singleton_subset_iff.mpr hHi_2) (Set.singleton_subset_iff.mpr hy))
        ![2, -1] h21 

      rw [Finset.affineCombination_eq_linear_combination _ _ _ h21, Fin.sum_univ_two, Matrix.cons_val_zero, 
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one, 
        Matrix.head_cons, neg_one_smul, ← sub_eq_add_neg] at h2x_y
      exact h2x_y

    rw [mem_extremePoints]
    push_neg
    rintro hxH'
    rcases hmemballmemIc with ⟨ ε, hε, hmemballmemIc ⟩
    rcases hxSegBallInterSeg ((2:ℝ) • x - y) y ε ⟨ hxyy, fun h => hyx h.2 ⟩ hε with ⟨ x1, x2, hmem, hsub, hne ⟩
    push_neg at hne ; clear hxH' hε hyx hy hxH hxyy
    unfold Hpolytope

    refine ⟨ x1, ?_, x2, ?_, ⟨ hmem, hne ⟩ ⟩ <;> clear hmem hne <;>
    rw [Set.mem_sInter] <;>
    intro Hi_s hHi_s <;>
    rw [Set.mem_image] at hHi_s <;>
    rcases hHi_s with ⟨ Hi_, hHi_, rfl ⟩ 

    · -- x1 ∈ Hpolytope hH_
      specialize hsub (left_mem_segment ℝ x1 x2)
      rcases (em (Hi_ ∈ Hpolytope.I H_ x)) with (hinI | hninI)
      · 
        apply hmemsegmemI x1 ?_ Hi_ hinI
        apply openSegment_subset_segment
        exact Set.mem_of_mem_inter_left hsub
      · 
        have : Hi_ ∈ H_ \ Hpolytope.I H_ x := by
          rw [Set.mem_diff]
          exact ⟨ hHi_, hninI ⟩
        exact hmemballmemIc x1 (Set.mem_of_mem_inter_right hsub) Hi_ this
      done
    · -- x2 ∈ Hpolytope hH_
      specialize hsub (right_mem_segment ℝ x1 x2)
      rcases (em (Hi_ ∈ Hpolytope.I H_ x)) with (hinI | hninI)
      · 
        apply hmemsegmemI x2 ?_ Hi_ hinI
        apply openSegment_subset_segment
        exact Set.mem_of_mem_inter_left hsub
      ·
        have : Hi_ ∈ H_ \ Hpolytope.I H_ x := by
          rw [Set.mem_diff]
          exact ⟨ hHi_, hninI ⟩
        exact hmemballmemIc x2 (Set.mem_of_mem_inter_right hsub) Hi_ this
    done

  · -- 2.
    intro hinterx
    rw [mem_extremePoints]
    refine ⟨ hxH, λ x1 hx1 x2 hx2 hx => ?_ ⟩

    have : segment ℝ x1 x2 ⊆ {x} → x1 = x ∧ x2 = x := by
      rw [Set.Nonempty.subset_singleton_iff (Set.nonempty_of_mem (left_mem_segment ℝ x1 x2)), 
        Set.eq_singleton_iff_unique_mem]
      exact fun hseg => ⟨ hseg.2 x1 (left_mem_segment ℝ x1 x2), hseg.2 x2 (right_mem_segment ℝ x1 x2) ⟩
    apply this; clear this

    rw [← hinterx, Set.subset_sInter_iff]
    rintro HiS ⟨ Hi_, hHi_, rfl ⟩
    simp only

    have hfxα : Hi_.f.1 x = Hi_.α := by
      have : x ∈ {x} := by
        exact Set.mem_singleton x
      rw [← hinterx, Set.mem_sInter] at this
      specialize this (frontier <| SetLike.coe Hi_) ⟨ Hi_, hHi_, rfl ⟩
      rw [frontierHalfspace_Hyperplane, Set.mem_setOf] at this
      exact this
    clear hinterx hxH

    -- unpacking the fact that x1, x2 are in Hpolytope
    rw [mem_Hpolytope] at hx1 hx2
    specialize hx1 Hi_ hHi_.1
    specialize hx2 Hi_ hHi_.1
    clear hHi_ hH_ H_

    -- Frontier of a halfspace is convex
    rw [frontierHalfspace_Hyperplane]
    have := Hyperplane_convex Hi_
    rw [convex_iff_segment_subset] at this
    apply this <;> 
    clear this <;> 
    rw [Set.mem_setOf] <;> 
    by_contra h <;>
    -- Since dual is linear map, if there is one end with less than α, with equal to α at some point in the middle (at x),
    -- then the other end must be greater than α, contradition!
    push_neg at h <;>
    have hlt := lt_of_le_of_ne (by assumption) h <;> 
    clear h
    · -- If Hi_.f x1 < Hi_.α, then Hi_.f x2 > Hi_.α
      rw [openSegment_eq_image', Set.mem_image] at hx
      rcases hx with ⟨ t, ht, rfl ⟩
      rw [Hi_.f.1.map_add, Hi_.f.1.map_smul] at hfxα 

      have : Hi_.f.1 x1 + t • Hi_.f.1 (x2 - x1) + (1-t) • Hi_.f.1 (x2 - x1) > Hi_.α := by
        rw [hfxα, gt_iff_lt]
        exact lt_add_of_le_of_pos (by linarith) <| (smul_pos_iff_of_pos (by linarith [ht.2])).mpr <|
         (smul_pos_iff_of_pos ht.1).mp <| pos_of_lt_add_right <| hfxα.symm ▸ hlt

      rw [add_assoc, ← add_smul, add_sub, add_comm t 1, add_sub_cancel, one_smul, ← Hi_.f.1.map_add, add_comm, sub_add_cancel] at this
      linarith
      done
    · -- If Hi_.f x2 < Hi_.α, then Hi_.f x1 > Hi_.α
      rw [openSegment_symm, openSegment_eq_image', Set.mem_image] at hx
      rcases hx with ⟨ t, ht, rfl ⟩
      rw [Hi_.f.1.map_add, Hi_.f.1.map_smul] at hfxα 

      have : Hi_.f.1 x2 + t • Hi_.f.1 (x1 - x2) + (1-t) • Hi_.f.1 (x1 - x2) > Hi_.α := by
        rw [hfxα, gt_iff_lt]
        exact lt_add_of_le_of_pos (by linarith) <| (smul_pos_iff_of_pos (by linarith [ht.2])).mpr <|
         (smul_pos_iff_of_pos ht.1).mp <| pos_of_lt_add_right <| hfxα.symm ▸ hlt
      
      rw [add_assoc, ← add_smul, add_sub, add_comm t 1, add_sub_cancel, one_smul, ← Hi_.f.1.map_add, add_comm, sub_add_cancel] at this
      linarith
      done
  done


lemma DualOfVpolytope_compactHpolytope {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Finite) 
  (hS0 : 0 ∈ interior (Vpolytope hS))
  : ∃ (H_ : Set (Halfspace d)) (hH_ : H_.Finite), 
  Hpolytope hH_ = polarDual (Vpolytope hS) ∧ IsCompact (Hpolytope hH_):= by
  -- Last statment follows from polarDual_origin
  suffices hHeqVdual : ∃ (H_ : Set (Halfspace d)) (hH_ : H_.Finite), 
    Hpolytope hH_ = polarDual (Vpolytope hS) from by
    rcases hHeqVdual with ⟨H_, hH_, hHeqVdual⟩
    refine ⟨ H_, hH_, hHeqVdual, ?_ ⟩
    exact hHeqVdual ▸ (polarDual_compact_if (Closed_Vpolytope hS) (Convex_Vpolytope hS) hS0) 
  
  -- main proof
  use pointDual '' (Subtype.val ⁻¹' (S \ {0}))
  use (by 
    apply Set.Finite.image
    apply Set.Finite.preimage _ _
    apply Set.injOn_of_injective
    exact Subtype.val_injective
    exact Set.Finite.diff hS {0}
    done)
  apply subset_antisymm
  · -- hard direction
    -- take x from Hpolytope of nonzero elements of S
    intro x hx
    -- Special treatment for x = 0
    cases' (em (x = 0)) with h h
    ·
      rw [h]
      exact polarDual_origin (Vpolytope hS)
    
    rw [mem_Hpolytope] at hx
    rw [mem_polarDual]
    intro p hp 


    /- 
      Magic: Since inner product is commutative over ℝ,
      DON'T imagine as x in each of the dual halfspaces of each s in S,
      instead, imagine S sitting inside the dual halfspace of x.
      halfspaces are convex hence Vpolytope of S sits inside the halfspace. QED
    -/
    let x' := (⟨ x, h ⟩ : { p : EuclideanSpace ℝ (Fin ↑d) // p ≠ 0 })
    have hx' : ↑x' = x := rfl
    rw [← hx', real_inner_comm, ←mem_pointDual]

    suffices h : S ⊆ SetLike.coe (pointDual x') from by
      apply convexHull_min h <| Halfspace_convex (pointDual x')
      exact hp

    -- Since x is in dual halfspace of each s in S, s is in dual halfspace of x
    intro s hs
    cases' (em (s = 0)) with h h
    ·
      exact h ▸ pointDual_origin x'

    specialize hx (pointDual ⟨ s, h ⟩) (Set.mem_image_of_mem _ ?_)
    · 
      rw [Set.mem_preimage, Subtype.coe_mk, Set.mem_diff]
      exact ⟨ hs, h ⟩
  
    rw [← Halfspace_mem, mem_pointDual, Subtype.coe_mk] at hx
    rw [mem_pointDual, Subtype.coe_mk, real_inner_comm]
    exact hx
    done
  
  · -- easy direction, simply need to show it is set intersection of a smaller set
    apply Set.sInter_subset_sInter
    apply Set.image_subset
    apply Set.image_subset
    rw [Set.preimage_subset_preimage_iff]
    apply subset_trans (by simp)  <| subset_convexHull _ _
    rw [Subtype.range_coe_subtype]
    intro x hx
    rw [Set.mem_diff, Set.mem_singleton_iff] at hx
    rw [Set.mem_setOf]
    exact hx.2
  done

lemma Vpolytope_of_Hpolytope : ∀ {H_ : Set (Halfspace d)} (hH_ : H_.Finite), IsCompact (Hpolytope hH_) → 
  ∃ (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Finite), Hpolytope hH_ = Vpolytope hS := by
  intro H_ hH_ hHcpt
  
  have hExHFinite: Set.Finite <| Set.extremePoints ℝ (Hpolytope hH_) := by
    have := ExtremePointsofHpolytope hH_ 

    let f := fun T : Set (Halfspace d) => ⋂₀ ((frontier <| SetLike.coe · ) '' T)
    let g : EuclideanSpace ℝ (Fin ↑d) ↪ Set (EuclideanSpace ℝ (Fin ↑d)) :=
      ⟨ fun x : EuclideanSpace ℝ (Fin ↑d) => Set.singleton x, Set.singleton_injective ⟩     

    -- power set of H_ is finite
    rcases Set.Finite.exists_finset_coe hH_ with ⟨ Hfin, hHfin ⟩
    let PHfin := Hfin.powerset
    let PH := Finset.toSet '' PHfin.toSet
    have hPH : PH.Finite := Set.Finite.image _ <| Finset.finite_toSet PHfin

    -- f '' (power set of H_) is finite
    have hfPH : Set.Finite <| f '' PH := Set.Finite.image f hPH

    -- g '' (Set.extremePoints ℝ (Hpolytope hH_)) ⊆ f '' (power set of H_) hence finite
    have hgfPH : g '' (Set.extremePoints ℝ (Hpolytope hH_)) ⊆ f '' PH := by
      intro Sx hSx
      rcases hSx with ⟨ x, hx, rfl ⟩
      change {x} ∈ f '' PH
      rw [Set.mem_image]
      refine ⟨ Hpolytope.I H_ x, ?_, ?_ ⟩
      · -- x ∈ Hpolytope hH_
        rw [Set.mem_image]
        rcases Set.Finite.exists_finset_coe (Set.Finite.subset hH_ (Hpolytope.I_sub x)) with ⟨ Ifin, hIfin ⟩
        refine ⟨ Ifin, ?_, hIfin ⟩
        rw [Finset.mem_coe, Finset.mem_powerset, ← Finset.coe_subset, hHfin, hIfin]
        exact Hpolytope.I_sub x
      · -- sInter of I H_ x is {x}
        rw [← ExtremePointsofHpolytope hH_ x (extremePoints_subset hx)]
        exact hx
      done

    have hgExFin : Set.Finite <| g '' (Set.extremePoints ℝ (Hpolytope hH_)) := Set.Finite.subset hfPH hgfPH

    -- Since g is embedding, Set.extremePoints ℝ (Hpolytope hH_) is finite
    have := Set.Finite.preimage_embedding g hgExFin
    rw [Function.Injective.preimage_image] at this
    exact this
    exact g.2
    done

  have := closure_convexHull_extremePoints hHcpt (Convex_Hpolytope hH_)
  have hVcl := Closed_Vpolytope hExHFinite
  rw [IsClosed.closure_eq] at this
  rw [← this]
  use Set.extremePoints ℝ (Hpolytope hH_)
  use hExHFinite
  rfl
  exact hVcl
  done

lemma Hpolytope_of_Vpolytope_0interior {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Finite) 
  (hV0 : 0 ∈ interior (Vpolytope hS)): 
  ∃ (H_ : Set (Halfspace d)) (hH_ : H_.Finite), Hpolytope hH_ = Vpolytope hS := by
  rcases DualOfVpolytope_compactHpolytope hS hV0 with ⟨ H_, hH_, hH_eq, hH_cpt ⟩
  rcases Vpolytope_of_Hpolytope hH_ hH_cpt with ⟨ S', hS', hS'eq ⟩
  have : 0 ∈ interior (Vpolytope hS') := by
    rw [←hS'eq, hH_eq, compact_polarDual_iff (Closed_Vpolytope hS)]
    exact Compact_Vpolytope hS
  rcases DualOfVpolytope_compactHpolytope hS' this with ⟨ H_', hH_', hH_'eq, _ ⟩
  refine ⟨ H_', hH_', ?_ ⟩
  rw [hH_'eq, ←hS'eq, hH_eq, doublePolarDual_self (Closed_Vpolytope hS) (Convex_Vpolytope hS) (interior_subset hV0)]
  done

lemma translationHomeo (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d) where
  toFun := (· + x)
  invFun := (· + -x)
  left_inv := fun y => by simp
  right_inv := fun y => by simp
  continuous_toFun := by continuity
  continuous_invFun := by continuity
  
lemma translationHomeo.toFun.def (x : EuclideanSpace ℝ (Fin d)) : 
  ↑(translationHomeo x) = (· + x) := by
  unfold translationHomeo
  simp
  done

lemma Hpolytope_of_Vpolytope_interior {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Finite) 
  (hVinterior : Set.Nonempty <| interior (Vpolytope hS)):
  ∃ (H_ : Set (Halfspace d)) (hH_ : H_.Finite), Hpolytope hH_ = Vpolytope hS := by
  let S' := S + {-hVinterior.some}
  have hS' : S'.Finite := by exact (Set.translation.Finite hS (-hVinterior.some))

  have : 0 ∈ interior (Vpolytope hS') := by
    rw [Vpolytope_translation hS, Set.add_singleton, ]
    have := @Homeomorph.image_interior _ _ _ _ (translationHomeo (-hVinterior.some)) (Vpolytope hS)
    rw [translationHomeo.toFun.def] at this
    rw [← this]; clear this
    rw [← Set.add_singleton, Set.mem_translation, neg_neg, zero_add]
    exact hVinterior.some_mem
    done

  rcases Hpolytope_of_Vpolytope_0interior hS' this with ⟨ H_', hH_', hH_'eq ⟩
  let H_ := (Halfspace_translation hVinterior.some) '' H_'
  have hH_ : H_.Finite := Set.Finite.image _ hH_'
  
  use H_
  use hH_
  ext x
  rw [Hpolytope_translation, hH_'eq, Vpolytope_translation, Set.neg_add_cancel_right']
  done