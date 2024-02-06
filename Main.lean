import «src».Polytope


variable {E  : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
open Pointwise PolarFunctional

set_option maxHeartbeats 400000
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

/-
Let 𝑋 be a closed convex subset of ℝ^𝑑. Then:
• 𝑋 is a 𝑉-polytope if it is the convex hull of a finite point set.
• 𝑋 is an 𝐻-polytope if it is the intersection of finitely many half spaces.

Theorem : Every 𝑉-polytope is an 𝐻-polytope, and every compact 𝐻-polytope is a 𝑉-polytope.
-/

-- As a ball around x is convex, it must contain a segment with x in its interior
lemma hxSegBallInterSeg : ∀ (x1 x2 : E) (ε : ℝ), x ∈ openSegment ℝ x1 x2 ∧ ¬ (x1 = x ∧ x2 = x) →
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


def Hpolytope.I (H_ : Set (PolarFunctional E)) (x : E) : Set (PolarFunctional E) :=
  { Hi_ ∈ H_ | x ∈ frontier Hi_.le_halfspace }

lemma Hpolytope.I_mem {H_ : Set (PolarFunctional E)} (x : E) :
  ∀ Hi_, Hi_ ∈ Hpolytope.I H_ x ↔ Hi_ ∈ H_ ∧ x ∈ frontier Hi_.le_halfspace := by
  rintro Hi_
  unfold I
  rw [Set.mem_setOf]
  done

lemma Hpolytope.I_sub {H_ : Set (PolarFunctional E)} (x : E) :
  Hpolytope.I H_ x ⊆ H_ := by
  unfold Hpolytope.I
  simp only [Set.sep_subset]
  done

lemma ExtremePointsofHpolytope (H_ : Set (PolarFunctional E)) [Fact H_.Finite] :
  ∀ x ∈ Hpolytope H_, x ∈ Set.extremePoints ℝ (Hpolytope H_) ↔
  ⋂₀ ((frontier ·.le_halfspace) '' Hpolytope.I H_ x) = {x} := by
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
      clear hyx hy hxH
      rw [openSegment_eq_image, Set.mem_image]
      refine ⟨ 1/2, by norm_num, ?_ ⟩
      rw [(by norm_num : (1:ℝ) - 1 / 2 = 1 / 2), smul_sub, sub_add_cancel, smul_smul,
        div_mul_cancel _ (by linarith), one_smul]
      done

    -- v is in halfspaces not in I by being inside a suitably small ball around x
    have hmemballmemIc : ∃ ε, ε > 0 ∧ ∀ v, v ∈ Metric.ball x ε → ∀ Hi_, Hi_ ∈ H_ \ Hpolytope.I H_ x →
      v ∈ Hi_.le_halfspace := by
      -- For all Hi ∉ I x, x is in the interior of Hi then we can fit a ball around x within Hi
      have hball : ∃ ε, ε > 0 ∧ Metric.ball x ε ⊆ ⋂₀ ((interior ·.le_halfspace) '' (H_ \ Hpolytope.I H_ x)) := by
        unfold Hpolytope at hxH
        have hxIcinterior : x ∈ ⋂₀ ((interior ·.le_halfspace) '' (H_ \ Hpolytope.I H_ x)) := by
          rintro HiS ⟨ Hi_, hHi_, rfl ⟩
          rw [Set.mem_diff, Hpolytope.I_mem, IsClosed.frontier_eq <| le_halfspace_closed Hi_,
            Set.mem_diff] at hHi_
          push_neg at hHi_
          exact hHi_.2 hHi_.1 <| hxH Hi_.le_halfspace ⟨ Hi_, hHi_.1, rfl ⟩

        have hIcinteriorOpen : IsOpen (⋂₀ ((interior ·.le_halfspace) '' (H_ \ Hpolytope.I H_ x))) := by
          apply Set.Finite.isOpen_sInter Fact.out
          exact fun _ ⟨ Hi_, _, h ⟩ => h ▸ isOpen_interior

        rw [Metric.isOpen_iff] at hIcinteriorOpen
        exact hIcinteriorOpen x hxIcinterior

      rcases hball with ⟨ ε, hε, hball ⟩
      refine ⟨ ε, hε, fun v hv Hi_ hHi_ => ?_ ⟩
      apply interior_subset
      exact (Set.mem_sInter.mp <| hball hv) (interior Hi_.le_halfspace) ⟨ Hi_, hHi_, rfl ⟩

    -- v is in halfspaces in I by being in the segment
    have hmemsegmemI : ∀ v, v ∈ segment ℝ ((2:ℝ) • x - y) y → ∀ Hi_, Hi_ ∈ Hpolytope.I H_ x → v ∈ Hi_.le_halfspace := by
      rintro v hv Hi_ hHi_
      -- x & y are in the hyperplane
      rw [Set.mem_sInter] at hy
      specialize hy (frontier Hi_.le_halfspace) ⟨ Hi_, hHi_, rfl ⟩
      have hHi_2 := hHi_.2
      rw [frontier_le_Halfspace_eq_Hyperplane] at hy hHi_2

      -- v ∈ segment ℝ ((2:ℝ) • x - y) y ⊆ frontier Hi_ ⊆ Hi_
      apply IsClosed.frontier_subset <| le_halfspace_closed Hi_
      rw [frontier_le_Halfspace_eq_Hyperplane]
      apply Set.mem_of_mem_of_subset hv
      apply (convex_iff_segment_subset.mp <| hyperplane_convex Hi_) _ hy

      -- segment is in the hyperplane as hyperplane is closed under affine combination
      have h21 : Finset.sum Finset.univ ![(2:ℝ), -1] = 1 := by
        rw [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        linarith
        done

      have h2x_y := hyperplane_affineClosed Hi_ ![x, y] (by
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
      specialize this (frontier Hi_.le_halfspace) ⟨ Hi_, hHi_, rfl ⟩
      rw [frontier_le_Halfspace_eq_Hyperplane, hyperplane_mem_iff] at this
      exact this
    clear hinterx hxH

    -- unpacking the fact that x1, x2 are in Hpolytope
    rw [Hpolytope.mem_iff] at hx1 hx2
    specialize hx1 Hi_ hHi_.1
    specialize hx2 Hi_ hHi_.1
    clear! hHi_

    -- Frontier of a halfspace is convex
    rw [frontier_le_Halfspace_eq_Hyperplane]
    have := hyperplane_convex Hi_
    rw [convex_iff_segment_subset] at this
    apply this <;>
    clear this <;>
    rw [hyperplane_mem_iff] <;>
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
        exact lt_add_of_le_of_pos (by linarith) <| (smul_pos_iff_of_pos_left (by linarith [ht.2])).mpr <|
         (smul_pos_iff_of_pos_left ht.1).mp <| pos_of_lt_add_right <| hfxα.symm ▸ hlt

      rw [add_assoc, ← add_smul, add_sub, add_comm t 1, add_sub_cancel, one_smul, ← Hi_.f.1.map_add, add_comm, sub_add_cancel] at this
      linarith
      done
    · -- If Hi_.f x2 < Hi_.α, then Hi_.f x1 > Hi_.α
      rw [openSegment_symm, openSegment_eq_image', Set.mem_image] at hx
      rcases hx with ⟨ t, ht, rfl ⟩
      rw [Hi_.f.1.map_add, Hi_.f.1.map_smul] at hfxα

      have : Hi_.f.1 x2 + t • Hi_.f.1 (x1 - x2) + (1-t) • Hi_.f.1 (x1 - x2) > Hi_.α := by
        rw [hfxα, gt_iff_lt]
        exact lt_add_of_le_of_pos (by linarith) <| (smul_pos_iff_of_pos_left (by linarith [ht.2])).mpr <|
         (smul_pos_iff_of_pos_left ht.1).mp <| pos_of_lt_add_right <| hfxα.symm ▸ hlt

      rw [add_assoc, ← add_smul, add_sub, add_comm t 1, add_sub_cancel, one_smul, ← Hi_.f.1.map_add, add_comm, sub_add_cancel] at this
      linarith
      done
  done


lemma DualOfVpolytope_compactHpolytope [FiniteDimensional ℝ E] {S : Set E} [Fact S.Finite]
  (hS0 : 0 ∈ interior (Vpolytope S))
  : ∃ (H_ : Set (PolarFunctional E)) ,
  Fact H_.Finite ∧ Hpolytope H_ = polarDual (Vpolytope S) ∧ IsCompact (Hpolytope H_):= by
  -- Last statment follows from polarDual_origin
  suffices hHeqVdual : ∃ (H_ : Set (PolarFunctional E)),
    Fact H_.Finite ∧ Hpolytope H_ = polarDual (Vpolytope S) from by
    rcases hHeqVdual with ⟨H_, hH_, hHeqVdual⟩
    refine ⟨ H_, hH_, hHeqVdual, ?_ ⟩
    rwa [hHeqVdual, ← zero_mem_interior_polarDual_iff_compact (polarDual_closed _), doublePolarDual_self (Closed_Vpolytope S) (Convex_Vpolytope S)]
    exact interior_subset hS0

  -- main proof
  use pointDual '' (Subtype.val ⁻¹' (S \ {0}))
  use (by infer_instance)

  apply subset_antisymm
  · -- hard direction
    -- take x from Hpolytope of nonzero elements of S
    intro x hx
    -- Special treatment for x = 0
    cases' (em (x = 0)) with h h
    ·
      rw [h]
      exact polarDual_origin_mem (Vpolytope S)

    rw [Hpolytope.mem_iff] at hx
    rw [polarDual_mem_iff]
    intro p hp


    /-
      Magic: Since inner product is commutative over ℝ,
      DON'T imagine as x in each of the dual halfspaces of each s in S,
      instead, imagine S sitting inside the dual halfspace of x.
      halfspaces are convex hence Vpolytope of S sits inside the halfspace. QED
    -/
    let x' := (⟨ x, h ⟩ : { p : E // p ≠ 0 })
    have hx' : ↑x' = x := rfl
    rw [← hx', real_inner_comm, ← pointDual_mem_iff]

    suffices h : S ⊆ (pointDual x').le_halfspace from by
      apply convexHull_min h <| le_halfspace_convex (pointDual x')
      exact hp

    -- Since x is in dual halfspace of each s in S, s is in dual halfspace of x
    intro s hs
    cases' (em (s = 0)) with h h
    ·
      exact h ▸ pointDual_origin_mem x'

    specialize hx (pointDual ⟨ s, h ⟩) (Set.mem_image_of_mem _ ?_)
    ·
      rw [Set.mem_preimage, Subtype.coe_mk, Set.mem_diff]
      exact ⟨ hs, h ⟩

    rw [← le_halfspace_mem_iff, pointDual_mem_iff, Subtype.coe_mk] at hx
    rw [pointDual_mem_iff, Subtype.coe_mk, real_inner_comm]
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

lemma Vpolytope_of_Hpolytope {H_ : Set (PolarFunctional E)} [Fact H_.Finite]
  (hHcpt : IsCompact (Hpolytope H_)) :
  ∃ (S : Set E) (hS : Fact (Set.Finite S)), Hpolytope H_ = Vpolytope S := by

  have hExHFinite: Fact <| Set.Finite <| Set.extremePoints ℝ (Hpolytope H_) := by
    have := ExtremePointsofHpolytope H_

    let f := fun T : Set (PolarFunctional E) => ⋂₀ ((frontier ·.le_halfspace ) '' T)
    let g : E ↪ Set E :=
      ⟨ fun x : E => Set.singleton x, Set.singleton_injective ⟩

    -- power set of H_ is finite
    rcases Set.Finite.exists_finset_coe (Fact.out : H_.Finite) with ⟨ Hfin, hHfin ⟩
    let PHfin := Hfin.powerset
    let PH := Finset.toSet '' PHfin.toSet
    have hPH : Fact PH.Finite := Fact.mk <| Set.Finite.image _ <| Finset.finite_toSet PHfin

    -- -- f '' (power set of H_) is finite
    -- have hfPH : Set.Finite <| f '' PH := Set.Finite.image f hPH

    -- g '' (Set.extremePoints ℝ (Hpolytope hH_)) ⊆ f '' (power set of H_) hence finite
    have hgfPH : g '' (Set.extremePoints ℝ (Hpolytope H_)) ⊆ f '' PH := by
      intro Sx hSx
      rcases hSx with ⟨ x, hx, rfl ⟩
      change {x} ∈ f '' PH
      rw [Set.mem_image]
      refine ⟨ Hpolytope.I H_ x, ?_, ?_ ⟩
      · -- x ∈ Hpolytope hH_
        rw [Set.mem_image]
        rcases Set.Finite.exists_finset_coe (Set.Finite.subset (Fact.out : H_.Finite) (Hpolytope.I_sub x)) with ⟨ Ifin, hIfin ⟩
        refine ⟨ Ifin, ?_, hIfin ⟩
        rw [Finset.mem_coe, Finset.mem_powerset, ← Finset.coe_subset, hHfin, hIfin]
        exact Hpolytope.I_sub x
      · -- sInter of I H_ x is {x}
        rw [← ExtremePointsofHpolytope H_ x (extremePoints_subset hx)]
        exact hx
      done

    have hgExFin : Set.Finite <| g '' (Set.extremePoints ℝ (Hpolytope H_)) := Set.Finite.subset (by infer_instance : Fact _).out hgfPH

    -- Since g is embedding, Set.extremePoints ℝ (Hpolytope hH_) is finite
    have := Set.Finite.preimage_embedding g hgExFin
    rw [Function.Injective.preimage_image] at this
    exact Fact.mk this
    exact g.2
    done

  have := closure_convexHull_extremePoints hHcpt (Hpolytope.Convex H_)
  have hVcl := @Closed_Vpolytope _ _ _ (Set.extremePoints ℝ (Hpolytope H_))
  rw [IsClosed.closure_eq] at this
  rw [← this]
  use Set.extremePoints ℝ (Hpolytope H_)
  use hExHFinite
  rfl
  exact hVcl
  done

theorem Hpolytope_of_Vpolytope_subsingleton [FiniteDimensional ℝ E] [Nontrivial E] {S : Set E}
  [Fact S.Finite] (hStrivial : Set.Subsingleton S):
    ∃ (H_ : Set (PolarFunctional E)), Fact H_.Finite ∧ Hpolytope H_ = Vpolytope S := by
  cases' Set.Subsingleton.eq_empty_or_singleton hStrivial with hSempty hSsingleton
  ·
    rw [Vpolytope, hSempty, convexHull_empty]
    rcases @Hpolytope.exist_finite_empty E _ _ _ with ⟨ H_, hH_Fin, hHempty ⟩
    exact ⟨ H_, hH_Fin, hHempty ⟩
  ·
    rcases hSsingleton with ⟨ x, hx ⟩
    rcases @origin_Hpolytope E _ _ _ _ with ⟨ H_, hH_Fin, hH_ ⟩
    refine ⟨ (·.translation x) '' H_, by infer_instance, ?_ ⟩
    rw [Vpolytope, hx, convexHull_singleton, Hpolytope.translation_eq, hH_,
      Set.singleton_add_singleton, zero_add]
  done

lemma Hpolytope_of_Vpolytope_0interior [FiniteDimensional ℝ E] {S : Set E} [Fact S.Finite]
  (hV0 : 0 ∈ interior (Vpolytope S)):
  ∃ (H_ : Set (PolarFunctional E)), Fact H_.Finite ∧ Hpolytope H_ = Vpolytope S := by
  rcases DualOfVpolytope_compactHpolytope hV0 with ⟨ H_, hH_, hH_eq, hH_cpt ⟩
  rcases Vpolytope_of_Hpolytope hH_cpt with ⟨ S', hS', hS'eq ⟩
  have : 0 ∈ interior (Vpolytope S') := by
    rw [←hS'eq, hH_eq, zero_mem_interior_polarDual_iff_compact (Closed_Vpolytope S)]
    exact Compact_Vpolytope S
  rcases DualOfVpolytope_compactHpolytope this with ⟨ H_', hH_', hH_'eq, _ ⟩
  refine ⟨ H_', hH_', ?_ ⟩
  rw [hH_'eq, ←hS'eq, hH_eq, doublePolarDual_self (Closed_Vpolytope S) (Convex_Vpolytope S) (interior_subset hV0)]
  done

lemma translationHomeo (x : E) : E ≃ₜ E where
  toFun := (· + x)
  invFun := (· + -x)
  left_inv := fun y => by simp
  right_inv := fun y => by simp
  continuous_toFun := by continuity
  continuous_invFun := by continuity

lemma translationHomeo.toFun.def (x : E) :
  ↑(translationHomeo x) = (· + x) := by
  unfold translationHomeo
  simp
  done

lemma Hpolytope_of_Vpolytope_interior [FiniteDimensional ℝ E] {S : Set E} [Fact S.Finite]
  (hVinterior : Set.Nonempty <| interior (Vpolytope S)):
  ∃ (H_ : Set (PolarFunctional E)), Fact H_.Finite ∧ Hpolytope H_ = Vpolytope S := by
  let S' := S + {-hVinterior.some}

  have : 0 ∈ interior (Vpolytope S') := by
    rw [Vpolytope_translation S, Set.add_singleton, ]
    have := @Homeomorph.image_interior _ _ _ _ (translationHomeo (-hVinterior.some)) (Vpolytope S)
    rw [translationHomeo.toFun.def] at this
    rw [← this]; clear this
    rw [← Set.add_singleton, Set.mem_translation, zero_sub,  neg_neg]
    exact hVinterior.some_mem
    done

  rcases Hpolytope_of_Vpolytope_0interior this with ⟨ H_', hH_', hH_'eq ⟩
  let H_ := (·.translation hVinterior.some) '' H_'

  refine ⟨ H_, by infer_instance, ?_ ⟩
  ext x
  rw [Hpolytope.translation_eq, hH_'eq, Vpolytope_translation S, ← Set.sub_eq_neg_add,
    Set.neg_add_cancel_right' (Set.Nonempty.some hVinterior)]
  done

variable {P : Type} [PseudoMetricSpace P] [NormedAddTorsor E P] [FiniteDimensional ℝ E]


lemma Vpolytope_of_Vpolytope_inter_cutSpace_fin {S : Set E} [Fact S.Finite]
  (hVinterior : Set.Nonempty (interior (Vpolytope S))) {H_ : Set (PolarFunctional E)} [Fact H_.Finite] :
  ∃ (S' : Set E) (hS : Fact (Set.Finite S')), Vpolytope S' = Vpolytope S ∩ Hpolytope H_ := by
  rcases Hpolytope_of_Vpolytope_interior hVinterior with ⟨ H_', hH_', hHV ⟩
  have hH_inter := Hpolytope.inter_eq H_' H_
  have : IsCompact (Vpolytope S ∩ Hpolytope H_) := IsCompact.inter_right (Compact_Vpolytope S) (Hpolytope.Closed H_)
  rw [← hHV, ← hH_inter] at this
  rcases Vpolytope_of_Hpolytope this with ⟨ S', hS', hSV ⟩
  exact ⟨ S', hS', by rw [← hSV, ← hHV, ← hH_inter] ⟩
  done

lemma InDown_eq_DownIn {p : AffineSubspace ℝ P} [Nonempty { x // x ∈ p }] {S : Set P} (x : p):
  (AffineIsometryEquiv.VSubconst ℝ x) '' ((@Subtype.val P (fun x => x ∈ p)) ⁻¹' S) =
  (@Subtype.val E fun x => x ∈ p.direction) ⁻¹' (S -ᵥ ({x.1} : Set P)) := by
  ext y
  rw [AffineIsometryEquiv.coe_VSubconst, Set.vsub_singleton, Set.mem_image, Set.mem_preimage, Set.mem_image]
  constructor
  ·
    rintro ⟨ v, h, rfl ⟩
    rw [Set.mem_preimage] at h
    refine ⟨ v, h, rfl ⟩
  ·
    rintro ⟨ v, h, h1 ⟩
    have := y.2
    rw [← h1, AffineSubspace.vsub_right_mem_direction_iff_mem x.2] at this
    refine ⟨ ⟨ v, this ⟩, h, ?_ ⟩
    have : v = (⟨ v, this ⟩ : { x // x ∈ p }).1 := rfl
    conv at h1 in v => rw [this]
    rw [← AffineSubspace.coe_vsub] at h1
    exact Subtype.val_injective h1
  done


lemma Nonempty_iff_Nonempty_interior_in_direction {S : Set E}{s : E} (hs : s ∈ S) (hS : Nonempty S) :
    (interior ((@AffineIsometryEquiv.VSubconst ℝ (affineSpan ℝ S).direction (affineSpan ℝ S) _ _ _ _ (AffineSubspace.toNormedAddTorsor (affineSpan ℝ (S))) ⟨ s, by apply subset_affineSpan; exact hs ⟩ ) ''
      ((@Subtype.val E fun x => x ∈ (affineSpan ℝ S)) ⁻¹' ((convexHull ℝ) S)))).Nonempty := by
  rw [Set.nonempty_coe_sort, ← @convexHull_nonempty_iff ℝ, ← intrinsicInterior_nonempty (convex_convexHull ℝ S),
    intrinsicInterior, Set.image_nonempty, affineSpan_convexHull] at hS
  rw [ ← AffineIsometryEquiv.coe_toHomeomorph, ← Homeomorph.image_interior, Set.image_nonempty]
  exact hS


theorem MainTheoremOfPolytopes [FiniteDimensional ℝ E] [Nontrivial E] :
  (∀ (S : Set E) [Fact S.Finite], ∃ (H_ : Set (PolarFunctional E)),
    Fact H_.Finite ∧ Hpolytope H_ = Vpolytope S) ∧
  ∀ {H_ : Set (PolarFunctional E)} [Fact H_.Finite], IsCompact (Hpolytope H_) →
  ∃ (S : Set E) (hS : S.Finite), Hpolytope H_ = Vpolytope S := by
  constructor
  · -- 1.
    intro S hS
    /-
    1. ConvexHull always have an intrinsic interior
    2. Any AffineSubspaces are intersections of hyperplanes
    3. Any hyperplane is an intersection of two Halfspaces
    4. Take union of the set of Halfspaces for Hpolytope in the affineSpan and for the affineSpan
    -/
    cases' em (S.Nontrivial) with hSnontrivial hStrivial
    · -- S is nontrivial
      -- Instance set up
      have := Set.nontrivial_coe_sort.mpr hSnontrivial
      have hSnonempty := Set.Nontrivial.nonempty hSnontrivial
      have := Set.nonempty_coe_sort.mpr hSnonempty

      rcases (Set.Nontrivial.nonempty hSnontrivial) with ⟨ s, hs ⟩
      have hsaff : s ∈ affineSpan ℝ S := by apply subset_affineSpan; exact hs
      let SpanS := affineSpan ℝ S
      let s' : SpanS := ⟨ s, hsaff ⟩

      rcases (Nonempty_iff_Nonempty_interior_in_direction hs this) with ⟨ x, hx ⟩

      have : ∃ S', Fact S'.Finite ∧ convexHull ℝ S' = (AffineIsometryEquiv.VSubconst ℝ s') '' ((@Subtype.val E fun x => x ∈ SpanS) ⁻¹' ((convexHull ℝ) S : Set E)) := by
        rw [InDown_eq_DownIn, ← @convexHull_singleton ℝ, Set.vsub_eq_sub, ← convexHull_sub,
          ← Submodule.coeSubtype]
        refine ⟨ Subtype.val ⁻¹' (S - {s}), by rw [Set.sub_singleton]; infer_instance, ?_ ⟩
        rw [← Submodule.coeSubtype, ← LinearMap.coe_toAffineMap, ← AffineMap.preimage_convexHull]
        all_goals (try rw [AffineMap.toFun_eq_coe])
        all_goals rw [LinearMap.coe_toAffineMap, Submodule.coeSubtype]
        exact Subtype.val_injective

        rw [Subtype.range_coe_subtype]
        exact AffineSubspace.direction_subset_subset (subset_affineSpan ℝ S)
          (subset_trans (Set.singleton_subset_iff.mpr hs) (subset_affineSpan ℝ S))
        done


      rcases this with ⟨ S', hS'Fin, hS'eq ⟩
      rw [← hS'eq] at hx
      have hS' : Set.Nonempty (interior (Vpolytope S')) := Set.nonempty_of_mem hx

      rcases @Hpolytope_of_Vpolytope_interior SpanS.direction _ _ _ _ _ hS'Fin hS' with ⟨ H_''1, hH''1, hHV ⟩

      let H_'1 : Set (PolarFunctional E) := (@PolarFunctional.extend _ _ _ SpanS.direction _) '' H_''1

      rcases Submodule_cutspace SpanS.direction with ⟨ H_'2, hH_'2, hH_'2Span' ⟩
      have hH_'2Span: Hpolytope H_'2 = SpanS.direction := hH_'2Span'.symm; clear hH_'2Span'

      let H_' : Set (PolarFunctional E) := (·.translation s) '' (H_'1 ∪ H_'2)
      have hH_'12 := Hpolytope.inter_eq H_'1 H_'2

      have : Nontrivial SpanS.direction := by
        apply AffineSubspace.direction_nontrivial_of_nontrivial
        exact affineSpan_nontrivial ℝ (Set.nontrivial_coe_sort.mpr hSnontrivial)

      refine ⟨ H_', by infer_instance, ?_ ⟩

      rw [Hpolytope.translation_eq, hH_'12, hH_'2Span, Hpolytope, ← Set.sInter_inter_comm, Set.image_image,
        Set.image_image, @Set.image_congr' _ _ _ _ (H_''1) (@extend_le_halfspace_inter_subspace_eq_le_halfspace _ _ _ SpanS.direction _),
        ← Set.image_image, Set.sInter_image, ← Set.image_sInter ?_ (Subtype.val_injective)]
      change Subtype.val '' Hpolytope H_''1 + {s} = Vpolytope S
      rw [hHV, Vpolytope, hS'eq]
      change Subtype.val '' ((AffineIsometryEquiv.toHomeomorph (AffineIsometryEquiv.VSubconst ℝ s')) '' (Subtype.val ⁻¹' (convexHull ℝ) S)) + {s} = Vpolytope S
      rw [AffineIsometryEquiv.coe_toHomeomorph]

      rw [InDown_eq_DownIn, Set.vsub_eq_sub]
      change ((↑) : SpanS.direction → E) '' (((↑) : SpanS.direction → E) ⁻¹' ((convexHull ℝ) S - {s})) + {s} = Vpolytope S
      rw [Subtype.image_preimage_coe, Set.inter_eq_self_of_subset_left ?_, Set.neg_add_cancel_right', Vpolytope]
      exact AffineSubspace.direction_subset_subset (convexHull_subset_affineSpan S)
              (subset_trans (Set.singleton_subset_iff.mpr hs) (subset_affineSpan ℝ S))

      -- In case Span of S has dim = 0
      all_goals (apply Set.Nonempty.image)
      all_goals (try (change Set.Nonempty (Halfspace.val (AffineSubspace.direction SpanS) '' H_''1)))
      all_goals (try apply Set.Nonempty.image)
      all_goals (by_contra h)
      all_goals (rw [Set.not_nonempty_iff_eq_empty] at h)
      all_goals (rw [Hpolytope, h, Set.image_empty, Set.sInter_empty] at hHV)
      all_goals (exact IsCompact.ne_univ (Compact_Vpolytope S') hHV.symm)
      done

    · -- S is trivial
      rw [Set.not_nontrivial_iff] at hStrivial
      exact Hpolytope_of_Vpolytope_subsingleton hStrivial
  · -- 2.
    exact Vpolytope_of_Hpolytope
  done
