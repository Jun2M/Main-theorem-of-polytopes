import «Chapter2»


variable {d : ℕ+}

/-
Let 𝑋 be a closed convex subset of ℝ^𝑑. Then:
• 𝑋 is a 𝑉-polytope if it is the convex hull of a finite point set.
• 𝑋 is an 𝐻-polytope if it is the intersection of finitely many half spaces.

Theorem : Every 𝑉-polytope is an 𝐻-polytope, and every compact 𝐻-polytope is a 𝑉-polytope.
-/

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
  (hI : ∀ x, I x ⊆ H_ ∧ ∀ Hi, Hi ∈ I x ↔ x ∈ frontier Hi.S) :
  ∀ x ∈ Hpolytope hH_, x ∈ Set.extremePoints ℝ (Hpolytope hH_) ↔ ⋂₀ ((frontier ·.S) '' I x) = {x} := by
  rintro x hxH
  constructor
  · -- 1.
    intro hxEx
    -- rw [mem_extremePoints] at hxEx
    rw [Set.eq_singleton_iff_unique_mem]
    have hxI : x ∈ ⋂₀ ((fun x => frontier x.S) '' I x) := by
      rw [Set.mem_sInter]
      rintro HiS ⟨ Hi_, hHi_, rfl ⟩ 
      rw [(hI x).2] at hHi_
      exact hHi_
    refine ⟨ hxI, ?_ ⟩
    contrapose! hxEx

    -- if not 0 dim, it much be more than 1 dim

    -- For all Hi ∉ I x, x is in the interior of Hi.S then we can fit a ball around x within Hi.S
    have hball : ∃ ε, ε > 0 ∧ Metric.ball x ε ⊆ ⋂₀ ((fun x => interior x.S) '' (H_ \ I x)) := by
      unfold Hpolytope at hxH
      have hxIcinterior : x ∈ ⋂₀ ((fun x => interior x.S) '' (H_ \ I x)) := by
        rw [Set.mem_sInter]
        rintro HiS ⟨ Hi_, hHi_, rfl ⟩ 
        rw [Set.mem_sInter] at hxH
        rw [Set.mem_diff, (hI x).2 Hi_] at hHi_
        specialize hxH Hi_.S ?_
        · 
          rw [Set.mem_image]
          exact ⟨ Hi_, hHi_.1, rfl ⟩

        rw [IsClosed.frontier_eq <| Halfspace_closed Hi_, Set.mem_diff] at hHi_
        push_neg at hHi_
        exact hHi_.2 hxH
      
      have hIcinteriorOpen : IsOpen (⋂₀ ((fun x => interior x.S) '' (H_ \ I x))) := by
        apply Set.Finite.isOpen_sInter (Set.Finite.image _ (Set.Finite.diff hH_ _))
        rintro _ ⟨ Hi_, hHi_, rfl ⟩
        exact isOpen_interior

      rw [Metric.isOpen_iff] at hIcinteriorOpen
      exact hIcinteriorOpen x hxIcinterior
    
    -- As a ball around x is convex, it must contain a segment with x in its interior
    have hxSegBallInterSeg : ∀ x1 x2 ε, x ∈ openSegment ℝ x1 x2 ∧ ¬ (x1 = x ∧ x2 = x) → 0 < ε → 
      ∃ x1' x2', openSegment ℝ x1' x2' ⊆ openSegment ℝ x1 x2 ∩ Metric.ball x ε ∧ ¬ (x1' = x ∧ x2' = x) := by 
      rintro x1 x2 ε ⟨ hxseg, hne ⟩ hε 
      push_neg at hne
      have hxseg' := hxseg
      rw [openSegment_eq_image', Set.mem_image] at hxseg
      rcases hxseg with ⟨ t, ht, htt ⟩ 
      let t1 := (-(min t (ε/norm (x2 - x1))/2))
      let t2 := ((min (1-t) (ε/norm (x2 - x1)))/2)
      use t1 • (x2 - x1) + x 
      use t2 • (x2 - x1) + x

      have hx12 : x1 ≠ x2 := by
        intro h
        rw [←h, openSegment_same] at hxseg'
        rw [←h] at hne
        exact hne (Set.eq_of_mem_singleton hxseg').symm (Set.eq_of_mem_singleton hxseg').symm

      have ht1pos: 0 < min t (ε / ‖x2 - x1‖) := by
        simp only [ge_iff_le, lt_min_iff]
        constructor
        linarith [ht.1]
        rw [div_pos_iff]
        left
        exact ⟨ hε, norm_sub_pos_iff.mpr (Ne.symm hx12) ⟩

      have ht2pos: 0 < min (1 - t) (ε / ‖x2 - x1‖) := by
        apply lt_min
        linarith [ht.2]
        rw [div_pos_iff]
        left
        exact ⟨ hε, norm_sub_pos_iff.mpr (Ne.symm hx12) ⟩

      constructor
      · -- 1. main proof
        rw [Set.subset_inter_iff]
        constructor
        · -- 1. smaller segment is in the segment
          have := @convex_openSegment ℝ _ _ _ _ x1 x2
          rw [convex_iff_openSegment_subset] at this
          apply this <;> clear this <;> rw [←htt] <;> 
          rw [@add_comm _ _ x1, ←add_assoc, ← add_smul, @add_comm _ _ _ t, openSegment_eq_image']
          · -- 1. first bound of the smaller segment is in the segment (boring ineq manipulation)
            exact ⟨ t + t1, 
              ⟨ lt_of_le_of_lt' (by linarith [min_le_left t (ε/norm (x2 - x1))] : t -t/2 ≤ t -(min t (ε / ‖x2-x1‖)/2)) 
                  (by linarith [ht.1]),
                lt_trans (by linarith [ht1pos] : t + (-(min t (ε/norm (x2 - x1))/2)) < t) ht.2 ⟩, 
              by simp only [ge_iff_le] ;rw [add_comm, @add_comm _ _ t t1, sub_eq_neg_add] ⟩
          · -- 2. second bound of the smaller segment is in the segment
            refine ⟨ t + t2,
              ⟨ lt_trans ht.1 (by linarith [ht2pos] : t < t + (min (1 - t) (ε / ‖x2 - x1‖) / 2)), ?_ ⟩,
              by simp only [ge_iff_le] ;rw [add_comm] ⟩
            exact lt_of_lt_of_le' (by linarith [ht.2]) 
              (by linarith [min_le_left (1 - t) ((ε / ‖x2 - x1‖))] : t + min (1 - t) (ε / ‖x2 - x1‖) / 2 ≤ t + ((1 - t) / 2))
          done
        · -- 2. smaller segment is in the ball
          clear ht hxseg' hne hball hxEx hxI hxH hI I hH_ H_
          rw [← half_lt_self_iff] at hε
          have := convex_ball x ε
          rw [convex_iff_openSegment_subset] at this
          apply this <;> clear this <;> rw [Metric.mem_ball] <;> norm_num <;>
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
        rcases (em (x1 = x)) with (rfl | hne1) <;> norm_num <;> intro h <;> rw [sub_eq_zero] at h <;> 
        cases' h with h h <;> try exact (ne_of_lt ht2pos) h.symm
        exact hx12 h.symm
        exact hx12 h.symm
        done
      done

    -- Finishing up
    rcases hxEx with ⟨ y, hy, hyx ⟩

    rw [mem_extremePoints]
    push_neg
    rintro hxH'
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

    rw [← hinterx, Set.subset_sInter_iff]; clear hinterx
    rintro HiS ⟨ Hi_, hHi_, rfl ⟩
    simp only
    rw [frontierHalfspace_Hyperplane, Set.subset_def]
    intro y hy

    unfold Hpolytope at hx1 hx2
    rw [Set.mem_sInter] at hx1 hx2
    have := Set.mem_image_of_mem (·.S) (Set.mem_of_subset_of_mem (hI x).1 hHi_)
    specialize hx1 Hi_.S this
    specialize hx2 Hi_.S this
    rw [(hI x).2, frontierHalfspace_Hyperplane, Set.mem_setOf ] at hHi_; clear this

    rw [Set.mem_setOf]
    by_contra h
    push_neg at h

    suffices ∃ t' : ℝ, t' ∈ Set.Icc 0 1 ∧ Hi_.f.1 ((AffineMap.lineMap x1 x2) t') > Hi_.α by
      rcases this with ⟨ t', ht', ht'α ⟩
      have h' := Set.mem_of_subset_of_mem (Convex.segment_subset (Halfspace_convex Hi_) hx1 hx2) (?_ : (AffineMap.lineMap x1 x2) t' ∈ segment ℝ x1 x2)
      rw [Halfspace_mem Hi_, ←not_lt ] at h'
      exact h' ht'α 

      rw [segment_eq_image_lineMap]
      exact Set.mem_image_of_mem _ ht'
      done
    
    cases' (lt_or_gt_of_ne h) with h h
    · 
      rw [←hHi_] at h
      rcases (Metric.isOpen_iff.mp (sorry : IsOpen (openSegment ℝ x1 x2))) x hx with ⟨ ε, hε, hεx ⟩
      rw [openSegment_eq_image_lineMap, Set.mem_image] at hx
      rcases hx with ⟨ t', ht', ht'x ⟩
      sorry
      done 
    · 
      rw [segment_eq_image_lineMap, Set.mem_image] at hy
      rcases hy with ⟨ t, ht, rfl ⟩
      exact ⟨ t, ht, h ⟩ 
  done


