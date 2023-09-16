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
      use (min 1 ε/norm (x1 - x)) • (x1 - x) + x 
      use (min 1 ε/norm (x2 - x)) • (x2 - x) + x
      constructor
      · -- 1.
        sorry
        done
      · -- 2.
        push_neg at hne
        push_neg
        rcases (em (x1 = x)) with (rfl | hne1)
        · 
          simp only [forall_true_left] at hne
          rw [sub_self, smul_zero, zero_add, eq_self, true_implies]
          contrapose! hne
          norm_num at hne
          cases' hne with h h
          ·
            exfalso
            rw [min_eq_iff] at h
            cases' h with h h
            linarith
            linarith
          · 
            rw [sub_eq_zero] at h
            exact h
        ·
          intro h
          exfalso
        done
      -- convex_ball Convex.openSegment_subset
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


