import «Chapter2» 
import «Main»











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
--   openSegment ℝ x y = intrinsicInterior ℝ (segment ℝ x y) := by
--   apply subset_antisymm
--   · -- 1.
--     intro z hz
--     rw [intrinsicInterior, Set.mem_image]
--     let z' : { x_2 // x_2 ∈ ↑(affineSpan ℝ (segment ℝ x y)) } := ⟨ z, ?_ ⟩ 
--     refine ⟨ z', ?_ , rfl ⟩
--     rw [mem_interior]
--     refine ⟨ Metric.ball z' ((min (dist z x) (dist z y))/2) , ?_, 
--       Metric.isOpen_ball, Metric.mem_ball_self ?_ ⟩
--     · 
--       intro w hw
--       rw [Set.mem_preimage]
--       rw [Metric.mem_ball, dist_comm] at hw
--       apply openSegment_subset_segment
--       rw [openSegment, Set.mem_setOf] at hz
--       rcases hz with ⟨ a, b, ha, hb, hab, hz ⟩
--       have := w.property
--       rw [← SetLike.mem_coe, coe_affineSpan, spanPoints, Set.mem_setOf] at this
--       rcases this with ⟨ w1, hw1, w2, hw2, hw ⟩
--       done

--     done
--   · -- 2.
--     sorry
--     done

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

  -- Metric.mem_closure_iff  
  -- 1. get basis for hyperplane
  -- 2. get a point in interior of Hi_
  -- 3. combine them to get a basis for entire space
  -- done

-- lemma HalfspaceIntrinsicFrontier (H_ : Halfspace d) : intrinsicFrontier ℝ H_.S = frontier H_.S := by
--   rw [intrinsicFrontier]
--   sorry
--   done