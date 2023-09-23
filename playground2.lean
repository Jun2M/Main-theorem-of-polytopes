import «Chapter2» 
import «Chapter3» 
import «Main»


variable {d : ℕ+}





-- Extreme points of H polytope is finite

-- lemma line_of_pair_linearmap  {k : Type u_1} {V : Type u_2} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] (v1 v2 : V) 
--   (f : V →ₗ[𝕜] 𝕜) : f v1 = a ∧ f v2 = a ↔ f '' (Set.range (@AffineMap.lineMap 𝕜 _ _ _ _ _ _ v1 v2)) = {a} := by
--   constructor
--   · 
--     rintro ⟨ h1, h2 ⟩
--     ext x
--     constructor
--     · -- 1.
--       rintro ⟨ v, hv, rfl ⟩
--       rw [Set.mem_singleton_iff]
--       rw [Set.mem_range] at hv
--       rcases hv with ⟨ t, rfl ⟩
--       rw [AffineMap.lineMap_apply_module]
--       rw [f.map_add, f.map_smul, h1, f.map_smul, h2, ← add_smul, sub_add_cancel, one_smul]
--       done
--     · -- 2.
--       rintro rfl; clear h2
--       rw [Set.mem_image]
--       refine ⟨ v1, ?_, h1 ⟩
--       rw [Set.mem_range]
--       use (0:𝕜)
--       rw [AffineMap.lineMap_apply_zero]
--       done
--   · 
--     rintro h
--     have h1 : f v1 ∈ f '' Set.range (@AffineMap.lineMap 𝕜 _ _ _ _ _ _ v1 v2) := by
--       apply Set.mem_image_of_mem
--       rw [Set.mem_range]
--       exact ⟨ 0, AffineMap.lineMap_apply_zero v1 v2 ⟩ 
--     rw [h] at h1

--     have h2 : f v2 ∈ f '' Set.range (@AffineMap.lineMap 𝕜 _ _ _ _ _ _ v1 v2) := by
--       apply Set.mem_image_of_mem
--       rw [Set.mem_range]
--       exact ⟨ 1, AffineMap.lineMap_apply_one v1 v2 ⟩ 
--     rw [h] at h2

--     rw [Set.mem_singleton_iff] at h1 h2
--     exact ⟨ h1, h2 ⟩
--   done

-- instance Halfspace.instSetLike {d : ℕ+} :
--   SetLike (Halfspace d) (EuclideanSpace ℝ (Fin d)) where
--   coe := Halfspace.S
--   coe_injective' := by
--     intro H1 H2 hH12
--     rcases H1 with ⟨⟨f1, hf1⟩, α1, S1, rfl⟩
--     rcases H2 with ⟨⟨f2, hf2⟩, α2, S2, rfl⟩
--     simp at hH12
--     congr <;> rw [Set.ext_iff] at hH12
    
    -- unfold NormedSpace.Dual at f1 f2
    -- rw [← LinearIsometryEquiv.map_eq_iff (InnerProductSpace.toDual ℝ _).symm]
    -- let x := (LinearIsometryEquiv.symm (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin ↑d)))) f1
    -- have hx : f1 = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin ↑d))) x := by simp

    -- rw [hx, @InnerProductSpace.toDual_apply ℝ (EuclideanSpace ℝ (Fin ↑d)) _ _ _ _ x] at hH12
    -- done





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