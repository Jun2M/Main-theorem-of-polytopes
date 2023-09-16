import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Convex.Independent

set_option maxHeartbeats 1000000

variable {d : ℕ+}

theorem DimensionalEquivalence {S : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d))} {n : ℕ+}
  [Nonempty S] (B_S : AffineBasis (Fin (n+1)) ℝ S) : 
  S ≃ (EuclideanSpace ℝ (Fin n)) := by
  refine ⟨fun x i => AffineBasis.coord B_S (Fin.succ i) x,
      fun u => (Finset.affineCombination ℝ Finset.univ B_S) (fun (i : Fin (n+1)) => 
      dite (i = 0) (fun h => 1-Finset.univ.sum (u ·)) fun h => u (Fin.pred i h)),
      ?_, ?_⟩
  ·
    sorry
    -- intro x
    -- simp only [Fin.succ_pred, dite_eq_ite, Finset.mem_univ]
    -- ext i
    -- have : (fun i =>
    --     if i = 0 then 1 - Finset.sum Finset.univ fun x_1 => (AffineBasis.coord B_S (Fin.succ x_1)) x
    --     else (AffineBasis.coord B_S i) x) = fun i => AffineBasis.coord B_S i x := by 
    --   ext i
    --   cases' em (i = 0) with h h
    --   ·
    --     simp only [h, ite_true]
    --     sorry
    --     done
    --   ·
    --     simp only [h, ite_false]
    --     done
    --   done
    -- rw [this, AffineBasis.affineCombination_coord_eq_self]
    -- done
  · 
    intro u
    simp only [Finset.mem_univ, not_true]
    ext i
    rw [AffineBasis.coord_apply_combination_of_mem B_S (Finset.mem_univ (Fin.succ i))]
    cases' em (Fin.succ i = 0) with h h
    ·
      simp only [h, dite_true]
      sorry
      done
    ·
      simp [h, dite_false]
      rw [Fin.pred_succ]
      done
    ·
      rw [Finset.sum_mk]
      sorry
      done 
  done

-- theorem segmentequiv {x y : EuclideanSpace ℝ (Fin d)} (hxy : x ≠ y) :
--   Set.Icc (0:ℝ) 1 ≃ segment ℝ x y := by
--   have hnorm : @HPow.hPow ℝ ℕ ℝ instHPow (norm (y - x)) (2:ℕ) ≠ 0 := by
--     apply Ne.symm
--     apply ne_of_lt
--     rw [sq_pos_iff, norm_ne_zero_iff, sub_ne_zero]
--     exact Ne.symm hxy

--   let f : Set.Icc (0:ℝ) 1 → segment ℝ x y := by
--     rintro ⟨t, ht⟩
--     use AffineMap.lineMap x y t
--     rw [segment_eq_image_lineMap]
--     use t
--     done
--   let f1 : segment ℝ x y → Set.Icc (0:ℝ) 1 := by
--     rintro ⟨v, hv⟩
--     use (inner (v -ᵥ x) (y -ᵥ x)) / (@HPow.hPow ℝ ℕ ℝ instHPow (norm (y -ᵥ x)) (2:ℕ))
--     rcases hv with ⟨a, b, ha, hb, hab, rfl⟩
--     have hbIcc : b ∈ Set.Icc 0 1 := by
--       rw [Set.mem_Icc]
--       refine ⟨ hb, ?_ ⟩
--       have : b = 1 - a := by linarith
--       rw [this]; clear this
--       linarith
--       done
--     rw [vsub_eq_sub, vsub_eq_sub, add_sub_right_comm]
--     have : a • x - x = (a - 1) • x := by rw [sub_smul, one_smul, sub_eq_add_neg, add_comm]
--     rw [this, inner_add_left, inner_smul_left, inner_smul_left, IsROrC.conj_to_real, 
--       IsROrC.conj_to_real]; clear this
--     have : a - 1 = - b := by linarith
--     rw [this, neg_mul_comm, ← inner_neg_left, ← left_distrib, add_comm, ←inner_add_left, 
--       ←sub_eq_add_neg, inner_self_eq_norm_sq_to_K, IsROrC.ofReal_real_eq_id, id_eq, 
--         @mul_div_cancel ℝ _ (@HPow.hPow ℝ ℕ ℝ instHPow (norm (y - x)) (2:ℕ)) b hnorm] ; clear this hab ha a
--     exact hbIcc

--   refine ⟨ f, f1, ?_, ?_ ⟩
--   · 
--     rintro ⟨t, ht⟩
--     simp only [vsub_eq_sub, IsROrC.inner_apply, map_sub, IsROrC.conj_to_real, Subtype.mk.injEq]
--     rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
--     simp only [add_sub_cancel, smul_eq_mul, IsROrC.inner_apply, map_mul, IsROrC.conj_to_real, map_sub]
--     rw [inner_smul_left, inner_self_eq_norm_sq_to_K, IsROrC.ofReal_real_eq_id, id_eq, 
--       IsROrC.conj_to_real, @mul_div_cancel ℝ _ (@HPow.hPow ℝ ℕ ℝ instHPow (norm (y - x)) (2:ℕ)) t hnorm]
--     done
--   · 
--     rintro ⟨v, hv⟩
--     rw [segment, Set.mem_setOf] at hv
--     rcases hv with ⟨a, b, ha, hb, hab, rfl⟩
--     simp only [vsub_eq_sub, IsROrC.inner_apply, map_sub, IsROrC.conj_to_real, smul_eq_mul, Subtype.mk.injEq]
--     rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_sub_right_comm]
--     have : a • x - x = (a - 1) • x := by rw [sub_smul, one_smul, sub_eq_add_neg, add_comm]
--     rw [this, inner_add_left, inner_smul_left, inner_smul_left, IsROrC.conj_to_real, 
--       IsROrC.conj_to_real]; clear this
--     have : a - 1 = - b := by linarith
--     rw [this, neg_mul_comm, ← inner_neg_left, ← left_distrib, ←inner_add_left]; clear this
--     have : -x + y = y - x := by rw [add_comm, ←sub_eq_add_neg]
--     rw [this, inner_self_eq_norm_sq_to_K, IsROrC.ofReal_real_eq_id, id_eq, 
--       @mul_div_cancel ℝ _ (@HPow.hPow ℝ ℕ ℝ instHPow (norm (y - x)) (2:ℕ)) b hnorm]; clear this
--     have : a = 1 - b := by linarith
--     rw [this, smul_sub, sub_smul, one_smul, sub_eq_neg_add, sub_eq_neg_add, add_assoc]; clear this
--     have : b • y + x = x + b • y := by rw [add_comm]
--     rw [this, add_assoc]
--   done

-- theorem segmentHomeomorph {x y : EuclideanSpace ℝ (Fin d)} (hxy : x ≠ y) :
--   Homeomorph (Set.Icc (0:ℝ) 1) (segment ℝ x y) := by
--   refine ⟨segmentequiv hxy, ?_, ?_⟩
--   ·
--     unfold segmentequiv 
--     simp only
--     apply Continuous.subtype_mk
--     rw [continuous_def]
--     intro s hs
--     rw [isOpen_induced_iff]
    
--     --LinearMap.continuous_of_finiteDimensional
--     done

--   · 
--     done 
--   done