import «Chapter2» 
import «Chapter3» 
import «Main»


variable {d : ℕ+}


lemma DualOfVpolytope_compactHpolytope {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Finite)
  (horigin : 0 ∈ interior (Vpolytope hS)) : ∃ (H : Set (Halfspace d)) (h : H.Finite), 
  Hpolytope h = polarDual (Vpolytope hS) ∧ 0 ∈ Hpolytope h := by
  -- Last statment follows from polarDual_origin
  suffices hHeqVdual : ∃ (H : Set (Halfspace d)) (h : H.Finite), Hpolytope h = polarDual (Vpolytope hS) from by
    rcases hHeqVdual with ⟨H, hH, hHeqVdual⟩
    use H, hH, hHeqVdual
    rw [hHeqVdual]
    exact polarDual_origin (Vpolytope hS)
    done
  
  use pointDual '' (Subtype.val ⁻¹' (S \ {0}))
  use (by 
    apply Set.Finite.image
    apply Set.Finite.preimage _ _
    apply Set.injOn_of_injective
    exact Subtype.val_injective
    exact Set.Finite.diff hS {0}
    done)
  apply subset_antisymm
  · 
    /-For the other direction, we use the Minkowski-Carathéodory Theorem 2.34. If 0≠𝑦 ∈𝑋∗, then
    ⟨𝑦,𝑥⟩≤1 (all𝑥 ∈𝑋 )
    However, since 𝑥 ↦ ⟨𝑦,𝑥⟩ is a non-zero linear form (and 𝑋 is full-dimensional), it takes its max-
    imum over 𝑋 on some proper face and hence at an extremepoint of 𝑋 (Exercise4.1below).
    Hence, for any 𝑥 ∈𝑋 , and 𝑦 in the rhs, we have
    ⟨𝑦,𝑥⟩≤( max 1≤𝑖≤𝑛 ⟨𝑦,𝑥𝑖⟩) ≤ 1
    so 𝑦 ∈ 𝑋 ∗. This is the other containment we needed to prove.
    For compactness, we note that if 𝑋∗ is non-compact, then by closedness and convexity, there
    is some 𝑦 ∈𝑋 ∗ so that 𝛼𝑦 ∈𝑋∗ for all 𝛼 ≥0. The only way this could happen is if ⟨𝑦,𝑥𝑖⟩ ≤ 0 for
    all 𝑥𝑖, contradicting that 0 is in the interior of 𝑋.
    -/
    intro x hx
    cases' (em (x = 0)) with h h
    ·
      rw [h]
      exact polarDual_origin (Vpolytope hS)
    
    rw [mem_Hpolytope] at hx
    rw [mem_polarDual]
    intro p hp 
    

    done
  · 
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
  done