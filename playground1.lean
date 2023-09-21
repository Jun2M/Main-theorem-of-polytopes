import «Chapter2» 
import «Chapter3» 
import «Main»


variable {d : ℕ+}


-- origin condition not needed?
lemma DualOfVpolytope_compactHpolytope {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Finite)
  : ∃ (H : Set (Halfspace d)) (h : H.Finite), 
  Hpolytope h = polarDual (Vpolytope hS) ∧ 0 ∈ Hpolytope h := by
  -- Last statment follows from polarDual_origin
  suffices hHeqVdual : ∃ (H : Set (Halfspace d)) (h : H.Finite), Hpolytope h = polarDual (Vpolytope hS) from by
    rcases hHeqVdual with ⟨H, hH, hHeqVdual⟩
    use H, hH, hHeqVdual
    rw [hHeqVdual]
    exact polarDual_origin (Vpolytope hS)
    done
  
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

    suffices h : S ⊆ (pointDual x').S from by
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
  
  · -- easy direction, simply need to show it is intersection of smaller sets
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