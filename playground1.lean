import «Chapter2» 
import «Chapter3» 
import «Main»


variable {d : ℕ+}
open Pointwise


lemma DualOfVpolytope_compactHpolytope' {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Finite) 
  (hS0 : 0 ∈ interior (Vpolytope hS))
  : ∃ (H_ : Set (Halfspace d)) (hH_ : H_.Finite), 
  Hpolytope hH_ = polarDual (Vpolytope hS) ∧ 0 ∈ Hpolytope hH_ ∧ IsCompact (Hpolytope hH_):= by
  -- Last statment follows from polarDual_origin
  suffices hHeqVdual : ∃ (H_ : Set (Halfspace d)) (hH_ : H_.Finite), 
    Hpolytope hH_ = polarDual (Vpolytope hS) from by
    rcases hHeqVdual with ⟨H_, hH_, hHeqVdual⟩
    have hHcpt : IsCompact (Hpolytope hH_) := sorry
    use H_, hH_, hHeqVdual
    refine ⟨ ?_, hHcpt ⟩
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
  done


lemma Vpolytope_of_Hpolytope : ∀ {H_ : Set (Halfspace d)} (hH_ : H_.Finite), IsCompact (Hpolytope hH_) → 
  ∃ (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Finite), Hpolytope hH_ = Vpolytope hS := by
  intro H_ hH_ hHcpt
  have := closure_convexHull_extremePoints hHcpt (Convex_Hpolytope hH_)
  have hExHFinite: Set.Finite <| Set.extremePoints ℝ (Hpolytope hH_) := by
    have := ExtremePointsofHpolytope hH_ 
    sorry
    done
    
  have hVcl := Closed_Vpolytope hExHFinite
  rw [IsClosed.closure_eq ] at this
  rw [← this]
  use Set.extremePoints ℝ (Hpolytope hH_)
  use hExHFinite
  rfl
  exact hVcl
  done
  
theorem MainTheoremOfPolytopes : 
  (∀ (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Finite), ∃ (H_ : Set (Halfspace d)) (hH_ : H_.Finite), 
    Hpolytope hH_ = Vpolytope hS) ∧ 
  ∀ {H_ : Set (Halfspace d)} (hH_ : H_.Finite), IsCompact (Hpolytope hH_) → 
  ∃ (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Finite), Hpolytope hH_ = Vpolytope hS := by
  constructor
  · -- 1.
    intro S hS
    cases' (em (interior (Vpolytope hS)).Nonempty) with hVpolytopeIntEmpty hVpolytopeIntNonempty
    · -- Interior is nonempty 
      let S' := (fun x => x - hVpolytopeIntEmpty.some) '' S
      have hS' : S'.Finite := by exact Set.Finite.image (fun x => x - Set.Nonempty.some hVpolytopeIntEmpty) hS

      have : 0 ∈ interior (Vpolytope hS') := by
        sorry
        done
      rcases DualOfVpolytope_compactHpolytope hS' this with ⟨ H_, hH_, hH_eq, hH_0, hH_cpt ⟩
      rcases Vpolytope_of_Hpolytope hH_ hH_cpt with ⟨ S'', hS'', hS''eq ⟩
      have : 0 ∈ interior (Vpolytope hS'') := by
        sorry
        done
      rcases DualOfVpolytope_compactHpolytope hS'' this with ⟨ H_', hH_', hH_'eq, hH_'0, hH_'cpt ⟩
      use H_' 
      use hH_'
      rw [hH_'eq, ←hS''eq, hH_eq]
      -- Double polar and done!
      sorry
      done
    · -- Interior is empty
      sorry
      done
  · -- 2.
    exact Vpolytope_of_Hpolytope
  done

