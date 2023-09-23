import «Chapter2» 
import «Chapter3» 
import «Main»


variable {d : ℕ+}
open Pointwise


lemma Vpolytope_of_Hpolytope : ∀ {H_ : Set (Halfspace d)} (hH_ : H_.Finite), IsCompact (Hpolytope hH_) → 
  ∃ (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Finite), Hpolytope hH_ = Vpolytope hS := by
  intro H_ hH_ hHcpt
  
  have hExHFinite: Set.Finite <| Set.extremePoints ℝ (Hpolytope hH_) := by
    have := ExtremePointsofHpolytope hH_ 

    let f := fun T : Set (Halfspace d) => ⋂₀ ((fun x => frontier x.S) '' T)
    let g : EuclideanSpace ℝ (Fin ↑d) ↪ Set (EuclideanSpace ℝ (Fin ↑d)) :=
      ⟨ fun x : EuclideanSpace ℝ (Fin ↑d) => Set.singleton x, Set.singleton_injective ⟩     
    
    -- power set of H_ is finite
    -- f '' (power set of H_) is finite
    -- g '' (Set.extremePoints ℝ (Hpolytope hH_)) ⊆ f '' (power set of H_) hence finite
    -- Since g is embedding, Set.extremePoints ℝ (Hpolytope hH_) is finite
    
    sorry
    done

  have := closure_convexHull_extremePoints hHcpt (Convex_Hpolytope hH_)

  have hVcl := Closed_Vpolytope hExHFinite

  rw [IsClosed.closure_eq ] at this
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
    done
  rcases DualOfVpolytope_compactHpolytope hS' this with ⟨ H_', hH_', hH_'eq, hH_'cpt ⟩
  use H_'
  use hH_'
  rw [hH_'eq, ←hS'eq, hH_eq, doublePolarDual_self (Closed_Vpolytope hS) (Convex_Vpolytope hS) (interior_subset hV0)]
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

      rcases Hpolytope_of_Vpolytope_0interior hS' this with ⟨ H_', hH_', hH_'eq ⟩
      let H_ := (Halfspace_translation hVpolytopeIntEmpty.some) '' H_'
      have hH_ : H_.Finite := by exact Set.Finite.image (Halfspace_translation hVpolytopeIntEmpty.some).Injective hH_'
      use H_' 
      use hH_'
      rw [hH_'eq, ←hS''eq, hH_eq]
      -- Double polar and done!
      rw [doublePolarDual_self]
      
      done
    · -- Interior is empty
      sorry
      done
  · -- 2.
    exact Vpolytope_of_Hpolytope
  done

