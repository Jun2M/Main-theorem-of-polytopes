import «Chapter2» 
import «Chapter3» 
import «Main»


variable {d : ℕ+}

  
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
      have hH_ : H_.Finite := Set.Finite.image _ hH_'
      
      use H_
      use hH_
      
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

