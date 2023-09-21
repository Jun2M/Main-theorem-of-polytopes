import «Chapter2» 
import «Chapter3» 
import «Main»


variable {d : ℕ+}


lemma Vpolytope_of_Hpolytope : ∀ (H : Finset (Halfspace d)), IsCompact (Hpolytope H) → ∃ (S : Finset (EuclideanSpace ℝ (Fin d))),
  Hpolytope H = Vpolytope S := by
  intro H hHcpt
  have := closure_convexHull_extremePoints hHcpt (Convex_Hpolytope H)
  have hExHFinite: Set.Finite <| Set.extremePoints ℝ (Hpolytope H) := sorry
  rcases Set.Finite.exists_finset_coe hExHFinite with ⟨ ExH, hExH ⟩
  have hVcl := Closed_Vpolytope ExH
  rw [IsClosed.closure_eq ] at this
  rw [← this]
  use ExH
  rw [← hExH]
  rfl
  rw [← hExH]
  exact hVcl
  done
  
theorem MainTheoremOfPolytopes : 
  (∀ (S : Finset (EuclideanSpace ℝ (Fin d))), ∃ (H : Finset (Halfspace d)), Hpolytope H = Vpolytope S) ∧ 
  ∀ (H : Finset (Halfspace d)), IsCompact (Hpolytope H) → ∃ (S : Finset (EuclideanSpace ℝ (Fin d))),
  Hpolytope H = Vpolytope S := by
  constructor
  · -- 1.
    intro S
    rcases DualOfVpolytope_compactHpolytope S with ⟨ H, hH, hH0 ⟩
    have : IsCompact (Hpolytope H) := by
      rw [hH]
      exact 
      done
    rcases Vpolytope_of_Hpolytope H this with ⟨ S', hS' ⟩
    rcases DualOfVpolytope_compactHpolytope S' with ⟨ H', hH', hH'0 ⟩
    use H'
    rw [hH', ← hS', hH]
    sorry
    done
  · -- 2.
    exact Vpolytope_of_Hpolytope
  done

