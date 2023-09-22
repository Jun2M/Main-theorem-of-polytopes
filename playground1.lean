import «Chapter2» 
import «Chapter3» 
import «Main»


variable {d : ℕ+}
open Pointwise

lemma Vpolytope_of_Hpolytope : ∀ (H_ : Set (Halfspace d)) (hH_ : H_.Finite), IsCompact (Hpolytope hH_) → 
  ∃ (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Finite), Hpolytope hH_ = Vpolytope hS := by
  intro H_ hH_ hHcpt
  have := closure_convexHull_extremePoints hHcpt (Convex_Hpolytope hH_)
  have hExHFinite: Set.Finite <| Set.extremePoints ℝ (Hpolytope hH_) := by
    have := ExtremePointsofHpolytope hH_ 
    sorry
    done
  -- rcases Set.Finite.exists_finset_coe hExHFinite with ⟨ ExH, hExH ⟩
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
  ∀ (H_ : Set (Halfspace d)) (hH_ : H_.Finite), IsCompact (Hpolytope hH_) → 
  ∃ (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Finite), Hpolytope hH_ = Vpolytope hS := by
  constructor
  · -- 1.
    intro S
    cases' (em (interior (Vpolytope hS)).Nonempty) with hVpolytopeIntEmpty hVpolytopeIntNonempty
    · -- Interior is nonempty 
      let S_ := S.toSet + {-hVpolytopeIntEmpty.some}
      let hS_ : S_.Finite := by
        apply Set.Finite.add
        exact S.finite_toSet
        exact Set.finite_singleton _
        done

      have h := hVpolytopeIntEmpty.some_mem
      -- rw [← Set.Finite.coe_toFinset hS_] at h
      have : 0 ∈ interior (Vpolytope (Set.Finite.toFinset hS_)) := by
        
        done
      rcases DualOfVpolytope_compactHpolytope hS_.toFinset this with ⟨ H, hH, hH0, hHcpt ⟩
      rcases Vpolytope_of_Hpolytope H hHcpt with ⟨ S', hS' ⟩
      have : 0 ∈ interior (Vpolytope S') := by
        rw [← hS']
        apply 
        done
      rcases DualOfVpolytope_compactHpolytope S' this with ⟨ H', hH', hH'0, hH'cpt ⟩
      use H'
      rw [hH', ← hS', hH]
      sorry
      done
    · -- Interior is empty
      sorry
      done
  · -- 2.
    exact Vpolytope_of_Hpolytope
  done

