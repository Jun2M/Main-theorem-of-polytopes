import «Chapter2» 
import «Chapter3» 
import «Main»


variable {d : ℕ+}
open Pointwise




theorem MainTheoremOfPolytopes : 
  (∀ (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Finite), ∃ (H_ : Set (Halfspace d)) (hH_ : H_.Finite), 
    Hpolytope hH_ = Vpolytope hS) ∧ 
  ∀ {H_ : Set (Halfspace d)} (hH_ : H_.Finite), IsCompact (Hpolytope hH_) → 
  ∃ (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Finite), Hpolytope hH_ = Vpolytope hS := by
  constructor
  · -- 1.
    intro S hS
    cases' (em (interior (Vpolytope hS)).Nonempty) with hVpolytopeIntNonempty hVpolytopeIntEmpty
    · -- Interior is nonempty 
      exact Hpolytope_of_Vpolytope_interior _ hVpolytopeIntNonempty
    · -- Interior is empty
      /-
      1. ConvexHull always have an intrinsic interior -- intrinsicInterior_nonempty!
      2. Any AffineSubspaces are intersections of hyperplanes
      3. Any hyperplane is an intersection of two Halfspaces -- Done!
      4. Take union of the set of Halfspaces for Hpolytope in the affineSpan and for the affineSpan
      -/
      cases' em (S.Nonempty) with hSnonempty hSempty 
      · -- S is nonempty 
        rw [← @convexHull_nonempty_iff ℝ] at hSnonempty
        rw [← intrinsicInterior_nonempty (convex_convexHull ℝ S)] at hSnonempty
        cases' hSnonempty with x hx
        unfold intrinsicInterior at hx
        rw [Set.mem_image] at hx
        rcases hx with ⟨ x, hx, rfl ⟩

        sorry
        done
      · -- S is empty
        rw [← @convexHull_nonempty_iff ℝ, Set.not_nonempty_iff_eq_empty] at hSempty
        rw [Vpolytope, hSempty]
        exact empty_Hpolytope
        done

  · -- 2.
    exact Vpolytope_of_Hpolytope
  done

