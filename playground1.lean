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
      1. ConvexHull always have an intrinsic interior
      2. Any AffineSubspaces are intersections of hyperplanes
      3. Any hyperplane is an intersection of two Halfspaces
      4. Take union of the set of Halfspaces for Hpolytope in the affineSpan and for the affineSpan, Done
      -/
      
      sorry
      done
  · -- 2.
    exact Vpolytope_of_Hpolytope
  done

