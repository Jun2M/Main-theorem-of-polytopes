import Mathlib.Analysis.Convex.Cone.Proper
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Data.Matroid.Dual
import src.MainTheorem

theorem Minkowski_Caratheory {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
  (hXcpt : IsCompact X) (hXCvx : Convex ℝ X) :
  ∀ x ∈ X, ∃ Y : Set _, Y.ncard = d + 1 ∧
    (Y ⊆ X.extremePoints ℝ) ∧ x ∈ convexHull ℝ Y := by
  sorry
  done
