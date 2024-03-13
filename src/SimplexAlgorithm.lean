import src.MainTheorem
import Mathlib.Analysis.Convex.Cone.Proper
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

structure LinearProgram (d p : ℕ+) where
  linearObjective : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ
  constraints : Matrix (Fin p) (Fin d) ℝ
  constraintRhs : (Fin p) → ℝ
  constraintsNonzero : ∀ i, constraints i ≠ 0 -- assume full rank instead?

namespace LinearProgram

variable {d p : ℕ+} (lp : LinearProgram d p)

def rows : Set (Fin d → ℝ) :=
  Set.range lp.constraints

noncomputable def conditions : Fin p → (Halfspace (EuclideanSpace ℝ (Fin d))) :=
  λ i => {
    f := pointDualLin ⟨ lp.constraints i, lp.constraintsNonzero i ⟩
    α := (@norm (EuclideanSpace ℝ (Fin ↑d)) _ (lp.constraints i : EuclideanSpace ℝ (Fin d)))⁻¹ * (lp.constraintRhs i)
  }

def conditions_finite : (Set.range lp.conditions).Finite  := Set.finite_range _


def feasibleSet : Set (EuclideanSpace ℝ (Fin d)) :=
  {x : EuclideanSpace ℝ (Fin d) | lp.constraints.mulVec x ≤ lp.constraintRhs}

def isFeasible (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  x ∈ lp.feasibleSet

def isOptimal (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  lp.isFeasible x ∧ ∀ y : EuclideanSpace ℝ (Fin d), lp.isFeasible y → lp.linearObjective y ≤ lp.linearObjective x

def simplex_tableau : Matrix (Fin (p+1)) (Fin (d + 2)) ℝ := λ i =>
  if i = 0 then
    InnerProductSpace.
  done

lemma feasibleSet_Hpolytope :
  lp.feasibleSet = Hpolytope lp.conditions_finite := by
  unfold feasibleSet
  ext x
  rw [mem_Hpolytope, Set.mem_setOf_eq, Pi.le_def]
  constructor
  · -- 1.
    intro h Hi hHimemCond
    simp only [Set.mem_range] at hHimemCond
    rcases hHimemCond with ⟨i, rfl⟩
    -- rw [← Halfspace_mem]
    specialize h i
    unfold Matrix.mulVec Matrix.dotProduct at h
    simp at h
    change Finset.sum Finset.univ (fun x_1 => inner (lp.constraints i x_1) (x x_1)) ≤ lp.constraintRhs i at h
    rw [← PiLp.inner_apply] at h
    simp only [conditions, ne_eq, pointDualLin, InnerProductSpace.toDual_apply, real_inner_smul_left]
    refine mul_le_mul (le_refl _) h ?h.mp.intro.c0 ?h.mp.intro.b0
    sorry
    rw [inv_nonneg]
    exact norm_nonneg _
    done
  · -- 2.
    sorry
    done
  done

def simplexMethod_step (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := by



end LinearProgram
