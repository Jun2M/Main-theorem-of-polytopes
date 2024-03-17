import src.MainTheorem
import Mathlib.Analysis.Convex.Cone.Proper
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

open Classical

structure LinearProgram (p d : ℕ+) (R : Type*) [LinearOrderedField R]  where
  maximize : Bool := true
  objectiveVector : (Fin d) → R
  constraints : Matrix (Fin p) (Fin d) R
  constraintRhs : (Fin p) → R
  constraintsNonzero : ∀ i, constraints i ≠ 0 -- assume full rank instead?
  -- empty column?

namespace LinearProgram

@[ext]
structure Tableau (p d : ℕ+) (R : Type*) [LinearOrderedField R] where
  A : Matrix (Fin (p+1)) (Fin (p+d+2)) R
  basic : (Fin (p+1) → Fin (p+d+2))

def simplex_tableau {p d : ℕ+} {R : Type*} [LinearOrderedField R] (lp : LinearProgram p d R) :
  Tableau p d R := by
  let AwithObjective : Matrix (Fin (p+1)) (Fin d) R :=
    λ i => if h : i = 0 then
      if !lp.maximize then -lp.objectiveVector else lp.objectiveVector
    else
      lp.constraints (i.pred h)

  let tableau : Matrix (Fin (p+1)) (Fin (p+d+2)) R := by
    apply Matrix.transpose
    apply (Equiv.vectorEquivFin (Fin (p+1) → R) _).1
    let v1 := Vector.ofFn (1 : Matrix (Fin (p+1)) (Fin (p+1)) R)
    let v2 := (Vector.ofFn (AwithObjective.transpose : (Fin d) → (Fin (p+1)) → R)).append
      (Vector.ofFn (λ _ i => if h : i = 0 then 0 else lp.constraintRhs (i.pred h) : (Fin 1) → (Fin (p+1)) → R))
    refine ⟨ v1.1 ++ v2.1, ?_⟩
    simp only [List.length_append, v1.2, v2.2]
    omega
    done

  exact ⟨ tableau, λ i => i ⟩
namespace Tableau

variable {R : Type*} [LinearOrderedField R] {p d : ℕ+} (T : Tableau p d R)

def simplex_step : Tableau p d R := by

  -- Decide which column to pivot on
  let AvailableColumns := (List.fin_range (p+d+2)).filter
    (λ x => x ∉ (Set.range T.basic) ∧ x ≠ Fin.last (p+d+1) ∧ T.A 0 x < 0)
  if h : AvailableColumns = [] then exact T else
  let pivot_col? : Option (Fin (p+d+2)) := AvailableColumns.argmax (T.A 0 ·)
  let pivot_col : Fin (p+d+2) := pivot_col?.get (by
    rw [← Option.ne_none_iff_isSome]
    intro hNone
    rw [List.argmax_eq_none] at hNone
    exact h hNone
  )

  -- Decide which row to pivot on
  let AvailableRows := ((List.fin_range (p+1)).tail.filter (T.A · pivot_col ≠ 0))
  let row_eval := λ i : Fin (p+1) => T.A i (Fin.last (p+d+1)) / T.A i pivot_col
  let pivot_row? : Option (Fin (p+1)) := AvailableRows.argmin row_eval
  let pivot_row : Fin (p+1) := pivot_row?.get (by
    -- We won't pick an all zero column to pivot on, right?
    sorry
  )

  -- Perform the pivot
  refine ⟨ T.A.rowOp_pivot pivot_row pivot_col ?_, Function.update T.basic pivot_row pivot_col ⟩
  have : pivot_row ∈ pivot_row? := by
    unfold_let pivot_row
    simp

  have := List.argmin_mem this
  rw [List.mem_filter] at this
  simp at this
  exact this.2
  done

def score_vertex : Vector R (p+d+1) := by
  let f : Fin (p+1) → (Fin (p+d+1) → R) := λ i => Pi.single (T.basic i) (T.A i (Fin.last (p+d+1)))
  exact Vector.ofFn (Finset.univ.sum f)
  done

def vertex : Vector R (p+d) := by exact (score_vertex T).tail

def score : R := (score_vertex T).head

def stop_condition : Bool := by
  let v := (Vector.ofFn (T.A 0)).tail
  exact v.1.all (0 ≤ ·)

end Tableau
end LinearProgram


def LinearProgram.Tableau.simplex_recur {R : Type*} [LinearOrderedField R] {p d : ℕ+} (T : Tableau p d R)
  : Tableau p d R :=
  if h : ¬ T.stop_condition then
    T.simplex_step.simplex_recur
  else
    T

  termination_by -T.score
  decreasing_by
    simp_wf  -- oof
    sorry



-- def rows : Set (Fin d → ℝ) :=
--   Set.range lp.constraints

-- noncomputable def conditions : Fin p → (Halfspace (EuclideanSpace ℝ (Fin d))) :=
--   λ i => {
--     f := pointDualLin ⟨ lp.constraints i, lp.constraintsNonzero i ⟩
--     α := (@norm (EuclideanSpace ℝ (Fin ↑d)) _ (lp.constraints i : EuclideanSpace ℝ (Fin d)))⁻¹ * (lp.constraintRhs i)
--   }

-- def conditions_finite : (Set.range lp.conditions).Finite  := Set.finite_range _


-- def feasibleSet : Set (EuclideanSpace ℝ (Fin d)) :=
--   {x : EuclideanSpace ℝ (Fin d) | lp.constraints.mulVec x ≤ lp.constraintRhs}

-- def isFeasible (x : EuclideanSpace ℝ (Fin d)) : Prop :=
--   x ∈ lp.feasibleSet

-- def isOptimal (x : EuclideanSpace ℝ (Fin d)) : Prop :=
--   lp.isFeasible x ∧ ∀ y : EuclideanSpace ℝ (Fin d), lp.isFeasible y → lp.linearObjective y ≤ lp.linearObjective x


-- lemma feasibleSet_Hpolytope :
--   lp.feasibleSet = Hpolytope lp.conditions_finite := by
--   unfold feasibleSet
--   ext x
--   rw [mem_Hpolytope, Set.mem_setOf_eq, Pi.le_def]
--   constructor
--   · -- 1.
--     intro h Hi hHimemCond
--     simp only [Set.mem_range] at hHimemCond
--     rcases hHimemCond with ⟨i, rfl⟩
--     -- rw [← Halfspace_mem]
--     specialize h i
--     unfold Matrix.mulVec Matrix.dotProduct at h
--     simp at h
--     change Finset.sum Finset.univ (fun x_1 => inner (lp.constraints i x_1) (x x_1)) ≤ lp.constraintRhs i at h
--     rw [← PiLp.inner_apply] at h
--     simp only [conditions, ne_eq, pointDualLin, InnerProductSpace.toDual_apply, real_inner_smul_left]
--     refine mul_le_mul (le_refl _) h ?h.mp.intro.c0 ?h.mp.intro.b0
--     sorry
--     rw [inv_nonneg]
--     exact norm_nonneg _
--     done
--   · -- 2.
--     sorry
--     done
--   done

-- def simplexMethod_step (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := by



-- end LinearProgram
