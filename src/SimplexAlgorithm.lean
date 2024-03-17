import src.MainTheorem
import Mathlib.Analysis.Convex.Cone.Proper
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional


structure LinearProgram (p d : ℕ+) (R : Type*) [LinearOrderedField R]  where
  minimize : Bool := true
  objectiveVector : (Fin d) → R
  constraints : Matrix (Fin p) (Fin d) R
  constraintRhs : (Fin p) → R
  constraintsNonzero : ∀ i, constraints i ≠ 0 -- assume full rank instead?

namespace LinearProgram

@[ext]
structure Tableau (n m : ℕ+) (R : Type*) [LinearOrderedField R] where
  A : Matrix (Fin (n+1)) (Fin m) R
  Rhs : (Fin (n+1)) → (Fin 2 → R)
  basic : (Fin (n+1) → Fin m)

structure result {p d : ℕ+} {R : Type*} [LinearOrderedField R] (lp : LinearProgram p d R) where
  value_vertex : Option (Vector ((Fin 2 → R)) (d+1))
  value : Option ((Fin 2 → R)) := value_vertex >>= (·.head)
  score : Option ((Fin 2 → R)) := if lp.minimize then value else value.map (-·)
  vertex : Option (Vector ((Fin 2 → R)) (d+1-1)) := value_vertex >>= (·.tail)
  hValue : value = value_vertex >>= (·.head) := by rfl
  hVertex : vertex = value_vertex >>= (·.tail) := by rfl

def Tableau.pivoting {n m : ℕ+} {R : Type*} [LinearOrderedField R] (T : Tableau n m R)
  (pivot_row : Fin (n+1)) (pivot_col : Fin m) (_h_ : T.A pivot_row pivot_col ≠ 0) :
  Tableau n m R :=
  let v := (T.A pivot_row pivot_col)⁻¹ • T.A pivot_row
  let r := (T.A pivot_row pivot_col)⁻¹ • T.Rhs pivot_row
  ⟨ λ j => if j = pivot_row then v else (- T.A j pivot_col) • v + T.A j,
    λ j => if j = pivot_row then r else (- T.A j pivot_col) • r + T.Rhs j,
    Function.update T.basic pivot_row pivot_col⟩

def Tableau.return {n p d : ℕ+} {R : Type*} [LinearOrderedField R] (lp : LinearProgram p d R) (T : Tableau n (p+d+1) R) :
  lp.result := by
  let f : Fin (n+1) → (Fin _ → (Fin 2 → R)) := λ i => Pi.single (T.basic i) (T.Rhs i)
  let f1 : Fin (p+d+1) → (Fin 2 → R) := Finset.univ.sum f
  let f2 : Fin (d+1) → (Fin 2 → R) := λ i => if i = 0 then f1 i else f1 (i + p)
  exact { value_vertex := some <| Vector.ofFn f2 }
  done

variable {p d : ℕ+} {R : Type*} [LinearOrderedField R]

-- Note the slack variables are the First p+1 columns of the tableau
-- The First row is the objective function
def simplex_tableau (lp : LinearProgram p d R) :
  Tableau p (p+d+1) R := by
  let AwithObjective : Matrix (Fin (p+1)) (Fin d) R :=
    λ i => if h : i = 0 then
      if lp.minimize then -lp.objectiveVector else lp.objectiveVector
    else
      lp.constraints (i.pred h)

  let A : Matrix (Fin (p+1)) (Fin (p+d+1)) R := by
    apply Matrix.transpose
    apply (Equiv.vectorEquivFin (Fin (p+1) → R) _).1
    let v1 := Vector.ofFn (1 : Matrix (Fin (p+1)) (Fin (p+1)) R)
    let v2 := Vector.ofFn (AwithObjective.transpose : (Fin d) → (Fin (p+1)) → R)
    refine ⟨ v1.1 ++ v2.1, ?_⟩
    simp only [List.length_append, v1.2, v2.2]
    omega
    done

  exact ⟨ A, (λ i => if h : i = 0 then 0 else
    λ j => if j = 0 then lp.constraintRhs (i.pred h) else 0), λ i => i ⟩

end LinearProgram

def LinearProgram.Tableau.Simplex_inner {p d n : ℕ+} {R : Type*} [LinearOrderedField R] (lp : LinearProgram p d R)
  (T : Tableau n (p+d+1) R) :
  lp.result :=

  let AvailableColumns := (p+d+1:ℕ).fin_list_range.filter (λ i => 0 < i ∧ T.A 0 i > 0)
  if hCol : AvailableColumns = [] then
    T.return lp
  else
  let pivot_col : Fin (p+d+1) := (AvailableColumns.argmax (T.A 0 ·)).get (by
  rw [← Option.ne_none_iff_isSome]
  intro hNone
  rw [List.argmax_eq_none] at hNone
  exact hCol hNone
  )

  let AvailableRows := (n+1:ℕ).fin_list_range.tail.filter (0 < T.A · pivot_col)
  if hRow : AvailableRows = [] then
    let T : Tableau (n+1) (p+d+1) R := {
      A :=      λ i => if i ≠ Fin.last (n+1) then T.A i else Pi.single pivot_col 1,
      Rhs :=    λ i => if i ≠ Fin.last (n+1) then T.Rhs i else Pi.single 1 1,
      basic :=  λ i => if i ≠ Fin.last (n+1) then T.basic i else pivot_col
    }
    let Final_T := T.pivoting (Fin.last (n+1)) pivot_col (by simp)
    Final_T.return lp
  else
  let row_eval := λ i : Fin (n+1) => T.Rhs i 0 / T.A i pivot_col
  let pivot_row : Fin (n+1) := (AvailableRows.argmin row_eval).get (by
    rw [← Option.ne_none_iff_isSome]
    intro hNone
    rw [List.argmin_eq_none] at hNone
    exact hRow hNone
  )
  let T := T.pivoting pivot_row pivot_col (by
    simp
    have : pivot_row ∈ (AvailableRows.argmin row_eval) := by
      unfold_let pivot_row
      simp
    have := List.argmin_mem this
    rw [List.mem_filter] at this
    simp at this
    exact ne_of_gt this.2
  )
  by exact T.Simplex_inner lp
  termination_by T.Rhs 0
  decreasing_by sorry

def LinearProgram.Tableau.Simplex {p d : ℕ+} {R : Type*} [LinearOrderedField R] (lp : LinearProgram p d R) :
  lp.result :=
  let T := lp.simplex_tableau
  T.Simplex_inner lp

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
