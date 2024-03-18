import Mathlib.Analysis.Convex.Cone.Proper
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Data.Matroid.Dual
import Mathlib.Data.Rat.Field
import Mathlib.Data.Matrix.Notation
-- import Mathlib
import src.SimplexAlgorithm


variable {R : Type*} [LinearOrderedField R] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)

-- def rowOp_smul  (i : Fin m) (c : R) :
--   Matrix (Fin m) (Fin n) R :=
--   A.updateRow i (c * A i ·)

-- def rowOp_add (i j : Fin m) :
--   Matrix (Fin m) (Fin n) R :=
--   A.updateRow j (A i + A j)

-- def rowOp_smul_add (c : R) (i : Fin m) (j : Fin m) :
--   Matrix (Fin m) (Fin n) R :=
--   A.updateRow j (c • A i + A j)

-- def rowOp_swap (i j : Fin m) :
--   Matrix (Fin m) (Fin n) R :=
--   let index_swap : Fin m → Fin m :=
--     λ k => if k = i then j else if k = j then i else k
--   λ i j => A (index_swap i) j

-- def rowOp_press (i : Fin m) (x : Fin n) (_h_ : A i x ≠ 0) :
--   Matrix (Fin m) (Fin n) R :=
--   A.rowOp_smul i (A i x)⁻¹

-- def rowOp_remove (i j : Fin m) (x : Fin n) (_h_ : A i x = 1) :
--   Matrix (Fin m) (Fin n) R :=
--   A.rowOp_smul_add (- A j x) i j


-- -- Some example from the internet
-- def lp : LinearProgram 3 2 ℚ where
--   minimize := false
--   objectiveVector := ![3, 2]
--   constraints := !![
--     2, 1;
--     2, 3;
--     3, 1
--   ]
--   constraintRhs := ![18, 42, 24]
--   constraintsNonzero := by
--     intro i h
--     have : (Matrix.of ![![2, 1], ![2, 3], ![3, 1]] i : Fin 2 → ℚ) 0 = 0 := by
--       rw [h]
--       rfl
--     fin_cases i <;>
--     simp at this

-- -- Introductory Example p.57
-- def lp : LinearProgram 3 2 ℚ where
--   minimize := false
--   objectiveVector := ![1, 1]
--   constraints := !![
--     -1, 1;
--     1, 0;
--     0, 1
--   ]
--   constraintRhs := ![1, 3, 2]
--   constraintsNonzero := by
--     intro i h
--     have htry0: (Matrix.of ![![-1, 1], ![1, 0], ![0, 1]] i : Fin 2 → ℚ) 0 = 0 := by
--       rw [h]
--       rfl
--     have htry1: (Matrix.of ![![-1, 1], ![1, 0], ![0, 1]] i : Fin 2 → ℚ) 1 = 0 := by
--       rw [h]
--       rfl
--     fin_cases i <;>
--     simp at htry0 htry1
--     done

-- -- Exception Handling: Unboundedness
-- def lp : LinearProgram 2 2 ℚ where
--   minimize := false
--   objectiveVector := ![1, 0]
--   constraints := !![
--     1, -1;
--     -1, 1
--   ]
--   constraintRhs := ![1, 2]
--   constraintsNonzero := by
--     intro i h
--     have htry0: (Matrix.of ![![1, -1], ![-1, 1]] i : Fin 2 → ℚ) 0 = 0 := by
--       rw [h]
--       rfl
--     fin_cases i <;>
--     simp at htry0
--     done

-- -- Exception Handling: Degeneracy
-- def lp : LinearProgram 2 2 ℚ where
--   minimize := false
--   objectiveVector := ![0, 1]
--   constraints := !![
--     -1, 1;
--     1, 0
--   ]
--   constraintRhs := ![0, 2]
--   constraintsNonzero := by
--     intro i h
--     have htry0: (Matrix.of ![![-1, 1], ![1, 0]] i : Fin 2 → ℚ) 0 = 0 := by
--       rw [h]
--       rfl
--     fin_cases i <;>
--     simp at htry0
--     done

-- -- Exception Handling: Infeasibility
-- def lp : LinearProgram 2 3 ℚ where
--   minimize := false
--   objectiveVector := ![1, 2, 0]
--   constraints := !![
--     1, 3, 1;
--     0, 2, 1
--   ]
--   constraintRhs := ![4, 2]
--   constraintsNonzero := by
--     intro i h
--     have htry0: (!![1, 3, 1; 0, 2, 1] i : Fin 3 → ℚ) 1 = 0 := congr_fun h 1
--     fin_cases i <;>
--     simp at htry0
--     done

-- infeasible origin
def lp : LinearProgram 3 2 ℚ where
  minimize := false
  objectiveVector := ![1, 2]
  constraints := !![
    1, 1;
    0, 1;
    -1, -1
  ]
  constraintRhs := ![2, 1, -1]
  constraintsNonzero := by
    intro i h
    have htry0: !![1, 1; 0, 1; -1, -1] i 1 = 0 := congr_fun h 1
    fin_cases i <;>
    simp at htry0
    done

def T  := lp.simplex_tableau
def Res := LinearProgram.Tableau.Simplex lp
#eval T.A
#eval T.Rhs
#eval Res.vertex
#eval Res.score

#eval lp.origin_feasible
def iT := lp.initial_tableau
#eval iT.A
#eval iT.Rhs
#eval iT.basic
def Res1 := iT.Simplex_inner lp
#eval Res1.basic
#eval Res1.vertex
#eval Res1.score


-- def p : ℕ+ := 2
-- def d : ℕ+ := 2
-- def AvailableColumns := (p+d+1:ℕ).fin_list_range.filter (λ i => 0 < i ∧ T.A 0 i > 0)
-- #eval AvailableColumns
-- def AvailableRows := (p+1:ℕ).fin_list_range.tail.filter (0 < T.A · 3)
-- #eval AvailableRows
-- def row_eval := λ i : Fin (p+1) => T.Rhs i 0 / T.A i 3
-- #eval AvailableRows.argmin row_eval

-- #eval T.A
-- #eval T.Rhs
-- #eval T.basic
-- #eval (T.pivoting 1 3 (by sorry)).A
-- #eval (T.pivoting 1 3 (by sorry)).Rhs

-- def AvailableColumns1 := (p+d+1:ℕ).fin_list_range.filter (λ i => 0 < i ∧ (T.pivoting 1 3 (by sorry)).A 0 i > 0)
-- #eval AvailableColumns1
-- def AvailableRows1 := (p+1:ℕ).fin_list_range.tail.filter (0 < (T.pivoting 1 3 (by sorry)).A · 4)
-- #eval AvailableRows1
-- def T' : LinearProgram.Tableau (p+1) (p+d+1) ℚ := {
--       A :=      λ i => if i ≠ Fin.last (p+1) then T.A i else Pi.single 4 1,
--       Rhs :=    λ i => if i ≠ Fin.last (p+1) then T.Rhs i else Pi.single 1 1,
--       basic :=  λ i => if i ≠ Fin.last (p+1) then T.basic i else 4
--     }
-- #eval T'.A
-- #eval T'.Rhs
-- #eval T'.basic
-- def Final_T := T'.pivoting (Fin.last p) 4 sorry
-- #eval Final_T.A
-- #eval Final_T.Rhs
-- #eval Final_T.basic
-- def r := Final_T.return'
-- #eval r.vertex
-- #eval r.value


-- #eval Res.T.isSome
-- #eval Res.T1.isSome
-- #eval (Res.T1.get (by sorry)).A
-- #eval (Res.T1.get (by sorry)).Rhs
-- #eval (Res.T1.get (by sorry)).basic


-- #eval T2.A
-- #eval T2.vertex
-- #eval T2.score

-- #eval T3.A
-- #eval T3.vertex
-- #eval T3.score

-- #eval T4.A
-- #eval T4.vertex
-- #eval T4.score

-- #eval T.simplex_recur.A
-- #eval T.simplex_recur.vertex
-- #eval T.simplex_recur.score

-- #eval (List.range 6).filter (λ x => ∀ ix ∈ (⟨[ (0, 0), (1, 4), (2, 5) ], by simp⟩ : Vector (Fin 3 × Fin 7) 3).1, ix.2 ≠ x)
