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

-- def T : Tableau 2 3 ℚ where
--   A := !![
--     (1:ℚ), 0, 0, 2, 3, 4, 0;
--     0    , 1, 0, 3, 2, 1, 10;
--     0    , 0, 1, 2, 5, 3, 15
--     ]
--   basic := (λ x => match x with
--   | 0 => 0
--   | 1 => 1
--   | 2 => 2
-- )

def lp : LinearProgram 3 2 ℚ where
  objectiveVector := ![-3, -2]
  constraints := !![
    2, 1;
    2, 3;
    3, 1
  ]
  constraintRhs := ![18, 42, 24]
  constraintsNonzero := by
    intro i h
    have : (Matrix.of ![![2, 1], ![2, 3], ![3, 1]] i : Fin 2 → ℚ) 0 = 0 := by
      rw [h]
      rfl
    fin_cases i <;>
    simp at this

def T  := lp.simplex_tableau
def T1 := T.simplex_step
def T2 := T1.simplex_step
def T3 := T2.simplex_step
def T4 := T3.simplex_step

#eval T.A
#eval T.vertex
#eval T.score

#eval T1.A
#eval T1.vertex
#eval T1.score

#eval T2.A
#eval T2.vertex
#eval T2.score


-- #eval T3.A
-- #eval T3.vertex
-- #eval T3.score

-- #eval T4.A
-- #eval T4.vertex
-- #eval T4.score

#eval T.simplex_recur.A
#eval T.simplex_recur.vertex
#eval T.simplex_recur.score

-- #eval (List.range 6).filter (λ x => ∀ ix ∈ (⟨[ (0, 0), (1, 4), (2, 5) ], by simp⟩ : Vector (Fin 3 × Fin 7) 3).1, ix.2 ≠ x)
