import Mathlib.Analysis.Convex.Cone.Proper
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import «Main»


open Pointwise Matrix

/-
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
open Pointwise


def Vpolytope {S : Set E} (_ : S.Finite): Set E :=
  convexHull ℝ S

lemma Convex_Vpolytope {S : Set E} (hS : S.Finite) : 
  Convex ℝ (Vpolytope hS) := convex_convexHull ℝ S

lemma Closed_Vpolytope {S : Set E} (hS : S.Finite) : 
  IsClosed (Vpolytope hS) := by exact Set.Finite.isClosed_convexHull hS
  
lemma Compact_Vpolytope {S : Set E} (hS : S.Finite) : 
  IsCompact (Vpolytope hS) := Set.Finite.isCompact_convexHull hS


def Hpolytope {H_ : Set (Halfspace E)} (_ : H_.Finite) : Set E :=
  ⋂₀ (SetLike.coe '' H_)

lemma Convex_Hpolytope {H_ : Set (Halfspace E)} (hH_ : H_.Finite) : Convex ℝ (Hpolytope hH_) := by
  apply convex_sInter
  rintro _ ⟨ Hi_, _, rfl ⟩
  exact Halfspace_convex Hi_

lemma Closed_Hpolytope {H : Set (Halfspace E)} (hH_ : H.Finite) : IsClosed (Hpolytope hH_) := by
  apply isClosed_sInter
  rintro _ ⟨ Hi_, _, rfl ⟩
  change IsClosed Hi_
  rw [Hi_.h]
  apply IsClosed.preimage (Hi_.f.1.cont)
  exact isClosed_Iic

lemma Hpolytope_same {H_ : Set (Halfspace E)} (hH_1 hH_2: H_.Finite) : 
  Hpolytope hH_1 = Hpolytope hH_2 := by
  unfold Hpolytope
  rfl

lemma mem_Hpolytope {H_ : Set (Halfspace E)} (hH_ : H_.Finite) (x : E) : 
  x ∈ Hpolytope hH_ ↔ ∀ Hi, Hi ∈ H_ → Hi.f.1 x ≤ Hi.α := by
  constructor <;> intro h
  · -- 1.
    intro Hi HiH
    unfold Hpolytope at h
    rw [Set.mem_sInter] at h
    specialize h Hi ⟨ Hi, HiH, rfl ⟩
    rw [Halfspace_mem] at h
    exact h
    done
  · -- 2.
    unfold Hpolytope
    rw [Set.mem_sInter]
    rintro _ ⟨ Hi_, hHi_, rfl ⟩
    specialize h Hi_ hHi_
    rw [Halfspace_mem]
    exact h
    done
-/

structure LinearProgram (d p : ℕ+) where
  linearObjective : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ
  constraints : Matrix (Fin p) (Fin d) ℝ
  constraintRhs : (Fin p) → ℝ

def LinearProgram.rows {d p : ℕ+} (lp : LinearProgram d p) : Set (Fin d → ℝ) :=
  Set.range lp.constraints
  
def LinearProgram.feasibleSet {d p : ℕ+} (lp : LinearProgram d p) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x : EuclideanSpace ℝ (Fin d) | lp.constraints.mulVec x ≤ lp.constraintRhs}

def LinearProgram.isFeasible {d p : ℕ+} (lp : LinearProgram d p) (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  x ∈ lp.feasibleSet

def LinearProgram.isOptimal {d p : ℕ+} (lp : LinearProgram d p) (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  lp.isFeasible x ∧ ∀ y : EuclideanSpace ℝ (Fin d), lp.isFeasible y → lp.linearObjective y ≤ lp.linearObjective x

lemma LinearProgram.feasibleSet_Hpolytope {d p : ℕ+} (lp : LinearProgram d p) : 
  lp.feasibleSet = Hpolytope (Set.finite_range (lp.constraints : Fin d → Fin p → ℝ) : Set.Finite (Set.range lp.constraints : Set (EuclideanSpace ℝ (Fin d)))) := by
  ext x
  rw [mem_Hpolytope]
  split
  · -- 1.
    intro h
    intro Hi
    rw [← Matrix.to_lin'_apply, ← Matrix.to_lin'_apply, Matrix.to_lin'_mul, Matrix.to_lin'_of, Matrix.to_lin'_apply, Matrix.to_lin'_apply, Matrix.to_lin'_of]
    specialize h Hi
    rw [Matrix.to_lin'_apply, Matrix.to_lin'_apply, Matrix.to_lin'_of] at h
    exact h
    done
  · -- 2.
    intro h
    intro Hi
    rw [← Matrix.to_lin'_apply, ← Matrix.to_lin'_apply, Matrix.to_lin'_mul, Matrix.to_lin'_of, Matrix.to_lin'_apply, Matrix.to_lin'_apply, Matrix.to_lin'_of]
    specialize h Hi
    rw [Matrix.to_lin'_apply, Matrix.to_lin'_apply, Matrix.to_lin'_of] at h
    exact h
    done
  done
