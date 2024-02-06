import «src».Polar


variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
open Pointwise PolarFunctional


def Vpolytope (S : Set E) [Fact (Set.Finite S)] : Set E :=
  convexHull ℝ S

lemma Convex_Vpolytope (S : Set E) [Fact (Set.Finite S)] :
  Convex ℝ (Vpolytope S) := convex_convexHull ℝ S

lemma Closed_Vpolytope (S : Set E) [Fact (Set.Finite S)] :
  IsClosed (Vpolytope S) := by exact Set.Finite.isClosed_convexHull Fact.out

lemma Compact_Vpolytope (S : Set E) [Fact (Set.Finite S)] :
  IsCompact (Vpolytope S) := Set.Finite.isCompact_convexHull Fact.out

lemma Vpolytope_translation (S : Set E) (x : E) [Fact (Set.Finite S)] :
  Vpolytope (S + {x}) = (Vpolytope S) + {x}:= by
  rw [Vpolytope, convexHull_add, convexHull_singleton]
  rfl
  done


def Hpolytope (H : Set (PolarFunctional E)) : Set E := ⋂₀ (le_halfspace '' H)

namespace Hpolytope

lemma Convex (H : Set (PolarFunctional E)) : Convex ℝ (Hpolytope H) := by
  apply convex_sInter
  rintro _ ⟨ Hi, _, rfl ⟩
  exact le_halfspace_convex Hi

lemma Closed (H : Set (PolarFunctional E)) : IsClosed (Hpolytope H) := by
  apply isClosed_sInter
  rintro _ ⟨ Hi, _, rfl ⟩
  change IsClosed Hi.le_halfspace
  rw [Hi.le_halfspace_def]
  apply IsClosed.preimage (Hi.f.1.cont)
  exact isClosed_Iic

lemma mem_iff (H : Set (PolarFunctional E)) (x : E) :
  x ∈ Hpolytope H ↔ ∀ Hi, Hi ∈ H → Hi.f.1 x ≤ Hi.α := by
  constructor <;> intro h
  · -- 1.
    intro Hi HiH
    unfold Hpolytope at h
    rw [Set.mem_sInter] at h
    specialize h Hi.le_halfspace ⟨ Hi, HiH, rfl ⟩
    rw [le_halfspace_mem_iff] at h
    exact h
    done
  · -- 2.
    unfold Hpolytope
    rw [Set.mem_sInter]
    rintro _ ⟨ Hi_, hHi_, rfl ⟩
    specialize h Hi_ hHi_
    rw [le_halfspace_mem_iff]
    exact h
    done

lemma exist_finite_empty [Nontrivial E] :
  ∃ (H : Set (PolarFunctional E)), Fact H.Finite ∧ Hpolytope H = ∅ := by
  rcases exists_ne (0 : E) with ⟨ x, hx ⟩
  let xhat := (norm x)⁻¹ • x
  let fval : NormedSpace.Dual ℝ E := InnerProductSpace.toDualMap ℝ _ xhat
  let f : {f : (NormedSpace.Dual ℝ E) // norm f = 1} := ⟨ fval , (by
    change norm (innerSL ℝ ((norm x)⁻¹ • x)) = 1
    have := @norm_smul_inv_norm ℝ _ E _ _ x hx
    rw [IsROrC.ofReal_real_eq_id, id_eq] at this
    rw [innerSL_apply_norm, this]
    done
  ) ⟩
  refine ⟨ {PolarFunctional.mk f (-1), PolarFunctional.mk (-f) (-1)} , ?_, ?_ ⟩

  apply Fact.mk
  simp only [map_smulₛₗ, map_inv₀, conj_trivial, Set.finite_singleton, Set.Finite.insert]

  ext x
  rw [Set.mem_empty_iff_false, iff_false, mem_iff]
  intro h
  have h1 := h (PolarFunctional.mk f (-1)) (by simp)
  have h2 := h (PolarFunctional.mk (-f) (-1)) (by simp)
  rw [unitSphereDual_neg, ContinuousLinearMap.neg_apply, neg_le, neg_neg] at h2
  change f.1 x ≤ -1 at h1
  linarith
  done

lemma exist_finite_hyperplane (Hi : PolarFunctional E) :
  ∃ (H : Set (PolarFunctional E)), H.Finite ∧ Hpolytope H = Hi.hyperplane := by
  refine ⟨ {PolarFunctional.mk Hi.f Hi.α, PolarFunctional.mk (-Hi.f) (-Hi.α)}, ?_, ?_ ⟩
  simp only [Set.finite_singleton, Set.Finite.insert]
  ext x
  simp only [mem_iff, hyperplane_mem_iff, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, neg_le_neg_iff]
  rw [(by rfl : (-Hi.f).1 x = -(Hi.f.1 x)), neg_le_neg_iff, le_antisymm_iff]
  done

lemma inter_eq (H1 H2 : Set (PolarFunctional E)) :
  Hpolytope (H1 ∪ H2) = Hpolytope H1 ∩ Hpolytope H2 := by
  ext x
  rw [mem_iff, Set.mem_inter_iff, mem_iff, mem_iff]
  constructor
  · -- 1
    intro h
    constructor <;> intro Hi_ hH <;> exact h Hi_ (by simp only [Set.mem_union, hH, true_or, or_true])
  · -- 2
    intro h Hi hHi
    rw [Set.mem_union] at hHi
    rcases hHi with hHi | hHi
    · -- 2.1
      exact h.1 Hi hHi
    · -- 2.2
      exact h.2 Hi hHi
  done

lemma translation_eq {H : Set (PolarFunctional E)} (x : E) :
  Hpolytope ((·.translation x) '' H) = (Hpolytope H) + {x}:= by
  rw [Hpolytope, Hpolytope, Set.sInter_image, Set.sInter_image]
  ext y
  rw [Set.mem_iInter, Set.add_singleton]
  simp only [Set.mem_iInter, SetLike.mem_coe, Set.image_add_right, Set.mem_preimage]
  constructor
  · -- 1.
    intro h Hi hHi
    specialize h (Hi.translation x) (Set.mem_image_of_mem _ hHi)
    rw [translation_le_halfspace_mem_iff, sub_eq_add_neg] at h
    exact h
  · -- 2.
    intro h Hi hHi
    specialize h (Hi.translation (-x)) ?_
    rw [Set.mem_image] at hHi
    rcases hHi with ⟨ Hi', hHi', rfl ⟩
    convert hHi'
    apply le_halfspace_inj
    ext z
    rw [translation_le_halfspace_mem_iff, translation_le_halfspace_mem_iff, sub_neg_eq_add, add_sub_cancel]
    simp only [translation_le_halfspace_mem_iff, sub_neg_eq_add, neg_add_cancel_right] at h
    exact h
  done

end Hpolytope

def orthoHyperplane (x : {x : E // x ≠ 0}) : Set (PolarFunctional E) :=
  { PolarFunctional.mk (pointDualLin x) 0, PolarFunctional.mk (pointDualLin ⟨ -x.1, by rw [neg_ne_zero]; exact x.2 ⟩) 0 }

lemma orthoHyperplane.Finite (x : {x : E // x ≠ 0}) : (orthoHyperplane x).Finite := by
  unfold orthoHyperplane
  simp only [Set.mem_singleton_iff, PolarFunctional.mk.injEq, and_true, Set.finite_singleton, Set.Finite.insert]

lemma orthoHyperplane.mem_iff (x : {x : E // x ≠ 0}) : ∀ (y : E), y ∈ Hpolytope (orthoHyperplane x) ↔ inner x.1 y = (0:ℝ) := by
  intro y
  rw [Hpolytope.mem_iff]
  constructor
  · -- 1.
    intro h
    have h1 := h (PolarFunctional.mk (pointDualLin x) 0)
    simp only [pointDualLin, ne_eq, map_inv₀, IsROrC.conj_to_real, orthoHyperplane, Set.mem_singleton_iff,
      PolarFunctional.mk.injEq, and_true, Set.mem_insert_iff, true_or, forall_true_left, InnerProductSpace.toDual_apply,
      inner_smul_left] at h1

    have h2 := h (PolarFunctional.mk (pointDualLin ⟨ -x.1, by rw [neg_ne_zero]; exact x.2 ⟩) 0)
    simp only [pointDualLin, ne_eq, norm_neg, smul_neg, map_inv₀, IsROrC.conj_to_real, orthoHyperplane,
      Set.mem_singleton_iff, PolarFunctional.mk.injEq, Subtype.mk.injEq, and_true, Set.mem_insert_iff,
      or_true, forall_true_left, InnerProductSpace.toDual_apply, inner_neg_left, inner_smul_left] at h2
    rw [neg_le, neg_zero] at h2
    have := le_antisymm h1 h2
    rw [mul_eq_zero] at this
    cases' this with h3 h4
    ·
      rw [inv_eq_zero, norm_eq_zero] at h3
      exfalso
      exact x.2 h3
    ·
      exact h4
  · -- 2.
    intro h H hH
    unfold orthoHyperplane at hH
    simp only [ne_eq, Set.mem_singleton_iff, PolarFunctional.mk.injEq, and_true, Set.mem_insert_iff] at hH
    cases' hH with H H <;>
    simp only [H, pointDualLin, norm_neg, smul_neg, map_inv₀, IsROrC.conj_to_real, InnerProductSpace.toDual_apply,
        inner_neg_left, inner_smul_left, neg_le, neg_zero, h, mul_zero, le_refl]
  done

lemma cutSpace_sUnion_orthoHyperplane (X : Set {x : E // x ≠ 0}) : ∀ (y : E), y ∈ Hpolytope (⋃₀ (orthoHyperplane '' X)) ↔ ∀ (i : ↑(orthoHyperplane '' X)), y ∈ Hpolytope ↑i := by
  intro y
  unfold Hpolytope
  rw [Set.sUnion_eq_iUnion, Set.image_iUnion, Set.sInter_iUnion, Set.mem_iInter]

lemma Hpolytope_orthoHyperplane_image_mem_iff (X : Set {x : E // x ≠ 0}) : ∀ (y : E), y ∈ Hpolytope (⋃₀ (orthoHyperplane '' X)) ↔ ∀ x ∈ X, inner x.1 y = (0:ℝ) := by
  intro y
  rw [cutSpace_sUnion_orthoHyperplane]
  constructor
  · -- 1.
    intro h
    intro x hx
    simp at h
    specialize h (orthoHyperplane x) x.1 x.2 hx rfl
    exact (orthoHyperplane.mem_iff x y).mp h
  · -- 2.
    intro h
    simp
    rintro a x1 x2 hx rfl
    rw [orthoHyperplane.mem_iff]
    exact h _ hx
  done


def Submodule_cut [FiniteDimensional ℝ E] (p : Subspace ℝ E) : Set (PolarFunctional E) :=
  ⋃₀ (orthoHyperplane '' (Subtype.val ⁻¹' (Set.range (Subtype.val ∘ FiniteDimensional.finBasis ℝ pᗮ))))


lemma Submodule_cut_finite [FiniteDimensional ℝ E] (p : Subspace ℝ E) : (Submodule_cut p).Finite := by
  apply Set.Finite.sUnion ?_ (fun t ht => by
    rcases ht with ⟨ x, _, rfl ⟩
    exact orthoHyperplane.Finite _)
  apply Set.Finite.image
  apply Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective _)
  apply Set.finite_range
  done

lemma Submodule_cutspace [FiniteDimensional ℝ E] (p : Subspace ℝ E) : ∃ H_ : Set (PolarFunctional E), Fact H_.Finite ∧ ↑p = Hpolytope H_ := by
  use Submodule_cut p
  use Fact.mk <| Submodule_cut_finite p
  ext x
  constructor
  · -- 1.
    rintro hx Hi_ ⟨ H, ⟨ _, ⟨ v, ⟨ i, hi ⟩, rfl ⟩ , hHHalfpair ⟩, rfl ⟩
    rw [le_halfspace_mem_iff]
    revert hHHalfpair H
    rw [← Hpolytope.mem_iff,  orthoHyperplane.mem_iff, ← hi, Submodule.inner_left_of_mem_orthogonal hx]
    exact Submodule.coe_mem ((FiniteDimensional.finBasis ℝ { x // x ∈ pᗮ }) i)
  · -- 2.
    rintro hHi_
    rw [Submodule_cut, Hpolytope_orthoHyperplane_image_mem_iff] at hHi_
    rw [SetLike.mem_coe, ← Submodule.orthogonal_orthogonal p]
    intro y hy
    have : ∀ i, inner (Subtype.val (FiniteDimensional.finBasis ℝ { x // x ∈ pᗮ } i)) x = (0:ℝ) := by
      intro i
      let v : E := (FiniteDimensional.finBasis ℝ { x // x ∈ pᗮ }) i
      let v' : { x // x ≠ 0 } := ⟨ v, fun hv => (Basis.ne_zero (FiniteDimensional.finBasis ℝ { x // x ∈ pᗮ }) i) (Submodule.coe_eq_zero.mp hv) ⟩
      exact hHi_ v' ⟨ i, rfl ⟩
    rw [← Submodule.mem_orthogonal_Basis] at this
    exact this _ hy
  done

lemma origin_Hpolytope [FiniteDimensional ℝ E] : ∃ (H_ : Set (PolarFunctional E)), Fact H_.Finite ∧ Hpolytope H_ = ({0} : Set E) := by
  refine ⟨ ⋃₀ (orthoHyperplane '' (Subtype.val ⁻¹' Set.range (FiniteDimensional.finBasis ℝ E))), ?_, ?_ ⟩
  · -- 1.
    apply Fact.mk
    apply Set.Finite.sUnion ?_ (fun t ht => by
      rcases ht with ⟨ x, _, rfl ⟩
      exact orthoHyperplane.Finite _)
    apply Set.Finite.image
    apply Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective _)
    exact Set.finite_range _
  · -- 2.
    ext x
    rw [Set.mem_singleton_iff]
    change x ∈ Hpolytope ( (⋃₀ (orthoHyperplane '' (Subtype.val ⁻¹' Set.range ↑(FiniteDimensional.finBasis ℝ E))))) ↔ x = 0
    rw [Hpolytope_orthoHyperplane_image_mem_iff]
    constructor
    · -- 1.
      intro h
      apply InnerProductSpace.ext_inner_left_basis (FiniteDimensional.finBasis ℝ E)
      intro i
      rw [inner_zero_right]
      simp only [Set.mem_preimage, Set.mem_range, forall_exists_index, Subtype.forall] at h
      exact h (FiniteDimensional.finBasis ℝ E i) (Basis.ne_zero (FiniteDimensional.finBasis ℝ E) i) i rfl
    · -- 2.
      rintro rfl x _
      rw [inner_zero_right]
  done
