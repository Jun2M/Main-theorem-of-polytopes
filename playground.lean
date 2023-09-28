import Mathlib.Analysis.Convex.Cone.Proper
import «Main»


def Set.Subtype {α : Type} {property : α → Prop} (S : Set α) (hS : ∀ s ∈ S, property s) : 
  ∃ S' : Set {x : α // property x}, Subtype.val '' S' = S ∧ Subtype.val ⁻¹' S = S':= by
  have : ∃ S' : Set {x : α // property x}, Subtype.val '' S' = S := CanLift.prf S hS
  rcases this with ⟨ S', hS' ⟩
  refine ⟨ S', hS', ?_ ⟩ 
  ext x
  rw [Set.mem_preimage, ← hS', Set.mem_image]
  constructor
  · -- 1.
    rintro ⟨ x', hx', hxx ⟩
    rw [Subtype.coe_inj] at hxx
    exact hxx ▸ hx'
  · -- 2.
    intro hx
    exact ⟨ x, hx, rfl ⟩
  done

def Set.Subtype_bijOn {α : Type} {property : α → Prop} (S : Set α) (hS : ∀ s ∈ S, property s) : 
  ∃ S' : Set {x : α // property x}, Set.BijOn Subtype.val S' S:= by
  rcases (CanLift.prf S hS : ∃ S' : Set {x : α // property x}, Subtype.val '' S' = S) with ⟨ S', hS' ⟩
  exact ⟨ S', by exact hS' ▸ Set.InjOn.bijOn_image (Set.injOn_of_injective Subtype.val_injective _) ⟩ 


lemma Subspace_IsClosed {d : ℕ+} (p : Subspace ℝ (EuclideanSpace ℝ (Fin d))) : IsClosed (p : Set (EuclideanSpace ℝ (Fin d))) := by
  apply Submodule.ClosedComplemented.isClosed
  unfold Submodule.ClosedComplemented
  use orthogonalProjection p 
  intro x
  apply orthogonalProjection_mem_subspace_eq_self
  done


variable {E P : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [PseudoMetricSpace P] [NormedAddTorsor E P] [FiniteDimensional ℝ E]
open Pointwise


def Submodule_cut (p : Subspace ℝ E) : Set (Halfspace E) := 
  ⋃₀ (orthoHyperplane '' (Subtype.val ⁻¹' (Set.range (Subtype.val ∘ FiniteDimensional.finBasis ℝ pᗮ))))


lemma Submodule_cut_finite (p : Subspace ℝ E) : (Submodule_cut p).Finite := by
  apply Set.Finite.sUnion ?_ (fun t ht => by
    rcases ht with ⟨ x, _, rfl ⟩
    exact orthoHyperplane.Finite _)
  apply Set.Finite.image
  apply Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective _)
  apply Set.finite_range
  done

lemma Submodule_cutspace (p : Subspace ℝ E) : ∃ H_ : Set (Halfspace E), H_.Finite ∧ ↑p = ⋂₀ (SetLike.coe '' H_) := by
  use Submodule_cut p
  use Submodule_cut_finite p
  ext x
  constructor <;> rw [Set.mem_sInter]
  · -- 1.
    rintro hx Hi_ ⟨ H, ⟨ _, ⟨ v, ⟨ i, hi ⟩, rfl ⟩ , hHHalfpair ⟩, rfl ⟩
    rw [Halfspace_mem]
    revert hHHalfpair H
    simp only [Function.comp_apply, ne_eq] at hi 
    rw [← mem_cutSpace,  orthoHyperplane_mem, ← hi, Submodule.inner_left_of_mem_orthogonal hx]
    exact Submodule.coe_mem ((FiniteDimensional.finBasis ℝ { x // x ∈ pᗮ }) i)
  · -- 2.
    rintro hHi_
    by_contra h
    sorry
    done
  done


lemma Vpolytope_of_Vpolytope_inter_cutSpace_fin {S : Set E} (hS : S.Finite) (hVinterior : Set.Nonempty (interior (Vpolytope hS)))
  {H_ : Set (Halfspace E)} (hH_ : H_.Finite) : 
  ∃ (S' : Set E) (hS' : S'.Finite), Vpolytope hS' = Vpolytope hS ∩ Hpolytope hH_ := by
  rcases Hpolytope_of_Vpolytope_interior _ hVinterior with ⟨ H_', hH_', hHV ⟩
  have hH_inter := inter_Hpolytope H_' H_ hH_' hH_
  have : IsCompact (Vpolytope hS ∩ Hpolytope hH_) := IsCompact.inter_right (Compact_Vpolytope hS) (Closed_cutSpace H_)
  rw [← hHV, ← hH_inter] at this
  rcases Vpolytope_of_Hpolytope (Set.Finite.union hH_' hH_) this with ⟨ S', hS', hSV ⟩
  exact ⟨ S', hS', by rw [← hSV, ← hHV, ← hH_inter] ⟩
  done

lemma toDirectionHomeo (x : P) : P ≃ₜ E where
  toFun := (· -ᵥ x)
  invFun := (· +ᵥ x)
  left_inv := fun y => by simp
  right_inv := fun y => by simp
  continuous_toFun := continuous_curry_right x continuous_vsub
  continuous_invFun := by continuity
  
lemma toDirectionHomeo.toFun.def (x : E) : 
  ↑(translationHomeo x) = (· + x) := by
  unfold translationHomeo
  simp
  done

theorem MainTheoremOfPolytopes [FiniteDimensional ℝ E] (h : ∃ x, x ≠ (0:E)): 
  (∀ (S : Set E) (hS : S.Finite), 
    ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite), 
    Hpolytope hH_ = Vpolytope hS) ∧ 
  ∀ {H_ : Set (Halfspace E)} (hH_ : H_.Finite), IsCompact (Hpolytope hH_) → 
  ∃ (S : Set E) (hS : S.Finite), Hpolytope hH_ = Vpolytope hS := by
  constructor
  · -- 1.
    intro S hS
    cases' (em (interior (Vpolytope hS)).Nonempty) with hVpolytopeIntNonempty hVpolytopeIntEmpty
    · -- Interior is nonempty 
      exact Hpolytope_of_Vpolytope_interior _ hVpolytopeIntNonempty
    · -- Interior is empty
      clear hVpolytopeIntEmpty
      /-
      1. ConvexHull always have an intrinsic interior -- intrinsicInterior_nonempty! but I need to deal with affine subspace
      2. Any AffineSubspaces are intersections of hyperplanes -- Done!
      3. Any hyperplane is an intersection of two Halfspaces -- Done!
      4. Take union of the set of Halfspaces for Hpolytope in the affineSpan and for the affineSpan -- Done!
      -/
      cases' em (S.Nonempty) with hSnonempty hSempty 
      · -- S is nonempty 
        have := hSnonempty
        rcases this with ⟨ s, hs ⟩
        let S' := S + {-s}
        have hS' : S'.Finite := Set.translation.Finite hS (-s)
        have hS'0 : 0 ∈ S' := by
          rw [Set.mem_translation, sub_eq_add_neg, zero_add, neg_neg]
          exact hs

        have : Nonempty (affineSpan ℝ S) := sorry
        -- rw [← @convexHull_nonempty_iff ℝ] at hS'nonempty
        -- rw [← intrinsicInterior_nonempty (convex_convexHull ℝ S')] at hS'nonempty
        -- cases' hS'nonempty with x hx
        -- unfold intrinsicInterior at hx
        -- rw [Set.mem_image] at hx
        -- rcases hx with ⟨ x, hx, rfl ⟩
        -- have : (spanPoints ℝ S') = vectorSpan ℝ S' := by
        --   sorry
        --   done
        -- have := @affineSpan_convexHull ℝ _ _ _ _ S'

        -- rw [this] at x
        -- sorry
        let S'' := (AffineSubspace.subtype (affineSpan ℝ S)) ⁻¹' S'
        -- have hS'' : S''.Finite := Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective _) hS'

        -- ???



        rcases @Hpolytope_of_Vpolytope_interior (vectorSpan ℝ S') _ _ _ _ _ sorry _ with ⟨ H_''1, hH''1, hHV ⟩

        let H_'1 : Set (Halfspace E) := (Halfspace.val (vectorSpan ℝ S')) '' H_''1
        have hH_'1 : H_'1.Finite := Set.Finite.image _ hH''1

        rcases Submodule_cutspace (vectorSpan ℝ S') with ⟨ H_'2, hH_'2, hH_'2Span' ⟩
        have hH_'2Span: Hpolytope hH_'2 = (vectorSpan ℝ S') := by
          rw [Hpolytope]
          exact hH_'2Span'.symm

        let H_' : Set (Halfspace E) := H_'1 ∪ H_'2
        have hH_' : H_'.Finite := Set.Finite.union hH_'1 hH_'2
        have hH_'12 := inter_Hpolytope H_'1 H_'2 hH_'1 hH_'2

        refine ⟨ H_', hH_', ?_ ⟩
        rw [hH_'12, hH_'2Span, Hpolytope, ← Set.sInter_inter_comm]
        change ⋂₀ ((fun x => x ∩ ↑(vectorSpan ℝ S')) '' ((fun x => SetLike.coe x) '' ((Halfspace.val (vectorSpan ℝ S')) '' H_''1))) = Vpolytope hS
        rw [Set.image_image, Set.image_image, @Set.image_congr' _ _ _ _ (H_''1) (Halfspace.val_eq' (vectorSpan ℝ S')), 
          ← Set.image_image, Set.sInter_image, ← Set.image_sInter ?_ (Subtype.val_injective)]
        change Subtype.val '' Hpolytope hH''1 = Vpolytope hS
        rw [hHV]
        -- Hpolytope side Done!!! The rest needs Vpolytope side to be done
        sorry
        sorry
        sorry
        
        done
      · -- S is empty
        rw [← @convexHull_nonempty_iff ℝ, Set.not_nonempty_iff_eq_empty] at hSempty
        rw [Vpolytope, hSempty]
        exact empty_Hpolytope h
        done

  · -- 2.
    exact Vpolytope_of_Hpolytope
  done

