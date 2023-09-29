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

lemma Submodule_cutspace (p : Subspace ℝ E) : ∃ H_ : Set (Halfspace E), H_.Finite ∧ ↑p = cutSpace H_ := by
  use Submodule_cut p
  use Submodule_cut_finite p
  ext x
  constructor
  · -- 1.
    rintro hx Hi_ ⟨ H, ⟨ _, ⟨ v, ⟨ i, hi ⟩, rfl ⟩ , hHHalfpair ⟩, rfl ⟩
    rw [Halfspace_mem]
    revert hHHalfpair H
    simp only [Function.comp_apply, ne_eq] at hi 
    rw [← mem_cutSpace,  orthoHyperplane_mem, ← hi, Submodule.inner_left_of_mem_orthogonal hx]
    exact Submodule.coe_mem ((FiniteDimensional.finBasis ℝ { x // x ∈ pᗮ }) i)
  · -- 2.
    rintro hHi_
    rw [Submodule_cut, orthoHyperplanes_mem] at hHi_
    rw [SetLike.mem_coe, ← Submodule.orthogonal_orthogonal p, Submodule.mem_orthogonal]
    intro y hy
    have : ∀ i, inner (Subtype.val (FiniteDimensional.finBasis ℝ { x // x ∈ pᗮ } i)) x = (0:ℝ) := by
      -- equivalent to hHi_, TODO
      sorry
      done
    
    rw [Basis.mem_submodule_iff' (FiniteDimensional.finBasis ℝ { x // x ∈ pᗮ })] at hy
    rcases hy with ⟨ a, rfl ⟩
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro i hi
    rw [real_inner_comm, inner_smul_right, real_inner_comm, this i, mul_zero]
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

def Equiv.VSubconst (x : P) : P ≃ E where
  toFun := (· -ᵥ x)
  invFun := (· +ᵥ x)
  left_inv := fun y => by simp
  right_inv := fun y => by simp

def LinearEquiv.id : E ≃ₗ[ℝ] E where
  toFun := AddHom.id E 
  invFun := AddHom.id E
  left_inv := fun y => by simp
  right_inv := fun y => by simp
  map_add' := by simp
  map_smul' := by simp

lemma LinearEquiv.id_apply (x : E) : LinearEquiv.id x = x := rfl

def AffineEquiv.VSubconst (x : P) : P ≃ᵃ[ℝ] E where
  toEquiv := Equiv.constVSub x
  linear := LinearEquiv.neg ℝ
  map_vadd' p' v := by simp [(Equiv.coe_constVSub), (vsub_vadd_eq_vsub_sub), neg_add_eq_sub]

lemma AffineEquiv.Vsubconst_linear_apply (x : P) (v : E) : (AffineEquiv.VSubconst x).linear v = -v := rfl

def AffineIsometryEquiv.VSubconst (x : P) : P ≃ᵃⁱ[ℝ] E where
  toAffineEquiv := AffineEquiv.VSubconst x
  norm_map := by simp [AffineEquiv.Vsubconst_linear_apply]


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
        have hsaff : s ∈ affineSpan ℝ ((convexHull ℝ) S) := by
          rw [affineSpan_convexHull]
          apply subset_affineSpan
          exact hs
        let s' : affineSpan ℝ ((convexHull ℝ) S) := ⟨ s, hsaff ⟩
        have haffn0 : Nonempty { x // x ∈ affineSpan ℝ ((convexHull ℝ) S) } := Set.Nonempty.to_subtype <| Set.nonempty_of_mem hsaff
        have haffNormedAddTorsor := (affineSpan ℝ ((convexHull ℝ) S)).toNormedAddTorsor
        -- let S' := S + {-s}
        -- have hS' : S'.Finite := Set.translation.Finite hS (-s)
        -- have hS'0 : 0 ∈ S' := by
        --   rw [Set.mem_translation, sub_eq_add_neg, zero_add, neg_neg]
        --   exact hs


        rw [← @convexHull_nonempty_iff ℝ, ← intrinsicInterior_nonempty (convex_convexHull ℝ S), 
          intrinsicInterior, Set.nonempty_image_iff, 
          ← @Set.nonempty_image_iff _ _ ((AffineIsometryEquiv.VSubconst s').toHomeomorph ) _] at hSnonempty
        rcases hSnonempty with ⟨ x, hx ⟩
        rw [Homeomorph.image_interior] at hx 

        -- hope
        have : ∃ S', convexHull ℝ S' = (AffineIsometryEquiv.VSubconst s').toHomeomorph ''
          ((@Subtype.val E fun x => x ∈ ↑(affineSpan ℝ ((convexHull ℝ) S))) ⁻¹' (convexHull ℝ) S) := by
          sorry
          done
        rcases this with ⟨ S', hS' ⟩
        rw [← hS'] at hx -- ???
        
        -- let S'' := (AffineSubspace.subtype (affineSpan ℝ S)) ⁻¹' S'
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

