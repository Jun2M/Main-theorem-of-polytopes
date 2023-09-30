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


variable {E P : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [PseudoMetricSpace P] [NormedAddTorsor E P] [FiniteDimensional ℝ E]
open Pointwise


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

lemma InDown_eq_DownIn {p : AffineSubspace ℝ P} [Nonempty { x // x ∈ p }] {S : Set P} (x : p):
  (AffineIsometryEquiv.VSubconst ℝ x) '' ((@Subtype.val P (fun x => x ∈ p)) ⁻¹' S) = 
  (@Subtype.val E fun x => x ∈ p.direction) ⁻¹' (S -ᵥ ({x.1} : Set P)) := by
  ext y
  rw [AffineIsometryEquiv.coe_VSubconst, Set.vsub_singleton, Set.mem_image, Set.mem_preimage, Set.mem_image]
  -- simp only [Set.mem_preimage, Subtype.exists, exists_and_left]
  constructor
  · 
    rintro ⟨ v, h, rfl ⟩
    rw [Set.mem_preimage] at h
    refine ⟨ v, h, rfl ⟩
  · 
    rintro ⟨ v, h, h1 ⟩
    have := y.2
    rw [← h1, AffineSubspace.vsub_right_mem_direction_iff_mem x.2] at this
    refine ⟨ ⟨ v, this ⟩, h, ?_ ⟩
    have : v = (⟨ v, this ⟩ : { x // x ∈ p }).1 := rfl 
    conv at h1 in v => rw [this]
    rw [← AffineSubspace.coe_vsub] at h1
    exact Subtype.val_injective h1
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
    /-
    1. ConvexHull always have an intrinsic interior
    2. Any AffineSubspaces are intersections of hyperplanes
    3. Any hyperplane is an intersection of two Halfspaces
    4. Take union of the set of Halfspaces for Hpolytope in the affineSpan and for the affineSpan
    -/
    cases' em (S.Nonempty) with hSnonempty hSempty 
    · -- S is nonempty 
      have := hSnonempty
      rcases this with ⟨ s, hs ⟩
      have hsaff : s ∈ affineSpan ℝ ((convexHull ℝ) S) := by
        rw [affineSpan_convexHull]
        apply subset_affineSpan
        exact hs
      
      let SpanS := affineSpan ℝ ((convexHull ℝ) S)
      let s' : SpanS := ⟨ s, hsaff ⟩
      have haffn0 : Nonempty { x // x ∈ SpanS } := Set.Nonempty.to_subtype <| Set.nonempty_of_mem hsaff

      rw [← @convexHull_nonempty_iff ℝ, ← intrinsicInterior_nonempty (convex_convexHull ℝ S), 
        intrinsicInterior, Set.nonempty_image_iff, 
        ← @Set.nonempty_image_iff _ _ ((AffineIsometryEquiv.VSubconst ℝ s').toHomeomorph ) _] at hSnonempty
      rcases hSnonempty with ⟨ x, hx ⟩
      rw [Homeomorph.image_interior, AffineIsometryEquiv.coe_toHomeomorph] at hx         
      let A := (AffineIsometryEquiv.VSubconst ℝ s') '' ((@Subtype.val E fun x => x ∈ ↑SpanS) ⁻¹' (convexHull ℝ) S)
      change x ∈ interior A at hx


      -- hope
      have : ∃ S', S'.Finite ∧ convexHull ℝ S' = A := by
        
        sorry
        done
      

      rcases this with ⟨ S', hS'Fin, hS'eq ⟩
      rw [← hS'eq] at hx
      have hS' : Set.Nonempty (interior (Vpolytope hS'Fin)) := by
        apply Set.nonempty_of_mem
        exact hx

      rcases @Hpolytope_of_Vpolytope_interior SpanS.direction _ _ _ _ _ hS'Fin hS' with ⟨ H_''1, hH''1, hHV ⟩

      let H_'1 : Set (Halfspace E) := (Halfspace.val SpanS.direction) '' H_''1
      have hH_'1 : H_'1.Finite := Set.Finite.image _ hH''1

      rcases Submodule_cutspace SpanS.direction with ⟨ H_'2, hH_'2, hH_'2Span' ⟩
      have hH_'2Span: Hpolytope hH_'2 = SpanS.direction := by
        rw [Hpolytope]
        exact hH_'2Span'.symm

      let H_' : Set (Halfspace E) := Halfspace_translation s '' (H_'1 ∪ H_'2)
      have hH_' : H_'.Finite := Set.Finite.image _ (Set.Finite.union hH_'1 hH_'2)
      have hH_'12 := inter_Hpolytope H_'1 H_'2 hH_'1 hH_'2

      refine ⟨ H_', hH_', ?_ ⟩
      rw [Hpolytope_translation, hH_'12, hH_'2Span, Hpolytope, ← Set.sInter_inter_comm]
      change ⋂₀ ((fun x => x ∩ ↑SpanS.direction) '' ((fun x => SetLike.coe x) '' ((Halfspace.val SpanS.direction) '' H_''1))) + {s} = Vpolytope hS
      rw [Set.image_image, Set.image_image, @Set.image_congr' _ _ _ _ (H_''1) (Halfspace.val_eq' SpanS.direction), 
        ← Set.image_image, Set.sInter_image, ← Set.image_sInter ?_ (Subtype.val_injective)]
      change Subtype.val '' Hpolytope hH''1 + {s} = Vpolytope hS
      rw [hHV, Vpolytope, hS'eq]
      change Subtype.val '' ((AffineIsometryEquiv.toHomeomorph (AffineIsometryEquiv.VSubconst ℝ s')) '' (Subtype.val ⁻¹' (convexHull ℝ) S)) + {s} = Vpolytope hS
      rw [AffineIsometryEquiv.coe_toHomeomorph]
      

      rw [Set.add_singleton]
      ext v
      constructor
      · 
        rintro ⟨ _, ⟨ _, ⟨ a, ha, rfl ⟩, rfl ⟩, rfl ⟩
        rw [Set.mem_preimage] at ha
        simp only [Set.le_eq_subset, AffineIsometryEquiv.coe_VSubconst]
        rw [← Submodule.subtype_apply, ← AffineSubspace.subtype_linear, ← vadd_eq_add]
        have hs': s = ↑s' := by rfl
        conv in s => rw [hs', ← AffineSubspace.subtype_apply]
        rw [← AffineMap.map_vadd (AffineSubspace.subtype SpanS) s', vsub_vadd, AffineSubspace.subtype_apply]
        exact ha
      · 
        intro hv
        refine ⟨ v - s, ?_, by simp only [sub_add_cancel] ⟩ 
        rw [Set.image_image]
        
        have hvaff : v ∈ affineSpan ℝ ((convexHull ℝ) S) := by
          apply subset_affineSpan
          exact hv
        let v' : SpanS := ⟨ v, hvaff ⟩

        refine ⟨ v', by rw [Set.mem_preimage]; exact hv, ?_ ⟩
        simp only [Set.le_eq_subset, AffineIsometryEquiv.coe_VSubconst, AffineSubspace.coe_vsub, vsub_eq_sub]
      
      -- carrying Nonempty around
      sorry
      sorry
      
      done
    · -- S is empty
      rw [← @convexHull_nonempty_iff ℝ, Set.not_nonempty_iff_eq_empty] at hSempty
      rw [Vpolytope, hSempty]
      exact empty_Hpolytope h
  · -- 2.
    exact Vpolytope_of_Hpolytope
  done

