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

lemma AffineMap.preimage_convexHull {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [OrderedRing 𝕜] 
  [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s : Set F} {f : E →ᵃ[𝕜] F} (hf : f.toFun.Injective) (hs : s ⊆ Set.range f):
  ↑f ⁻¹' (convexHull 𝕜) s = (convexHull 𝕜) (↑f ⁻¹' s) := by
  have h1 := Set.image_preimage_eq_of_subset hs
  ext x
  rw [Set.mem_preimage, ← Function.Injective.mem_set_image hf, AffineMap.toFun_eq_coe, AffineMap.image_convexHull, h1]
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


lemma Nonempty_iff_Nonempty_interior_in_direction {S : Set E}{s : E} (hs : s ∈ S) (hS : Nonempty S) :
    (interior ((@AffineIsometryEquiv.VSubconst ℝ (affineSpan ℝ S).direction (affineSpan ℝ S) _ _ _ _ (AffineSubspace.toNormedAddTorsor (affineSpan ℝ (S))) ⟨ s, by apply subset_affineSpan; exact hs ⟩ ) '' 
      ((@Subtype.val E fun x => x ∈ (affineSpan ℝ S)) ⁻¹' ((convexHull ℝ) S)))).Nonempty := by 
  rw [Set.nonempty_coe_sort, ← @convexHull_nonempty_iff ℝ, ← intrinsicInterior_nonempty (convex_convexHull ℝ S), 
    intrinsicInterior, Set.nonempty_image_iff, affineSpan_convexHull] at hS
  rw [ ← AffineIsometryEquiv.coe_toHomeomorph, ← Homeomorph.image_interior, Set.nonempty_image_iff]
  exact hS

theorem Set.vsub_eq_sub {G : Type} [AddGroup G] (g1 g2 : Set G) : g1 -ᵥ g2 = g1 - g2 :=
  rfl

theorem MainTheoremOfPolytopes [FiniteDimensional ℝ E] [Nontrivial E] : 
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
    cases' em (S.Nontrivial) with hSnontrivial hStrivial
    · -- S is nonempty 
      have hSnonempty := Set.Nontrivial.nonempty hSnontrivial
      rcases (Set.Nontrivial.nonempty hSnontrivial) with ⟨ s, hs ⟩
      have hsaff : s ∈ affineSpan ℝ S := by apply subset_affineSpan; exact hs
      let SpanS := affineSpan ℝ S
      let s' : SpanS := ⟨ s, hsaff ⟩

      have := Set.nonempty_coe_sort.mpr hSnonempty
      rcases (Nonempty_iff_Nonempty_interior_in_direction hs this) with ⟨ x, hx ⟩

      have : Nontrivial SpanS.direction := by
        rcases Set.Subtype S (subset_affineSpan ℝ S) with ⟨ S', hS1, hS2 ⟩
        apply @Set.nontrivial_of_nontrivial _ ((AffineIsometryEquiv.VSubconst ℝ s') '' S')
        apply Set.Nontrivial.image _ (AffineIsometryEquiv.injective _)
        rw [← hS1] at hSnontrivial
        exact Set.nontrivial_of_image _ _ hSnontrivial
        done
      
      have : ∃ S', S'.Finite ∧ convexHull ℝ S' = (AffineIsometryEquiv.VSubconst ℝ s') '' ((@Subtype.val E fun x => x ∈ SpanS) ⁻¹' ((convexHull ℝ) S : Set E)) := by
        rw [InDown_eq_DownIn, ← @convexHull_singleton ℝ, Set.vsub_eq_sub, ← convexHull_sub, 
          ← Submodule.coeSubtype]
        refine ⟨ Subtype.val ⁻¹' (S - {s}), ?_, ?_ ⟩
        · 
          apply Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective _)
          rw [Set.sub_singleton]
          exact Set.Finite.image _ hS
        · 
          rw [← Submodule.coeSubtype, ← LinearMap.coe_toAffineMap, ← AffineMap.preimage_convexHull]
          all_goals (try rw [AffineMap.toFun_eq_coe])
          all_goals rw [LinearMap.coe_toAffineMap, Submodule.coeSubtype]
          exact Subtype.val_injective

          rw [Subtype.range_coe_subtype]
          change S - {s} ⊆ (affineSpan ℝ S).direction
          rw [AffineSubspace.coe_direction_eq_vsub_set (Set.Nonempty.mono (subset_affineSpan ℝ S) hSnonempty), Set.vsub_eq_sub]
          exact Set.sub_subset_sub (subset_affineSpan ℝ S) (subset_trans (Set.singleton_subset_iff.mpr hs) (subset_affineSpan ℝ S))
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
        
        have hvaff : v ∈ affineSpan ℝ S := by
          rw [← affineSpan_convexHull]
          apply subset_affineSpan
          exact hv
        let v' : SpanS := ⟨ v, hvaff ⟩

        refine ⟨ v', by rw [Set.mem_preimage]; exact hv, ?_ ⟩
        simp only [Set.le_eq_subset, AffineIsometryEquiv.coe_VSubconst, AffineSubspace.coe_vsub, vsub_eq_sub]
      
      -- In case Span of S has dim = 0
      all_goals (apply Set.Nonempty.image)
      all_goals (try (change Set.Nonempty (Halfspace.val (AffineSubspace.direction SpanS) '' H_''1)))
      all_goals (try apply Set.Nonempty.image)
      all_goals (by_contra h)
      all_goals (rw [Set.not_nonempty_iff_eq_empty] at h)
      all_goals (rw [Hpolytope, h, Set.image_empty, Set.sInter_empty] at hHV)
      all_goals (exact IsCompact.ne_univ (Compact_Vpolytope hS'Fin) hHV.symm)
      done
    · -- S is empty
      rw [Set.not_nontrivial_iff] at hStrivial
      cases' Set.Subsingleton.eq_empty_or_singleton hStrivial with hSempty hSsingleton
      · 
        rw [Vpolytope, hSempty, convexHull_empty]
        exact empty_Hpolytope
      ·
        rcases hSsingleton with ⟨ x, hx ⟩
        rcases @origin_Hpolytope E _ _ _ _ with ⟨ H_, hH_Fin, hH_ ⟩
        refine ⟨ Halfspace_translation x '' H_, Set.Finite.image (Halfspace_translation x) hH_Fin, ?_ ⟩
        rw [Vpolytope, hx, convexHull_singleton, Hpolytope_translation hH_Fin, hH_, Set.singleton_add_singleton, zero_add]
        done 
  · -- 2.
    exact Vpolytope_of_Hpolytope
  done

