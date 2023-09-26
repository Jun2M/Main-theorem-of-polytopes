import «Chapter2» 
import «Chapter3» 
import «Main»


lemma Subspace_IsClosed {d : ℕ+} (p : Subspace ℝ (EuclideanSpace ℝ (Fin d))) : IsClosed (p : Set (EuclideanSpace ℝ (Fin d))) := by
  apply Submodule.ClosedComplemented.isClosed
  unfold Submodule.ClosedComplemented
  use orthogonalProjection p 
  intro x
  apply orthogonalProjection_mem_subspace_eq_self
  done


variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] 
open Pointwise


-- lemma subtypeval_comm_convexHull (S : Set E) : 
--   (@convexHull ℝ (vectorSpan ℝ S) _ _ _ (Subtype.val ⁻¹' S)) = Subtype.val ⁻¹' (convexHull ℝ S) := by
--   apply subset_antisymm
--   · -- ⊆
--     intro x hx
--     cases' hx with y hy
--     cases' hy with hy1 hy2
--     rw [← hy2]
--     exact ⟨ y, convexHull_mono (Set.image_subset _ hy1) hy1, rfl ⟩
--   · -- ⊇
--     intro x hx
--     cases' hx with y hy
--     cases' hy with hy1 hy2
--     rw [← hy2]
--     exact ⟨ y, convexHull_mono (Set.image_subset _ hy1) hy1, rfl ⟩
--   done



lemma Subspace_inter_Halfspaces (p : Subspace ℝ (EuclideanSpace ℝ (Fin d))) : ∃ H_ : Set (Halfspace (EuclideanSpace ℝ (Fin d))), ↑p = ⋂₀ (SetLike.coe '' H_) := by
  
  -- exists_maximal_orthonormal
  done

noncomputable def Halfspace.val (p : Subspace ℝ E) [CompleteSpace p] (H_' : Halfspace p) : Halfspace E := by
  rcases H_' with ⟨ ⟨ f, hf ⟩, C ⟩ 
  have := Real.exists_extension_norm_eq p f
  choose g hg using this
  exact ⟨ ⟨ g, hg.2 ▸ hf ⟩, C ⟩
  done

lemma convexHull_Subtype_val_preimage (S : Set E) (p : Subspace ℝ E) : 
  (@convexHull ℝ (vectorSpan ℝ S) _ _ _ (Subtype.val ⁻¹' S)) ⊆ Subtype.val ⁻¹' (convexHull ℝ S) := by
  intro x hx
  have : (@Subtype.val E (fun x => x ∈ (vectorSpan ℝ S))) ⁻¹' S ⊆ Subtype.val ⁻¹' (convexHull ℝ) S := by
    apply Set.preimage_mono
    exact subset_convexHull ℝ S
    done
  apply this

  done

lemma Hpolytope_of_Vpolytope_0 [FiniteDimensional ℝ E] {S : Set E} (hS : S.Finite) (hS0 : 0 ∈ S):
  ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite), Hpolytope hH_ = Vpolytope hS := by
  have hSinSpan : S ⊆ vectorSpan ℝ S := by
    intro x hx
    apply vsub_set_subset_vectorSpan
    apply Set.vsub_subset_vsub_left (Set.singleton_subset_iff.mpr hS0)
    rw [Set.vsub_singleton]
    simp only [vsub_eq_sub, sub_zero, Set.image_id']
    exact hx

  let S' : Set (vectorSpan ℝ S) := (@Subtype.val E (fun x => x ∈ (vectorSpan ℝ S))) ⁻¹' S
  have hS' : S'.Finite := Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective _) hS
  have : Set.Nonempty (interior (Vpolytope hS')) := by
    change Set.Nonempty (interior (convexHull ℝ ((@Subtype.val E (fun x => x ∈ (vectorSpan ℝ S))) ⁻¹' S)))
    sorry
    done
  have hVSimage : Vpolytope hS = Subtype.val '' (Vpolytope hS') := by sorry

  rcases @Hpolytope_of_Vpolytope_interior (vectorSpan ℝ S) _ _ _ _ _ hS' this with ⟨ H_'1, hH_'1, hHV ⟩

  let H_1 : Set (Halfspace E) := (Halfspace.val (vectorSpan ℝ S)) '' H_'1
  have hH_1 : H_1.Finite := Set.Finite.image _ hH_'1

  let H_2 : Set (Halfspace E) := by sorry
  have hH_2 : H_2.Finite := by sorry
  have hH_2Span : Hpolytope hH_2 = (vectorSpan ℝ S) := sorry

  let H_ : Set (Halfspace E) := H_1 ∪ H_2
  have hH_ : H_.Finite := Set.Finite.union hH_1 hH_2
  have hH_12 := inter_Hpolytope H_1 H_2 hH_1 hH_2
  refine ⟨ H_, hH_, ?_ ⟩
  rw [hH_12, hVSimage, hH_2Span, ← hHV]

  sorry
  done



theorem MainTheoremOfPolytopes [FiniteDimensional ℝ E] : 
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
      1. ConvexHull always have an intrinsic interior -- intrinsicInterior_nonempty!
      2. Any AffineSubspaces are intersections of hyperplanes
      3. Any hyperplane is an intersection of two Halfspaces -- Done!
      4. Take union of the set of Halfspaces for Hpolytope in the affineSpan and for the affineSpan
      -/
      cases' em (S.Nonempty) with hSnonempty hSempty 
      · -- S is nonempty 
        have := hSnonempty
        rcases this with ⟨ s, hs ⟩
        let S' := S + {-s}
        have hS' : S'.Finite := Set.translation.Finite hS (-s)
        have hS'0 : 0 ∈ S' := by
          rw [Set.mem_translation, neg_neg, zero_add]
          exact hs

        have : Nonempty (affineSpan ℝ S) := sorry
        let S'' := (AffineSubspace.subtype (affineSpan ℝ S)) ⁻¹' S'
        have hS'' : S''.Finite := Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective _) hS'

        rcases @Hpolytope_of_Vpolytope_interior (vectorSpan ℝ S') _ _ _ _ _ hS'' _ with ⟨ H_''1, hH''1, hHV ⟩

        let H_'1 : Set (Halfspace E) := (Halfspace.val (vectorSpan ℝ S')) '' H_''1
        have hH_'1 : H_'1.Finite := Set.Finite.image _ hH''1


        let H_'2 : Set (Halfspace E) := by sorry
        have hH_'2 : H_'2.Finite := by sorry

        let H_' : Set (Halfspace E) := H_'1 ∪ H_'2
        have hH_' : H_'.Finite := Set.Finite.union hH_'1 hH_'2
        have hH_'12 := inter_Hpolytope H_'1 H_'2 hH_'1 hH_'2
        have hH_'V' : Hpolytope hH_' = Vpolytope hS' := by sorry




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
        done
      · -- S is empty
        rw [← @convexHull_nonempty_iff ℝ, Set.not_nonempty_iff_eq_empty] at hSempty
        rw [Vpolytope, hSempty]
        exact empty_Hpolytope h
        done

  · -- 2.
    exact Vpolytope_of_Hpolytope
  done

