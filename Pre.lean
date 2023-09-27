import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Dual


open Pointwise


lemma Set.translation.Finite {α β : Type} [AddGroup α] [AddTorsor α β] {S : Set α} (hS : S.Finite) (x : β) : 
  (S +ᵥ ({x} : Set β)).Finite := by 
  rw [Set.vadd_singleton]
  exact Set.Finite.image _ hS

lemma Set.detranslation.Finite {α β : Type} [AddGroup α] [AddTorsor α β] {S : Set β} (hS : S.Finite) (x : β) : 
  (S -ᵥ ({x} : Set β)).Finite := by 
  rw [Set.vsub_singleton]
  exact Set.Finite.image _ hS

lemma Set.mem_translation {α β : Type} [AddGroup α] [AddTorsor α β] {S : Set α} (x s : β) : 
  s ∈ S +ᵥ ({x} : Set β) ↔ s -ᵥ x ∈ S := by
  rw [Set.vadd_singleton, Set.mem_image]
  constructor
  · -- 1.
    rintro ⟨y, hy, rfl⟩
    rw [vadd_vsub]
    exact hy
  · -- 2.
    intro h
    exact ⟨s -ᵥ x, h, by rw [vsub_vadd]⟩
  done

lemma Set.mem_detranslation {α β : Type} [AddGroup α] [AddTorsor α β] {S : Set β} (x : β) (s : α) : 
  s ∈ S -ᵥ ({x} : Set β) ↔ s +ᵥ x ∈ S := by
  rw [Set.vsub_singleton, Set.mem_image]
  constructor
  · -- 1.
    rintro ⟨y, hy, rfl⟩
    rw [vsub_vadd]
    exact hy
  · -- 2.
    intro h
    exact ⟨s +ᵥ x, h, by rw [vadd_vsub]⟩
  done

lemma Set.neg_add_cancel_right' {α β : Type} [AddGroup α] {S : Set β} [AddTorsor α β] [Neg β] (x : β) : 
  S -ᵥ {x} +ᵥ {x} = S := by
  ext y
  simp only [vsub_singleton, vadd_singleton, mem_image, exists_exists_and_eq_and, vsub_vadd, exists_eq_right]
  done

theorem Set.Finite.isOpen_sInter {s : Set (Set α)} (hs : s.Finite) [TopologicalSpace α] :
  (∀ t ∈ s, IsOpen t) → IsOpen (⋂₀ s) :=
  Finite.induction_on hs (fun _ => by rw [sInter_empty]; exact isOpen_univ) fun _ _ ih h => by
    simp only [sInter_insert, ball_insert_iff] at h ⊢
    exact h.1.inter (ih h.2)

lemma interior_eq_compl_closure_compl [TopologicalSpace α] {s : Set α} : interior s = (closure sᶜ)ᶜ := by
  rw [← compl_compl s, compl_compl sᶜ, interior_compl]
  done

lemma continuous_curry_right {α : Type u} {β : Type v} {γ : Type u_1} [TopologicalSpace α] 
  [TopologicalSpace β] [TopologicalSpace γ] {g : α × β → γ} (b : β) (h : Continuous g) :
  Continuous (λ a => Function.curry g a b) := by 
  exact continuous_curry b <| @Continuous.comp (β × α) (α × β) γ _ _ _ g (Prod.swap) h (continuous_swap) 

lemma Set.translation.continuous {E P : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] 
  [CompleteSpace E] [PseudoMetricSpace P] [NormedAddTorsor E P] (x : P) : 
  Continuous (fun s : E => s +ᵥ x) := by
  exact continuous_curry_right x ((NormedAddTorsor.to_continuousVAdd).1)
