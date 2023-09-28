import Mathlib.Analysis.Convex.Intrinsic


open Pointwise


lemma Set.translation.Finite {α : Type} [AddGroup α]  {S : Set α} (hS : S.Finite)  (x : α) : 
  (S + ({x} : Set α)).Finite := by 
  rw [Set.add_singleton]
  exact Set.Finite.image _ hS

lemma Set.mem_translation {α : Type} [AddGroup α] {S : Set α}  (x s : α) : 
  s ∈ S + ({x} : Set α) ↔ s - x ∈ S := by
  rw [Set.add_singleton, Set.mem_image]
  constructor
  · -- 1.
    rintro ⟨y, hy, rfl⟩
    rw [add_sub_cancel]
    exact hy
  · -- 2.
    intro h
    exact ⟨s - x, h, by rw [sub_add_cancel]⟩
  done

lemma Set.sub_eq_neg_add {α : Type} [AddGroup α] (S : Set α) (x : α) : 
  S - {x} = S + {(-x)} := by
  ext y
  simp only [sub_singleton, mem_image, add_singleton, image_add_right, neg_neg, mem_preimage]
  refine ⟨ ?_, fun h => ⟨y + x, h, by rw [add_sub_cancel]⟩ ⟩
  rintro ⟨z, hz, rfl⟩
  rw [sub_add_cancel]
  exact hz

lemma Set.neg_add_cancel_right' {α : Type} [AddGroup α] {S : Set α} (x : α) : 
  S - {x} + {x} = S := by
  ext y
  simp only [sub_singleton, add_singleton, mem_image, exists_exists_and_eq_and, sub_add_cancel, exists_eq_right]
  done

theorem Set.Finite.isOpen_sInter {s : Set (Set α)} (hs : s.Finite) [TopologicalSpace α] :
  (∀ t ∈ s, IsOpen t) → IsOpen (⋂₀ s) :=
  Finite.induction_on hs (fun _ => by rw [sInter_empty]; exact isOpen_univ) fun _ _ ih h => by
    simp only [sInter_insert, ball_insert_iff] at h ⊢
    exact h.1.inter (ih h.2)

lemma interior_eq_compl_closure_compl [TopologicalSpace α] {s : Set α} : interior s = (closure sᶜ)ᶜ := by
  rw [← compl_compl s, compl_compl sᶜ, interior_compl]
  done

lemma Set.sInter_inter_comm {α : Type u_1} {s : Set (Set α)} (hs : s.Nonempty) {t : Set α} : ⋂₀ ((· ∩ t) '' s) = (⋂₀ s) ∩ t := by
  ext x
  simp only [mem_sInter, mem_inter_iff, mem_singleton_iff, and_imp]
  constructor
  · -- 1.
    intro h
    have : Nonempty.some hs ∩ t ∈ (fun x => x ∩ t) '' s := by
      rw [mem_image]
      exact ⟨Nonempty.some hs, hs.some_mem, rfl⟩
    refine ⟨ ?_, (h (hs.some ∩ t) this).2⟩
    intro y hy
    have : y ∩ t ∈ (fun x => x ∩ t) '' s := by
      rw [mem_image]
      exact ⟨y, hy, rfl⟩
    exact (h (y ∩ t) this).1
  · -- 2.
    rintro h y ⟨ z, hz, rfl ⟩ 
    exact mem_inter (h.1 z hz) h.2
  done

lemma Set.image_sInter {α : Type u_1} {β : Type u_2} {S : Set (Set α)} (hS : S.Nonempty) {f : α → β} (hf : f.Injective) :
  f '' ⋂₀ S = ⋂ (s : Set α) (_ : s ∈ S), f '' s := by
  apply subset_antisymm (image_sInter_subset S f)
  intro y hy
  rw [Set.mem_image]
  have : f '' Nonempty.some hS ∈ range fun s => ⋂ (_ : s ∈ S), f '' s := by
    simp
    refine ⟨Nonempty.some hS, ?_⟩
    ext x
    rw [Set.mem_iInter]
    simp [hS.some_mem]
    done
  rcases hy (f '' hS.some) this with ⟨x, _, rfl⟩
  refine ⟨x, ?_, rfl⟩
  rw [Set.mem_iInter] at hy
  simp at hy
  rw [Set.mem_sInter]
  intro s hs
  rcases hy s hs with ⟨z, hz, hzz⟩
  have := hf hzz
  exact this ▸ hz
  done

lemma continuous_curry_right {α : Type u} {β : Type v} {γ : Type u_1} [TopologicalSpace α] 
  [TopologicalSpace β] [TopologicalSpace γ] {g : α × β → γ} (b : β) (h : Continuous g) :
  Continuous (λ a => Function.curry g a b) := by 
  exact continuous_curry b <| @Continuous.comp (β × α) (α × β) γ _ _ _ g (Prod.swap) h (continuous_swap) 
