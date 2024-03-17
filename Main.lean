import src.MainTheorem


#print axioms MainTheoremOfPolytopes
/-
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α
axiom Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α},
  r a b → Quot.mk r a = Quot.mk r b
-/


axiom F : False

example : 0 = 1 := by
  exfalso
  exact F
