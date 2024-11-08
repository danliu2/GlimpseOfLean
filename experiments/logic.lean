import GlimpseOfLean.Library.Basic
open Function

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by {
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  constructor
  · exact h hp
  · exact h' hq
}

example (p q r : Prop) (h: p -> r) (h': q -> s)
