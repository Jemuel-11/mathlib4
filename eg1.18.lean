variable (p q r: Prop)
theorem example_18:

    p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  have hp : p := And.left h
  have hqr : q ∨ r := And.right h

  cases hqr with
  |  inl hq =>
      have hpq : p ∧ q := And.intro hp hq
      exact Or.inl hpq
  |  inr hr =>
      have hpr : p ∧ r := And.intro hp hr
      exact Or.inr hpr
