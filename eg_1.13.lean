variable (p q r: Prop)
theorem example1_13:
    (p ∧ q → r) → (p→q→r) := by
    intro hpqr
    intro hp
    intro hq
    have hpq: p ∧ q := And.intro hp hq
    exact hpqr hpq
