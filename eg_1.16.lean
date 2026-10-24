variable (p q r:Prop)
theorem Eg1_16:
(q→r) → (p∨q) → (p∨r) := by
  intro hqr
  intro hpq
  exact Or.elim hpq (fun hp:p => Or.intro_left r hp)
              (fun hq:q => Or.intro_right p (hqr hq))
