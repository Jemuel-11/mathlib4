variable (p q r : Prop)

theorem eg1_17:
  ((p ∨ q) ∨ r) → (p ∨ (q ∨ r)) :=
  fun h =>
      Or.elim h
        (fun hpq =>
          Or.elim hpq
            (fun hp => Or.inl hp)
            (fun hq => Or.inr (Or.inl hq)))
        (fun hr => Or.inr (Or.inr hr))
