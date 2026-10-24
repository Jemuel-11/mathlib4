variable (p q r : Prop)

theorem eg1_15 :
(p→q) → (p∧r)→ (q∧r) :=
fun hpq: p→q =>
  fun hpr : p∧r =>
    have hp :p := hpr.left
    have hq : q := hpq hp
    And.intro hq hpr.right
