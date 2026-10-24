variable (p q r : Prop)

theorem eg1_14 :
  (p→q→r) → (p∧q→r) :=
  fun hpqr : p→q→r =>
    fun hpq : p∧q =>
      hpqr hpq.left hpq.right
