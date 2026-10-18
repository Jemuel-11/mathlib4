import Mathlib



def seq_converges_to (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n > N, |a n - L| < ε

theorem bob_theorem (a b c : ℕ → ℝ) (L : ℝ)
  (a_le_b : a ≤ b) (b_le_c : b ≤ c)
  (a_to_L : seq_converges_to a L)
  (c_to_L : seq_converges_to c L) :
  seq_converges_to b L := by
  unfold seq_converges_to
  unfold seq_converges_to at a_to_L
  intro ε ε_pos
  let ν := ε ^ 2
  obtain ⟨N₁, hN₁⟩ := a_to_L ε ε_pos
  obtain ⟨N₂, hN₂⟩ := c_to_L ε ε_pos

  let N : ℕ := max N₁ N₂
  have N₂_le_N : N₂ ≤ N := by
    exact Nat.le_max_right N₁ N₂
  use N
  intro n
  intro n_gt_N
  rw [abs_lt]
  refine ⟨sorry, ?_⟩
