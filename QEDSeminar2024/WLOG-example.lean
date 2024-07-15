import Mathlib

open Real

example (a b : ℝ) (h_ne : a ≠ b) : False := by
  wlog h : a < b generalizing a b with h'
  · rw [not_lt] at h
    specialize h' b a h_ne.symm
    exact h' ((lt_of_le_of_ne h) h_ne.symm)
  sorry
