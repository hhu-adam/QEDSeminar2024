import Mathlib
open Real

example {fmin fmax : ℝ} (h : fmin ≤ 0 ∧ 0 ≤ fmax) : 2 = 3 := by
  by_cases h_const : fmin = 0 ∧ fmax = 0
  · sorry
  · have h_notconst : fmin < 0 ∨ 0 < fmax := by
      rw [not_and_or] at h_const
      push_neg at h_const
      rcases h_const with h_fmin_not0 | h_fmax_not0
      · left
        exact h_fmin_not0.lt_of_le h.1
      · right
        exact (h_fmax_not0.symm).lt_of_le h.2
    clear h_const
    by_cases h_easy : fmin < 0 ∧ 0 < fmax
    · sorry
    · have h_noteasy : fmin = 0 ∨ 0 = fmax := by
        rw [not_and_or] at h_easy
        repeat rw [eq_iff_le_not_lt]
        rcases h_easy with h_not_fmin_lt_0 | h_not_0_lt_fmax
        · left
          exact ⟨ h.1, h_not_fmin_lt_0⟩ 
        · right
          exact ⟨h.2,h_not_0_lt_fmax⟩
      clear h_easy
      wlog h_pos : fmin = 0 ∧ 0 < fmax
      · have : fmin < 0 ∧ 0 = fmax := by
          rw [not_and_or] at h_pos
          rcases h_pos with h_fmin_lt_0 | h_0_lt_fmax
          · right
            sorry
          · left 
            sorry  
        sorry
    sorry    
