import Mathlib
open Real

example { A B : Prop} (hA : A) (hB : B) : A ∧ B := by
  constructor
  · exact hA
  · exact hB

example { A B : Prop} (hnotA : ¬ A) (hAorB: A ∨ B) : B := by
  exact (or_iff_right hnotA).mp hAorB
  
/- Outline of the distinction of cases in the proof of 
   " not continuous function ℝ → ℝ can have all fibres
     of cardinality exactly 2 ",
   for figuring out how to phrase the first WLOG statement
   that uses symmetry at the x-axis.
   (A second WLOG branch in the final proof intended to use
    symmetry at the x-axis is missing from this outline.)
-/


example {fmin fmax : ℝ} (h : fmin ≤ 0 ∧ 0 ≤ fmax) : 2 = 2 := by
  by_cases h_const : fmin = 0 ∧ fmax = 0
  · sorry  -- PROOF in the case that f is constant
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
    · sorry  -- PROOF in the easy case that f has a proper maximum and a proper minimum on the chosen interval
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
          rcases h_pos with h_not_fmin_0 | h_not_0_lt_fmax
          · constructor
            · push_neg at h_not_fmin_0
              exact h_not_fmin_0.lt_of_le h.1
            · exact (or_iff_right h_not_fmin_0).mp h_noteasy
          · constructor
            · exact (or_iff_left h_not_0_lt_fmax).mp h_notconst
            · rw [eq_iff_le_not_lt]
              exact ⟨ h.2, h_not_0_lt_fmax ⟩ 
        sorry -- PROOF that it indeed suffices to complete the argument under the hypothesis declared by WLOG
      sorry -- PROOF of the main statement under the hypothesis declared by WLOG
