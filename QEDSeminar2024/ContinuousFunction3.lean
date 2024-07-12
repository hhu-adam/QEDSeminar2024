import Mathlib


open Function Set 

lemma my_ne_of_image_ne {A B : Type} {f : A → B } {a₁ a₂ : A} (h : f a₁ ≠ f a₂) : a₁ ≠ a₂ := by
  exact fun a => h (congrArg f a)

lemma my_twoset_is_finite {A : Type} {S : Set A} (h : ncard S = 2) : Finite S := by
  apply finite_of_ncard_ne_zero
  rw [h]
  simp


open Real

/- main statement -/

theorem main_thm : ¬ ∃ f : ℝ → ℝ, Continuous f ∧ ∀ y : ℝ, ncard (f ⁻¹' {y}) = 2 := by 
  intro h_main
  obtain ⟨ f, hf, hfib ⟩ := h_main
  obtain ⟨ x₁, x₂, h_ne, h_fib_eq ⟩ := ncard_eq_two.mp (hfib 0)
  have h_zero_at_x : x₁ ∈ f ⁻¹' {0} ∧ x₂ ∈ f ⁻¹'{0} := by
    rw [h_fib_eq]
    tauto
  have h_zero_at_x' : f x₁ = 0 ∧ f x₂ = 0 := h_zero_at_x
    --change x₁ ∈ f ⁻¹' {0} ∧ x₂ ∈ f ⁻¹'{0}    
  have h_min :  ∃ x ∈ uIcc x₁ x₂, IsMinOn f (uIcc x₁ x₂) x := by
    apply IsCompact.exists_isMinOn
    · exact isCompact_uIcc
    · exact nonempty_uIcc
    · exact Continuous.continuousOn hf
  have h_max :  ∃ x ∈ uIcc x₁ x₂, IsMaxOn f (uIcc x₁ x₂) x := by
    apply IsCompact.exists_isMaxOn
    · exact isCompact_uIcc
    · exact nonempty_uIcc
    · exact Continuous.continuousOn hf
  obtain ⟨ x_min, h_min, h_min_at_x_min ⟩ := h_min
  obtain ⟨ x_max, h_max, h_max_at_x_max ⟩ := h_max
  rw [isMinOn_iff] at h_min_at_x_min
  rw [isMaxOn_iff] at h_max_at_x_max
  have h_x₃ : ∃ x ∈ uIcc x_min x_max, x ∈ f⁻¹' {0} := by
    apply intermediate_value_uIcc
    · exact Continuous.continuousOn hf
    · rw [← h_zero_at_x.1]
      rw [mem_uIcc]
      left
      constructor
      · exact h_min_at_x_min x₁ left_mem_uIcc
      · exact h_max_at_x_max x₁ left_mem_uIcc
  obtain ⟨ x₃, h₃, h_zero_at_x₃ ⟩ := h_x₃  
  --
  have h_incl : uIcc x_min x_max ⊆ uIcc x₁ x₂ := by
    apply uIcc_subset_uIcc
    exact h_min
    exact h_max  
  --
  by_cases h_easy : x₁ ∉ uIcc x_min x_max ∧ x₂ ∉ uIcc x_min x_max
  · have h_ne₁₃ : x₁ ≠ x₃ := by
      by_contra h_eq
      rw [h_eq] at h_easy
      exact h_easy.1 h₃ 
    have h_ne₂₃: x₂ ≠ x₃ := by
      by_contra h_eq
      rw [h_eq] at h_easy
      exact h_easy.2 h₃
    have h_fin : Finite (f ⁻¹'{0} ) := my_twoset_is_finite (hfib 0)
    have h_lt2 : 2 < ncard (f ⁻¹' {0}) := by
      rw [two_lt_ncard ]
      exact ⟨x₁, h_zero_at_x.1, x₂, h_zero_at_x.2, x₃, h_zero_at_x₃, h_ne, h_ne₁₃, h_ne₂₃⟩ 
    have h_contra : 2 ≠ ncard (f ⁻¹'{0}) := Nat.ne_of_lt h_lt2
    have : 2 = ncard (f ⁻¹'{0}) := (hfib 0).symm
    contradiction
  
