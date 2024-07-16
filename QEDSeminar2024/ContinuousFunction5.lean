import Mathlib


open Function Set

lemma my_ne_of_image_ne {A B : Type} {f : A → B } {a₁ a₂ : A} (h : f a₁ ≠ f a₂) : a₁ ≠ a₂ := by
  exact fun a => h (congrArg f a)

lemma my_twoset_is_finite {A : Type} {S : Set A} (h : ncard S = 2) : Finite S := by
  apply finite_of_ncard_ne_zero
  rw [h]
  simp

example (f: ℝ → ℝ) (x : ℝ) : (-f) x = - (f x) := by
  exact rfl

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
  obtain ⟨ xmin, h_min, h_min_at_xmin ⟩ := h_min
  obtain ⟨ xmax, h_max, h_max_at_xmax ⟩ := h_max
  rw [isMinOn_iff] at h_min_at_xmin
  rw [isMaxOn_iff] at h_max_at_xmax

  have h_incl : uIcc xmin xmax ⊆ uIcc x₁ x₂ := by
    apply uIcc_subset_uIcc
    exact h_min
    exact h_max
  --
  --by_cases h_easy : x₁ ∉ uIcc xmin xmax ∧ x₂ ∉ uIcc xmin xmax
  by_cases h_easy : f xmin < 0 ∧ 0 < f xmax
  · have h_x₃ : ∃ x ∈ uIcc xmin xmax, x ∈ f⁻¹' {0} := by
      apply intermediate_value_uIcc
      · exact Continuous.continuousOn hf
      · rw [← h_zero_at_x.1]
        rw [mem_uIcc]
        left
        constructor
        · exact h_min_at_xmin x₁ left_mem_uIcc
        · exact h_max_at_xmax x₁ left_mem_uIcc
    obtain ⟨ x₃, h₃, h_zero_at_x₃ ⟩ := h_x₃
    --
    have h_ne₁₃ : x₁ ≠ x₃ := by
      sorry
    have h_ne₂₃: x₂ ≠ x₃ := by
      sorry
    have h_fin : Finite (f ⁻¹'{0} ) := my_twoset_is_finite (hfib 0)
    have h_lt2 : 2 < ncard (f ⁻¹' {0}) := by
      rw [two_lt_ncard ]
      exact ⟨x₁, h_zero_at_x.1, x₂, h_zero_at_x.2, x₃, h_zero_at_x₃, h_ne, h_ne₁₃, h_ne₂₃⟩
    have h_contra : 2 ≠ ncard (f ⁻¹'{0}) := Nat.ne_of_lt h_lt2
    have : 2 = ncard (f ⁻¹'{0}) := (hfib 0).symm
    contradiction
  clear h_zero_at_x h_fib_eq h_incl
  · rw [not_and_or] at h_easy
    simp at h_easy
    wlog h_proper_max : 0 < f xmax generalizing f xmin xmax
    · specialize this (-f)
      have hf' : Continuous (-f) := continuous_neg_iff.mpr hf
      specialize this hf'
      have hfib' : ∀ y : ℝ, ((-f) ⁻¹'{y}).ncard = 2 := by
        intro y
        have : (-f) ⁻¹'{y} = f⁻¹'{-y} := by
          ext
          simp
          exact neg_eq_iff_eq_neg          
        rw [this]
        exact hfib (-y)
      specialize this hfib'  
      have h_zero_at_x'' : (-f) x₁ = 0 ∧ (-f) x₂ = 0 := by
        simp
        exact h_zero_at_x'
      specialize this h_zero_at_x''  
      specialize this xmax h_max
      have h_f'_min_at_xmax : ∀ x ∈ uIcc x₁ x₂, (-f) xmax ≤ (-f) x := by
        intro x hx
        simp
        exact h_max_at_xmax x hx
      specialize this h_f'_min_at_xmax
      specialize this xmin h_min
      have h_f'_max_at_xmin : ∀ x ∈ uIcc x₁ x₂, (-f) x ≤ (-f) xmin := by
        intro x hx
        simp
        exact h_min_at_xmin x hx
      specialize this h_f'_max_at_xmin
      rw [not_and_or] at this
      simp at this
      rw [not_and_or] at h_easy
      simp at h_easy
      simp at h_proper_max
      have h'' : 0 ≤ f xmin := this h_easy.symm
      
∀ x ∈ uIcc x₁ x₂, (-f) xmax ≤ (-f) x
      have h_proper_max' : 0 < (-f) xmax := by
          rw [not_lt] at h_proper_max
          have : 0 < - (f xmax) := by 
            exact rfl 
          --simp only [Pi.neg_apply, neg_lt_neg_iff]
          exact hx'_lt

      done
    done 
  done 
