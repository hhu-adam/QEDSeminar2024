import Mathlib


open Function Set 

lemma my_ne_of_image_ne {A B : Type} {f : A → B } {a₁ a₂ : A} (h : f a₁ ≠ f a₂) : a₁ ≠ a₂ := by
  exact fun a => h (congrArg f a)

lemma my_twoset_is_finite {A : Type} {S : Set A} (h : ncard S = 2) : Finite S := by
  apply finite_of_ncard_ne_zero
  rw [h]
  simp

lemma my_second_element {A : Type} {S : Set A} { a : A } (h : ncard S = 2) (ha : a ∈ S) : ∃ b ∈ S, a ≠ b := by
    apply ncard_eq_two.mp at h
    rcases h with ⟨ a', b', h_ne, hS ⟩ 
    rw [hS] at ha
    rw [hS]
    change a = a' ∨ a = b' at ha
    rcases ha with ha' | hb'
    · use b'
      constructor
      · tauto
      rw [ha']
      exact h_ne
    · use a'
      constructor
      · tauto
      rw [hb']
      exact h_ne.symm

lemma my_second_element' {A : Type} {S : Set A} { a : A } (h : ncard S = 2) (ha : a ∈ S) : ∃ b, S = {a, b} := by
    apply ncard_eq_two.mp at h
    rcases h with ⟨ a', b', h_ne, hS ⟩ 
    rw [hS] at ha
    rw [hS]
    change a = a' ∨ a = b' at ha
    rcases ha with ha' | hb'
    · tauto
    · rw [pair_comm a' b']
      tauto 

example {A : Type} [LinearOrder A] (a b : A) : max a b = a ∨ max a b = b := by
  exact max_choice a b

example {A : Type} (S : Set ℕ) (f : ℕ → A) (a : A) (hs : s ∈ S) (hfs : f s = a) (ht : t ∈ S) (hft : f t = a ) : f (max s t) = a := by
  rcases max_choice s t with hs | ht
  · rw [hs]
    exact hfs
  · rw [ht]
    exact hft

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
  let x₁₂ := max x₁ x₂
  have h_zero_at_x₁₂ : f x₁₂ = 0 := by
    change f (max x₁ x₂) = 0
    rcases max_choice x₁ x₂ with h₁ | h₂ 
    · rw [h₁] 
      exact h_zero_at_x.1
    · rw [h₂]
      exact h_zero_at_x.2
  have h_min :  ∃ x ∈ uIcc x₁₂ (x₁₂+1), IsMinOn f (uIcc x₁₂ (x₁₂+1)) x := by
    apply IsCompact.exists_isMinOn
    · exact isCompact_uIcc
    · exact nonempty_uIcc
    · exact Continuous.continuousOn hf
  have h_max :  ∃ x ∈ uIcc x₁₂ (x₁₂+1), IsMaxOn f (uIcc x₁₂ (x₁₂+1)) x := by
    apply IsCompact.exists_isMaxOn
    · exact isCompact_uIcc
    · exact nonempty_uIcc
    · exact Continuous.continuousOn hf
  obtain ⟨ x_min, h_min, h_min_at_x_min ⟩ := h_min
  obtain ⟨ x_max, h_max, h_max_at_x_max ⟩ := h_max
  rw [isMinOn_iff] at h_min_at_x_min
  rw [isMaxOn_iff] at h_max_at_x_max
  specialize h_min_at_x_min x₁₂ left_mem_uIcc
  specialize h_max_at_x_max x₁₂ left_mem_uIcc
  rw [h_zero_at_x₁₂] at h_min_at_x_min
  rw [h_zero_at_x₁₂] at h_max_at_x_max
  have h : ∃ x_max₂ ∈ f⁻¹' { f x_max }, x_max ≠ x_max₂ := by
    apply my_second_element 
    · exact hfib (f x_max)
    · rfl
  obtain ⟨ x_max₂, h_x_max₂, h_max_ne ⟩ := h
