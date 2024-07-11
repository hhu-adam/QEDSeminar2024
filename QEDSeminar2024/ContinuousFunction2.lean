import Mathlib


open Function Set 


example (A : Type) (B : Type) (f : A → B ) (S : Set A) (b : B) (h : b ∈ f '' S) : ∃ a ∈ S, f a = b  := by
  rw [mem_image] at h
  assumption

example (A : Type) (B : Type) (f : A → B ) (a : A) (b : B) (h : a ∈ f ⁻¹' {b}) : f a = b := by
  exact h

open Real
variable (a b c : ℝ)
example (hb : b ∈ Icc a c) : a ≤ b := by
  rw [Set.mem_Icc] at hb
  tauto
  --exact hb.1
  
example : a ∈ ({a, b} : Set ℝ) := by 
  tauto 

example (ha : 0 ≤ a) : (a/2 ≤ a) := by
  linarith
  --exact half_le_self ha

example (ha : 0 ≤ a) : (0 ≤ a/2) := by
  linarith
  

/- sets with few elements -/

lemma two_set (S : Set ℝ ) (hS : ncard S = 2) : ∃ (x₁ x₂ : ℝ ), x₁ < x₂ ∧ S = {x₁, x₂} := by 
  apply ncard_eq_two.mp at hS
  obtain ⟨ x₁, x₂, h_ne, h_S_eq ⟩ := hS
  by_cases h_lt : x₁ < x₂ 
  · use x₁, x₂ 
  · use x₂, x₁
    · constructor
      rw [not_lt] at h_lt
      exact Ne.lt_of_le h_ne.symm h_lt
      rw [pair_comm x₂ x₁]
      exact h_S_eq


lemma not_two_set (S : Set ℝ) [hSf : Finite S] (x₁ x₂ x₃ : ℝ ) (h1 : x₁ ∈ S) (h2 : x₂ ∈ S) (h3 : x₃ ∈ S) (h12: x₁ < x₂) (h23: x₂ < x₃) : ncard S ≠ 2 := by
  intro hS
  have h_lt : 2 < S.ncard := by
    rw [two_lt_ncard]
    -- short-cut from here: exact ⟨x₁, h1, x₂, h2, x₃, h3, ne_of_lt h12, ne_of_lt (h12.trans h23), ne_of_lt h23⟩ 
    use x₁
    constructor
    exact h1
    use x₂
    constructor
    exact h2
    use x₃ 
    constructor
    exact h3
    constructor
    exact ne_of_lt h12
    constructor
    exact ne_of_lt (h12.trans h23)
    exact ne_of_lt h23
  have : 2 ≠ S.ncard := Nat.ne_of_lt h_lt
  symm at hS
  contradiction

/- main statement -/

theorem main_thm : ¬ ∃ f : ℝ → ℝ, Continuous f ∧ ∀ y : ℝ, ncard (f ⁻¹' {y}) = 2 := by 
  intro h_main
  obtain ⟨ f, hf, hfib ⟩ := h_main
  obtain ⟨ x₁, x₂, h_ne, h_fib_eq ⟩ := ncard_eq_two.mp (hfib 0)
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
  obtain ⟨ x_max, h_man, h_max_at_x_max ⟩ := h_max
  rw [isMinOn_iff] at h_min_at_x_min
  rw [isMaxOn_iff] at h_max_at_x_max
  have h_x₃ : ∃ x ∈ uIcc x_min x_max, x ∈ f⁻¹' {0} := by
    apply intermediate_value_uIcc
    · exact Continuous.continuousOn hf
    · have h_x₁ : f x₁ = 0 := by
       change x₁ ∈ f ⁻¹' {0} 
       rw [h_fib_eq]
       tauto
      rw [← h_x₁]
      rw [mem_uIcc]
      left
      constructor
      · exact h_min_at_x_min x₁ left_mem_uIcc
      · exact h_max_at_x_max x₁ left_mem_uIcc
  

/- closed interval is compact -/

def myI : Set ℝ := Icc 0 1

example : IsCompact (Icc 0 1 : Set ℝ) := isCompact_Icc
