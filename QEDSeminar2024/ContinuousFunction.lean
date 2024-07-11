import Mathlib

open Function Set Real

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
  rcases h_main with ⟨ f, hf, hfib ⟩ 
  have h0 := hfib 0
  apply two_set at h0
  obtain ⟨ x₁, x₂, h_ne, h_fib_eq ⟩ := h0
  have h_comp : IsCompact (Icc x₁ x₂) := isCompact_Icc
  have h_none_e : (Icc x₁ x₂).Nonempty := by 
    simp
    exact le_of_lt h_ne
  have h_max :  ∃ x ∈ Icc x₁ x₂, IsMaxOn f (Icc x₁ x₂) x := by
    apply IsCompact.exists_isMaxOn
    exact h_comp
    exact h_none_e
    exact Continuous.continuousOn hf
  rcases h_max with ⟨m, hm, hmmax⟩ 
  rw [isMaxOn_iff] at hmmax
  clear h_comp h_none_e
  have h_ivt : Icc (f x₁) (f m) ⊆ f '' Icc x₁ m := by
    apply intermediate_value_Icc
    · rw [Set.mem_Icc] at hm
      tauto
    · exact Continuous.continuousOn hf
  have : ∃ z ∈ Icc x₁ x₂, z ∈ f ⁻¹' {f m/2} := by 
    have : f m/2 ∈ f '' Icc x₁ m := by
      have : f m/2 ∈ Icc (f x₁) (f m) := by
        have : x₁ ∈ f ⁻¹' {0} := by
          rw [h_fib_eq]
          tauto 
        rw [this]
        rw [Set.mem_Icc]
        have h' : f x₁ ≤ f m := by 
          apply hmmax  
          rw [Set.mem_Icc]
          constructor
          · linarith
          · linarith
        change f x₁ = 0 at this
        rw [this] at h'
        constructor
        · linarith
        · linarith
      exact mem_of_subset_of_mem h_ivt this
      
        --rw [← this]
        
     
  --use x₁, x₂
  --constructor
  --· exact h_ne
  --· change x₁ ∈ f ⁻¹' {0} ∧ x₂ ∈ f ⁻¹' {0}
  --  rw [h_fib_eq]
  --  tauto

/- closed interval is compact -/

def myI : Set ℝ := Icc 0 1

example : IsCompact (Icc 0 1 : Set ℝ) := isCompact_Icc
