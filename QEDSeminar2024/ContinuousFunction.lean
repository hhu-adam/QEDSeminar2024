import Mathlib


open Function Set 


example (A : Type) (B : Type) (f : A → B ) (S : Set A) (b : B) (h : b ∈ f '' S) : ∃ a ∈ S, f a = b  := by
  rw [mem_image] at h
  assumption

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

example {x₁ x₂ : ℝ } (h : x₁ ≤ x₂ ): x₁ ∈ Icc x₁ x₂ := by
  exact left_mem_Icc.mpr h

lemma my_max_left_boundary {x₁ x₂ y : ℝ} (f : ℝ → ℝ) (hx : x₁ ≤ x₂) (h : ∀ x ∈ Icc x₁ x₂, f x ≤ y ) : f x₁ ≤ y := by
  exact h x₁ (left_mem_Icc.mpr hx)
  
  
lemma my_max_right_boundary {x₁ x₂ y : ℝ} (f : ℝ → ℝ) (hx : x₁ ≤ x₂) (h : ∀ x ∈ Icc x₁ x₂, f x ≤ y ) : f x₂ ≤ y := by
  exact h x₂ (right_mem_Icc.mpr hx)


lemma my_average {y₁ y₂ : ℝ} (h : y₁ ≤ y₂) : (y₁ + y₂)/2 ∈ Icc y₁ y₂ := by 
  rw [Set.mem_Icc]
  constructor
  · linarith
  · linarith

lemma my_ivt ( f : ℝ → ℝ) (hf : Continuous f) (x₁ x₂ y : ℝ) (hx: x₁ ≤ x₂ ) (hy : y ∈ Icc (f x₁) (f x₂)) : ∃ z ∈ Icc x₁ x₂, z ∈ f ⁻¹' {y} := by
  apply intermediate_value_Icc
  · rw [Set.mem_Icc] at hy
    tauto
  · exact Continuous.continuousOn hf
  assumption

  /-have : ∃ z ∈ Icc x₁ x₂, z ∈ f ⁻¹' {f m/2} := by 
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
    rw [mem_image] at this  -/

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
  --
  have hy : f m/2 ∈ Icc (f x₁) (f m) := by
    have hx : x₁ ≤ x₂ := le_of_lt h_ne
    have h' : f x₁ ≤ f m := by  
      exact hmmax x₁ (left_mem_Icc.mpr hx)
    apply my_average at h'
    have hx₁ : f x₁ = 0 := by 
      change x₁ ∈ f ⁻¹' {0}
      rw [h_fib_eq]
      tauto 
    simp [hx₁] at h'
    simp [hx₁]
    exact h'
  have : ∃ z₁ ∈ Icc x₁ m, z₁ ∈ f ⁻¹' {f m/2} := by 
    apply my_ivt 
    · exact hf
    · rw [Set.mem_Icc] at hm
      exact hm.1
    · exact hy 
  have : ∃ z₂ ∈ Icc m x₂, z₂ ∈ f ⁻¹' {f m/2} := by 
    apply my_ivt 
    · exact hf
    · rw [Set.mem_Icc] at hm
      exact hm.2
    · exact hy 

/- closed interval is compact -/

def myI : Set ℝ := Icc 0 1

example : IsCompact (Icc 0 1 : Set ℝ) := isCompact_Icc
