import Mathlib


open Function Set

lemma my_ne_of_image_ne {A B : Type} {f : A → B } {a₁ a₂ : A} (h : f a₁ ≠ f a₂) : a₁ ≠ a₂ := by
  exact fun a => h (congrArg f a)

lemma my_twoset_is_finite {A : Type} {S : Set A} (h : ncard S = 2) : Finite S := by
  apply finite_of_ncard_ne_zero
  rw [h]
  simp

lemma my_two_set {S : Set ℝ } (hS : ncard S = 2) : ∃ (x₁ x₂ : ℝ ), x₁ < x₂ ∧ S = {x₁, x₂} := by 
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

lemma my_not_two_set {S : Set ℝ} [hSf : Finite S] {x₁ x₂ x₃ : ℝ} (h1 : x₁ ∈ S) (h2 : x₂ ∈ S) (h3 : x₃ ∈ S) (h12: x₁ < x₂) (h23: x₂ < x₃) : ncard S ≠ 2 := by
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


open Real

/- main statement -/

theorem main_thm : ¬ ∃ f : ℝ → ℝ, Continuous f ∧ ∀ y : ℝ, ncard (f ⁻¹' {y}) = 2 := by
  intro h_main
  obtain ⟨ f, hf, hfib ⟩ := h_main
  obtain ⟨ x₁, x₂, h_x₁_lt_x₂, h_fib_eq ⟩ := my_two_set (hfib 0)
  suffices : ∃ v p₁ p₂ p₃ : ℝ, p₁ < p₂ ∧ p₂ < p₃ ∧ f p₁ = v ∧ f p₂ = v ∧ f p₃  = v
  · obtain ⟨ v, p₁ , p₂, p₃, h₁₂, h₂₃, hfp₁, hfp₂, hfp₃ ⟩ := this
    change p₁ ∈ f ⁻¹' {v} at hfp₁
    change p₂ ∈ f ⁻¹' {v} at hfp₂
    change p₃ ∈ f ⁻¹' {v} at hfp₃
    have h_fin : Finite (f ⁻¹'{v} ) := my_twoset_is_finite (hfib v) 
    have : ncard (f ⁻¹'{v}) ≠ 2 := my_not_two_set hfp₁ hfp₂ hfp₃ h₁₂ h₂₃
    specialize hfib v
    contradiction
  /- here the proof begins …   -/
  have h_zero_at_x : x₁ ∈ f ⁻¹' {0} ∧ x₂ ∈ f ⁻¹'{0} := by
    rw [h_fib_eq]
    tauto
  have h_zero_at_x' : f x₁ = 0 ∧ f x₂ = 0 := h_zero_at_x
    --change x₁ ∈ f ⁻¹' {0} ∧ x₂ ∈ f ⁻¹'{0}
  have h_min :  ∃ x ∈ Icc x₁ x₂, IsMinOn f (Icc x₁ x₂) x := by
    apply IsCompact.exists_isMinOn
    · exact isCompact_Icc
    · exact nonempty_Icc.mpr (le_of_lt h_x₁_lt_x₂)
    · exact Continuous.continuousOn hf
  have h_max :  ∃ x ∈ Icc x₁ x₂, IsMaxOn f (Icc x₁ x₂) x := by
    apply IsCompact.exists_isMaxOn
    · exact isCompact_Icc
    · exact nonempty_Icc.mpr (le_of_lt h_x₁_lt_x₂)
    · exact Continuous.continuousOn hf
  obtain ⟨ xmin, h_min, h_min_at_xmin ⟩ := h_min
  obtain ⟨ xmax, h_max, h_max_at_xmax ⟩ := h_max
  rw [isMinOn_iff] at h_min_at_xmin
  rw [isMaxOn_iff] at h_max_at_xmax
  --
  have h_min_max_ineq : f xmin ≤ 0 ∧ 0 ≤ f xmax := by
    specialize h_min_at_xmin x₁ (left_mem_Icc.mpr (le_of_lt h_x₁_lt_x₂))
    specialize h_max_at_xmax x₁ (left_mem_Icc.mpr (le_of_lt h_x₁_lt_x₂))
    rw [h_zero_at_x'.1] at h_min_at_xmin
    rw [h_zero_at_x'.1] at h_max_at_xmax
    exact ⟨ h_min_at_xmin, h_max_at_xmax ⟩ 
  --  
  by_cases h_const : f xmin = 0 ∧ f xmax = 0
  · /-  The trivial case when f is CONSTANT on the chosen interval  -/
    have : ∃ x : ℝ, x ∈ Ioo x₁ x₂ := exists_between h_x₁_lt_x₂
    obtain ⟨ x , hx ⟩ := this
    specialize h_min_at_xmin x (Ioo_subset_Icc_self hx)
    specialize h_max_at_xmax x (Ioo_subset_Icc_self hx)
    rw [h_const.1] at h_min_at_xmin
    rw [h_const.2] at h_max_at_xmax
    have : f x = 0 := by
      rw [eq_iff_le_not_lt, not_lt]
      exact ⟨ h_max_at_xmax, h_min_at_xmin ⟩ 
    use 0, x₁, x, x₂
    aesop
  · /- Now for the NON-CONSTANT cases. -/
    have h_notconst : f xmin < 0 ∨ 0 < f xmax := by
      rw [not_and_or] at h_const
      push_neg at h_const
      rcases h_const with h_fmin_not0 | h_fmax_not0
      · left
        exact h_fmin_not0.lt_of_le h_min_max_ineq.1
      · right
        exact (h_fmax_not0.symm).lt_of_le h_min_max_ineq.2
    clear h_const  
    --  
    by_cases h_easy : f xmin < 0 ∧ 0 < f xmax
    · /-   First, the EASY case when f has both a proper minimum and a proper maximum on the chosen interval.   -/
      have h_x : ∃ x ∈ uIcc xmin xmax, x ∈ f⁻¹' {0} := by  -- uIoo does not seem to exist 
        apply intermediate_value_uIcc
        · exact Continuous.continuousOn hf
        · rw [mem_uIcc]
          left
          exact h_min_max_ineq
      obtain ⟨ x, h_x, h_zero_at_x ⟩ := h_x
      /- Still need to show x₁ < x < x₂.
         Will do this by first showing x₁ < xmin < x₂ and x₁ < xmax < x₂.
         This is ugly. :(
       -/
      rw [← h_zero_at_x'.1] at h_easy
      have : xmin ≠ x₁ := (my_ne_of_image_ne (ne_of_lt h_easy.1))
      have h_x₁_lt_xmin : x₁ < xmin := (this.symm).lt_of_le h_min.1
      have : x₁ ≠ xmax := (my_ne_of_image_ne (ne_of_lt h_easy.2))
      have h_x₁_lt_xmax : x₁ < xmax := this.lt_of_le h_max.1
      rw [h_zero_at_x'.1, ← h_zero_at_x'.2] at h_easy
      have : xmin ≠ x₂ := my_ne_of_image_ne (ne_of_lt h_easy.1)
      have h_xmin_lt_x₂ : xmin < x₂ := this.lt_of_le h_min.2
      have : x₂ ≠ xmax := my_ne_of_image_ne (ne_of_lt h_easy.2)
      have h_xmax_lt_x₂ : xmax < x₂ := (this.symm).lt_of_le h_max.2
      rw [mem_Icc] at h_min
      rw [mem_uIcc] at h_x
      have h_x₁_lt_x : x₁ < x := by
        rcases h_x with h_x_1 | h_x_2
        · linarith
        · linarith
      have h_ne₂₃: x < x₂ := by
        rcases h_x with h_x_1 | h_x_2
        · linarith
        · linarith
      /- Now we've finally shown that x₁ < x < x₂, and this case is almost done.-/
      have h_fin : Finite (f ⁻¹'{0} ) := my_twoset_is_finite (hfib 0)
      use 0, x₁, x, x₂
      aesop
    · /- Now come the cases where exactly one of {f xmin, f xmax} is ≠ 0.  -/
      have h_noteasy : f xmin = 0 ∨ 0 = f xmax := by
        rw [not_and_or] at h_easy
        repeat rw [eq_iff_le_not_lt]
        rcases h_easy with h_not_fmin_lt_0 | h_not_0_lt_fmax
        · left
          exact ⟨ h_min_max_ineq.1, h_not_fmin_lt_0⟩ 
        · right
          exact ⟨ h_min_max_ineq.2, h_not_0_lt_fmax⟩
      clear h_easy
      /- We reduce to the case that f xmin = 0 and f xmax ≠ 0 using symmetry of the 
         problem along the x-axis, using WLOG.  -/
      clear h_fib_eq h_zero_at_x
      wlog h_pos : f xmin = 0 ∧ 0 < f xmax  generalizing f xmin xmax with h_wlog
      · have : f xmin < 0 ∧ 0 = f xmax := by
          rw [not_and_or] at h_pos
          rcases h_pos with h_not_fmin_0 | h_not_0_lt_fmax
          · constructor
            · push_neg at h_not_fmin_0
              exact h_not_fmin_0.lt_of_le h.1
            · exact (or_iff_right h_not_fmin_0).mp h_noteasy
          · constructor
            · exact (or_iff_left h_not_0_lt_fmax).mp h_notconst
            · rw [eq_iff_le_not_lt]
              exact ⟨ h_min_max_ineq.2, h_not_0_lt_fmax ⟩ 
        /- PROOF that it indeed suffices to complete the argument under the hypothesis declared by WLOG-/
        specialize h_wlog (-f)
        have hf' : Continuous (-f) := continuous_neg_iff.mpr hf
        specialize h_wlog hf'
        have hfib' : ∀ y : ℝ, ((-f) ⁻¹'{y}).ncard = 2 := by
          intro y
          have : (-f) ⁻¹'{y} = f⁻¹'{-y} := by
            ext
            simp
            exact neg_eq_iff_eq_neg          
          rw [this]
          exact hfib (-y)
        specialize h_wlog hfib'        
        have h_zero_at_x'' : (-f) x₁ = 0 ∧ (-f) x₂ = 0 := by
          simp
        specialize h_wlog h_zero_at_x''
        have h_max_at_xmax' : ∀ x ∈ Icc x₁ x₂, (-f) xmax ≤ (-f) x := by
          intro x hx
          specialize h_max_at_xmax x hx
          simp
          exact h_max_at_xmax
        specialize h_wlog xmax h_max h_max_at_xmax' 
        have h_min_at_xmin' : ∀ x ∈ Icc x₁ x₂, (-f) x ≤ (-f) xmin := by
          intro x hx
          specialize h_min_at_xmin x hx
          simp
          exact h_min_at_xmin
        specialize h_wlog xmin h_min h_min_at_xmin'
        simp at h_wlog
        aesop
      sorry -- PROOF of the main statement under the hypothesis declared by WLOG
