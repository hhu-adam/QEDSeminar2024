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

lemma my_neg_preserves_ncard { S : Set ℝ} [Finite S]: (-S).ncard = S.ncard := by
  rw [← Set.image_neg]
  rw [ncard_image_iff]
  exact (Injective.injOn neg_injective)

/- main statement -/

theorem main_thm : ¬ ∃ f : ℝ → ℝ, Continuous f ∧ ∀ y : ℝ, ncard (f ⁻¹' {y}) = 2 := by 
  /- Let x₁ < x₂ be the two points in the fibre of 0.
     We may assume WLOG that ∃ x ∈ [x₁, x₂] such that f x > 0 
     -- if no such x exists, use symmetry at the x-axis, i.e. pass to the function -f.                     
  -/
  suffices : ¬ (  ∃ f : ℝ → ℝ, ∃ x₁ x₂ : ℝ, ∃ x ∈ Ioo x₁ x₂, Continuous f ∧ (∀ y : ℝ, ncard (f ⁻¹' {y}) = 2)
                               ∧ x₁ < x₂ ∧ f x₁ = f x₂ ∧ f x₁ < f x )
  · intro h_main
    apply this
    clear this
    obtain ⟨ f, hf, hfib ⟩ := h_main
    obtain ⟨ x₁, x₂, h_ne, h_fib_eq ⟩ := my_two_set (hfib 0)
    have h_zero_at_x : x₁ ∈ f ⁻¹' {0} ∧ x₂ ∈ f ⁻¹'{0} := by
      rw [h_fib_eq]
      tauto
    have h_zero_at_x' : f x₁ = 0 ∧ f x₂ = 0 := h_zero_at_x
    by_cases h : ∃ x ∈ Ioo x₁ x₂, f x₁ < f x
    · obtain ⟨ x, hx⟩ := h
      use f, x₁, x₂, x
      aesop
    · by_cases h' : ∃ x ∈ Ioo x₁ x₂, f x < f x₁ 
      · obtain ⟨ x', hx', hx'_lt ⟩ := h'
        use (-f), x₁, x₂, x'
        have hfib' : ∀ y : ℝ, ((-f) ⁻¹'{y}).ncard = 2 := by
          have : ∀ y : ℝ, (-f) ⁻¹'{y} = f⁻¹'{-y} := by
            intro y
            ext 
            simp
            exact neg_eq_iff_eq_neg
          intro y
          rw [this y]
          exact hfib (-y)
        have hf' : Continuous (-f) := by
          exact continuous_neg_iff.mpr hf
        have hx'_lt' : (-f) x₁ < (-f) x' := by
          simp only [Pi.neg_apply, neg_lt_neg_iff]
          exact hx'_lt
        aesop 
      · push_neg at h
        push_neg at h'
        obtain ⟨ x, hx ⟩ := exists_between h_ne
        have hx_zero : f x = 0 := by
          specialize h x (mem_Ioo.1 hx)
          specialize h' x (mem_Ioo.2 hx)
          linarith
        have hfin : Finite (f ⁻¹'{0} ) := my_twoset_is_finite (hfib 0)  
        have : ncard (f ⁻¹'{0}) ≠ 2 := my_not_two_set h_zero_at_x.1 hx_zero h_zero_at_x.2 hx.1 hx.2
        specialize hfib 0
        contradiction
  /- As f is continuous, it attains a maximum at some point xmax₁ ∈ [x₁, x₂]. 
     As we have just assumed that f attains a value > 0 somewhere along that interval,
     the maximum at xmax₁ is a proper maximum, i.e. f xmax₁ > 0.
     By the assumption on the fibres of f, there is another point xmax₂ (somewhere in ℝ) 
     where the same value f xmax₁ is attained (i.e. f xmax₂ = f xmax₁).
     We may assume WLOG that xmax₁ < xmax₂
     -- otherwise use symmetry along the y-axis, i.e. pass to the function x ↦ f(-x).
  -/
  suffices : ¬ (  ∃ f : ℝ → ℝ, ∃ x₁ x₂ x_max₁ x_max₂ : ℝ, Continuous f ∧ (∀ y : ℝ, ncard (f ⁻¹' {y}) = 2)
                              ∧ x₁ < x_max₁ ∧ x_max₁ < x₂ ∧ x_max₁ < x_max₂ ∧ IsMaxOn f (Icc x₁ x₂) x_max₁ ∧ f x₁ = f x₂ ∧ f x_max₁ = f x_max₂   
                              ∧ f x₁ < f x_max₁)
  · intro h_main
    apply this
    clear this
    obtain ⟨ f, x₁, x₂, x, hx, hf, hfib, h_x₁_lt_x₂, h_fx₁_eq_fx₂, h_fx₁_lt_fx⟩ := h_main
    have :  ∃ x_max ∈ Icc x₁ x₂, IsMaxOn f (Icc x₁ x₂) x_max := by
      apply IsCompact.exists_isMaxOn
      · exact isCompact_Icc
      · exact nonempty_Icc.2 (le_of_lt h_x₁_lt_x₂)
      · exact Continuous.continuousOn hf
    obtain ⟨ x_max₁, h_max₁, h_max_at_x_max₁ ⟩ := this
    have h_proper_max : f x₁ < f x_max₁ := by
      rw [isMaxOn_iff] at h_max_at_x_max₁
      specialize h_max_at_x_max₁ x (mem_Icc_of_Ioo hx)
      exact gt_of_ge_of_gt h_max_at_x_max₁ h_fx₁_lt_fx 
    have : ∃ x_max₂ ∈ f⁻¹' { f x_max₁ }, x_max₁ ≠ x_max₂ := by
      apply my_second_element 
      · exact hfib (f x_max₁)
      · exact rfl
    obtain ⟨ x_max₂, h_max₂, h_xmax₁_ne_xmax₂⟩ := this
    rw [mem_Icc] at h_max₁
    have h_x₁_lt_xmax₁ : x₁ < x_max₁ := lt_of_le_of_ne h_max₁.1 (my_ne_of_image_ne (ne_of_lt h_proper_max)) 
    have h_xmax₁_lt_max₂ : x_max₁ < x₂ := by  
      rw [h_fx₁_eq_fx₂] at h_proper_max
      exact lt_of_le_of_ne h_max₁.2 (my_ne_of_image_ne (ne_of_lt h_proper_max).symm) 
    by_cases h : x_max₁ < x_max₂
    · use f, x₁, x₂, x_max₁, x_max₂
      aesop
    · use fun x ↦ f (-x), -x₂, -x₁, -x_max₁, -x_max₂ 
      have hf' : Continuous fun x ↦ f (-x) := Continuous.comp' hf continuous_neg
      have hfib' : ∀ y : ℝ, ((fun x ↦ f (-x)) ⁻¹'{y}).ncard = 2 := by
        intro y
        have : (fun x ↦ f (-x)) ⁻¹'{y} = -f⁻¹'{y} := by
          exact rfl
        have h_fin : Finite (f ⁻¹'{y} ) := my_twoset_is_finite (hfib y) 
        rw [this, my_neg_preserves_ncard, ← hfib y]
      have h' : -x_max₁ < -x_max₂ := by
        simp
        rw [not_lt] at h
        exact lt_of_le_of_ne h (id (Ne.symm h_xmax₁_ne_xmax₂))
      have h_max' : IsMaxOn (fun x => f (-x)) (Icc (-x₂) (-x₁)) (-x_max₁) := by
        rw [isMaxOn_iff]
        intro x hx
        simp 
        set x' := -x
        obtain ⟨ hxx₂, hxx₁ ⟩ := mem_Icc.mpr hx
        rw [← neg_le] at hxx₂
        rw [le_neg] at hxx₁ 
        change x₁ ≤ x' at hxx₁
        change x' ≤ x₂ at hxx₂
        have hx' : x' ∈ Icc x₁ x₂ := by
          rw [mem_Icc]
          exact ⟨ hxx₁, hxx₂ ⟩
        exact h_max_at_x_max₁ hx'
      aesop
  /- After these trivial reductions :) we are finally ready for the main part of the proof,
     which of course uses the intermediate value theorem.
  -/    
  intro h_main
  obtain ⟨ f, x₁, x₂, xmax₁, xmax₂, hf, hfib, h_x₁_lt_xmax₁, h_xmax₁_lt_x₂, h_xmax₁_lt_xmax₂, h_max_at_max₁, h_fx₁_eq_fx₂, h_fxmax₁_eq_fxmax₂, h_fx₁_lt_fxmax₁⟩ := h_main
  by_cases h : x₂ < xmax₂
  · have : ∃ v : ℝ, v ∈ Ioo (f x₁) (f xmax₁) := exists_between h_fx₁_lt_fxmax₁ 
    obtain ⟨ v, hv ⟩ := this
    have h₁: ∃ p₁ ∈ Ioo x₁ xmax₁, p₁ ∈ f ⁻¹' {v} := by
      apply intermediate_value_Ioo 
      · exact le_of_lt h_x₁_lt_xmax₁
      · exact Continuous.continuousOn hf
      · exact hv 
    have h₂: ∃ p₂ ∈ Ioo xmax₁ x₂, p₂ ∈ f ⁻¹' {v} := by
      apply intermediate_value_Ioo' 
      · exact le_of_lt h_xmax₁_lt_x₂
      · exact Continuous.continuousOn hf
      · rw [← h_fx₁_eq_fx₂]
        exact hv  
    have h₃: ∃ p₃ ∈ Ioo x₂ xmax₂, p₃ ∈ f ⁻¹' {v} := by
      apply intermediate_value_Ioo
      · exact le_of_lt h
      · exact Continuous.continuousOn hf
      · rw [← h_fx₁_eq_fx₂,← h_fxmax₁_eq_fxmax₂]
        exact hv 
    have h_fin : Finite (f ⁻¹'{v} ) := my_twoset_is_finite (hfib v)
    obtain ⟨p₁, h_p₁, h_p₁v⟩ := h₁
    obtain ⟨p₂, h_p₂, h_p₂v⟩ := h₂
    obtain ⟨p₃, h_p₃, h_p₃v⟩ := h₃
    apply my_not_two_set h_p₁v h_p₂v h_p₃v
    · exact lt_trans h_p₁.2 h_p₂.1
    · exact lt_trans h_p₂.2 h_p₃.1
    exact hfib v
  · sorry
    

      
     

      
      
