import Mathlib

example (x y : ℝ) : |x + y| + |x - y| ≥ |x| + |y| := by

  have h : 2 * |x| ≤ |x + y| + |x - y| := by
    calc 2 * |x|
    _ = |2| * |x| := by rw [abs_two]
    _ = |2 * x| := by exact Eq.symm (abs_mul 2 x)
    _ = |x + x| := by ring_nf
    _ = |(x + y) + (x - y)| := by ring
    _ ≤ |x + y| + |x - y| := by exact abs_add (x + y) (x - y)

  have i : 2 * |y| ≤ |x + y| + |x - y| := by
    calc 2 * |y|
    _ = |2| * |y| := by rw [abs_two]
    _ = |2 * y| := by exact Eq.symm (abs_mul 2 y)
    _ = |y + y| := by ring_nf
    _ = |(x + y) - (x - y)| := by ring
    _ ≤ |x + y| + |x - y| := by exact abs_sub (x + y) (x - y)

  calc |x| + |y|
  _ = 1/2 * ((2 * |x|) + (2 * |y|)) := by ring_nf
  _ ≤ 1/2 * ((|x + y| + |x - y|) + (2 * |y|)) := by
    simp
    assumption
  _ ≤ 1/2 * ((|x + y| + |x - y|) + (|x + y| + |x - y|)) := by
    simp
    assumption
  _ = |x + y| + |x - y| := by ring




open Complex

example (z w : ℂ) : ‖z + w‖^2 + ‖z - w‖^2 = 2 * (‖z‖^2 + ‖w‖^2) := by

  calc ‖z + w‖^2 + ‖z - w‖^2
  _ = (z + w).re * (z + w).re + (z + w).im * (z + w).im + ‖z - w‖^2 := by
    rw [← normSq_apply]
    rw [normSq_eq_norm_sq]
  _ = (z + w).re * (z + w).re + (z + w).im * (z + w).im + (z - w).re * (z - w).re + (z - w).im * (z - w).im := by
    rw [← normSq_eq_norm_sq]
    rw [normSq_apply]
    ring_nf
  _ = (z.re + w.re) * (z.re + w.re) + (z.im + w.im) * (z.im + w.im)
   + (z.re - w.re) * (z.re - w.re) + (z.im - w.im) * (z.im - w.im) := by simp
  _ = (z.re) ^ 2 + 2 * z.re * w.re + (w.re) ^ 2 + (z.im) ^ 2 + 2 * z.im * w.im + (w.im) ^ 2
   + (z.re) ^ 2 - 2 * z.re * w.re + (w.re) ^ 2 + (z.im) ^ 2 - 2 * z.im * w.im + (w.im) ^ 2 := by ring_nf
  _ = 2 * ((z.re) ^ 2 + (z.im) ^ 2) + 2 * ((w.re) ^ 2 + (w.im) ^ 2) := by ring_nf
  _ = 2 * ‖z‖^2 +  2 * ‖w‖^2 := by
    rw [← normSq_eq_norm_sq]
    rw [normSq_apply]
    rw [← normSq_eq_norm_sq]
    rw [normSq_apply]
    ring_nf
  _ = 2 * (‖z‖^2 + ‖w‖^2) := by ring_nf




example (x y : ℝ) : |x + y| ≤ |x| + |y| := by

  exact abs_add x y



example (n : ℕ) (h : ℤ) {h₁ : h ≥ -1}: (1 + h)^n ≥ 1 + n * h := by
  sorry
  /- induction n with
  | _ => sorry
  | succ n hn => sorry -/
