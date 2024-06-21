-- import Mathlib
import Mathlib.Tactic
import Mathlib.Data.Nat.Cast.Defs

instance intQuotRel : Setoid (ℕ × ℕ) where
  r a b := a.1 + b.2 = b.1 + a.2
  iseqv := {
    refl := fun x => rfl
    symm := fun {x y} h => Eq.symm h
    trans := fun {x y z} hxy hyz => by
      apply add_right_cancel (b := y.1 + y.2)
      trans (x.1 + y.2) + (y.1 + z.2)
      · ring
      · rw [hxy, hyz]
        ring
  }

def myInt := Quotient intQuotRel

def g : ℕ × ℕ → ℤ := fun (a, b) => a - b

#check g (1,1) 

example (x y : ℕ ) (h : x = y) : (x : ℤ) = y := by
  simp 
  assumption

theorem g_welldef (x y : ℕ × ℕ) (h : x ≈ y) : g x = g y := by
  simp [g]
  have h' : (x.1 : ℤ) = y.1 + x.2 - y.2 := by
    trans x.1 + y.2 - y.2
    ring
    rw [← Nat.cast_add]
    rw [h]
    rw [Nat.cast_add]
  rw [h']
  ring 

def g' : myInt → ℤ := Quotient.lift g g_welldef

theorem g'_bijective : (Function.Bijective g') := by
  sorry
