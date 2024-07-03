--import Mathlib
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Basic

variable (n : ℕ) [hn : NeZero n]

-----------------------------------------
-- some easy examples                    
example : (n : ZMod n) = 0 := by
  apply CharP.cast_eq_zero

example (a : ZMod 12) : a + 12 = a := by
  have h: (12 : ZMod 12) = 0 := by
    apply CharP.cast_eq_zero
  rw [h]  
  ring

example (a : ZMod n) : a + n = a := by
  simp only [CharP.cast_eq_zero, add_zero]


example (a : ZMod 12) : a*12 = 0 := by
  have h: (12 : ZMod 12) = 0 := by
    apply CharP.cast_eq_zero
  rw [h]  
  ring
  
example (a : ZMod n) : a*n = 0 := by
  simp only [CharP.cast_eq_zero, mul_zero]

------------------------------------------
-- The canonical projection pr: Z → Z/n   

def pr (n : ℕ): ℤ →+* ZMod n := {
  toFun := fun a => a 
  map_one' := Int.cast_one
  map_mul' := Int.cast_mul 
  map_zero' := Int.cast_zero
  map_add' := Int.cast_add
}

#check pr n

example (a b c : ℤ ) : pr n (a * b - c) = pr n a * pr n b - pr n c := by
  simp
   
example (n : ℕ) [NeZero n] (a : ZMod n) : ∃ a' : ℤ, pr n a' = a := by
  use ZMod.val a
  simp 

lemma pr_val_id (n : ℕ) [NeZero n] (a : ZMod n) : pr n (ZMod.val a : ℤ ) = a := by
  simp
  
theorem pr_zero_iff_n_dvd (a : ℤ ): pr n a = 0 ↔ ↑n∣a := by
   simp [pr]
   rw [← Int.cast_zero]
   rw [ZMod.intCast_eq_intCast_iff] -- translates between "mathlib's (Fin n)-based version of Z/n" and "mod n arithmetic"
   rw [Int.modEq_zero_iff_dvd] -- the key statement in the language of "mod n arithmetic": a = 0 mod n ↔ n∣a

----------------------------------------                                     

theorem ZMod.isDomain (p : ℕ) (hp : p.Prime) : IsDomain (ZMod p) := {
  mul_left_cancel_of_ne_zero := by 
    have hp' : NeZero p := { out := Nat.Prime.ne_zero hp }
    intro a b c ha h
    let a' := (ZMod.val a : ℤ) 
    let b' := (ZMod.val b : ℤ)
    let c' := (ZMod.val c : ℤ)
    have hpra : pr p a' = a := pr_val_id p a 
    have hprb : pr p b' = b := pr_val_id p b 
    have hprc : pr p c' = c := pr_val_id p c 
    have ha' : ¬( ↑p∣a') := by 
      rw [← pr_zero_iff_n_dvd p a']
      rw [hpra]
      assumption
    have h' : ↑p∣a*(b-c) := by 
      sorry
    sorry 
  mul_right_cancel_of_ne_zero := by
    sorry
  exists_pair_ne := by 
    sorry
}
