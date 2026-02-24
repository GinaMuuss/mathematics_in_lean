import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  apply abs_of_nonneg at h
  apply (Eq.ge)
  exact h
  apply (le_trans (le_of_lt h) (abs_nonneg x))



theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  sorry

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  rw [abs_of_nonneg h]
  linarith [le_abs_self x, le_abs_self y]
  rw [abs_of_neg h]
  rw [neg_add]
  linarith [neg_le_abs_self x, neg_le_abs_self y]


theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  intro h1
  rcases le_or_gt 0 (y) with h | h
  apply Or.inl
  rw [← abs_of_nonneg h]
  exact h1
  apply Or.inr
  rw [← abs_of_neg h]
  exact h1



theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  sorry

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨ x, y, rfl | rfl⟩; linarith [sq_nonneg x, sq_nonneg y]; linarith [sq_nonneg x, sq_nonneg y]

#check eq_zero_or_eq_zero_of_mul_eq_zero
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1: (x^2 = (x-1)*(x+1)+1 ) := by ring_nf
  rw [h1] at h
  nth_rw 4 [← zero_add 1] at h
  apply add_right_cancel at h
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h
  rcases h with h | h
  apply Or.inl
  linarith
  apply Or.inr
  linarith



example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
    have h1: (x^2 - y^2 = (x-y)*(x+y) ) := by ring_nf
    have h2: (x^2 - y^2 = 0):= by linarith [h]
    rw [h1] at h2
    apply eq_zero_or_eq_zero_of_mul_eq_zero at h2
    rcases h2 with h | h
    apply Or.inl
    linarith
    apply Or.inr
    linarith



section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry
