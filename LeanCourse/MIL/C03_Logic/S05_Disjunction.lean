import LeanCourse.Common
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
  . rw [abs_of_neg h]
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
  · rw [abs_of_nonneg]
    exact h
  rw [abs_of_neg]
  linarith
  exact h

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rw [← abs_neg]
  apply le_abs_self

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 x with h1 | h1
  rcases le_or_gt 0 y with h2 | h2
  have : 0 ≤ x + y := by linarith
  rw [abs_of_nonneg this, abs_of_nonneg h1, abs_of_nonneg h2]
  rcases le_or_gt 0 (x+y) with h3 | h3
  rw [abs_of_nonneg h3, abs_of_nonneg h1, abs_of_neg h2]
  linarith
  rw [abs_of_neg h3, abs_of_nonneg h1, abs_of_neg h2]
  linarith
  rcases le_or_gt 0 y with h2 | h2
  rcases le_or_gt 0 (x+y) with h3 | h3
  rw [abs_of_nonneg h3, abs_of_neg h1, abs_of_nonneg h2]
  linarith
  rw [abs_of_neg h3, abs_of_neg h1, abs_of_nonneg h2]
  linarith
  have : x + y < 0 := by linarith
  rw [abs_of_neg this, abs_of_neg h1, abs_of_neg h2]
  linarith

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  intro h1
  rcases le_or_gt 0 y with h2 | h2
  left
  rw [abs_of_nonneg h2] at h1
  exact h1
  right
  rw [abs_of_neg h2] at h1
  exact h1
  intro h
  rcases h with h | h
  apply lt_of_lt_of_le
  exact h
  exact le_abs_self y
  apply lt_of_lt_of_le
  exact h
  exact neg_le_abs_self y

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  sorry

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, h1 | h2⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x-1)*(x+1) = 0 := by
    ring
    rw [h]
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  left
  apply eq_of_sub_eq_zero h
  right
  apply eq_of_sub_eq_zero
  ring
  rw [add_comm]
  exact h

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x-y)*(x+y) = 0 := by
    ring
    rw [h]
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  left
  apply eq_of_sub_eq_zero h
  right
  apply eq_neg_of_add_eq_zero_left h

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
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro h
  rcases em P with h' | h'
  right
  apply h h'
  left
  exact h'
  intro h
  intro h'
  rcases h with h2 | h2
  contradiction
  exact h2
