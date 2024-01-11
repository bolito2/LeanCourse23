import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.Complex.Polynomial
import Init.System.IO

section
open MvPolynomial

variable {n : ℕ} (n_pos : n > 0)

def Transposition (i : Fin n)(j : Fin n) : (Fin n → Fin n) :=
  λ k => if k = i then j else if k = j then i else k

noncomputable def SwapVariables (p : MvPolynomial (Fin n) ℂ) (i : Fin n) (j : Fin n) : MvPolynomial (Fin n) ℂ :=
  (rename (Transposition i j)) p

noncomputable def circleEquation : MvPolynomial (Fin 2) ℂ := X 0 ^ 2 + X 1 ^ 2 - 1

example : circleEquation = SwapVariables circleEquation 0 1 := by
  simp [circleEquation, SwapVariables, Transposition]
  ring

#check IsLocalization.mk' (FractionRing (MvPolynomial (Fin n) ℂ))

noncomputable def Demazure (p : MvPolynomial (Fin n) ℂ) (i : Fin n) (h : i < n - 1) : FractionRing (MvPolynomial (Fin n) ℂ)  :=
  have : i < n := by
    have : n - 1 < n := by
      apply Nat.sub_lt
      apply n_pos
      apply Nat.le_refl
    apply Nat.lt_trans h this

  let i' : Fin n := ⟨i, this⟩

  have h' : i + 1 < n := by
    apply Nat.add_lt_of_lt_sub h

  let i'_plus_1 : Fin n := ⟨i + 1, h'⟩
  let numerator := (p - SwapVariables p i' i'_plus_1)
  let denominator : (MvPolynomial (Fin n) ℂ) := (X i' - X i'_plus_1)

  let numerator_in_frac := algebraMap (MvPolynomial (Fin n) ℂ) (FractionRing (MvPolynomial (Fin n) ℂ)) numerator
  let denominator_in_frac := algebraMap (MvPolynomial (Fin n) ℂ) (FractionRing (MvPolynomial (Fin n) ℂ)) denominator

  numerator_in_frac / denominator_in_frac

lemma wario :  2 > 0 := by norm_num
lemma wah :  0 < 2 - 1 := by norm_num

noncomputable def waluigi : FractionRing (MvPolynomial (Fin 2) ℂ ) := Demazure wario circleEquation 0 wah
example : waluigi = 0 := by
  simp [waluigi, Demazure, circleEquation, SwapVariables, Transposition]
  sorry
