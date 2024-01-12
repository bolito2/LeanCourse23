import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.Complex.Polynomial
import Init.System.IO

section
open MvPolynomial

variable {n : ℕ} (n_pos : n > 0)

def Transposition (i : Fin n)(j : Fin n) : (Fin n → Fin n) :=
  fun k ↦ if k = i then j else if k = j then i else k

noncomputable def SwapVariables (p : MvPolynomial (Fin n) ℂ) (i : Fin n) (j : Fin n) : MvPolynomial (Fin n) ℂ :=
  (rename (Transposition i j)) p

noncomputable def circleEquation : MvPolynomial (Fin 2) ℂ := X 0 ^ 2 + X 1 ^ 2 - 1

example : circleEquation = SwapVariables circleEquation 0 1 := by
  simp [circleEquation, SwapVariables, Transposition]
  ring

lemma transposition_order_two (i : Fin n) (j : Fin n) : Transposition i j ∘ Transposition i j = (fun k ↦ k) := by
  simp[Transposition]
  funext k
  unfold Function.comp

  dsimp
  rcases eq_or_ne j i with i_eq_j | i_ne_j

  rcases eq_or_ne k i with k_eq_i | k_ne_i
  rw[if_pos k_eq_i, if_pos rfl, if_pos i_eq_j, i_eq_j, ← k_eq_i]

  rw[if_neg k_ne_i]
  rw[← i_eq_j] at k_ne_i
  rw[if_neg k_ne_i, if_neg k_ne_i, if_neg]
  rw[← i_eq_j]
  exact k_ne_i

  rcases eq_or_ne k i with k_eq_i | k_ne_i
  rw[if_pos k_eq_i, if_neg i_ne_j, if_pos rfl]
  rw[k_eq_i]
  rw[if_neg k_ne_i]

  rcases eq_or_ne k j with k_eq_j | k_ne_j
  rw[if_pos k_eq_j, if_pos rfl, k_eq_j]
  rw[if_neg k_ne_j, if_neg k_ne_i, if_neg k_ne_j]


lemma swap_variables_order_two (p : MvPolynomial (Fin n) ℂ) (i : Fin n) (j : Fin n) :
SwapVariables (SwapVariables p i j) i j = p := by
  simp[SwapVariables]
  rw[transposition_order_two]
  apply MvPolynomial.rename_id


noncomputable def Demazure (p : MvPolynomial (Fin (n + 1)) ℂ) (i : ℕ) (h : i < n) : MvPolynomial (Fin (n + 1)) ℂ  :=
  have : i < n + 1 := by
    have : n < n + 1 := by
      nth_rewrite 1 [← Nat.add_zero n]
      apply Nat.add_lt_add_left
      norm_num
    apply Nat.lt_trans h
    apply this

  let i' : Fin (n + 1) := ⟨i, this⟩

  have h' : i + 1 < n + 1 := by
    apply Nat.add_lt_add_right h

  let i'_plus_1 : Fin (n + 1) := ⟨i + 1, h'⟩
  let numerator := - (p - SwapVariables p i' i'_plus_1)
  let numerator_Xi_on_end := SwapVariables numerator i' n
  let numerator_X := (finSuccEquiv ℂ n).toFun numerator_Xi_on_end

  let X_i : MvPolynomial (Fin n) ℂ := MvPolynomial.X ⟨i, h⟩
  let denominator_X : Polynomial (MvPolynomial (Fin n) ℂ) := (Polynomial.X - Polynomial.C X_i)

  let division := numerator_X.divByMonic denominator_X
  let division_mv := (finSuccEquiv ℂ n).invFun division

  SwapVariables division_mv i' n



lemma wario :  2 > 0 := by norm_num
lemma wah :  0 < 2 - 1 := by norm_num

noncomputable def waluigi : FractionRing (MvPolynomial (Fin 2) ℂ ) := Demazure wario circleEquation 0 wah
example : waluigi = 0 := by
  simp [waluigi, Demazure, circleEquation, SwapVariables, Transposition]
  sorry
