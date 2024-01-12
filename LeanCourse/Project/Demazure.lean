import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.Complex.Polynomial
import Init.System.IO

noncomputable section
open MvPolynomial

variable {n : ℕ} (n_pos : n > 0)

/- TODO: Use mathlib's permutations -/

def Transposition (i : Fin n)(j : Fin n) : (Fin n → Fin n) :=
  fun k ↦ if k = i then j else if k = j then i else k

def SwapVariables (p : MvPolynomial (Fin n) ℂ) (i : Fin n) (j : Fin n) : MvPolynomial (Fin n) ℂ :=
  (rename (Transposition i j)) p

def circleEquation : MvPolynomial (Fin 2) ℂ := X 0 ^ 2 + X 1 ^ 2 - 1

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


lemma zero_of_swap_variables_zero (i : Fin n) (j : Fin n) : SwapVariables 0 i j = 0 := by
  rw[SwapVariables]
  have : (0 : MvPolynomial (Fin n) ℂ) = C 0 := by
    refine C_0.symm
  rw[this]
  exact rename_C (Transposition i j) 0

lemma i_le_nsucc_of_i_le_n (i : ℕ) (h : i < n) : i < n + 1 := by
  have : n < n + 1 := by
      nth_rewrite 1 [← Nat.add_zero n]
      apply Nat.add_lt_add_left
      norm_num
  apply Nat.lt_trans h
  apply this

def DemazureNumerator (p : MvPolynomial (Fin (n + 1)) ℂ) (i : ℕ) (h : i < n) : Polynomial (MvPolynomial (Fin n) ℂ)  :=
  let i' : Fin (n + 1) := ⟨i, i_le_nsucc_of_i_le_n i h⟩

  have h' : i + 1 < n + 1 := by
    apply Nat.add_lt_add_right h

  let i'_plus_1 : Fin (n + 1) := ⟨i + 1, h'⟩

  let numerator := - (p - SwapVariables p i' i'_plus_1)
  let numerator_X_i_succ_on_end := SwapVariables numerator i'_plus_1 n
  (finSuccEquiv ℂ n).toFun numerator_X_i_succ_on_end

def DemazureDenominator (p : MvPolynomial (Fin (n + 1)) ℂ) (i : ℕ) (h : i < n) : Polynomial (MvPolynomial (Fin n) ℂ)  :=
  have h' : i + 1 < n + 1 := by
    apply Nat.add_lt_add_right h

  let X_i : MvPolynomial (Fin n) ℂ := MvPolynomial.X ⟨i, h⟩
  let denominator_X : Polynomial (MvPolynomial (Fin n) ℂ) := (Polynomial.X - Polynomial.C X_i)

  denominator_X

noncomputable def Demazure (p : MvPolynomial (Fin (n + 1)) ℂ) (i : ℕ) (h : i < n) : MvPolynomial (Fin (n + 1)) ℂ  :=

let numerator := DemazureNumerator p i h
let denominator := DemazureDenominator p i h

let division := numerator.divByMonic denominator
let division_mv := (finSuccEquiv ℂ n).invFun division

let i' : Fin (n + 1) := ⟨i, i_le_nsucc_of_i_le_n i h⟩

SwapVariables division_mv i' n


lemma demazure_is_polynomial : ∀(i : ℕ) (h : i < n), ∀(p : MvPolynomial (Fin (n + 1)) ℂ),
  (DemazureNumerator p i h).modByMonic (DemazureDenominator p i h) = 0 := by
    intro i h p
    simp[DemazureDenominator, DemazureNumerator]

    have swappy : SwapVariables p { val := i, isLt := i_le_nsucc_of_i_le_n i h } { val := i + 1, isLt := Nat.add_lt_add_right h 1 } - p = 0 := by
      sorry

    rw[swappy]
    rw[zero_of_swap_variables_zero]
    rw[MvPolynomial.finSuccEquiv_zero]
