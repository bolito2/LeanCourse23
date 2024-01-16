import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.Complex.Polynomial
import Init.System.IO

import Mathlib.Data.Complex.Basic

import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.Rename
import Mathlib.Data.MvPolynomial.Polynomial

noncomputable section
open MvPolynomial

variable {n : ℕ} (n_pos : n > 0)

/- TODO: Use mathlib's permutations -/

def Transposition (i : Fin n)(j : Fin n) : (Fin n → Fin n) :=
  fun k ↦ if k = i then j else if k = j then i else k

def SwapVariablesFun (i j : Fin n) (p : MvPolynomial (Fin n) ℂ) : (MvPolynomial (Fin n) ℂ) :=
  (rename (Transposition i j)) p

lemma swap_variables_map_zero (i j : Fin n) : SwapVariablesFun i j 0 = 0 := by
  rw[SwapVariablesFun]
  have : (0 : MvPolynomial (Fin n) ℂ) = C 0 := by
    refine C_0.symm
  rw[this]
  exact rename_C (Transposition i j) 0

lemma swap_variables_map_one (i j : Fin n) : SwapVariablesFun i j 1 = 1 := by
  simp[SwapVariablesFun]

lemma swap_variables_add (i j : Fin n) : ∀p q :
 MvPolynomial (Fin n) ℂ, SwapVariablesFun i j (p + q) = SwapVariablesFun i j p + SwapVariablesFun i j q := by
  intro p q
  simp[SwapVariablesFun]

lemma swap_variables_mul (i j : Fin n) : ∀p q :
 MvPolynomial (Fin n) ℂ, SwapVariablesFun i j (p * q) = SwapVariablesFun i j p * SwapVariablesFun i j q := by
  intro p q
  simp[SwapVariablesFun]

def SwapVariables (i : Fin n) (j : Fin n) : RingHom (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) where
  toFun := SwapVariablesFun i j
  map_zero' := swap_variables_map_zero i j
  map_one' := swap_variables_map_one i j
  map_add' := swap_variables_add i j
  map_mul' := swap_variables_mul i j


def circleEquation : MvPolynomial (Fin 2) ℂ := X 0 ^ 2 + X 1 ^ 2 - C 1

example : circleEquation = SwapVariables 0 1 circleEquation := by
  simp [circleEquation, SwapVariables, SwapVariablesFun, Transposition]
  ring

lemma transposition_order_two (i : Fin n) (j : Fin n) : Transposition i j ∘ Transposition i j = (fun k ↦ k) := by
  funext k
  simp[Transposition]

  by_cases h1 : k = i
  simp[h1]
  by_cases h2 : k = j
  simp [h2]
  simp[h1,h2]

lemma swap_variables_order_two (p : MvPolynomial (Fin n) ℂ) (i : Fin n) (j : Fin n) :
  SwapVariables i j (SwapVariables i j p) = p := by
  simp[SwapVariables, SwapVariablesFun]
  rw[transposition_order_two]
  apply MvPolynomial.rename_id


def DemazureNumerator (p : MvPolynomial (Fin (n + 1)) ℂ) (i : Fin n) : Polynomial (MvPolynomial (Fin n) ℂ)  :=
  let i' : Fin (n + 1) := Fin.castSucc i
  let i'_plus_1 : Fin (n + 1) := Fin.succ i

  let numerator := p - SwapVariablesFun i' i'_plus_1 p
  let numerator_X_i_at_start := SwapVariablesFun i' 0 numerator
  (finSuccEquiv ℂ n) numerator_X_i_at_start


def DemazureDenominator (p : MvPolynomial (Fin (n + 1)) ℂ) (i : Fin n) : Polynomial (MvPolynomial (Fin n) ℂ)  :=
  let X_i : MvPolynomial (Fin n) ℂ := MvPolynomial.X i
  let denominator_X : Polynomial (MvPolynomial (Fin n) ℂ) := (Polynomial.X - Polynomial.C X_i)

  denominator_X

def Demazure (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ) : MvPolynomial (Fin (n + 1)) ℂ  :=
  let numerator := DemazureNumerator p i
  let denominator := DemazureDenominator p i

  let division := numerator.divByMonic denominator
  let division_mv := (finSuccEquiv ℂ n).invFun division

  let i' : Fin (n + 1) := Fin.castSucc i

  SwapVariablesFun i' n division_mv

lemma fin_succ_ne_fin_castSucc (i : Fin n) : Fin.succ i ≠ Fin.castSucc i := by
  apply Fin.val_ne_iff.mp
  dsimp
  norm_num

lemma demazure_is_polynomial : ∀(i : Fin n), ∀(p : MvPolynomial (Fin (n + 1)) ℂ),
  (DemazureNumerator p i).modByMonic (DemazureDenominator p i) = 0 := by
    intro i p
    simp[DemazureNumerator, DemazureDenominator]

    rw[MvPolynomial.polynomial_eval_eval₂]
    simp[SwapVariablesFun]

    repeat
      rw[MvPolynomial.eval₂_rename]

    apply sub_eq_zero_of_eq


    apply MvPolynomial.eval₂_congr
    intro j c _ _

    dsimp
    simp[Transposition]


    by_cases h1 : j = Fin.castSucc i
    by_cases h2 : j = Fin.succ i
    by_cases h3 : j = 0
    simp[h1,h2,h3, fin_succ_ne_fin_castSucc i, Fin.succ_ne_zero]
    simp[h1,h2,h3, fin_succ_ne_fin_castSucc i, Fin.succ_ne_zero]

    by_cases h3 : j = 0
    simp[h1,h2,h3, fin_succ_ne_fin_castSucc i, Fin.succ_ne_zero]
    simp[h1,h2,h3, fin_succ_ne_fin_castSucc i, Fin.succ_ne_zero]

    by_cases h2 : j = Fin.succ i
    by_cases h3 : j = 0

    simp[h1,h2,h3, fin_succ_ne_fin_castSucc i, Fin.succ_ne_zero]
    simp[h1,h2,h3, fin_succ_ne_fin_castSucc i, Fin.succ_ne_zero]

    by_cases h3 : j = 0
    simp[h3] at h1
    simp[h3] at h2
    simp[h1,h2,h3, fin_succ_ne_fin_castSucc i, Fin.succ_ne_zero]
    simp[h1,h2,h3, fin_succ_ne_fin_castSucc i, Fin.succ_ne_zero]
    

lemma composition_independent (i : Fin n) (j : Fin n) (h : |i - j| > Fin.ofNat' 1 n_pos) :
  Demazure i ∘ Demazure j = Demazure j ∘ Demazure i := by
  sorry
