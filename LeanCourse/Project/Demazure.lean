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

def SwapVariables (p : MvPolynomial (Fin n) ℂ) (i : Fin n) (j : Fin n) : MvPolynomial (Fin n) ℂ :=
  (rename (Transposition i j)) p

def circleEquation : MvPolynomial (Fin 2) ℂ := X 0 ^ 2 + X 1 ^ 2 - C 1

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

def DemazureNumerator (p : MvPolynomial (Fin (n + 1)) ℂ) (i : Fin n) : Polynomial (MvPolynomial (Fin n) ℂ)  :=
  let i' : Fin (n + 1) := Fin.castSucc i
  let i'_plus_1 : Fin (n + 1) := Fin.succ i

  let numerator := p - SwapVariables p i' i'_plus_1
  let numerator_X_i_at_start := SwapVariables numerator i' 0
  (finSuccEquiv ℂ n) numerator_X_i_at_start


def DemazureDenominator (p : MvPolynomial (Fin (n + 1)) ℂ) (i : Fin n) : Polynomial (MvPolynomial (Fin n) ℂ)  :=
  let X_i : MvPolynomial (Fin n) ℂ := MvPolynomial.X i
  let denominator_X : Polynomial (MvPolynomial (Fin n) ℂ) := (Polynomial.X - Polynomial.C X_i)

  denominator_X

noncomputable def Demazure (p : MvPolynomial (Fin (n + 1)) ℂ) (i : Fin n) : MvPolynomial (Fin (n + 1)) ℂ  :=
  let numerator := DemazureNumerator p i
  let denominator := DemazureDenominator p i

  let division := numerator.divByMonic denominator
  let division_mv := (finSuccEquiv ℂ n).invFun division

  let i' : Fin (n + 1) := Fin.castSucc i

  SwapVariables division_mv i' n

def DemazureNumeratorHom (i : Fin n) : (MvPolynomial (Fin (n + 1)) ℂ) →+* (Polynomial (MvPolynomial (Fin n) ℂ)) :=
  if i_not_last : i + 1 < n then eval₂Hom (RingHom.comp Polynomial.C C) (fun k ↦ if k_not_last : k.val < n then (if k = i + 1 then Polynomial.X else Polynomial.C (X ⟨k, k_not_last⟩ )) else Polynomial.C (X ⟨i + 1, i_not_last⟩ ))
  else eval₂Hom (RingHom.comp Polynomial.C C) (fun k ↦ if k_not_last : k.val < n then Polynomial.C (X ⟨k, k_not_last⟩ ) else Polynomial.X)

lemma wah :  ∀(i : Fin n), ∀(p : MvPolynomial (Fin (n + 1)) ℂ),
  (DemazureNumeratorHom i p).modByMonic (DemazureDenominator p i) = 0 := by
    intro i p
    simp[DemazureNumeratorHom, DemazureDenominator]
    sorry

lemma fin_succ_ne_fin_castSucc (i : Fin n) : ¬Fin.succ i = Fin.castSucc i := by
  apply Fin.val_ne_iff.mp
  dsimp
  norm_num

lemma demazure_is_polynomial : ∀(i : Fin n), ∀(p : MvPolynomial (Fin (n + 1)) ℂ),
  (DemazureNumerator p i).modByMonic (DemazureDenominator p i) = 0 := by
    intro i p
    simp[DemazureNumerator, DemazureDenominator]
    rw[MvPolynomial.polynomial_eval_eval₂]
    simp[SwapVariables]
    repeat
      rw[MvPolynomial.eval₂_rename]
    apply sub_eq_zero_of_eq
    apply MvPolynomial.eval₂_congr
    intro j c h coeff_ne_zero

    dsimp
    rcases eq_or_ne j i with j_eq_i | j_neq_i
    rw [j_eq_i]

    simp[Transposition]
    rw[if_neg, if_neg]
    simp[Fin.cases]
    exact Fin.succ_ne_zero i
    apply fin_succ_ne_fin_castSucc

    rcases eq_or_ne j (i + 1) with j_eq_i_succ | j_ne_i_succ
    rw[j_eq_i_succ]

    simp[Transposition]
    rw[if_neg, if_neg]
    simp[Fin.cases]
    exact Fin.succ_ne_zero i
    apply fin_succ_ne_fin_castSucc

    rcases eq_or_ne j 0 with j_eq_zero | j_ne_zero
    rw[j_eq_zero]

    simp[Transposition]

    rcases eq_or_ne (0 : Fin (n + 1)) (Fin.castSucc i) with i_eq_zero | i_ne_zero
    rw[if_pos i_eq_zero, if_pos i_eq_zero, if_neg, if_neg]
    simp[Fin.cases]
    exact Fin.succ_ne_zero i
    apply fin_succ_ne_fin_castSucc

    repeat rw[if_neg i_ne_zero]
    repeat rw[if_neg]

    
