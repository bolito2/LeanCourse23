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

namespace Demazure
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

lemma swap_variables_commutes (i j : Fin n) : ∀r : ℂ, SwapVariablesFun i j (C r) = C r := by
  intro r
  simp[SwapVariablesFun]

def SwapVariables (i : Fin n) (j : Fin n) : AlgHom ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) where
  toFun := SwapVariablesFun i j
  map_zero' := swap_variables_map_zero i j
  map_one' := swap_variables_map_one i j
  map_add' := swap_variables_add i j
  map_mul' := swap_variables_mul i j
  commutes' := swap_variables_commutes i j

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

def DemazureNumerator (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ) : Polynomial (MvPolynomial (Fin n) ℂ)  :=
  let i' : Fin (n + 1) := Fin.castSucc i
  let i'_plus_1 : Fin (n + 1) := Fin.succ i

  let numerator := p - SwapVariables i' i'_plus_1 p
  let numerator_X_i_at_start : MvPolynomial (Fin (n + 1)) ℂ := SwapVariables i' 0 numerator
  (finSuccEquiv ℂ n) numerator_X_i_at_start

lemma demazure_numerator_add (i : Fin n) : ∀ p q : MvPolynomial (Fin (n + 1)) ℂ,
  DemazureNumerator i (p + q) = DemazureNumerator i p + DemazureNumerator i q := by
  simp[DemazureNumerator]

  exact fun p q ↦
    add_sub_add_comm
      (eval₂ (RingHom.comp Polynomial.C MvPolynomial.C)
        (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i)
        (SwapVariables (Fin.castSucc i) 0 p))
      (eval₂ (RingHom.comp Polynomial.C C)
        (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i)
        ((SwapVariables (Fin.castSucc i) 0) q))
      (eval₂ (RingHom.comp Polynomial.C C)
        (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i)
        ((SwapVariables (Fin.castSucc i) 0) ((SwapVariables (Fin.castSucc i) (Fin.succ i)) p)))
      (eval₂ (RingHom.comp Polynomial.C C)
        (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i)
        ((SwapVariables (Fin.castSucc i) 0) ((SwapVariables (Fin.castSucc i) (Fin.succ i)) q)))



def DemazureDenominator (i : Fin n) : Polynomial (MvPolynomial (Fin n) ℂ)  :=
  let X_i : MvPolynomial (Fin n) ℂ := MvPolynomial.X i
  let denominator_X : Polynomial (MvPolynomial (Fin n) ℂ) := (Polynomial.X - Polynomial.C X_i)

  denominator_X

lemma demazure_denominator_monic : ∀ i : Fin n, Polynomial.Monic (DemazureDenominator i) := by
  intro i
  simp[DemazureDenominator]
  exact Polynomial.monic_X_sub_C (X i)

lemma fin_succ_ne_fin_castSucc (i : Fin n) : Fin.succ i ≠ Fin.castSucc i := by
  apply Fin.val_ne_iff.mp
  dsimp
  norm_num

lemma demazure_division_exact : ∀(i : Fin n), ∀(p : MvPolynomial (Fin (n + 1)) ℂ),
  (DemazureNumerator i p).modByMonic (DemazureDenominator i) = 0 := by
    intro i p
    simp[DemazureNumerator, DemazureDenominator]

    simp[MvPolynomial.polynomial_eval_eval₂]
    simp[SwapVariables, SwapVariablesFun]

    repeat
      rw[MvPolynomial.eval₂_rename]

    apply sub_eq_zero_of_eq
    apply congr_arg

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

lemma demazure_division_exact' : ∀(i : Fin n), ∀(p : MvPolynomial (Fin (n + 1)) ℂ),
   DemazureDenominator i * ((DemazureNumerator i p).divByMonic (DemazureDenominator i)) = DemazureNumerator i p := by
  intro i p

  have wario :
  (DemazureNumerator i p).modByMonic (DemazureDenominator i) +
   DemazureDenominator i * (DemazureNumerator i p).divByMonic (DemazureDenominator i) =
    DemazureNumerator i p  := Polynomial.modByMonic_add_div (DemazureNumerator i p) (demazure_denominator_monic i)
  rw[demazure_division_exact i p] at wario
  simp at wario
  exact wario

def DemazureFun (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ) : MvPolynomial (Fin (n + 1)) ℂ  :=
  let numerator := DemazureNumerator i p
  let denominator := DemazureDenominator i

  let division := numerator.divByMonic denominator
  let division_mv : MvPolynomial (Fin (n + 1)) ℂ := (AlgEquiv.symm (finSuccEquiv ℂ n)) division

  let i' : Fin (n + 1) := Fin.castSucc i
  let n' : Fin (n + 1) := n

  SwapVariables i' n' division_mv

lemma demazure_map_add (i : Fin n) : ∀p q : MvPolynomial (Fin (n + 1)) ℂ,
  DemazureFun i (p + q) = DemazureFun i p + DemazureFun i q := by
  intro p q
  simp[DemazureFun, SwapVariables]
  simp[← swap_variables_add (Fin.castSucc i) n]
  apply congr_arg
  rw[← AlgEquiv.map_add (AlgEquiv.symm (MvPolynomial.finSuccEquiv ℂ n)) (DemazureNumerator i p /ₘ DemazureDenominator i) (DemazureNumerator i q /ₘ DemazureDenominator i) ]
  apply congr_arg

  have h : (DemazureDenominator i) * (DemazureNumerator i (p + q) /ₘ DemazureDenominator i) = (DemazureDenominator i)* (DemazureNumerator i p /ₘ DemazureDenominator i + DemazureNumerator i q /ₘ DemazureDenominator i) := by
    simp[mul_add]
    simp[demazure_division_exact']
    exact demazure_numerator_add i p q

  sorry

lemma demazure_map_smul (i : Fin n) : ∀ (r : ℂ) (p : MvPolynomial (Fin (n + 1)) ℂ),
DemazureFun i (r • p) = r • DemazureFun i p := by
  intro r p
  simp[DemazureFun, SwapVariables, MvPolynomial.smul_eq_C_mul]
  nth_rewrite 2 [← swap_variables_commutes (Fin.castSucc i) n]
  rw[← swap_variables_mul]
  apply congr_arg
  rw[← MvPolynomial.smul_eq_C_mul]
  rw[← MvPolynomial.smul_eq_C_mul]
  rw[← AlgEquiv.map_smul (AlgEquiv.symm (MvPolynomial.finSuccEquiv ℂ n)) r (DemazureNumerator i p /ₘ DemazureDenominator i) ]
  apply congr_arg

  sorry

def Demazure (i : Fin n) : LinearMap (RingHom.id ℂ) (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial (Fin (n + 1)) ℂ) where
  toFun := DemazureFun i
  map_add' := demazure_map_add i
  map_smul' := demazure_map_smul i
