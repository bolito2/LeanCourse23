import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.Complex.Polynomial
import Init.System.IO

import Mathlib.Data.Complex.Basic

import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.Rename
import Mathlib.Data.MvPolynomial.Polynomial

import Mathlib.Data.Finsupp.Defs

set_option maxHeartbeats 10000000

noncomputable section
open MvPolynomial

variable {n : ℕ} (n_pos : n > 0) (n_gt_1 : n > 1)

namespace Demazure

/- Swapping variables of a polynomial is an algebra homomorphism -/

def TranspositionFun (i j : Fin n) : Fin n → Fin n :=
  fun k ↦ if k = i then j else if k = j then i else k

lemma transposition_order_two (i j : Fin n): ∀k : Fin n, TranspositionFun i j (TranspositionFun i j k) = k := by
  intro k
  simp[TranspositionFun]

  by_cases h1 : k = i
  simp[h1]
  by_cases h2 : k = j
  simp [h2]
  simp[h1,h2]

lemma transposition_order_two' (i j : Fin n): TranspositionFun i j ∘ TranspositionFun i j = fun k ↦ k := by
  funext k
  exact transposition_order_two i j k

lemma transposition_symmetric {i j : Fin n} : TranspositionFun i j = TranspositionFun j i := by
  funext k
  simp[TranspositionFun]
  by_cases h1 : k = i
  simp[h1]
  by_cases h2 : i = j
  simp [h2]
  simp[h1,h2]
  simp[h1]

def Transposition (i j : Fin n) : Equiv.Perm (Fin n) where
  toFun := TranspositionFun i j
  invFun := TranspositionFun i j
  left_inv := by
   simp[Function.LeftInverse]
   exact transposition_order_two i j
  right_inv := by
    simp[Function.RightInverse]
    exact transposition_order_two i j

def SwapVariablesFun (i j : Fin n) (p : MvPolynomial (Fin n) ℂ) : (MvPolynomial (Fin n) ℂ) :=
  (renameEquiv ℂ (Transposition i j)) p

@[simp]
lemma swap_variables_map_zero (i j : Fin n) : SwapVariablesFun i j 0 = 0 := by
  rw[SwapVariablesFun]
  have : (0 : MvPolynomial (Fin n) ℂ) = C 0 := by
    refine C_0.symm
  rw[this]
  exact rename_C (Transposition i j) 0

@[simp]
lemma swap_variables_map_one {i j : Fin n} : SwapVariablesFun i j 1 = 1 := by
  simp[SwapVariablesFun]

@[simp]
lemma swap_variables_add {i j : Fin n} : ∀p q :
 MvPolynomial (Fin n) ℂ, SwapVariablesFun i j (p + q) = SwapVariablesFun i j p + SwapVariablesFun i j q := by
  intro p q
  simp[SwapVariablesFun]

@[simp]
lemma swap_variables_sub {i j : Fin n} : ∀p q :
 MvPolynomial (Fin n) ℂ, SwapVariablesFun i j (p - q) = SwapVariablesFun i j p - SwapVariablesFun i j q := by
  intro p q
  simp[SwapVariablesFun]

@[simp]
lemma swap_variables_mul {i j : Fin n} : ∀p q :
 MvPolynomial (Fin n) ℂ, SwapVariablesFun i j (p * q) = SwapVariablesFun i j p * SwapVariablesFun i j q := by
  intro p q
  simp[SwapVariablesFun]

@[simp]
lemma swap_variables_commutes {i j : Fin n} : ∀r : ℂ, SwapVariablesFun i j (C r) = C r := by
  intro r
  simp[SwapVariablesFun]

@[simp]
lemma swap_variables_order_two {i j : Fin n} {p : MvPolynomial (Fin n) ℂ} :
  SwapVariablesFun i j (SwapVariablesFun i j p) = p := by
  simp[SwapVariablesFun, Transposition]
  rw[transposition_order_two' i j]
  apply MvPolynomial.rename_id

@[simp]
def SwapVariables (i : Fin n) (j : Fin n) : AlgEquiv ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) where
  toFun := SwapVariablesFun i j
  invFun := SwapVariablesFun i j
  left_inv := by
    simp[Function.LeftInverse]

  right_inv := by
    simp[Function.RightInverse]
    intro p
    exact swap_variables_order_two

  map_mul' := swap_variables_mul
  map_add' := swap_variables_add
  commutes' := swap_variables_commutes

/- Easy example -/

def circleEquation : MvPolynomial (Fin 2) ℂ := X 0 ^ 2 + X 1 ^ 2 - C 1

example : circleEquation = SwapVariables 0 1 circleEquation := by
  simp [circleEquation, SwapVariables, SwapVariablesFun, Transposition, TranspositionFun]
  ring

def DemazureNumerator (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ) : Polynomial (MvPolynomial (Fin n) ℂ)  :=
  let i' : Fin (n + 1) := Fin.castSucc i
  let i'_plus_1 : Fin (n + 1) := Fin.succ i

  let numerator := p - SwapVariables i' i'_plus_1 p
  let numerator_X_i_at_start : MvPolynomial (Fin (n + 1)) ℂ := SwapVariables i' 0 numerator
  (finSuccEquiv ℂ n) numerator_X_i_at_start

lemma unfold_demazure_numerator {i : Fin n} {p : MvPolynomial (Fin (n + 1)) ℂ} : DemazureNumerator i p =
eval₂ (RingHom.comp Polynomial.C C) (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (X k)) i)
    (SwapVariablesFun (Fin.castSucc i) 0 (p - SwapVariablesFun (Fin.castSucc i) (Fin.succ i) p)) := by
  simp[DemazureNumerator, SwapVariables]

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

lemma demazure_numerator_C_mul (i : Fin n) : ∀ (p : MvPolynomial (Fin (n + 1)) ℂ) (r : ℂ),
 DemazureNumerator i (C r * p) = Polynomial.C (C r) * DemazureNumerator i p := by
  simp[DemazureNumerator, SwapVariables]
  exact fun p r ↦
    (mul_sub (Polynomial.C (C r))
        (eval₂ (RingHom.comp Polynomial.C C)
          (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (X k)) i)
          ((SwapVariables (Fin.castSucc i) 0) p))
        (eval₂ (RingHom.comp Polynomial.C C)
          (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (X k)) i)
          ((SwapVariables (Fin.castSucc i) 0)
            ((SwapVariables (Fin.castSucc i) (Fin.succ i)) p)))).symm

def DemazureDenominator (i : Fin n) : Polynomial (MvPolynomial (Fin n) ℂ)  :=
  let X_i : MvPolynomial (Fin n) ℂ := MvPolynomial.X i
  let denominator_X : Polynomial (MvPolynomial (Fin n) ℂ) := (Polynomial.X - Polynomial.C X_i)

  denominator_X

lemma demazure_denominator_ne_zero : ∀ i : Fin n, DemazureDenominator i ≠ 0 := by
  intro i
  simp[DemazureDenominator]
  exact Polynomial.X_sub_C_ne_zero (X i)

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
    simp[Transposition, TranspositionFun]


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

def DemazureFun (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ) : MvPolynomial (Fin (n + 1)) ℂ  :=
  let numerator := DemazureNumerator i p
  let denominator := DemazureDenominator i

  let division := numerator.divByMonic denominator
  let division_mv : MvPolynomial (Fin (n + 1)) ℂ := (AlgEquiv.symm (finSuccEquiv ℂ n)) division

  let i' : Fin (n + 1) := Fin.castSucc i
  let n' : Fin (n + 1) := n

  SwapVariables i' 0 division_mv

-- The main theorem to prove

lemma poly_mul_cancel {p q r : Polynomial (MvPolynomial (Fin n) ℂ)} (hr : r ≠ 0) : p = q ↔ (r * p) = (r * q) := by
  constructor
  intro h
  exact congrArg (HMul.hMul r) h
  intro h
  simp[Polynomial.ext] at h
  rcases h with h1|h2
  exact h1
  contradiction

lemma poly_div_cancel {p q r : Polynomial (MvPolynomial (Fin n) ℂ)} (hr : Polynomial.Monic r) (hp : p %ₘ r = 0) (hq :  q %ₘ r = 0) : p = q ↔ (p /ₘ r) = (q /ₘ r) := by
  constructor
  intro h
  exact congrFun (congrArg Polynomial.divByMonic h) r
  intro h
  have div_p : p %ₘ r + r * (p /ₘ r) = p := Polynomial.modByMonic_add_div p hr
  have div_q : q %ₘ r + r * (q /ₘ r) = q := Polynomial.modByMonic_add_div q hr

  simp[hp] at div_p
  simp[hq] at div_q

  rw[← div_p, ← div_q]
  apply (poly_mul_cancel (Polynomial.Monic.ne_zero hr)).mp h

lemma poly_exact_div_mul_cancel {p q : Polynomial (MvPolynomial (Fin n) ℂ)}
 (q_monic : Polynomial.Monic q) (exact_div : p %ₘ q = 0) : q * (p /ₘ q) = p := by
  nth_rewrite 2 [← sub_zero p]
  apply eq_sub_of_add_eq
  rw[add_comm]
  rw[← exact_div]
  exact Polynomial.modByMonic_add_div p q_monic

lemma demazure_division_exact' : ∀(i : Fin n), ∀(p : MvPolynomial (Fin (n + 1)) ℂ),
   DemazureDenominator i * ((DemazureNumerator i p) /ₘ (DemazureDenominator i)) = DemazureNumerator i p := by
  intro i p

  apply poly_exact_div_mul_cancel (demazure_denominator_monic i) (demazure_division_exact i p)

lemma demazure_map_add (i : Fin n) : ∀p q : MvPolynomial (Fin (n + 1)) ℂ,
  DemazureFun i (p + q) = DemazureFun i p + DemazureFun i q := by
  intro p q
  simp[DemazureFun, SwapVariables]
  rw[← swap_variables_add]
  apply congr_arg
  rw[← AlgEquiv.map_add (AlgEquiv.symm (MvPolynomial.finSuccEquiv ℂ n)) (DemazureNumerator i p /ₘ DemazureDenominator i) (DemazureNumerator i q /ₘ DemazureDenominator i) ]
  apply congr_arg

  apply (poly_mul_cancel (demazure_denominator_ne_zero i)).mpr
  simp[mul_add]
  simp[demazure_division_exact']
  exact demazure_numerator_add i p q

lemma demazure_map_smul (i : Fin n) : ∀ (r : ℂ) (p : MvPolynomial (Fin (n + 1)) ℂ),
DemazureFun i (r • p) = r • DemazureFun i p := by
  intro r p
  simp[DemazureFun, SwapVariables, MvPolynomial.smul_eq_C_mul]
  nth_rewrite 2 [← swap_variables_commutes]
  rw[← swap_variables_mul]
  apply congr_arg
  nth_rewrite 2 [← MvPolynomial.finSuccEquiv_comp_C_eq_C]
  simp[RingHom.comp]
  rw[← AlgEquiv.map_mul]
  apply congr_arg

  apply (poly_mul_cancel (demazure_denominator_ne_zero i)).mpr
  rw[← mul_assoc]
  rw [mul_comm (DemazureDenominator i) (Polynomial.C (C r))]
  simp[demazure_division_exact']
  rw[mul_assoc]
  rw[demazure_division_exact' i p]
  exact demazure_numerator_C_mul i p r

def Demazure (i : Fin n) : LinearMap (RingHom.id ℂ) (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial (Fin (n + 1)) ℂ) where
  toFun := DemazureFun i
  map_add' := demazure_map_add i
  map_smul' := demazure_map_smul i

lemma one_of_div_by_monic_self : ∀ (p : Polynomial (MvPolynomial (Fin n) ℂ)) (h : Polynomial.Monic p), p /ₘ p = 1 := by
  intro p hp
  apply (poly_mul_cancel (Polynomial.Monic.ne_zero hp)).mpr
  ring
  have : p %ₘ p = 0 := by
    refine (Polynomial.dvd_iff_modByMonic_eq_zero hp).mpr ?_
    rfl
  apply poly_exact_div_mul_cancel hp this


lemma demazure_not_multiplicative : ∀ (i : Fin n), ∃(p q : MvPolynomial (Fin (n+1)) ℂ),
  Demazure i (p * q) ≠ Demazure i p * Demazure i q := by
  intro i
  use (X i)
  use C 1
  simp[Demazure, DemazureFun, DemazureNumerator, DemazureDenominator,
   SwapVariables, SwapVariablesFun, Transposition, TranspositionFun,
   fin_succ_ne_fin_castSucc, Fin.succ_ne_zero]

  rw[one_of_div_by_monic_self]
  simp[AlgHom.map_one]
  exact Polynomial.monic_X_sub_C (X i)

lemma element_in_submonoid (x : MvPolynomial (Fin (n + 1)) ℂ) : x ∈ Submonoid.powers (x) := by
  simp[Submonoid.mem_powers]

def DemazureNumerator' (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ) : MvPolynomial (Fin (n + 1)) ℂ  :=
  let i' : Fin (n + 1) := Fin.castSucc i
  let i'_plus_1 : Fin (n + 1) := Fin.succ i

  p - SwapVariables i' i'_plus_1 p

def DemazureDenominator' (i : Fin n) : MvPolynomial (Fin (n + 1)) ℂ :=
  let i' : Fin (n + 1) := Fin.castSucc i
  let i'_plus_1 : Fin (n + 1) := Fin.succ i

  X i' - X i'_plus_1

def DemazureFun' (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ) :
 Localization (Submonoid.powers (DemazureDenominator' i))   :=

  Localization.mk (DemazureNumerator' i p) ⟨DemazureDenominator' i, element_in_submonoid (DemazureDenominator' i)⟩

lemma demazure_fun'_add (i : Fin n) : ∀p q : MvPolynomial (Fin (n + 1)) ℂ,
  DemazureFun' i (p + q) = DemazureFun' i p + DemazureFun' i q := by
  intro p q
  rw[DemazureFun']
  rw[DemazureFun']
  rw[DemazureFun']

  rw[Localization.add_mk_self]
  have : DemazureNumerator' i (p + q) = DemazureNumerator' i p + DemazureNumerator' i q := by
    simp[DemazureNumerator']
    ring
  rw[this]

lemma demazure_fun'_smul (i : Fin n) : ∀ (r : ℂ) (p : MvPolynomial (Fin (n + 1)) ℂ),
DemazureFun' i (r • p) = r • DemazureFun' i p := by
  intro r p
  rw[DemazureFun']
  rw[DemazureFun']

  rw[Localization.smul_mk]
  have : DemazureNumerator' i (r • p) = r • DemazureNumerator' i p := by
    simp[DemazureNumerator', SwapVariables]
    exact (smul_sub r p (SwapVariablesFun (Fin.castSucc i) (Fin.succ i) p)).symm
  rw[this]


def Demazure' (i : Fin n) :
LinearMap (RingHom.id ℂ)
(MvPolynomial (Fin (n + 1)) ℂ)
 (Localization (Submonoid.powers (DemazureDenominator' i))) where
  toFun := DemazureFun' i
  map_add' := demazure_fun'_add i
  map_smul' := demazure_fun'_smul i

namespace PolyFraction

structure PolyFraction (n : ℕ) where
  numerator : MvPolynomial (Fin (n + 1)) ℂ
  denominator : MvPolynomial (Fin (n + 1)) ℂ
  denominator_ne_zero : denominator ≠ 0

def add : PolyFraction n → PolyFraction n → PolyFraction n := by
  intro p q
  exact ⟨p.numerator * q.denominator + q.numerator * p.denominator, p.denominator * q.denominator, mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero⟩

def sub : PolyFraction n → PolyFraction n → PolyFraction n := by
  intro p q
  exact ⟨p.numerator * q.denominator - q.numerator * p.denominator, p.denominator * q.denominator, mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero⟩

def mul : PolyFraction n → PolyFraction n → PolyFraction n := by
  intro p q
  exact ⟨p.numerator * q.numerator, p.denominator * q.denominator, mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero⟩

def inv (p : PolyFraction n) (h : p.numerator ≠ 0) : PolyFraction n := by
  exact ⟨p.denominator, p.numerator, h⟩

@[simp]
def one : PolyFraction n where
  numerator := 1
  denominator := 1
  denominator_ne_zero := one_ne_zero

@[simp]
def zero : PolyFraction n where
  numerator := 0
  denominator := 1
  denominator_ne_zero := one_ne_zero

def DemazureDenominator (i : Fin n) : PolyFraction n := by
  exact ⟨DemazureDenominator' i, 1, one_ne_zero⟩

lemma swap_variables_ne_zero (i j : Fin (n + 1)) : ∀ p : MvPolynomial (Fin (n + 1)) ℂ, p ≠ 0 → SwapVariables i j p ≠ 0 := by
  intro p hp
  intro h
  apply hp
  rw[← AlgEquiv.map_zero (SwapVariables i j)] at h
  apply AlgEquiv.injective (SwapVariables i j)
  exact h

lemma wario (i : Fin n) : (X (Fin.castSucc i) : MvPolynomial (Fin (n + 1)) ℂ) - X (Fin.succ i) ≠ 0 := by
  apply MvPolynomial.ne_zero_iff.mpr
  use Finsupp.single (Fin.succ i) 1
  rw[MvPolynomial.coeff_sub]
  rw[MvPolynomial.coeff_X]
  rw[MvPolynomial.coeff_X']

  have h : Finsupp.single (Fin.castSucc i) 1 ≠ Finsupp.single (Fin.succ i) 1 := by
    apply FunLike.ne_iff.mpr
    use Fin.castSucc i
    simp [fin_succ_ne_fin_castSucc i]

  rw [if_neg h]
  simp


@[simp]
def Demazure (i : Fin n) : PolyFraction n →  PolyFraction n := fun p =>
   ⟨
    p.numerator * (SwapVariables (Fin.castSucc i) (Fin.succ i) p.denominator) - (SwapVariables (Fin.castSucc i) (Fin.succ i) p.numerator) * p.denominator,
    p.denominator * (SwapVariables (Fin.castSucc i) (Fin.succ i) p.denominator) * (X (Fin.castSucc i) - X (Fin.succ i)),
    mul_ne_zero (mul_ne_zero p.denominator_ne_zero (swap_variables_ne_zero (Fin.castSucc i) (Fin.succ i) p.denominator p.denominator_ne_zero)) (wario i)
    ⟩

@[simp]
lemma transposition_first {i j : Fin (n + 1)} : TranspositionFun i j i = j := by
  simp [TranspositionFun]

@[simp]
lemma transposition_second {i j : Fin (n + 1)} : TranspositionFun i j j = i := by
  simp [TranspositionFun]

@[simp]
lemma transposition_none {i j k : Fin (n + 1)} (h1 : k ≠ i) (h2 : k ≠ j) :
TranspositionFun i j k = k := by
  simp [TranspositionFun, h1, h2]

@[simp]
lemma swap_variables_first {i j : Fin (n + 1)} : SwapVariablesFun i j (X i) = X j := by
  simp [SwapVariables, SwapVariablesFun, Transposition, TranspositionFun]

lemma swap_variables_symmetrical {i j : Fin (n + 1)} {p : MvPolynomial (Fin (n + 1)) ℂ} : SwapVariablesFun i j p = SwapVariablesFun j i p := by
  simp [SwapVariables, SwapVariablesFun, Transposition, transposition_symmetric]

@[simp]
lemma swap_variables_second {i j : Fin (n + 1)} : SwapVariablesFun i j (X j) = X i := by
  simp [SwapVariables, SwapVariablesFun, Transposition, TranspositionFun]

@[simp]
lemma swap_variables_none {i j k : Fin (n + 1)} (h1 : k ≠ i) (h2 : k ≠ j) :
SwapVariablesFun i j (X k) = X k := by
  simp [SwapVariables, SwapVariablesFun, Transposition, TranspositionFun, h1, h2]

@[simp]
lemma swap_variables_none' {i j k : Fin (n + 1)} {h1 : k ≠ i} {h2 : k ≠ j} :
SwapVariablesFun i j (X k) = X k := by
  simp [SwapVariables, SwapVariablesFun, Transposition, TranspositionFun, h1, h2]

@[simp]
def equals (p q : PolyFraction n) : Prop := p.numerator * q.denominator = q.numerator * p.denominator

@[simp]
def of_polynomial (p : MvPolynomial (Fin (n + 1)) ℂ) : PolyFraction n := by
  exact ⟨p, 1, one_ne_zero⟩

lemma demazure_order_two : ∀ (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ),
  equals (Demazure i (Demazure i (of_polynomial p) )) zero := by
  intro i p
  simp[equals]
  ring

@[simp]
lemma wario_number_one {n : ℕ} {a : ℕ} {h : a < n} {a' : ℕ} {h' : a' < n} :
({ val := a, isLt := h } : Fin n) ≠ { val := a', isLt := h' } ↔ a ≠ a' := by
  rw[ne_eq]
  rw[ne_eq]
  apply not_iff_not.mpr
  exact Fin.mk_eq_mk


lemma i_ne_i_plus_1 {i : ℕ} {h : i < n + 1}  {h' : i + 1 < n + 1}  :
 ({ val := i, isLt := h } : Fin (n + 1)) ≠ { val := i + 1, isLt := h' } := by
  rw[wario_number_one]
  linarith

@[simp]
lemma omg {i : ℕ} : i + 1 + 1 = i + 2 := by
  ring

lemma transposition_commutes_adjacent {i : Fin n} {j : Fin (n + 1)} (h0 : i < n + 1) (h1 : i + 1 < n + 1) (h2 : i + 2 < n + 1) :
  TranspositionFun ⟨i, h0⟩ ⟨i + 1, h1⟩ (TranspositionFun ⟨i + 1, h1⟩ ⟨i + 2, h2⟩ (TranspositionFun ⟨i, h0⟩ ⟨i + 1, h1⟩ j)) =
    TranspositionFun ⟨i + 1, h1⟩ ⟨i + 2, h2⟩ (TranspositionFun ⟨i, h0⟩ ⟨i + 1, h1⟩ (TranspositionFun ⟨i + 1, h1⟩ ⟨i + 2, h2⟩ j)) := by
  by_cases c0 : j = ⟨i, h0⟩
  simp[c0]
  by_cases c1 : j = ⟨i + 1, h1⟩
  simp[c1]
  by_cases c2 : j = ⟨i + 2, h2⟩
  simp[c2]

  simp[c0,c1,c2]


lemma swap_variables_commutes_adjacent {i : Fin n} {p : MvPolynomial (Fin (n + 1)) ℂ} (h0 : i < n + 1) (h1 : i + 1 < n + 1) (h2 : i + 2 < n + 1) :
  SwapVariablesFun ⟨i, h0⟩ ⟨i + 1, h1⟩ (SwapVariablesFun ⟨i + 1, h1⟩ ⟨i + 2, h2⟩ (SwapVariablesFun ⟨i, h0⟩ ⟨i + 1, h1⟩ p)) =
    SwapVariablesFun ⟨i + 1, h1⟩ ⟨i + 2, h2⟩ (SwapVariablesFun ⟨i, h0⟩ ⟨i + 1, h1⟩ (SwapVariablesFun ⟨i + 1, h1⟩ ⟨i + 2, h2⟩ p)) := by
  simp[SwapVariablesFun, Transposition, Function.comp]

  have huh : (fun x ↦
        TranspositionFun { val := i, isLt := h0 } { val := i + 1, isLt := h1 }
          (TranspositionFun { val := i + 1, isLt := h1 } { val := i + 2, isLt := h2 }
            (TranspositionFun { val := i, isLt := h0 } { val := i + 1, isLt := h1 } x))) =

          (fun x ↦
        TranspositionFun { val := i + 1, isLt := h1 } { val := i + 2, isLt := h2 }
          (TranspositionFun { val := i, isLt := h0 } { val := i + 1, isLt := h1 }
            (TranspositionFun { val := i + 1, isLt := h1 } { val := i + 2, isLt := h2 } x))) := by

            funext j
            rw[transposition_commutes_adjacent h0 h1 h2]
  rw[huh]


lemma unfold_non_adjacent (i j : Fin n) (h : |(i.val : ℤ ) - j.val| > 1) :
  (Fin.castSucc i : Fin (n + 1)) ≠ (Fin.castSucc j : Fin (n + 1)) ∧
  (Fin.castSucc i : Fin (n + 1)) ≠ (Fin.succ j : Fin (n + 1)) ∧
  (Fin.succ i : Fin (n + 1)) ≠ (Fin.castSucc j : Fin (n + 1)) ∧
  (Fin.succ i : Fin (n + 1)) ≠ (Fin.succ j : Fin (n + 1)) := by
    constructor
    · apply Fin.val_ne_iff.mp
      simp [Fin.castSucc]
      intro wah
      simp[wah] at h
    constructor
    · apply Fin.val_ne_iff.mp
      simp [Fin.castSucc]
      intro wah
      simp[wah] at h
    constructor
    · apply Fin.val_ne_iff.mp
      simp [Fin.castSucc]
      intro wah
      simp[← wah] at h
    apply Fin.val_ne_iff.mp
    simp [Fin.castSucc]
    intro wah
    simp[wah] at h

lemma transposition_commutes_non_adjacent (i j : Fin n) {k : Fin (n + 1)} (h : |(i.val : ℤ ) - j.val| > 1) :
  TranspositionFun (Fin.castSucc i) (Fin.succ i) (TranspositionFun (Fin.castSucc j) (Fin.succ j) k) =
   TranspositionFun (Fin.castSucc j) (Fin.succ j) (TranspositionFun (Fin.castSucc i) (Fin.succ i) k) := by
    rcases unfold_non_adjacent i j h with ⟨h1, h2, h3, h4⟩

    by_cases c0 : k = Fin.castSucc i
    simp[h1,h2,h3,h4,c0]
    simp[transposition_none h3 h4]

    by_cases c1 : k = Fin.succ i
    simp[h1,h2,h3,h4,c1]
    simp[transposition_none h3 h4]

    by_cases c2 : k = Fin.castSucc j
    simp[h1,h2,h3,h4,c2]
    simp[transposition_none h2.symm h4.symm]
    simp[transposition_none h1.symm h3.symm]

    by_cases c3 : k = Fin.succ j
    simp[transposition_none h1.symm h3.symm, c3]
    simp[transposition_none h2.symm h4.symm]

    simp[h1,h2,h3,h4,c0,c1,c2,c3]

lemma swap_variables_commutes_non_adjacent (i j : Fin n) (h : |(i.val : ℤ ) - j.val| > 1)
 {p : MvPolynomial (Fin (n + 1)) ℂ} :
  SwapVariablesFun (Fin.castSucc i) (Fin.succ i) (SwapVariablesFun (Fin.castSucc j) (Fin.succ j) p) =
   SwapVariablesFun (Fin.castSucc j) (Fin.succ j) (SwapVariablesFun (Fin.castSucc i) (Fin.succ i) p) := by
    simp[SwapVariablesFun, Transposition, Function.comp]

    have wah : (fun x ↦ TranspositionFun (Fin.castSucc i) (Fin.succ i) (TranspositionFun (Fin.castSucc j) (Fin.succ j) x)) =
    (fun x ↦ TranspositionFun (Fin.castSucc j) (Fin.succ j) (TranspositionFun (Fin.castSucc i) (Fin.succ i) x)) :=
    by
      funext k
      rw[transposition_commutes_non_adjacent i j h]
    rw[wah]


lemma composition_non_adjacent (i j : Fin n)  (h : |(i.val : ℤ ) - j.val| > 1) : ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  equals ((Demazure i ∘ Demazure j) (of_polynomial p)) ((Demazure j ∘ Demazure i) (of_polynomial p)) := by
  intro p
  simp[equals]

  rcases unfold_non_adjacent i j h with ⟨h1, h2, h3, h4⟩

  simp[swap_variables_commutes_non_adjacent i j h, h1, h2, h3, h4, h1.symm, h2.symm, h3.symm, h4.symm]

  rw[swap_variables_none']
  rw[swap_variables_none']

  ring

  exact h3
  exact h4
  exact h2.symm
  exact h4.symm
