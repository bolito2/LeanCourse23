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

namespace Demazure

variable {n : ℕ} (n_pos : n > 0) (n_gt_1 : n > 1)

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
lemma swap_variables_mul' (i j : Fin n) : ∀p q :
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

lemma poly_cancel_left {p q r : MvPolynomial (Fin n) ℂ} (hr : r ≠ 0) : (r * p) = (r * q) → p = q := by
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

structure PolyFraction' (n : ℕ) where
  numerator : MvPolynomial (Fin (n + 1)) ℂ
  denominator : MvPolynomial (Fin (n + 1)) ℂ
  denominator_ne_zero : denominator ≠ 0


def r (n : ℕ) : PolyFraction' n → PolyFraction' n → Prop :=
  fun p q => p.numerator * q.denominator = q.numerator * p.denominator

lemma r_equiv : Equivalence (r n) := by
  constructor
  intro p
  simp[r]
  ring
  intro p q
  simp[r]
  ring
  intro h
  simp[h]
  intro x y z
  simp[r]
  intro h1 h2

  by_cases h3 : y.numerator = 0
  simp[h3, y.denominator_ne_zero] at h1
  simp[h3, y.denominator_ne_zero] at h2
  simp[h1, h2, h3]

  apply poly_cancel_left y.denominator_ne_zero
  apply poly_cancel_left h3
  ring
  rw[mul_assoc y.numerator]
  rw[mul_comm y.denominator x.numerator]
  rw[h1]
  rw[mul_comm y.numerator (y.numerator * x.denominator)]
  rw[mul_assoc]
  rw[h2]
  ring

instance s (n : ℕ) : Setoid (PolyFraction' n) where
  r := r n
  iseqv := r_equiv

#check Quotient (s n)

def PolyFraction (n : ℕ) := (Quotient (s n))

def mk := Quotient.mk (s n)

instance has_equiv : HasEquiv (PolyFraction' n) := instHasEquiv

lemma equiv_r {a b : PolyFraction' n} : (r n) a b ↔ a ≈ b := by
  rfl

@[simp]
lemma lift2_r {a b : PolyFraction' n} {f : PolyFraction' n → PolyFraction' n → PolyFraction n}
{c :  ∀ (a₁ b₁ a₂ b₂ : PolyFraction' n), a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂} : Quotient.lift₂ f c (mk a) (mk b) = f a b := by
  rfl

lemma get_polyfraction_rep (p : PolyFraction n) : ∃p' : PolyFraction' n, mk p' = p := by
    simp[mk]
    apply Quotient.exists_rep p

def add' {n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction' n :=
  fun p q => ⟨p.numerator * q.denominator + q.numerator * p.denominator, p.denominator * q.denominator, mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero⟩

def add_mk {n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction n :=
  fun p q => mk (add' p q)

lemma add'_s {n : ℕ} : ∀ a₁ b₁ a₂ b₂ : PolyFraction' n, a₁ ≈ a₂ → b₁ ≈ b₂ → add_mk a₁ b₁ = add_mk a₂ b₂ := by
  intro a1 b1 a2 b2
  intro h1 h2
  simp[add_mk]
  apply Quotient.sound
  apply equiv_r.mp
  simp[r, add']
  ring
  rw[← equiv_r] at h1
  rw[← equiv_r] at h2
  simp[r] at h1
  simp[r] at h2

  rw[mul_comm a1.numerator]
  rw[mul_assoc b1.denominator]
  rw[h1]

  rw[mul_comm b1.numerator]
  rw[mul_assoc a1.denominator]
  rw[mul_comm b1.numerator]
  rw[mul_assoc a1.denominator]
  rw[mul_assoc a2.denominator]
  rw[h2]
  ring

def add : PolyFraction n → PolyFraction n → PolyFraction n :=
  fun p q ↦ Quotient.lift₂ (add_mk) (add'_s) p q

def sub' {n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction n :=
  fun p q ↦ mk ⟨p.numerator * q.denominator - q.numerator * p.denominator, p.denominator * q.denominator, mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero⟩

lemma sub'_s {n : ℕ} : ∀ a₁ b₁ a₂ b₂ : PolyFraction' n, a₁ ≈ a₂ → b₁ ≈ b₂ → (sub' a₁ b₁) = (sub' a₂ b₂) := by
  intro a1 b1 a2 b2
  intro h1 h2
  simp[sub']
  apply Quotient.sound
  apply equiv_r.mp
  simp[r]
  ring
  rw[← equiv_r] at h1
  rw[← equiv_r] at h2
  simp[r] at h1
  simp[r] at h2

  rw[mul_comm a1.numerator]
  rw[mul_assoc b1.denominator]
  rw[h1]

  rw[mul_comm b1.numerator]
  rw[mul_assoc a1.denominator]
  rw[mul_comm b1.numerator]
  rw[mul_assoc a1.denominator]
  rw[mul_assoc a2.denominator]
  rw[h2]
  ring

def sub : PolyFraction n → PolyFraction n → PolyFraction n :=
  fun p q ↦ Quotient.lift₂ (sub') (sub'_s) p q

def mul'{n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction' n :=
  fun p q => ⟨p.numerator * q.numerator, p.denominator * q.denominator, mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero⟩

def mul_mk {n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction n :=
  fun p q => mk (mul' p q)

lemma mul'_s {n : ℕ} : ∀ a₁ b₁ a₂ b₂ : PolyFraction' n, a₁ ≈ a₂ → b₁ ≈ b₂ → (mul_mk a₁ b₁) = (mul_mk a₂ b₂) := by
  intro a1 b1 a2 b2
  intro h1 h2
  simp[mul_mk]
  apply Quotient.sound
  apply equiv_r.mp
  simp[r, mul']
  ring
  rw[← equiv_r] at h1
  rw[← equiv_r] at h2
  simp[r] at h1
  simp[r] at h2

  rw[mul_comm a1.numerator]
  rw[mul_assoc b1.numerator]
  rw[h1]

  rw[mul_comm b1.numerator]
  rw[mul_assoc (a2.numerator * a1.denominator)]
  rw[h2]
  ring

def mul : PolyFraction n → PolyFraction n → PolyFraction n :=
  fun p q ↦ Quotient.lift₂ (mul_mk) (mul'_s) p q

def inv' (p : PolyFraction' n) (h : p.numerator ≠ 0) : PolyFraction' n := by
  exact ⟨p.denominator, p.numerator, h⟩

def inv_mk (p : PolyFraction' n) (h : p.numerator ≠ 0) : PolyFraction n :=
  mk (inv' p h)

lemma inv'_s (n : ℕ) : ∀ (a₁ a₂ : PolyFraction' n) (h1 : a₁.numerator ≠ 0) (h2 : a₂.numerator ≠ 0),
 a₁ ≈ a₂ → (inv_mk a₁ h1) = (inv_mk a₂ h2) := by
  intro a1 a2
  intro h1 h2
  intro h
  simp[inv_mk]
  apply Quotient.sound
  apply equiv_r.mp
  simp[r, inv']
  ring
  rw[← equiv_r] at h
  simp[r] at h
  rw[mul_comm]
  rw[← h]
  ring

def inv (p : PolyFraction' n) (h : p.numerator ≠ 0) : PolyFraction n := by
  apply Quotient.lift (inv_mk p h) (inv'_s n)
  sorry

@[simp]
def one' : PolyFraction' n where
  numerator := 1
  denominator := 1
  denominator_ne_zero := one_ne_zero

def one : PolyFraction n := mk one'

@[simp]
def zero' : PolyFraction' n where
  numerator := 0
  denominator := 1
  denominator_ne_zero := one_ne_zero

def zero : PolyFraction n := mk zero'

def neg' (p : PolyFraction' n) : PolyFraction' n :=
  ⟨-p.numerator, p.denominator, p.denominator_ne_zero⟩

def neg_mk (p : PolyFraction' n) : PolyFraction n := mk (neg' p)

lemma neg_s (n : ℕ) : ∀ (a₁ a₂ : PolyFraction' n), a₁ ≈ a₂ → (neg_mk a₁) = (neg_mk a₂) := by
  intro a1 a2
  intro h
  simp[neg_mk]
  apply Quotient.sound
  apply equiv_r.mp
  simp[r, neg']
  ring
  rw[← equiv_r] at h
  simp[r] at h
  rw[h]

def neg (p : PolyFraction n) : PolyFraction n := Quotient.lift neg_mk (neg_s n) p

@[simp]
lemma add_comm (p q : PolyFraction n) : add p q = add q p := by
  rcases get_polyfraction_rep p with ⟨p', hp⟩
  rcases get_polyfraction_rep q with ⟨q', hq⟩
  simp[add]
  rw[← hp]
  rw[← hq]
  simp[lift2_r]
  simp[add_mk]
  apply Quotient.sound
  apply equiv_r.mp
  simp[r, add']
  ring

@[simp]
lemma add_assoc (p q r : PolyFraction n) : add (add p q) r = add p (add q r) := by
  rcases get_polyfraction_rep p with ⟨p', hp⟩
  rcases get_polyfraction_rep q with ⟨q', hq⟩
  rcases get_polyfraction_rep r with ⟨r', hr⟩
  rw[← hp]
  rw[← hq]
  rw[← hr]

  have hpq : (add (mk p') (mk q')) = mk (add' p' q') := by
    simp[add, add_mk]

  have hqr : (add (mk q') (mk r')) = mk (add' q' r') := by
    simp[add, add_mk]

  rw[hpq, hqr]
  simp[add, lift2_r]
  simp[add']
  apply Quotient.sound
  apply equiv_r.mp
  simp[Demazure.r, add']
  ring

def DDenominator (i : Fin n) : PolyFraction' n := by
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
def of_polynomial (p : MvPolynomial (Fin (n + 1)) ℂ) : PolyFraction' n := by
  exact ⟨p, 1, one_ne_zero⟩

def Dem' (i : Fin n) : PolyFraction' n →  PolyFraction' n := fun p =>
   ⟨
    p.numerator * (SwapVariables (Fin.castSucc i) (Fin.succ i) p.denominator) - (SwapVariables (Fin.castSucc i) (Fin.succ i) p.numerator) * p.denominator,
    p.denominator * (SwapVariables (Fin.castSucc i) (Fin.succ i) p.denominator) * (X (Fin.castSucc i) - X (Fin.succ i)),
    mul_ne_zero (mul_ne_zero p.denominator_ne_zero (swap_variables_ne_zero (Fin.castSucc i) (Fin.succ i) p.denominator p.denominator_ne_zero)) (wario i)
    ⟩

lemma demazure_order_two : ∀ (i : Fin n) (p : PolyFraction' n),
  (Dem' i (Dem' i p)) ≈ zero' := by
  intro i p
  rw[← equiv_r]
  simp[r, Dem']
  ring

lemma Dem_well_defined (i : Fin n) : ∀ (p q : PolyFraction' n) (h : p ≈ q), ((mk ∘ Dem' i) p) = ((mk ∘ Dem' i) q) := by
  intro p q h
  simp[Dem']
  apply Quotient.sound
  apply equiv_r.mp
  simp[r]
  rw[← equiv_r] at h
  simp[r] at h
  ring
  rw[mul_comm p.numerator]
  rw[mul_assoc (SwapVariablesFun (Fin.castSucc i) (Fin.succ i) p.denominator)]
  rw[h]

  rw[mul_comm (SwapVariablesFun (Fin.castSucc i) (Fin.succ i) p.numerator)]
  rw[mul_assoc p.denominator]
  rw[mul_comm (SwapVariablesFun (Fin.castSucc i) (Fin.succ i) p.numerator)]
  rw[mul_assoc p.denominator]
  rw[mul_assoc q.denominator]
  rw[← swap_variables_mul]
  rw[h]

  simp[swap_variables_mul]
  ring

def Dem (i : Fin n) (p : PolyFraction n) : PolyFraction n :=
  Quotient.lift (mk ∘ (Dem' i)) (Dem_well_defined i) p

@[simp]
lemma lift_r {a: PolyFraction' n} {f : PolyFraction' n → PolyFraction' n}
{c :  ∀ (a₁ a₂ : PolyFraction' n), a₁ ≈ a₂ → mk (f a₁) = mk (f a₂)} : Quotient.lift (mk ∘ f) c (mk a) = mk (f a) := by
  rfl

lemma demazure_quot_order_two : ∀ (i : Fin n) (p : PolyFraction n),
  (Dem i (Dem i p)) = zero := by
  intro i p
  rcases get_polyfraction_rep p with ⟨p', rfl⟩
  simp[Dem]
  rw[lift_r]
  rw[lift_r]
  rw[zero]
  apply Quotient.sound
  exact demazure_order_two i p'

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

  lemma demazure_definitions_equivalent : ∀ i : Fin n, ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  equals (Dem i (of_polynomial p)) (of_polynomial (DemazureFun i p)) := by
  intro i p
  simp[equals, Dem]

  have h : DemazureDenominator i * ((DemazureNumerator i p) /ₘ (DemazureDenominator i)) = DemazureNumerator i p := demazure_division_exact' i p

  apply (SwapVariables (Fin.castSucc i) (0 : Fin (n + 1))).injective
  apply (MvPolynomial.finSuccEquiv ℂ n).injective

  have h2 : DemazureNumerator i p =  (MvPolynomial.finSuccEquiv ℂ n)
    ((SwapVariables (Fin.castSucc i) 0) (p - SwapVariablesFun (Fin.castSucc i) (Fin.succ i) p)) := by
    simp [DemazureNumerator]


  rw[← h2]
  rw[← h]
  simp [SwapVariables]
  rw[swap_variables_none (fin_succ_ne_fin_castSucc i) (Fin.succ_ne_zero i)]
  simp

  have h3 : DemazureDenominator i = Polynomial.X - Polynomial.C (X i) := by
    simp [DemazureDenominator]

  rw[← h3]
  rw [mul_comm (eval₂ (RingHom.comp Polynomial.C C) (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (X k)) i)
      (SwapVariablesFun (Fin.castSucc i) 0 (DemazureFun i p))) (DemazureDenominator i)]
  rw[← poly_mul_cancel (demazure_denominator_ne_zero i)]
  simp[DemazureFun]
  have h4 {q : MvPolynomial (Fin (n + 1)) ℂ } : eval₂ (RingHom.comp Polynomial.C C) (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (X k)) i)
    q = (MvPolynomial.finSuccEquiv ℂ n) q := by
    simp
  rw[h4]
  nth_rewrite 1 [← AlgEquiv.coe_apply_coe_coe_symm_apply (finSuccEquiv ℂ n) (DemazureNumerator i p /ₘ DemazureDenominator i)]
  rfl

-/
