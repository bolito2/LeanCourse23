import LeanCourse.Project.Demazure
import LeanCourse.Project.DemazureAux

noncomputable section
namespace Demazure

open MvPolynomial

variable {n : ℕ} (n_pos : n > 0)

/- Basic composition relations for Demazure operators -/

lemma symm_invariant_swap_variables {i j : Fin n} {g : MvPolynomial (Fin n) ℂ} (h : MvPolynomial.IsSymmetric g) :
  SwapVariables i j g = g := by
  simp[SwapVariables, SwapVariablesFun]
  exact h (Transposition i j)

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

lemma DemAux_commutes_adjacent (i : Fin n) (h : i + 1 < n) : ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  (DemAux i ∘ DemAux ⟨i+1, h⟩ ∘ DemAux i) (mk' p) = (DemAux ⟨i+1, h⟩ ∘ DemAux i ∘ DemAux ⟨i+1, h⟩) (mk' p) := by
  intro p
  simp[DemAux, mk']
  repeat rw[lift_r]
  simp[DemAux']
  apply mk_eq.mpr
  simp[h, Fin.castSucc, Fin.succ, Fin.castAdd, Fin.castLE]
  norm_num

  have h0 : i < n + 1 := by
    linarith
  have h1 : i + 1 < n + 1 := by
    linarith
  have h2 : i + 2 < n + 1 := by
    linarith

  simp [swap_variables_commutes_adjacent h0 h1 h2]
  ring


lemma composition_adjacent' (i : Fin n) (h : i + 1 < n) : ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  (Demazure i ∘ Demazure ⟨i+1, h⟩ ∘ Demazure i) p = (Demazure ⟨i+1, h⟩ ∘ Demazure i ∘ Demazure ⟨i+1, h⟩) p := by
  intro p
  simp[Demazure]
  apply eq_of_eq_mk'.mp
  repeat rw[← demazure_definitions_equivalent]
  apply DemAux_commutes_adjacent


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
  equals ((DemAux i ∘ DemAux j) (of_polynomial p)) ((DemAux j ∘ DemAux i) (of_polynomial p)) := by
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

/-- Composition with multiplication by monomial -/
lemma composition_mul_monomial_non_adjacent (i j : Fin n) (h : |(i.val : ℤ ) - j.val| > 1) : ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  equals (DemAux i (of_polynomial (p * X (Fin.castSucc j)))) (mul (DemAux i (of_polynomial p)) (of_polynomial (X (Fin.castSucc j)))) := by
  intro p
  simp[equals, mul]

  rcases unfold_non_adjacent i j h with ⟨h1, h2, h3, h4⟩
  left
  simp[swap_variables_commutes_non_adjacent i j h, h1, h2, h3, h4, h1.symm, h2.symm, h3.symm, h4.symm]
  ring

lemma composition_mul_monomial_adjacent (i : Fin n) (h : i + 1 < n) : ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  equals (DemAux i (of_polynomial (p * X (Fin.castSucc i)))) (add (mul (DemAux i (of_polynomial p)) (of_polynomial (X (Fin.succ i)))) (of_polynomial p)) := by
  intro p
  simp[equals, mul, add]
  left
  ring

end Demazure

