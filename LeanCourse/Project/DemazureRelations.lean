import LeanCourse.Project.Demazure

noncomputable section
namespace Demazure
variable {n : ℕ} (n_pos : n > 0)

/- Basic composition relations for Demazure operators -/

lemma composition_non_adjacent (i j : Fin n) (h : |i - j| > Fin.ofNat' 1 n_pos) :
  Demazure i ∘ Demazure j = Demazure j ∘ Demazure i := by
  sorry

lemma composition_adjacent (i : Fin n) (h : i + 1 < n) :
  Demazure i ∘ Demazure ⟨i+1, h⟩ ∘ Demazure i = Demazure ⟨i+1, h⟩ ∘ Demazure i ∘ Demazure ⟨i+1, h⟩ := by
  sorry

/- Lemmas with symmetric polynomials -/

lemma symm_invariant_swap_variables (i j : Fin n) (g : MvPolynomial (Fin n) ℂ) (h : MvPolynomial.IsSymmetric g) :
  SwapVariables i j g = g := by
  simp[SwapVariables, SwapVariablesFun]
  exact h (Transposition i j)

lemma mul_symm (i : Fin n) (f g : MvPolynomial (Fin (n + 1)) ℂ) (h : MvPolynomial.IsSymmetric g) :
  Demazure i (g * f) = g * Demazure i f := by
  simp[Demazure, DemazureFun]
  rw[← symm_invariant_swap_variables (Fin.castSucc i) 0 g h]
  simp[SwapVariables]
  rw[← swap_variables_mul (Fin.castSucc i) 0]
  apply congrArg

  sorry
