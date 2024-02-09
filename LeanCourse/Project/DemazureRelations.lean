import LeanCourse.Project.Demazure
import LeanCourse.Project.DemazureAux
import LeanCourse.Project.DemazureAuxRelations

noncomputable section
open MvPolynomial

namespace Demazure

variable {n : ℕ} (n_pos : n > 0) (n_gt_1 : n > 1)

lemma demazure_order_two : ∀ (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ),
  Demazure i (Demazure i p) = 0 := by
  intro i p
  apply eq_zero_of_mk'_zero.mp
  simp[Demazure]
  rw[← demazure_definitions_equivalent]
  rw[← demazure_definitions_equivalent]

  exact demazure_quot_order_two i (mk' p)

lemma demaux_commutes_adjacent (i : Fin n) (h : i + 1 < n) : ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  (Demazure i ∘ Demazure ⟨i+1, h⟩ ∘ Demazure i) p = (Demazure ⟨i+1, h⟩ ∘ Demazure i ∘ Demazure ⟨i+1, h⟩) p := by
  intro p
  simp[Demazure]
  apply eq_of_eq_mk'.mp
  repeat rw[← demazure_definitions_equivalent]
  apply DemAux_commutes_adjacent

def IsSymmetric (p : PolyFraction n) : Prop := ∃p' : PolyFraction' n,
 mk p' = p ∧ MvPolynomial.IsSymmetric p'.numerator ∧ MvPolynomial.IsSymmetric p'.denominator

lemma Demazure_mul_symm (i : Fin n) (g f : MvPolynomial (Fin (n + 1)) ℂ) (h : MvPolynomial.IsSymmetric g) :
 Demazure i (g*f) = g*(Demazure i f) := by
  simp[Demazure]
  rw[← eq_of_eq_mk']
  rw[← demazure_definitions_equivalent]
  rw [← mk'_mul]
  rw [← mk'_mul]
  rw[← demazure_definitions_equivalent]

  have : IsSymmetric (mk' g) := by
    simp[IsSymmetric]
    use (to_frac g)
    simp[to_frac]
    constructor
    rfl
    exact h

  exact DemAux_mul_symm i (mk' g) (mk' f) this


def Dem (i : Fin n) : LinearMap (RingHom.id (MvPolynomial.symmetricSubalgebra (Fin (n + 1)) ℂ))
 (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial (Fin (n + 1)) ℂ) where
  toFun := DemazureFun i
  map_add' := demazure_map_add i
  map_smul' := by
    intro r x
    simp
    let p : MvPolynomial (Fin (n + 1)) ℂ := r
    have wah : p = r := by rfl
    have h : MvPolynomial.IsSymmetric p := by
      apply (MvPolynomial.mem_symmetricSubalgebra p).mp
      rw[wah]
      exact SetLike.coe_mem r
    exact Demazure_mul_symm i p x h
