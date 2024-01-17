import LeanCourse.Project.Demazure

noncomputable section
namespace Demazure
variable {n : ℕ} (n_pos : n > 0)

lemma composition_non_adjacent (i j : Fin n) (h : |i - j| > Fin.ofNat' 1 n_pos) :
  Demazure i ∘ Demazure j = Demazure j ∘ Demazure i := by
  sorry

lemma composition_adjacent (i : Fin (n - 1)) :
  Demazure i ∘ Demazure (Fin.succ i : Fin n) ∘ Demazure i = Demazure (i + 1) ∘ Demazure i ∘ Demazure (i + 1) := by
  sorry
