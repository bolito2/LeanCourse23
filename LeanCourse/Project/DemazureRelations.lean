import LeanCourse.Project.Demazure

noncomputable section
namespace Demazure
variable {n : ℕ} (n_pos : n > 0)

lemma composition_non_adjacent (i j : Fin n) (h : |i - j| > Fin.ofNat' 1 n_pos) :
  Demazure i ∘ Demazure j = Demazure j ∘ Demazure i := by
  sorry

lemma composition_adjacent (i : Fin n) (h : i + 1 < n) :
  Demazure i ∘ Demazure ⟨i+1, h⟩ ∘ Demazure i = Demazure ⟨i+1, h⟩ ∘ Demazure i ∘ Demazure ⟨i+1, h⟩ := by
  sorry
