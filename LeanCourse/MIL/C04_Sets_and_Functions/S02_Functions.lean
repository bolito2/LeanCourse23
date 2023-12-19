import LeanCourse.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  intro h x xs
  apply h
  use x, xs

  intro h y yfs
  rcases yfs with ⟨x, xs, fxy⟩
  rw [← fxy]
  apply h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro y ⟨x, xs, fxy⟩
  have : x = y := h fxy
  rw[← this]
  exact xs
example : f '' (f ⁻¹' u) ⊆ u := by
  rintro x ⟨y, yfinvu, fyx⟩
  rw [← fyx]
  apply yfinvu

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, fxy⟩
  use x
  constructor
  rw[← fxy] at yu
  apply yu
  exact fxy

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, fxy⟩
  rw [← fxy]
  use x
  constructor
  apply h xs
  rfl

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨yfs, ynft⟩
  rcases yfs with ⟨x, xs, fxy⟩
  have : x ∈ s \ t := by
    constructor
    exact xs
    intro h
    apply ynft
    use x
  use x

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
  rintro ⟨i, x, xAi, fxeq⟩
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y; simp
  intro x h fxeq i
  use x
  exact ⟨h i, fxeq⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y; simp
  intro h
  rcases h i with ⟨x, xAi, fxeq⟩
  use x; constructor
  · intro i'
    rcases h i' with ⟨x', x'Ai, fx'eq⟩
    have : f x = f x' := by rw [fxeq, fx'eq]
    have : x = x' := injf this
    rw [this]
    exact x'Ai
  exact fxeq

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos
  intro h
  calc
    x = (sqrt x)^2 := by rw[sq_sqrt xpos]
    _ = (sqrt y)^2 := by rw[h]
    _ = y := by rw[sq_sqrt ypos]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xpos y ypos
  intro h
  dsimp at h
  calc
    x = sqrt (x^2) := by rw[sqrt_sq xpos]
    _ = sqrt (y^2) := by rw[h]
    _ = y := by rw[sqrt_sq ypos]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  constructor
  rintro ⟨x, xpos, sxy⟩
  dsimp
  dsimp at xpos
  rw[← sxy]
  rcases lt_or_eq_of_le xpos with h|h
  apply le_of_lt
  apply sqrt_pos.2 h
  rw[← h]
  rw[sqrt_zero]
  intro ypos
  dsimp at ypos
  use y^2
  constructor
  dsimp
  exact sq_nonneg y
  exact sqrt_sq ypos

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  constructor
  rintro ⟨x, xsqy⟩
  dsimp at xsqy
  dsimp
  rw[← xsqy]
  exact sq_nonneg x
  intro h
  dsimp at h
  use sqrt y
  dsimp
  exact sq_sqrt h

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  intro h x
  have : f (inverse f (f x)) = f x := by
    apply inverse_spec
    use x
  apply h this
  intro h x y fxfy
  have : inverse f (f x) = inverse f (f y) := by
    rw[fxfy]

  rw[h] at this
  rw[h] at this
  exact this

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  intro h y
  rw[Surjective] at h
  have yim : ∃x, f x = y := h y
  exact inverse_spec y yim
  intro h y
  use inverse f y
  apply h
end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by
    rw[h] at h₁
    exact h₁
  contradiction

-- COMMENTS: TODO: improve this
end
