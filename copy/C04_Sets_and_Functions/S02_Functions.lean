import MIL.Common
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
  rintro h
  simp at h
  exact h
  rintro h
  simp
  exact h


example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨ y, hy, a⟩
  rw [(h a).symm]
  exact hy


example : f '' (f ⁻¹' u) ⊆ u := by
  rintro x ⟨ y, hy, rfl⟩
  exact hy

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, fxeq⟩
  use x
  constructor
  · show f x ∈ u
    rw [fxeq]
    exact yu
  exact fxeq


example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x ⟨y, ⟨xs, h1⟩ ⟩
  use y
  exact ⟨ h xs, h1⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x h1
  exact h h1


example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  rintro h
  exact h
  rintro h
  exact h


example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x ⟨y, ⟨ xst, hyx⟩ ⟩
  constructor
  use y
  exact ⟨xst.1, hyx ⟩
  use y
  exact ⟨xst.2, hyx ⟩


example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x ⟨ ⟨ y, ⟨ hy, hxy⟩ ⟩, ⟨ y2, ⟨ hy2, hxy2⟩⟩ ⟩
  rw [hxy2.symm] at hxy
  specialize h hxy
  rw [h.symm] at hy2
  rw [h.symm] at hxy2
  use y
  exact ⟨ ⟨ hy, hy2⟩, hxy2⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x ⟨⟨ y, ⟨ ys, fyx⟩ ⟩ , h ⟩
  use y
  by_cases h1: y ∈ t
  exfalso
  simp at h
  specialize h y h1
  exact h fyx
  exact ⟨⟨ ys, h1⟩ , fyx ⟩


example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
  fun x ↦ id

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  constructor
  . intro ⟨ ⟨ y, a, b⟩ , hxv⟩
    use y
    constructor
    constructor
    exact a
    show f y ∈ v
    rw [b]
    exact hxv
    exact b
  intro ⟨ y, ⟨ a, c⟩ , b⟩
  constructor
  use y
  rw [b.symm]
  exact c

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro x ⟨ y, ⟨ a, c⟩ , b⟩
  constructor
  use y
  rw [b.symm]
  exact c

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨ a, b ⟩
  constructor
  use x
  exact b

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x h
  rcases h with h|h
  constructor
  use x
  exact Or.inr h


variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  constructor
  rintro ⟨y, hyAi, hfyx⟩
  simp at hyAi
  simp
  obtain ⟨ i, hy⟩ := hyAi
  use i
  use y
  simp
  intro i y yAi fyx
  use y
  exact ⟨⟨i, yAi ⟩, fyx⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro x ⟨ y, ⟨ hi, fyx⟩ ⟩
  simp
  intro i
  use y
  simp at hi
  exact ⟨hi i, fyx⟩


example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  rintro x h
  simp at h
  simp
  obtain ⟨ y, ⟨ yAi, fyx⟩ ⟩ := (h i)
  use y
  constructor
  intro j
  obtain ⟨ y2, ⟨ yAi2, fyx2⟩ ⟩ := (h j)
  rw [fyx2.symm] at fyx
  specialize injf fyx
  rw [injf]
  exact yAi2
  exact fyx



example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  constructor
  repeat
  intro hi
  simp at hi
  simp
  exact hi

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  constructor
  repeat
  intro h
  simp at h
  simp
  exact h

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
  unfold InjOn
  intro x1 hx1 x2 hx2 h
  calc
    x1 = (sqrt x1) ^ 2 := by exact Eq.symm (sq_sqrt hx1)
    _ = (sqrt x2) ^ 2 := by rw[h]
    _ = x2 := by exact (sq_sqrt hx2)


example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  unfold InjOn
  intro x1 hx1 x2 hx2 h
  dsimp at h
  calc
    x1 = sqrt (x1 ^ 2) := by exact Eq.symm (sqrt_sq hx1)
    _ = sqrt (x2 ^ 2) := by rw[h]
    _ = x2 := by exact (sqrt_sq hx2)

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x
  constructor
  intro ⟨ y, ⟨ hy, sqrtyx⟩ ⟩
  rw [sqrtyx.symm]
  apply sqrt_nonneg
  intro h
  use x ^ 2
  exact ⟨ sq_nonneg x, sqrt_sq h⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x
  constructor
  intro ⟨ y, hy⟩
  dsimp at hy
  rw [hy.symm]
  exact sq_nonneg y
  intro hx
  dsimp at hx
  use sqrt x
  dsimp
  exact sq_sqrt hx

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

example : Injective f ↔ LeftInverse (inverse f) f := ⟨
  fun h x => h (inverse_spec (h:=⟨x, rfl⟩) ),
  fun h x1 x2 h1 => Eq.trans (h x1).symm (Eq.trans (congrArg (inverse f) h1) (h x2))
  ⟩


example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  intro h x
  apply h
  apply inverse_spec
  use x
  intro h x1 x2 h1
  rw [(h x1).symm, (h x2).symm, h1]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  intro h x
  apply inverse_spec
  exact h x
  intro h y
  use inverse f y
  exact h y
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
  have h₂ : j ∈ S := by
    exact h₁
  have h₃ : j ∉ S := by
    rw [h] at h₁
    exact h₁
  contradiction

-- COMMENTS: TODO: improve this
end
