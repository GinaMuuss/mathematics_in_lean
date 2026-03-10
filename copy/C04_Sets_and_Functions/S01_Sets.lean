import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨ xs, xt ⟩ | ⟨ xs, xu ⟩ )
  constructor
  exact xs
  constructor
  exact xt
  constructor
  exact xs
  exact Or.inr xu

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨ xs, xt ⟩ | ⟨ xs, xu ⟩ )
  exact ⟨ xs, Or.inl xt⟩
  exact ⟨ xs, Or.inr xu⟩

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨ xs, hh ⟩
  exact ⟨ ⟨xs, (fun xnt => hh (Or.inl xnt))⟩,  (fun xnt => hh (Or.inr xnt))⟩


example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm (fun x ⟨ xs, xt⟩ => ⟨ xt, xs⟩) (fun x ⟨ xs, xt⟩ => ⟨ xt, xs⟩)
example : s ∩ (s ∪ t) = s := by
  apply Subset.antisymm
  rintro x ⟨ xs, (xs | xt)⟩
  exact xs
  exact xs
  rintro x xs
  exact ⟨ xs, Or.inl xs⟩


example : s ∪ s ∩ t = s := by
  apply Subset.antisymm
  rintro x (xs | ⟨ xs, xt⟩ )
  exact xs
  exact xs
  rintro x xs
  exact Or.inl xs

example : s \ t ∪ t = s ∪ t := by
  ext x
  apply Iff.intro
  rintro xs
  rcases xs with h | h
  exact Or.inl h.1
  exact Or.inr h
  rintro xs
  rcases xs with h | h
  rcases em (x ∈ t) with h1 | h1
  exact Or.inr h1
  exact Or.inl ⟨ h, h1⟩
  exact Or.inr h


example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  apply Subset.antisymm
  rintro x h
  rcases h with ⟨xs, xnt⟩  | ⟨ xt, xns⟩
  exact ⟨Or.inl xs , fun (h2: x ∈ (s ∩ t)) => (absurd h2.2 xnt) ⟩
  exact ⟨Or.inr xt , fun (h2: x ∈ (s ∩ t)) => (absurd h2.1 xns) ⟩
  rintro x ⟨ ha, hb⟩
  rcases ha with (ha1| ha2)
  exact (Or.inl ⟨ ha1, fun (h3: x ∈ t) => absurd ⟨ha1, h3 ⟩ hb⟩ )
  exact (Or.inr ⟨ ha2, fun (h3: x ∈ s) => absurd ⟨h3, ha2 ⟩ hb⟩ )


example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  apply Subset.antisymm
  -- First inclusion, from the left
  . rintro x (⟨ha, hb⟩ | ⟨ha, hb⟩)
  -- In case x is in s \ t
    . exact ⟨Or.inl ha, (fun h2: x ∈ s ∩ t => (hb h2.right))⟩
    -- In case x is in t \ s
    exact ⟨Or.inr ha, (fun h2: x ∈ s ∩ t => (hb h2.left))⟩
    -- Second inclusion
  rintro x ⟨(ha | ha), hc⟩
  -- First case, with x in s
  . apply Or.inl
    constructor
    exact ha
    by_contra h
    exact hc (⟨ha, h⟩)
  -- Second case, with x in t
  apply Or.inr
  constructor
  exact ha
  by_contra h
  exact hc ⟨h, ha⟩


def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial


#check Nat.Prime.eq_two_or_odd
#check Nat.odd_iff
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n ⟨h1, h2⟩ he
  unfold Even at he
  obtain ⟨r, hr⟩ := he
  apply Nat.Prime.eq_two_or_odd at h1
  dsimp at h2
  rcases h1 with h1 | h1
  linarith!
  rw [hr] at h1
  rw [← mul_two, Nat.mul_mod_left r 2] at h1
  linarith!


#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  rintro x xs
  exact ⟨ h₀ x (ssubt xs), h₁ x (ssubt xs)⟩

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  obtain ⟨ x, ⟨ hs, hneven, hprime ⟩ ⟩ := h
  use x
  exact ⟨ (ssubt hs), hprime⟩

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp
  constructor
  intro h
  rcases h with h|h
  exact (fun i => Or.inr h)
  exact (fun i => Or.inl (h i))
  intro h
  by_cases xs: x ∈ s
  exact Or.inl xs
  apply Or.inr
  intro i
  specialize h i
  rcases h with h | h
  exact h
  exfalso
  exact (xs h)



def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

#check Nat.exists_infinite_primes
example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  simp
  obtain ⟨ p, hp⟩ := (Nat.exists_infinite_primes x)
  use p
  exact ⟨ hp.2, hp.1⟩
end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
