import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos


theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  specialize hs n (le_of_max_le_left hn)
  specialize ht n (le_of_max_le_right hn)
  have h : (|s n - a| + |t n - b| < ε / 2 + ε / 2) := by linarith
  norm_num at h
  have h2: (|s n + t n - (a + b)| ≤ |s n - a| + |t n - b|) := by
    rw [← sub_sub, add_sub_right_comm, add_sub_assoc]
    apply (abs_add (s n - a) (t n - b))
  apply lt_of_le_of_lt h2 h


theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  unfold ConvergesTo
  unfold ConvergesTo at cs
  intro ε hε
  have hcε : ε / |c| > 0 := by
    exact div_pos hε acpos
  specialize cs (ε/|c|) hcε
  obtain ⟨ N, hN⟩ := cs
  use N
  intro n hn
  specialize hN n hn
  dsimp
  rw [← mul_sub_left_distrib]
  rw [abs_mul]
  apply (lt_div_iff₀ acpos).1 at hN
  linarith


theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  specialize h n hn
  have h1: |s n - a| + |a| ≥ |s n - a + a| := by
    exact abs_add_le (s n - a) a
  simp at h1
  apply (add_lt_add_iff_left |a|).2 at h
  linarith

example {a b c d: ℝ } (h: a < b) (h1: c < d) (h2: b > 0) (h3: d > 0): a*c < b*d := by
  refine mul_lt_mul_of_nonneg_of_pos' ?_ h1 ?_ h2

#check max_le_iff

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use (max N₀ N₁)
  intro n hn
  specialize h₁ n (max_le_iff.1 hn).2
  specialize h₀ n (max_le_iff.1 hn).1
  rw [sub_zero]
  rw [sub_zero] at h₁
  have h: |t n| * |s n| < ε / B * B
  refine mul_lt_mul_of_nonneg_of_pos' ?_ ?_ ?_ ?_
  exact le_of_lt h₁
  exact h₀
  exact abs_nonneg (s n)
  exact pos₀
  rw [abs_mul]
  have h1: ε / B * B = ε := by sorry
  rw [h1] at h
  linarith


theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by sorry
  have absb : |s N - b| < ε := by sorry
  have : |a - b| < |a - b| := by sorry
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
