import Mathlib

open Finset BigOperators

example {a r : ℝ} (n : ℕ) (h : r ≠ 1) :
  ∑ i in range (n+1), a * r^i = (a * r^(n+1) - a) / (r - 1) := by
  have hr: r-1 ≠ 0 := by exact sub_ne_zero_of_ne h
  induction n with
  | zero =>
  simp [Finset.sum_range_one, pow_zero, mul_one]
  symm
  rw [div_eq_iff]
  ring
  exact hr
  | succ n ih =>
  rw [sum_range_succ]
  rw [ih]
  apply eq_of_sub_eq_zero
  rw [← mul_left_inj' hr]
  field_simp [h]
  ring_nf

open Nat

example (n k : ℕ) (h : k ≤ n) : choose n 0 = 1 ∧ choose n n = 1 ∧ choose n k = choose n (n - k) := by
  constructor
  exact choose_zero_right n
  constructor
  exact choose_self n
  symm
  exact choose_symm h

example (f : ℕ → ℤ) (h0: f 1 = 1) (h1: f 2 = 5)
  (h : ∀ n ≥ 2, f (n + 1) = f n + 2 * f (n - 1)) :
  ∀ n ≥ 1, f n = 2^n + (-1)^n := by
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    obtain _ | _ | _ | n := n
    · omega -- case 0
    · simp [h0] -- case 1
    · simp [h1] -- case 2
    · simp [h, ih]
      ring
