import Mathlib

theorem quadratic_one {x : ℝ} : x^2 - x - 6 = 0 -> x = -2 ∨ x = 3 := by
  intro h
  have h1 : (x - 3) * (x + 2) = 0 := by
    linarith [h]
  cases' (mul_eq_zero.mp h1)
  ·
    right
    linarith
  ·
    left
    linarith

theorem quadratic_simple {x : ℝ} : x^2 - 2*x + 1 = 0 -> x = 1 := by
  intro h
  replace h : (x - 1)^2 = 0 := by linarith
  replace h : (x - 1) = 0 := pow_eq_zero h
  linarith
