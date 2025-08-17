namespace nn

example (x q : Nat) : 37*x + q = 37*x + q := by
  rfl

example (x y: Nat) : (y = x + 7) → 2*y = 2*(x + 7) := by
  intro h
  rw [h]

example (a b c: Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [Nat.add_zero, Nat.add_zero]

example (n : Nat) : Nat.succ n = n + 1 := by
  sorry

example : 2 + 2 = 4 := by
  nth_rewrite 2 [two_eq_succ_one] -- only change the second `2` to `succ 1`.
  rw [add_succ]
  rw [one_eq_succ_zero]
  rw [add_succ, add_zero] -- two rewrites at once
  rw [← three_eq_succ_two] -- change `succ 2` to `3`
  rw [← four_eq_succ_three]
  rfl


end nn
