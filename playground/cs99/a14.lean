-- Canonical definition: fib 0 = 1, fib 1 = 1
def fib : Nat → Nat
  | 0     => 1
  | 1     => 1
  | n + 2 => fib n + fib (n + 1)

-- Efficient impelementation
def fibAux (n : Nat) : Nat :=
  go n 1 1
where
  go (n a b : Nat) :=
    match n with
    | 0 => a
    | n + 1 => go n b (a + b)

#check fibAux.go

theorem go_eq_fib : fibAux.go (n + 1) a (a + b) = a * fib (n + 1) + b * fib n := by
  sorry

theorem fibAux_eq_fib : fibAux n = fib n := by
  unfold fibAux
  sorry
