import Mathlib

--- snippet Rewrite 1
example (h1 : a = b) (h2 : b = c) : a = c := by
  rewrite [h1, h2]
  rfl

example (h1 : a = b) (h2 : b = c) : a = c :=
  Eq.mpr (congrArg (fun x => x = c) h1)
 (Eq.mpr (congrArg (fun x => x = c) h2)
 (Eq.refl c))
--- snippet Rewrite 2
example (x y : ℕ) : x * (y * z) = x * (z * y) := by
  rewrite [Nat.mul_comm y z]
  rfl
--- snippet Rewrite 3
example (x : ℤ) : x + (-x) = 0 := by
  rewrite [← Int.add_zero (-x), Int.add_neg_cancel_left]
  rfl
--- end
section
--- snippet Calc
variable (a b c d e : ℕ)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

example : a = e := by
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4
--- end
end
--- snippet Calc-Induction
theorem mystery (n m : Nat) : (n ≤ n + m) := by
  induction n
  case zero =>
    apply Nat.zero_le
  case succ n h =>
    calc
      n + 1 ≤ (n + m) + 1 := Nat.succ_le_succ h
      _     = n + (m + 1) := by apply Nat.add_assoc
      _     = n + (1 + m) := by rw [Nat.add_comm m 1]
      _     = (n + 1) + m := Eq.symm $ Nat.add_assoc n 1 m
--- snippet Congr
example (x y : ℕ) (f : ℕ → ℕ) : f (x + y + 1) = f (y + x + 1) := by
  congr 2
  apply Nat.add_comm
--- snippet Calc-rewrite exercise
example (x y z : ℕ) : (x + y) * (z + y) = y * (z + y) + z * x + y * x := sorry
--- end

section

variable (x y z : ℤ)
--- snippet Conv
example (f : ℤ → ℤ) : f (x + y * z) = f (x + z * y) := by
  conv =>
    lhs
    arg 1
    rhs
    rewrite [Int.mul_comm]
--- snippet Conv Pattern Match
example (f : ℤ → ℤ) : f (x + y * z) = f (x + z * y) := by
  conv =>
    pattern y * z
    rewrite [Int.mul_comm]
--- snippet Conv Intro
example : (∀ (a : ℤ), a * x = a * y) ↔ (∀ (b : ℤ), b * y = b * x) := by
  conv =>
    lhs
    intro
    rw [eq_comm]
--- snippet Conv Tactic
example (g : ℤ → ℤ → ℤ)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . skip
    . tactic => exact h₂
--- end
end

--- snippet Simp 1
example {f f' : Nat → Nat}
  (h1 : ∀ x, f (f x) = f x)
  (h2 : ∀ x, f' x = f x) :
    f' (f' (f' x)) = f' x := by
  -- rw [h2, h2, h2, h1, h1]
  simp [h2, h1]
--- snippet Simp 2
example : 0 * n + (0 + n) = n := by simp
--- snippet Simp 3
example {p : Prop}
  (h1 : y = 0 → x = 0) (h2 : p → 0 = y) (h3 : p) : x = 0 := by
  simp [h1, h2, h3]
--- snippet Simp 4
example {p : α → Prop} (h : p x) : p x = True := by simp [h]
example {p : α → Prop} (h : p x ∧ ¬p y) : p x = True := by simp [h]
example {p : α → Prop} (h : p a ↔ p b) : p a = p b := by simp [h]
--- snippet Simp 5
example (xs : List Nat) : xs.map (fun n => n + 1) = xs.map (fun n => 1 + n) := by
  simp [Nat.add_comm]
--- snippet wildcard simp
example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
--- snippet simp at
example (x y : Nat) (h : x + 0 = 4 + y - 4) : x = (y + 123 - 123) := by
  simp at h ⊢
  assumption
--- snippet simpa
example (x y : Nat) (h : x + 0 = 4 + y - 4) : x = (y + 123 - 123) := by
  simpa using h
--- snippet simp_all 1
example {m n : Nat} (h1 : n + m = m) (h2 : m = n) : n + n = n := by
  -- simp [h2] at h1; simp [h1]
  simp_all
--- snippet simp_all 2
open Classical in
example {p : α → Prop} {f : α → α} :
  (p x → f x = y) → (if p x then f x else y) = y := by
  simp_all
--- snippet loop
example (x y : Nat) : x + y + z = z + (x + y) := by
  simp [Nat.add_comm x y, ← Nat.add_comm]
--- snippet Parallel Combinator
example (x y : ℕ) : 0 < x → 0 < y → 0 < x * y := by
  intro hx hy
  apply Nat.zero_lt_of_ne_zero
  have := Nat.ne_zero_iff_zero_lt.mpr hx
  have := Nat.ne_zero_iff_zero_lt.mpr hy
  simp
  constructor <;> intro <;> contradiction
--- snippet Try Combinator
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption
