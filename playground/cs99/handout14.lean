-- import Mathlib

section
--- snippet Clamp
def clamp (n : Nat) : Nat :=
  if n < 10 then
    n
  else
    10
example (x : Nat) (p : x < 10) : clamp x = x :=
  have : (clamp x = x) = (x = x) := congrArg
    (· = x) (dif_pos p)
  this ▸ rfl
--- snippet Clamp'
example (x : Nat) (p : x < 10) : clamp x = x := by
  unfold clamp -- Delete and see what happens
  simp [p]
--- end
end

section
--- snippet β-reduction
#reduce (λ x f => f (f x)) 5 (λ y => y * 2)
--- snippet δ-reduction
def x := 5
#reduce x
--- snippet ζ-reduction
#reduce let y := 10; y + y
--- snippet η-expansion
def f (x y : Nat) := x + y
#reduce f (y := 5)
--- snippet ι-reduction
#reduce Nat.rec (motive := λ _ => Nat) 0 (λ n prev => prev + n * n) 4
--- end
end

section
--- snippet Noncomputable
noncomputable def getFactor (n : ℕ) : n ≠ 1 → ℕ := λ _ =>
  let div := Nat.exists_prime_and_dvd ‹n ≠ 1›
  Exists.choose div
--- end
end

section
--- snippet Partial
partial def mystery (x : Nat) : Nat :=
  if x != 10 then
    mystery (x + 1)
  else
    15
--- snippet Factorial
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => fact n * (n + 1)
--- snippet Discrete Log
def discrlog : Nat → Nat
  | 0 => 0
  | (s+1) => 1 + discrlog ((s+1) / 2)
--- snippet Ackermann
def ackermann : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ackermann x 1
  | x+1, y+1 => ackermann x (ackermann (x+1) y)
--- snippet Discrete Log Proof
#print discrlog.proof_1
#check discrlog.proof_2
--- end
end

section
--- snippet Palindrome
inductive Palindrome : List α → Prop where
  | nil      : Palindrome []
  | single   : (a : α) → Palindrome [a]
  | sandwich : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])
--- snippet Palindrome reverse
theorem palindrome_reverse (h : Palindrome as) : Palindrome as.reverse := by
  induction h with
  | nil => exact Palindrome.nil
  | single a => exact Palindrome.single a
  | sandwich a h ih => simp; exact Palindrome.sandwich _ ih
--- end
end
