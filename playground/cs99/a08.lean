/-!
# Lean 4 Tactics Exercises

This file contains a sequence of increasingly rich exercises demonstrating key Lean 4 tactics covered in Lecture 8.
-/

namespace A08

/-!
## 1. Evenness of zero
Prove that 0 is even, where `even` is defined by an existential.
-/

def Even (n : Nat) : Prop := ∃ k, n = 2 * k

theorem even_zero : Even 0 := by
  -- Use `exact` and `rfl` tactics to exhibit the witness `0`.
  -- Lean also provides the `exists` which you can use to simplify the proof
  -- exists 0
  exact Exists.intro 0 rfl

/-!
## 2. Evenness preserved under addition of two
Show that if `n` is even then so is `n + 2`.
-/

theorem even_add_two : Even n → Even (n + 2) := by
  -- Use `intro` to get a proof of `Even n` and `cases` to destructure the existential,
  -- then reconstruct.
  intro h
  rcases h with ⟨k, hk⟩
  exact ⟨k + 1, congrArg (· + 2) hk⟩

/-!
## 3. Sum of first `n` naturals: recursive definition
Define `sum_up` by recursion.
-/

def sum : Nat → Nat
  | 0     => 0
  | n + 1 => sum n + (n + 1)

#eval sum 6

/-!
## 4. Sum formula: `sum_up n ≥ n`
Prove a simple inequality using `suffices` and induction.
-/

theorem sum_ne_gt (n : Nat) : ¬(n > sum n) := by
  -- Use `suffices` to change the goal to `∀ k, sum k ≥ k`. Use `Nat.not_lt_of_ge` to
  -- prove the extra goal introduced by `suffices`.
  -- Proceed by induction on `k` for the rest of the proof. Use the `apply?` tactic
  -- to let Lean suggest the appropriate theorem to complete the proof.
  suffices h : ∀ k, k ≤ sum k by
    -- if we have that, plug in k = n and flip > to ¬> using not_lt_of_ge
    exact Nat.not_lt_of_ge (h n)
  intro k
  induction k
  case zero => exact Nat.zero_le (sum 0)
  case succ n h=>
    have hupper : n + n + 1 <= sum (n + 1) := Nat.add_le_add_right h (n + 1)
    have hlower : n + 1 ≤ n + n + 1 := Nat.le_add_left (n + 1) n
    exact Nat.le_trans hlower hupper

-- Let's define a simple list type and prove some properties about it.
inductive List α where
  | nil  : List α
  | cons : α → List α → List α

/-!
## 5. Exist head of nonempty list
Prove that any nonempty `List α` has a head element.
-/

theorem List.exists_head : ∀ (l : List α), l ≠ nil → ∃ x xs, cons x xs = l := by
  intro hl _hnn
  cases hl
  case cons x' xs' => exact ⟨x', xs', rfl⟩
  case nil => contradiction

-- A function `length` that computes the length of a list.
def List.length : List α → Nat
  | nil       => 0
  | cons _ xs => 1 + length xs

-- A function `append` that appends two lists.
def List.append : List α → List α → List α
  | nil, ys       => ys
  | cons x xs, ys => cons x (append xs ys)

/-!
## 6. Append length
Prove that the length of the append of two lists is the sum of their lengths.
-/

theorem List.length_append : ∀ (xs ys : List α), length (append xs ys) = length xs + length ys := by
  -- Use `induction` on `xs` and `unfold` the definition of `List.append`.
  -- Use `apply?` to let Lean suggest the appropriate theorem to complete the proof.
  intro hx hy
  induction hx
  case nil =>
    unfold List.append List.length
    simp [Nat.zero_add]
  case cons x' xs' hi =>
    -- simpa [List.append, List.length, Nat.add_assoc]
    unfold List.append List.length
    rw [hi]
    rw [Nat.add_assoc]
    simp [List.length]
    exact length.eq_def hy
