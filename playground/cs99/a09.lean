-- Exercise Borrowed from: https://github.com/IPDSnelting/tba-2022
-- Original author: Sebastian Ullrich

/- TACTICS  -/

namespace A09

-- definitions from last week
-- NOTE: The `TBA` namespace makes sure we don't use the standard library `Nat`.
inductive Nat : Type where
  | zero : Nat
  | succ (n : Nat) : Nat

open Nat

def add (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)

-- With this command we add a notation for `add`. From now on we will be able to write `m + n` for
-- `add m n`. The 65 denotes how strongly the operator should bind to what's adjacent to it.
-- The `priority` means that Lean will prefer it over the built-in `+`.
infix:65 (priority := high) " + " => add

def mul (m n : Nat) : Nat :=
  match n with
  | zero   => zero
  | succ n => (mul m n) + m

-- We also want a notation for `mul`, with a higher binding strength than addition so that
-- `a + b * c` means `a + (b * c`)`.
infix:70 (priority := high) " * " => mul

inductive LE : Nat → Nat → Prop where
  | refl (n : Nat) : LE n n
  | succ : LE m n → LE m (succ n)

-- lower binding strength than either addition or multiplication
infix:50 (priority := high) " ≤ " => LE

-- Let's start by reproving some theorems from last week, but this time with tactics!
-- useful tactics:
-- * `induction ... with ...`
-- * `rw [f]` to unfold applications of a function `f`
-- * `rw [h]` to rewrite every `a` to `b` if `h : a = b`
-- * `apply/exact`
-- * `simp/simp_all`... are powerful and basically always useful, though make sure that you could also
--   do the proof without them
theorem zero_add : zero + n = n := by
  induction n with
  | zero => rfl
  | succ _n hn =>
    exact congrArg succ hn


theorem le_add : m ≤ m + n := by
  -- have h := LE.refl m
  induction n with
  | zero => exact LE.refl m
  | succ n' hn =>
    refine LE.succ ?_
    exact hn

-- Alright, let's start automating more!
attribute [simp] add mul
-- These definitions will now automatically be unfolded when you use `simp/simp_all`

theorem add_comm_helper : (m + n).succ = m.succ + n := by
  induction n with
  | zero => rfl
  | succ n' hn => exact congrArg succ hn

-- This one is a bit more tricky, you might need to prove a helper lemma!
theorem add_comm : n + m = m + n := by
  induction m with
  | zero => exact Eq.symm zero_add
  | succ m' hm =>
    rw [<- add_comm_helper]
    exact congrArg succ hm

-- Associativity can be proven in a similar way.
theorem add_assoc : (m + n) + k = m + (n + k) := by
  sorry

def one := succ zero

theorem mul_one : m * one = m := by
  sorry

-- To prove associativity of multiplication, you might have to come up with
-- some more lemmas about multiplication first. Some are similar to the above laws of
-- addition, some use both addition and multiplication ("distributivity" is the keyword).

theorem mul_assoc : (m * n) * k = m * (n * k) := by
  sorry

-- Remember the structures for semigroups and monoids which we defined last week?
structure Semigroup (α : Type) where
  mul   : α → α → α
  assoc : mul (mul a b) c = mul a (mul b c)

structure Monoid (α : Type) extends Semigroup α where
  e     : α
  e_mul : mul e a = a
  mul_e : mul a e = a

-- You should now be able to instantiate two of them, including proofs!
def Nat_add_Monoid : Monoid Nat := sorry

def Nat_mul_Monoid : Monoid Nat := sorry

-- Let's now prove a theorem about trees. We will define a tree as either a leaf or a node with
-- a left and right subtree. The value of the node is stored in the middle.
inductive Tree (α) where
  | leaf
  | node (l : Tree α) (v : α) (r : Tree α)

-- We will define a function `mirror` that takes a tree and returns its mirror image.
-- The mirror image of a tree is obtained by swapping the left and right subtrees of each node.
@[simp] def Tree.mirror : Tree α → Tree α
  | leaf           => leaf
  | node l v r     => node (mirror r) v (mirror l)

-- The `@[simp]` attribute tells Lean to automatically unfold the definition of `mirror` when
-- using `simp` or `simp_all`. This is similar to what we did for addition and multiplication.
theorem Tree.mirror_involutive : ∀ (t : Tree α), t.mirror.mirror = t := by
  sorry

-- Finally, let's define a `reverse` function for lists and prove an interesting
-- property about it: that reversing a list twice gives you the original list back.
@[simp] def rev : List α → List α
  | []       => []
  | x :: xs  => rev xs ++ [x]

-- You may need to prove a helper lemma first, similar to the one for addition.
theorem rev_rev_helper : ∀ ys, rev (rev xs ++ ys) = rev ys ++ xs := by
  -- Remember to use `apply?` to let Lean suggest the appropriate theorem to complete proofs.
  -- `simp` knows a lot about `++`. Use `simp?` tactic to see what it knows.
  sorry

-- Now you can prove the main theorem!
theorem rev_rev : ∀ (xs : List α), rev (rev xs) = xs := by
  sorry

end A09
