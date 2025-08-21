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
theorem zero_add {n} : zero + n = n := by
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
theorem add_comm {n m} : n + m = m + n := by
  induction m with
  | zero => exact Eq.symm zero_add
  | succ m' hm =>
    rw [<- add_comm_helper]
    exact congrArg succ hm

-- Associativity can be proven in a similar way.
theorem add_assoc : (m + n) + k = m + (n + k) := by
  induction m with
  | zero =>
    rw [zero_add]
    rw [zero_add]
  | succ m' hm =>
    rw [← @add_comm_helper]
    rw [← @add_comm_helper]
    rw [hm]
    rw [<- add_comm_helper]

def one := succ zero

theorem mul_zero {n}: zero * n = zero := by
  induction n with
  | zero => rfl
  | succ n' hn => exact hn

theorem one_mul : one * m = m := by
  rw [one]
  induction m with
  | zero =>
    rw [mul]
  | succ m' hm =>
    rw [mul]
    rw [hm]
    rfl

theorem succ_plus_one : succ m = m + one := by
  rfl

-- To prove associativity of multiplication, you might have to come up with
-- some more lemmas about multiplication first. Some are similar to the above laws of
-- addition, some use both addition and multiplication ("distributivity" is the keyword).

theorem mul_distr : (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
    simp [mul_zero, zero_add]
  | succ a' ha =>
    simp [mul]
    simp [ha]
    simp [add_assoc]
    apply congrArg (fun t => a * a' + t)
    simp [← add_assoc]
    simp [add_comm]

theorem mul_succ : succ m * n = m * n + n := by
  rw [succ_plus_one]
  rw [mul_distr]
  rw [one_mul]

theorem mul_comm {n m} : n * m = m * n := by
  induction m with
  | zero =>
    simp [mul_zero]
  | succ _ hm =>
    rw [mul_succ]
    rw [mul]
    rw [hm]

theorem mul_assoc : (m * n) * k = m * (n * k) := by
  induction m with
  | zero =>
    simp [mul_zero]
  | succ _ hm =>
    simp [mul_succ]
    simp [mul_distr]
    simp [hm]

-- Remember the structures for semigroups and monoids which we defined last week?
structure Semigroup (α : Type) where
  mul   : α → α → α
  assoc : mul (mul a b) c = mul a (mul b c)

structure Monoid (α : Type) extends Semigroup α where
  e     : α
  e_mul : mul e a = a
  mul_e : mul a e = a

-- You should now be able to instantiate two of them, including proofs!
def Nat_add_Semigroup : Semigroup Nat := by
  constructor
  · exact add_assoc

def Nat_add_Monoid : Monoid Nat := by
  refine
  { toSemigroup := Nat_add_Semigroup
    e           := zero
    e_mul       := by
      intro a
      exact @zero_add a
    mul_e       := fun {a} => rfl }

def Nat_mul_Semigroup : Semigroup Nat := by
  constructor
  · exact mul_assoc

def Nat_mul_Monoid : Monoid Nat := by
  refine
  { toSemigroup := Nat_mul_Semigroup
    e           := one
    e_mul       := by
      intro a
      exact @one_mul a
    mul_e       := by
      intro a
      have h := @one_mul a
      rw [mul_comm] at h
      exact h
  }

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
  intro t
  induction t with
  | leaf => simp
  | node l v r lh rh =>
    simp [mirror]
    exact ⟨lh, rh⟩

-- Finally, let's define a `reverse` function for lists and prove an interesting
-- property about it: that reversing a list twice gives you the original list back.
@[simp] def rev : List α → List α
  | []       => []
  | x :: xs  => rev xs ++ [x]

-- You may need to prove a helper lemma first, similar to the one for addition.
theorem rev_rev_helper (xs : List α) : ∀ ys, rev (rev xs ++ ys) = rev ys ++ xs := by
  induction xs with
  | nil =>
    simp [rev]
  | cons _ _ _ =>
    simp_all [rev]


-- Now you can prove the main theorem!
theorem rev_rev : ∀ (xs : List α), rev (rev xs) = xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x' xs' ih =>
    simp [rev, rev_rev_helper]

end A09
