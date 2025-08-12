/- Q1:
Prove without using any tactics other than the french bracket ‹⋯›
-/
section
-- definition of `<`
#print Nat.lt

example (x : Nat) : x < x + 1 := by
  change x.succ <= x + 1
  exact Nat.le_refl x.succ

example (x : Nat) : x - 1 ≤ x := by
  cases x with
  | zero =>
    exact Nat.le_refl 0
  | succ x' =>
    change x' <= x'.succ
    exact Nat.le_succ x'

example (x y : Nat) : x = y + 1 → x + 1 = y + 2 := by
  intro h
  rewrite [h]
  rfl

example (n : Nat) : 0 < n → n < 2 * n := by
  intro h
  have h1 := Nat.add_le_add h (Nat.le_refl n)
  rw [Nat.add_comm] at h1
  rw [Nat.two_mul]
  exact h1
end

/- Q2:
Prove with tactics
-/
section
example (x : Nat) : x < x + 1 := by
  -- simp
  exact Nat.lt_add_one x
example (x : Nat) : x - 1 ≤ x := by
  -- simp
  exact Nat.sub_le x 1
example (x y : Nat) : x = y + 1 → x + 1 = y + 2 := by
  -- simp
  -- exact fun a => (fun {m k n} => Nat.add_left_inj.mpr) a
  sorry
example (n : Nat) : 0 < n → n < 2 * n := by
  sorry
end

/- Q3:
Write a function which conforms to this type.
-/
def upperBound (x y : Nat) : { z // z ≤ x ∧ z ≤ y } := sorry

/- Q4:
Prove
-/
section
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry

-- These may require classical logic.
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
end

/- Q5:
Formalize these mathematical statements
-/
section
/-- For any natural number n,  There exists m s.t. m > n and m is even -/
def greater_than_even : Prop := sorry
/-- For any two natural numbers n,m, there is a natural number which divides
both of them such that no larger number has this property. -/
def greatest_common_divisor : Prop := sorry
/-- No natural number may be equalt o its successor -/
def no_eq_succ : Prop := sorry
/-- There exists a natural number strictly between 11 and 12 -/
def nat_between : Prop := sorry
/-- There exists a natural number that is divisible by 3, 5, 7 which is less than 200 -/
def div357 : Prop := sorry
end
