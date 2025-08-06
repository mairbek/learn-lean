/- Q1:
Manually determine the types of the following expressions, and then check with
the machine for correctness.
-/
namespace Mystery
#check Nat
def x01 := Nat → Nat
def x02 := λ (x : Nat) => x
def x03 := λ { a : Type 2 } => [a, a]
def x04 := Type 1 → List (Type 1)
def x05 := Nat → Prop
def x06 := Nat → (1 = 1)
def x07 := ∀ (n : Nat), n = n
def x08 := let z := 2; z = 2
def x09.{u} := { α : Type  u} → (a : α) → List α
-- Remember → is right associative.
def x10.{u} := { m : Type u → Type u} → (α : Type u) → (m α)
end Mystery

/- Q2:
Without using classical reasoning (Law of Excluded Middle and Choice), prove
(from Theorem Proving in lean 4)
-/
section
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := sorry
example : p ∨ q ↔ q ∨ p := sorry

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
end

/- Q3:
With classical reasoning, prove
(from Theorem Proving in lean 4)
-/
section
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
/-- How would you prove this informally? -/
example : (p ∧ ¬ p) → 1 = 0 := sorry
end

/- Q4:
In a certain town there is a (male) barber that shaves all and only the men who
do not shave themselves. Prove that this is a contradiction
(from Theorem Proving in Lean 4)
-/
section
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry
end
