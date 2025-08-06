/- Q1:
Manually determine the types of the following expressions, and then check with
the machine for correctness.
-/
namespace Mystery
#check Nat
def x01 := Nat → Nat
-- Type
#check x01
def x02 := λ (x : Nat) => x
-- Nat -> Nat
#check x02
def x03 := λ { a : Type 2 } => [a, a]
-- Type 2 -> List Type 2
#check x03
def x04 := Type 1 → List (Type 1)
-- Type 2
#check x04

def x05 := Nat → Prop
-- Type
#check x05

def x06 := Nat → (1 = 1)
-- Prop
#check x06

def x07 := ∀ (n : Nat), n = n
-- Prop
#check x07
def x08 := let z := 2; z = 2
-- Prop
#check x08
def x09.{u} := { α : Type  u} → (a : α) → List α
-- Type u+1
#check x09
-- Remember → is right associative.
def x10.{u} := { m : Type u → Type u} → (α : Type u) → (m α)
-- Type u+1
#check x10
end Mystery

/- Q2:
Without using classical reasoning (Law of Excluded Middle and Choice), prove
(from Theorem Proving in lean 4)
-/
section
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  have mp : p ∧ q → q ∧ p := λ ⟨ hp, hq ⟩ => ⟨ hq, hp ⟩
  have mpr : q ∧ p→ p ∧ q := λ ⟨ hq, hp ⟩ => ⟨ hp, hq ⟩
  exact Iff.intro mp mpr

example : p ∨ q ↔ q ∨ p := by
  exact ⟨ Or.symm, Or.symm ⟩

  -- Longer version
  -- have mp : p ∨ q → q ∨ p := λ hpq =>
  --   match hpq with
  --   | Or.inl hp => Or.inr hp
  --   | Or.inr hq => Or.inl hq
  -- have mpr : q ∨ p → p ∨ q := λ hqp =>
  --   match hqp with
  --   | Or.inl hq => Or.inr hq
  --   | Or.inr hp => Or.inl hp
  -- exact Iff.intro mp mpr


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun (⟨ ⟨ hp, hq ⟩, hr ⟩ : (p ∧ q) ∧ r) => ⟨ hp, hq, hr ⟩ )
    (fun (⟨ hp, hq, hr ⟩ : p ∧ q ∧ r) => ⟨ ⟨ hp, hq ⟩, hr ⟩ )

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  have mp : (p ∨ q) ∨ r → p ∨ (q ∨ r) := by
    intro hpqr
    obtain ((hp | hq) | hr) := hpqr
    · exact Or.inl hp
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr hr)
  have mpr : p ∨ (q ∨ r) → (p ∨ q) ∨ r  := by
    intro hpqr
    obtain (hp | (hq | hr)) := hpqr
    · exact Or.inl (Or.inl hp)
    · exact Or.inl (Or.inr hq)
    · exact Or.inr hr
  exact ⟨ mp, mpr ⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  have mp : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
    intro h
    obtain ⟨hp, (hq | hr) ⟩  := h
    · exact Or.inl ⟨ hp, hq ⟩
    · exact Or.inr ⟨ hp, hr ⟩
  have mpr : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) := by
    intro h
    obtain (⟨hp, hq⟩ | ⟨hp, hr⟩) := h
    · exact ⟨ hp, Or.inl hq ⟩
    · exact ⟨ hp, Or.inr hr ⟩
  exact ⟨ mp, mpr ⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  have mp : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) := by
    intro h
    obtain (hp | ⟨ hq, hr ⟩) := h
    · exact ⟨ Or.inl hp, Or.inl hp ⟩
    · exact ⟨ Or.inr hq, Or.inr hr ⟩
  have mpr : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r) := by
    intro h
    obtain ⟨ (hp | hq), (hp | hr) ⟩ := h
    · exact Or.inl hp
    · exact Or.inl hp
    · exact Or.inl hp
    · exact Or.inr ⟨hq, hr⟩
  exact ⟨ mp, mpr ⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  have mp :(p → (q → r)) → (p ∧ q → r) := by
    intro h
    exact λ ⟨hp, hq⟩  => h hp hq
  have mpr : (p ∧ q → r) → (p → (q → r)) := by
    intro h
    exact λ hp hq => h ⟨hp, hq⟩
  exact ⟨mp, mpr⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  have mp : ((p ∨ q) → r) → (p → r) ∧ (q → r) := by
    intro h
    exact ⟨λ hp => h (Or.inl hp), λ hq => h (Or.inr hq)⟩
  have mpr : (p → r) ∧ (q → r) → ((p ∨ q) → r) := by
    intro h
    have ⟨hpr, hqr⟩  := h
    exact λ hpqr => by
      obtain (hp | hq) := hpqr
      · exact hpr hp
      · exact hqr hq
  exact ⟨mp, mpr⟩
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
