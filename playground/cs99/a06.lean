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

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  have mp: ¬(p ∨ q) → ¬p ∧ ¬q := by
    intro h
    have hnp := λ hp => h (Or.inl hp)
    have hnq := λ hq => h (Or.inr hq)
    exact ⟨hnp, hnq⟩
  have mpr: ¬p ∧ ¬q → ¬(p ∨ q)  := by
    intro h
    obtain ⟨hnp, hnq⟩ := h
    exact λ hpq => by
      obtain (hp | hq) := hpq
      · exact hnp hp
      · exact hnq hq
  exact ⟨mp, mpr⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  rintro (hnp | hnq) ⟨hp, hq⟩
  · exact hnp hp
  · exact hnq hq

example : ¬(p ∧ ¬p) := by
  intro ⟨ hp, hnp⟩
  exact hnp hp

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨hp, hnq⟩ h
  exact hnq (h hp)

example : ¬p → (p → q) := by
  intro np hp
  exact np.elim hp

example : (¬p ∨ q) → (p → q) := by
  rintro (hnp | hq) hp
  · exact hnp.elim hp
  · exact hq

example : p ∨ False ↔ p := by
  have mp: p ∨ False → p := by
    rintro (hp | False)
    · exact hp
    · exact False.elim
  have mpr: p → p ∨ False := by
    intro hp
    exact Or.inl hp
  exact ⟨mp, mpr⟩

example : p ∧ False ↔ False := by
  constructor
  · intro ⟨_, False⟩
    exact False
  · exact False.elim

example : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  exact hnq.elim (hpq hp)
end

/- Q3:
With classical reasoning, prove
(from Theorem Proving in lean 4)
-/
section
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  obtain (hp | hnp) := Classical.em p
  ·
    obtain (hq | hr) := h hp
    · exact Or.inl λ _ => hq
    · exact Or.inr λ _ => hr
  ·
    have hpq : p → q := λ hp => hnp.elim hp
    exact Or.inl hpq

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  obtain (hp | hnp) := Classical.em p
  ·
    have hnq : ¬q := fun hq => h ⟨ hp, hq ⟩
    exact Or.inr hnq
  ·
    exact Or.inl hnp

example : ¬(p → q) → p ∧ ¬q := by
  intro h
  obtain (hp | hnp) := Classical.em p
  ·
    have hnq : ¬ q := fun hq => h (fun _ => hq)
    exact ⟨ hp, hnq ⟩
  ·
    have imp : p → q := fun hp => hnp.elim hp
    exact h.elim imp

example: (p → q) → (¬p ∨ q) := by
  intro h
  obtain (hp | hnp) := Classical.em p
  · exact Or.inr (h hp)
  · exact Or.inl hnp

example : (¬q → ¬p) → (p → q) := by
  intro hnqp
  obtain (hq | hnq) := Classical.em q
  · exact fun hp => hq
  · exact fun hp => (hnqp hnq).elim hp

example : p ∨ ¬p := Classical.em p

example : (((p → q) → p) → p) := by
  intro h
  obtain (hp | hnp) := Classical.em p
  ·
    exact hp
  .
    have hpq : p → q := fun hp => absurd hp hnp
    exact h hpq
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
