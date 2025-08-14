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
  have h' := Nat.add_le_add h (Nat.le_refl n)
  rw [Nat.add_comm] at h'
  rw [Nat.two_mul]
  exact h'
end

/- Q2:
Prove with tactics
-/
section
example (x : Nat) : x < x + 1 := by
  exact Nat.lt_add_one x

example (x : Nat) : x - 1 ≤ x := by
  exact Nat.sub_le x 1

example (x y : Nat) : x = y + 1 → x + 1 = y + 2 := by
  intro h
  rw [h]

example (n : Nat) : 0 < n → n < 2 * n := by
  intro h
  have h' := Nat.add_lt_add_left h n   -- n + 0 < n + n
  simpa [Nat.two_mul, Nat.add_zero] using h'
end

/- Q3:
Write a function which conforms to this type.
-/
def upperBound (x y : Nat) : { z // z ≤ x ∧ z ≤ y } :=
  if h: y <= x then
    ⟨y, ⟨h, Nat.le_refl y⟩⟩
  else
    have hx : x ≤ y := (Nat.le_total x y).resolve_right h
    ⟨x, ⟨Nat.le_refl x, hx⟩⟩

/- Q4:
Prove
-/
section
variable (α : Type) (p q : α → Prop)
-- example from the book
example : (∀ x, p x ∧ q x) → ∀ x, p x :=
  fun h : ∀ x, p x ∧ q x =>
  fun x => show p x from (h x).left


example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  · intro h
    exact ⟨(fun x => (h x).left), (fun x => (h x).right)⟩
  · intro ⟨ hp, hq ⟩
    exact fun x => ⟨hp x, hq x⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro hpqx hpx x
  have hpq := hpqx x
  have hp := hpx x
  exact hpq hp

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h x
  obtain (hpx | hqx) := h
  · exact Or.inl (hpx x)
  · exact Or.inr (hqx x)

-- These may require classical logic.
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) := by
  intro x
  have mp : (∀x:α, r) → r := fun hr => hr x
  have mpr : r → (∀ x : α, r) := fun hr _ => hr
  exact ⟨mp, mpr⟩

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  ·
    intro h
    obtain (hr | hnr) := Classical.em r
    · exact Or.inr hr
    ·
      exact Or.inl fun x => by
        obtain (hx | hr) := h x
        · exact hx
        · exact hnr.elim hr
  ·
    intro h x
    obtain (h1 | hr) := h
    · exact Or.inl (h1 x)
    · exact Or.inr hr

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor
  ·
    intro h hr x
    exact h x hr
  ·
    intro h x hr
    exact (h hr) x
end

/- Q5:
Formalize these mathematical statements
-/
section
/-- For any natural number n,  There exists m s.t. m > n and m is even -/
def greater_than_even(n : Nat) := ∃m: Nat, m > n ∧ 2∣m

/-- For any two natural numbers n,m, there is a natural number which divides
both of them such that no larger number has this property. -/
def greatest_common_divisor(n m: Nat) : Prop :=
  ∃ d, d ∣ n ∧ d ∣ m ∧ ∀ e, e ∣ n → e ∣ m → e ≤ d

/-- No natural number may be equal to its successor -/
def no_eq_succ : Prop := ¬∃n : Nat, n = n.succ
/-- There exists a natural number strictly between 11 and 12 -/
def nat_between : Prop := ∃n, n > 11 ∧ n < 12
/-- There exists a natural number that is divisible by 3, 5, 7 which is less than 200 -/
def div357(n: Nat) : Prop := 3∣n ∧ 5∣n ∧ 7∣n ∧ n < 200

example: ∃n, 3∣n ∧ 5∣n ∧ 7∣n ∧ n < 200 := by
  have h: 3∣105 ∧ 5∣105 ∧ 7∣105 ∧ 105 < 200 := by simp
  exact Exists.intro 105 h

end
