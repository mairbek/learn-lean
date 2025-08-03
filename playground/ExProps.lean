variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun (⟨ hp, hq ⟩ : p ∧ q) => ⟨ hq, hp ⟩ )
    (fun (⟨ hq, hp ⟩ : q ∧ p) => ⟨ hp, hq ⟩)

-- TODO(mairbek): maybe use match here?
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun (h : p ∨ q) =>  Or.elim h
      (fun hp : p =>
        show q ∨ p from Or.intro_right q hp)
      (fun hq : q =>
        show q ∨ p from Or.intro_left p hq)
    )
    (fun (h : q ∨ p) =>  Or.elim h
      (fun hq : q =>
        show p ∨ q from Or.intro_right p hq)
      (fun hp : p =>
        show p ∨ q from Or.intro_left q hp)
    )

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun (⟨ ⟨ hp, hq ⟩, hr ⟩ : (p ∧ q) ∧ r) => ⟨ hp, hq, hr ⟩ )
    (fun (⟨ hp, hq, hr ⟩ : p ∧ q ∧ r) => ⟨ ⟨ hp, hq ⟩, hr ⟩ )

-- other properties
example : (h : p → q) → (¬q → ¬p) :=
  fun (hpq : p->q) (hnq: ¬ q) (hp: p) =>
    hnq (hpq hp)

-- proof v1
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun not_p_and_not_q =>
    match not_p_and_not_q with
    | Or.inl not_p => fun ⟨ hp, hq ⟩ => not_p hp
    | Or.inr not_q => fun ⟨ hp, hq ⟩ => not_q hq

-- proof v2
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h ⟨ hp, hq ⟩  =>
    match h with
    | Or.inl not_p => not_p hp
    | Or.inr not_q => not_q hq

-- proof v2 with tactics
example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  rintro (np | nq) ⟨ hp, hq ⟩
  exact np hp
  exact nq hq

variable (p: Prop)
#check ¬p

example : ¬p → p → False :=
  fun not_p p => not_p p
-- ¬p can be rewritten as (p → False)
example : (p → False) → p → False :=
  fun not_p p => not_p p

-- so we can just make it id function
example : ¬p → p → False := id

end
