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

-- proof 1 with tactics
example : (¬p ∨ q) → (p → q) := by
  rintro (hnp | hq) hp
  exact absurd hp hnp
  exact hq

-- proof2: fp
example : (¬p ∨ q) → (p → q) :=
  fun h hp =>
  match h with
  | Or.inl hnp => absurd hp hnp
  | Or.inr hq => hq

-- proof 1 with fp
example : ¬(p ∧ ¬p) :=
  fun ⟨ hp, hnp ⟩ => hnp hp

-- proof 2 (explicit negation as fun → False)
example : (p ∧ ¬p) → False :=
  fun ⟨ hp, hnp ⟩ => hnp hp

-- proof 3 with tactics
example : ¬(p ∧ ¬p) := by
  rintro ⟨ hp, hnp ⟩
  exact hnp hp

-- proof 1: fp
example : ¬p → (p → q) :=
  fun hnp hp => absurd hp hnp

-- proof2: tactics
example : ¬p → (p → q) := by
  rintro hnp hp
  exact absurd hp hnp

example : (p → q) → (¬q → ¬p) :=
  fun h hnq hp =>
    hnq (h hp)

example : p ∨ False -> p := by
  rintro (hp | f)
  exact hp
  exact False.elim f

example : p ∧ False → False := by
  rintro ⟨ _, f ⟩
  exact f


variable (p: Prop)
#check ¬p

example : ¬p → p → False :=
  fun hnp hp => hnp hp
-- ¬p can be rewritten as (p → False)
example : (p → False) → p → False :=
  fun hnp hp => hnp hp

-- so we can just make it id function
example : ¬p → p → False := id

-- mairbek's attempt
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

example : ¬(p → q) → p ∧ ¬q := by
  intro h
  obtain (hp | hnp) := Classical.em p
  ·
    have hnq : ¬ q := fun hq => h (fun _ => hq)
    exact ⟨ hp, hnq ⟩
  ·
    have imp : p → q := fun hp => hnp.elim hp
    exact h.elim imp

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  obtain (hp | hnp) := Classical.em p
  ·
    have hnq : ¬q := fun hq => h ⟨ hp, hq ⟩
    exact Or.inr hnq
  ·
    exact Or.inl hnp

example : (((p → q) → p) → p) := by
  intro h
  obtain (hpq | hnpq) := Classical.em (p → q)
  ·
    exact h hpq
  ·
    exact Classical.byContradiction
      (fun hnp => by
        have hpq: p → q := fun hp => absurd hp hnp
        exact hnpq hpq
      )
