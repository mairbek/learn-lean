variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun (⟨ hp, hq ⟩ : p ∧ q) => ⟨ hq, hp ⟩ )
    (fun (⟨ hq, hp ⟩ : q ∧ p) => ⟨ hp, hq ⟩)

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
