-- and is (a b Prop): Prop
variable (p q: Prop)

theorem t1: p → q → p :=
  fun hp : p => fun _ : q => hp

theorem t1_short (hp : p) (hq : q) : p := hp

theorem t1_full {p q : Prop} (hp : p) (hq : q) : p := hp


#check And

section
variable (p q : Prop)

theorem and_rfl : p ∧ q -> q ∧ p :=
  fun ⟨ hp, hq⟩ => ⟨ hq, hp ⟩
end

section
variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq: q) : p ∨ q := Or.intro_right p hq

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)

-- shorter examples
example (hp : p) : p ∨ q := Or.inl hp
example (hq: q) : p ∨ q := Or.inr hq

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.inr hp)
    (fun hq : q =>
      show q ∨ p from Or.inl hq)

end

section
variable (p q : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)

end
