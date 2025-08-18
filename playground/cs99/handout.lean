--- snippet Exists.intro
example : ∃ x : Nat, x * 2 = 10 :=
  Exists.intro 5 rfl -- Can also be ⟨5, rfl⟩
--- snippet Exists.elim
example (p q : Nat → Prop) (h : ∃ x, p x ∧ q x) : ∃ x, q x :=
  h.elim λ x ⟨_hp, hq⟩ => ⟨x, hq⟩
--- end

--- snippet Constructor
example (n : Nat) : 0 ≤ n ∧ 0 ≤ 2 * n := by
  constructor
  apply Nat.zero_le
  apply Nat.zero_le
--- snippet Constructor'
example (n : Nat) : 0 ≤ n ∧ 0 ≤ 2 * n :=
  ⟨by apply Nat.zero_le, by apply Nat.zero_le⟩
--- snippet Cases
example (p : Prop) : ¬¬ p → p := by
  intro
  cases Classical.em p
  · assumption
  · contradiction
--- snippet Hygiene
example (p : Prop) : ¬¬ p → p := by
  intro; cases Classical.em p
  case inl h =>
    exact h
  case inr =>
    contradiction
--- snippet Induction
example (n : Nat) : n ≤ n + 1 := by
  induction n
  case zero =>
    apply Nat.zero_le
  case succ =>
    apply Nat.succ_le_succ
    assumption
--- snippet Induction'
example (n m : Nat) : n ≤ n + m := by
  induction n
  case zero =>
    apply Nat.zero_le
  case succ n h =>
    have h3 : n + (1 + m) = n + (m + 1) :=
      Nat.add_comm 1 m ▸ rfl
    have h1 : (n + m) + 1 = (n + 1) + m :=
      Nat.add_assoc n m 1 ▸ h3 ▸ (Eq.symm $ Nat.add_assoc n 1 m)
    apply Eq.subst (motive := λ z => n + 1 ≤ z) h1
    apply Nat.succ_le_succ
    exact h
--- snippet Decide
example (x : Nat) : 4 * x ≤ 10 * x := by
  apply Nat.mul_le_mul_right
  decide
--- snippet Neq
example (x : Nat) : x > 0 → x ≠ 0 := by
  intro xg xz
  suffices h : 0 > 0 from by contradiction
  exact xz ▸ xg
--- snippet Induction on negation
example (x : Nat) : x ≠ x + 1 := by
  induction x
  case zero => decide
  case succ =>
    intro hz
    have := Nat.succ_inj'.mp hz
    contradiction
--- snippet Custom motive
example (x : Nat) : x ≤ x + x :=
  Nat.recOn
    (motive := λ z => z ≤ x + z)
    x -- major
    (Nat.zero_le _ : 0 ≤ x + 0)
    λ z h => Nat.succ_le_succ ‹z ≤ x + z›
--- snippet Induction motive
example (x : Nat) : x ≤ x + x := by
  suffices h : ∀ y, y ≤ x + y by exact h x
  intro y; induction y
  case zero => apply Nat.zero_le
  case succ y h =>
    apply Eq.subst (Nat.add_assoc x y 1)
    exact Nat.succ_le_succ h
--- snippet Strong Induction
example (x : Nat) : x ≤ x + x := by
  induction x using Nat.strongRecOn
  sorry
--- end

--- snippet Unfold
def invert (x : Nat) : Nat :=
  if x = 0 then 1 else 0
example : invert 1 = 0 := by
  unfold invert
  rfl
--- snippet Recursive Increment
def recinc (x : Nat) : Nat :=
  if x = 0 then
    1
  else
    1 + recinc (x - 1)
--- snippet Proof of Recursive Increment
example (x : Nat) : recinc x = x + 1 := by
  unfold recinc
  induction x
  rfl
  rename_i n hi
  have : n + 1 ≠ 0 := by
    intro
    contradiction
  have hn : (if n + 1 = 0 then 1 else 1 + recinc (n + 1 - 1)) = _
    := if_neg ‹n + 1 ≠ 0›
  apply Eq.trans hn
  unfold recinc
  simp [hn]
  have hz := congrArg (1 + · = n + 1 + 1) hi
  apply hz.mpr
  rewrite [Nat.add_comm 1 (n + 1)]
  rfl
--- end

example (x y : Nat) (f : Nat → Nat) : f (x + y + 1) = f (y + x + 1) := by
  congr 2
  apply Nat.add_comm
