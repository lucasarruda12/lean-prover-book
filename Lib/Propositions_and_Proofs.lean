variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
  (fun h : p ∧ q => And.intro h.right h.left)
  (fun h: q ∧ p => And.intro h.right h.left)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
  (fun h : p ∨ q =>
    Or.elim h
      (fun h : p => Or.inr h)
      (fun h : q => Or.inl h)
  )
  (fun h : q ∨ p =>
    Or.elim h
      (fun h : q => Or.inr h)
      (fun h : p => Or.inl h)
  )

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
  (
    fun h : (p ∧ q) ∧ r =>
      And.intro
        (h.left.left)
        (And.intro h.left.right h.right)
  )
  (
    fun h : p ∧ (q ∧ r) =>
      And.intro
        (And.intro h.left h.right.left)
        (h.right.right)
  )
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
  (
    fun h : (p ∨ q) ∨ r =>
      Or.elim h
        (
          fun hpq : p ∨ q =>
          Or.elim hpq
            (fun hp : p => Or.inl hp)
            (fun hq : q => Or.inr (Or.inl hq))
        )
        (fun hr : r => Or.inr (Or.inr hr))
  )
  (
    fun h : p ∨ (q ∨ r) =>
      Or.elim h
        (fun hp : p => Or.inl (Or.inl hp))
        (
          fun hqr : q ∨ r =>
          Or.elim hqr
            (fun hq : q => Or.inl (Or.inr hq))
            (fun hr : r => Or.inr hr)
        )
  )

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
