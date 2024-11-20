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
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
  (fun h : p ∧ (q ∨ r) =>
    Or.elim h.right
      (fun hq : q => Or.inl (And.intro h.left hq))
      (fun hr : r => Or.inr (And.intro h.left hr))
  )
  (fun h : (p ∧ q) ∨ (p ∧ r) =>
    Or.elim h
      (fun hpq : p ∧ q =>
        And.intro hpq.left (Or.inl hpq.right)
      )
      (fun hpr : p ∧ r =>
        And.intro hpr.left (Or.inr hpr.right)
      )
  )
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
  (fun h : p ∨ (q ∧ r) =>
    Or.elim h
    (fun hp : p => And.intro (Or.inl hp) (Or.inl hp))
    (fun hqr : q ∧ r =>
      And.intro
      (Or.inr hqr.left)
      (Or.inr hqr.right))
  )
  (fun h : (p ∨ q) ∧ (p ∨ r) =>
    Or.elim h.left
    (fun hp : p => Or.inl hp)
    (fun hq : q =>
      Or.elim h.right
      (fun hp : p => Or.inl hp)
      (fun hr : r => Or.inr (And.intro hq hr))
    )
  )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
  (fun h : p → (q → r) =>
    fun hpq : p ∧ q => h hpq.left hpq.right
  )
  (fun h : (p ∧ q) → r =>
    fun hp : p => fun hq : q => h (And.intro hp hq)
  )
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
  (fun h : ((p ∨ q) → r) =>
    And.intro
    (fun hp : p => h (Or.inl hp))
    (fun hq : q => h (Or.inr hq))
  )
  (fun h : (p → r) ∧ (q → r) =>
    fun hpq : p ∨ q =>
    Or.elim hpq
    (fun hp : p => h.left hp)
    (fun hq : q => h.right hq)
  )
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
  (fun h : ¬(p ∨ q) =>
    And.intro
    (fun hp : p => h (Or.inl hp))
    (fun hq : q => h (Or.inr hq))
  )
  (fun h : ¬p ∧ ¬q =>
    fun hpq : p ∨ q =>
      Or.elim hpq
      (fun hp : p => h.left hp)
      (fun hq : q => h.right hq)
  )

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h : ¬p ∨ ¬q =>
  Or.elim h
  (fun hnp : ¬p => fun hpq : p ∧ q => hnp hpq.left)
  (fun hnq : ¬q => fun hpq : p ∧ q => hnq hpq.right)

example : ¬(p ∧ ¬p) :=
  fun h : p ∧ ¬p => h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
  fun h : p ∧ ¬q =>
    fun hpq : p → q => h.right (hpq h.left)

example : ¬p → (p → q) :=
  fun hnp : ¬p =>
    fun hp : p => False.elim (hnp hp)

example : (¬p ∨ q) → (p → q) :=
  fun hnpq : ¬p ∨ q =>
    fun hp : p =>
      Or.elim hnpq
      (fun hnp : ¬p => False.elim (hnp hp))
      id

example : p ∨ False ↔ p :=
  Iff.intro
  (fun hpf : p ∨ False =>
    Or.elim hpf id False.elim
  )
  (Or.inl)

example : p ∧ False ↔ False :=
  Iff.intro
  (fun hpf : p ∧ False => False.elim hpf.right)
  (False.elim)

example : (p → q) → (¬q → ¬p) :=
  fun hpq : p → q =>
    fun hnq : ¬q => fun hp : p => hnq (hpq hp)
