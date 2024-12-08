-- Redoing chapter three with tactics!

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  case mp =>
    intro pq
    apply And.intro
    exact pq.right
    exact pq.left
  case mpr =>
    intro qp
    apply And.intro
    exact qp.right
    exact qp.left

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  case mp =>
    intro pq
    apply Or.elim pq
    case left =>
      intro p
      exact Or.inr p
    case right =>
      intro q
      exact Or.inl q
  case mpr =>
    intro qp
    apply Or.elim qp
    case left =>
      intro q
      exact Or.inr q
    case right =>
      intro p
      exact Or.inl p

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  case mp =>
    intro ⟨⟨p, q⟩, r⟩
    exact ⟨p, q, r⟩
  case mpr =>
    intro ⟨p, q, r⟩
    exact ⟨⟨p, q⟩, r⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  case mp =>
    intro
    | Or.inl (Or.inl hp) => exact Or.inl hp
    | Or.inl (Or.inr hq) => exact Or.inr (Or.inl hq)
    | Or.inr hr          => exact Or.inr (Or.inr hr)
  case mpr =>
    intro
    | Or.inl hp          => exact Or.inl (Or.inl hp)
    | Or.inr (Or.inl hq) => exact Or.inl (Or.inr hq)
    | Or.inr (Or.inr hr) => exact Or.inr hr


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  case mp =>
    intro
    | ⟨hp, Or.inl hq⟩ => exact Or.inl ⟨hp, hq⟩
    | ⟨hp, Or.inr hr⟩ => exact Or.inr ⟨hp, hr⟩

  case mpr =>
    intro
    | Or.inl ⟨hp, hq⟩ => exact ⟨hp, Or.inl hq⟩
    | Or.inr ⟨hp, hr⟩ => exact ⟨hp, Or.inr hr⟩


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  case mp =>
    intro
    | Or.inl hp       => exact ⟨Or.inl hp, Or.inl hp⟩
    | Or.inr ⟨hq, hr⟩ => exact ⟨Or.inr hq, Or.inr hr⟩
  case mpr =>
    intro
    | ⟨Or.inl hp, _⟩ => exact Or.inl hp
    | ⟨_, Or.inl hp⟩ => exact Or.inl hp
    | ⟨Or.inr hq, Or.inr hr⟩ => exact Or.inr ⟨hq, hr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  case mp =>
    intro h
    intro ⟨hp, hq⟩
    exact (h hp) hq
  case mpr =>
    intros h hp hq
    exact h ⟨hp, hq⟩

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
