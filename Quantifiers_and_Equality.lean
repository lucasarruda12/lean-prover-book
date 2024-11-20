-- Prove these equivalences:

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
  (
    fun h : ∀ x, p x ∧ q x =>
      And.intro
      (fun x : α => (h x).left)
      (fun x : α => (h x).right)
  )
  (
    fun h : (∀ x, p x) ∧ (∀ x, q x) =>
      fun x : α =>
        And.intro (h.left x) (h.right x)
  )

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h1 : ∀ x, p x → q x =>
    fun h2 : ∀ x, p x =>
      fun x : α => (h1 x) (h2 x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) =>
    fun x : α =>
      Or.elim h
      (fun hpx : ∀ x, p x => Or.inl (hpx x))
      (fun hqx : ∀ x, q x => Or.inr (hqx x))
