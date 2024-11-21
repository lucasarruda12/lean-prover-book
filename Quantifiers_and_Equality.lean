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

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun a : α =>
    Iff.intro
    (fun h : (∀ _ : α, r) => h a)
    (fun h : r => fun _ : α => h)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
  (fun h : (∀ x, p x ∨ r) =>
    Or.elim (Classical.em r)
    (Or.inr)
    (fun hnr : ¬r =>
      have hxpx : ∀x, p x :=
        fun x : α =>
          Or.elim (h x)
          (id)
          (fun hr : r => False.elim (hnr hr))
      Or.inl hxpx
    )
  )
  (fun h : (∀ x, p x) ∨ r =>
    fun x : α =>
      Or.elim h
      (fun h : (∀ x, p x) => Or.inl (h x))
      (Or.inr)
  )

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
  (fun h : ∀ x, r → p x =>
    fun hr : r => fun x : α => h x hr
  )
  (fun h : (r → ∀ x, p x) =>
    fun x : α => fun hr : r => h hr x
  )
