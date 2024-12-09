section -- Redoing chapter three with tactics!

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

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  case mp =>
    intro h
    exact ⟨h ∘ Or.inl , h ∘ Or.inr⟩
  case mpr =>
    intro h
    intro
    | Or.inl hq => exact h.left hq
    | Or.inr hr => exact h.right hr

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  case mp =>
    intro h
    exact ⟨h ∘ Or.inl, h ∘ Or.inr⟩
  case mpr =>
    intro h
    intro
    | Or.inl hp => exact h.left hp
    | Or.inr hq => exact h.right hq

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro
  | Or.inl hnp =>
    intro ⟨hp, _⟩
    exact hnp hp
  | Or.inr hnq =>
    intro ⟨_, hq⟩
    exact hnq hq

example : ¬(p ∧ ¬p) := by
  intro ⟨p, np⟩
  exact np p

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨hp, hnq⟩ h
  exact (hnq ∘ h) hp

example : ¬p → (p → q) := by
  intro hnp hp
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro h hp
  match h with
  | Or.inl hnp => contradiction
  | Or.inr hq  => exact hq

example : p ∨ False ↔ p := by
  apply Iff.intro
  case mp =>
    intro
    | Or.inl hp => exact hp
    | Or.inr f => contradiction
  case mpr =>
    exact Or.inl

example : p ∧ False ↔ False := by
  apply Iff.intro
  case mp => exact And.right
  case mpr =>
    intro hf
    contradiction

example : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  exact (hnq ∘ hpq) hp

-- 3.2
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro hpqor
  match Classical.em q with
  | Or.inl hq  =>
    apply Or.inl
    intro _
    exact hq
  | Or.inr hnq =>
    apply Or.inr
    intro hp
    match hpqor hp with
    | Or.inl hq => contradiction
    | Or.inr hr => exact hr


example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  match Classical.em p with
  | Or.inl hp  =>
    apply Or.inr
    intro hq
    exact h ⟨hp, hq⟩
  | Or.inr hnp => exact Or.inl hnp

example : ¬(p → q) → p ∧ ¬q := by
  intro hnpq
  match Classical.em p with
  | Or.inl hp =>
    match Classical.em q with
    | Or.inl hq =>
      have hpq : p → q := fun _ => hq
      contradiction
    | Or.inr hnq =>
      exact ⟨hp, hnq⟩
  | Or.inr hnp =>
    have hpq : p → q := fun (hp : p) => False.elim (hnp hp)
    contradiction

example : (p → q) → (¬p ∨ q) := by
  intro hpq
  match Classical.em p with
  | Or.inl hp  => exact Or.inr (hpq hp)
  | Or.inr hnp => exact Or.inl hnp

example : (¬q → ¬p) → (p → q) := by
  intro hnqnp hp
  match Classical.em q with
  | Or.inl hq  => exact hq
  | Or.inr hnq =>
    exact False.elim (hnqnp hnq hp)

example : p ∨ ¬p := by
  exact Classical.em p

example : (((p → q) → p) → p) := by
  intro h
  apply byContradiction
  intro hnp
  have hpq : p → q := by
    intro hp
    contradiction
  exact False.elim $ hnp $ h hpq -- Lean also understands the $ :O

-- 3.3

example : ¬(p ↔ ¬p) := by
  intro h
  have hnp : ¬p := by
    intro hp
    have hnp' := h.mp hp
    exact False.elim (hnp' hp)
  have hp := h.mpr hnp
  exact False.elim (hnp hp)

end -- End of chapter three

section -- 4.1

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  case mp =>
    intro faxpxqx
    apply And.intro
    case left =>
      intro x
      exact (faxpxqx x).left
    case right =>
      intro x
      exact (faxpxqx x).right
  case mpr =>
    intro ⟨hpx, hqx⟩
    intro x
    exact ⟨hpx x, hqx x⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro hpxqx hpx x
  exact (hpxqx x) (hpx x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro
  | Or.inl hpx =>
    intro x
    exact Or.inl (hpx x)
  | Or.inr hqx =>
    intro x
    exact Or.inr (hqx x)

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _: α, r) ↔ r) := by
  intro a
  apply Iff.intro
  case mp  =>
    intro har
    exact har a
  case mpr =>
    intro hr _
    exact hr

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  case mp =>
    intro hpxr
    match Classical.em r with
    | Or.inl hr  => exact Or.inr hr
    | Or.inr hnr =>
      have hpx : ∀ x, p x := by
        intro a
        match hpxr a with
        | Or.inl hpx => exact hpx
        | Or.inr hr  => exact False.elim (hnr hr)
      exact Or.inl hpx
  case mpr =>
    intro
    | Or.inl hpx =>
      intro a
      exact Or.inl (hpx a)
    | Or.inr hr =>
      intro a
      exact Or.inr hr

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  case mp  =>
    intro hrpx hr a
    exact hrpx a hr
  case mpr =>
    intro hrpx a hr
    exact hrpx hr a

end -- 4.1

section --barber!

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have who_shaves_barber := h barber
  -- Shameless copy-paste from previous chapter :P
  have hnp : ¬shaves barber barber := by
    intro hp
    have hnp' := who_shaves_barber.mp hp
    exact False.elim (hnp' hp)
  have hp := who_shaves_barber.mpr hnp
  exact False.elim (hnp hp)

end --barber!

section -- 4.4
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := by
  intro ⟨_, hr⟩
  exact hr

example (a : α) : r → (∃ _ : α, r) := by
  intro hr
  exact ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  case mp  =>
    intro ⟨x, ⟨hpx, hr⟩⟩
    exact ⟨⟨x, hpx⟩, hr⟩
  case mpr =>
    intro ⟨⟨x, hpx⟩, hr⟩
    exact ⟨x, ⟨hpx, hr⟩⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  case mp =>
    intro
    | ⟨x, Or.inl hpx⟩ => exact Or.inl ⟨x, hpx⟩
    | ⟨x, Or.inr hqx⟩ => exact Or.inr ⟨x, hqx⟩
  case mpr =>
    intro
    | Or.inl ⟨x, hpx⟩ => exact ⟨x, Or.inl hpx⟩
    | Or.inr ⟨x, hqx⟩ => exact ⟨x, Or.inr hqx⟩


example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  apply Iff.intro
  case mp =>
    intro hfaxpx
    intro ⟨x, hnpx⟩
    have hpx := hfaxpx x
    contradiction
  case mpr =>
    intro hnexnpx
    intro x
    apply Classical.byContradiction
    intro hnpx
    exact hnexnpx ⟨x, hnpx⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro
  case mp  =>
    intro ⟨x, hpx⟩
    intro h
    have hnpx := h x
    contradiction
  case mpr =>
    intro h
    apply Classical.byContradiction
    intro nexpx
    have faxnpx : ∀ x, ¬ p x := by
      intro x hpx
      have expx : ∃ x, p x := ⟨x, hpx⟩
      contradiction
    contradiction

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  case mp =>
    intro nexpx
    intro x hpx
    have expx : ∃ x, p x := ⟨x, hpx⟩
    contradiction
  case mpr =>
    intro faxnpx
    intro ⟨x, hpx⟩
    have hnpx := faxnpx x
    contradiction

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  case mp =>
    intro nfaxpx
    apply Classical.byContradiction
    intro nexnpx
    have faxpx : ∀x, p x := by
      intro x
      apply Classical.byContradiction
      intro hnpx
      have exnpx : ∃ x, ¬ p x := ⟨x, hnpx⟩
      contradiction
    contradiction
  case mpr =>
    intro ⟨x, hnpx⟩
    intro faxpx
    have hpx := faxpx x
    contradiction

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  apply Iff.intro
  case mp  =>
    intro faxpxr
    intro ⟨x, px⟩
    exact faxpxr x px
  case mpr =>
    intro h
    intro x px
    exact h ⟨x, px⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  case mp =>
    intro ⟨x, hpxr⟩
    intro faxpx
    exact hpxr (faxpx x)
  case mpr =>
    intro faxpxr
    match Classical.em (∀x, p x) with
    | Or.inl faxpx  =>
      have hpar : p a → r := fun _ => faxpxr faxpx
      exact ⟨a, hpar⟩
    | Or.inr nfaxpx =>
      have ⟨x, hnpx⟩ : ∃ x, ¬ p x := by
        apply Classical.not_forall.mp
        exact nfaxpx
      have hpxr : p x → r := by
        intro hpx
        contradiction
      exact ⟨x, hpxr⟩


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  case mp =>
    intro ⟨x, hrpx⟩
    intro hr
    exact ⟨x, hrpx hr⟩
  case mpr =>
    intro hrexpx
    match Classical.em r with
    | Or.inl hr  =>
      have ⟨x, hpx⟩ := hrexpx hr
      exact ⟨x, fun _ => hpx⟩
    | Or.inr hnr =>
      have hrpa : r → p a := by
        intro hr
        contradiction
      exact ⟨a, hrpa⟩

end

section -- 5.2

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  exact ⟨Or.inl hp, ⟨Or.inr (Or.inl hp), Or.inr (Or.inr hp)⟩⟩

end
