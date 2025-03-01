section
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

end

section

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : α → ((∀ _ : α, r) ↔ r) :=
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

end


section

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have h12 := h barber
  have h1 : ¬shaves barber barber :=
    fun h2 : shaves barber barber => h12.mp h2 h2
  have h2 := h12.mpr h1
  False.elim (h1 h2)

-- This should have been a two-line proof,
-- but i don't know how to import from the
-- previous exercise file and it's getting late.
-- sorry!

end


section

-- My auxiliary definitions
def divides (n m : Nat) : Prop :=
  ∃ k, n * k = m
infixr:60 " | " => divides

def fermat_number (n : Nat) : Prop :=
  ∃ m : Nat, (2 ^ 2 ^ m) + 1 = n

def odd (n : Nat) : Prop :=
  2 | (n + 1)
-- end

def even (n : Nat) : Prop :=
  2 | n

def prime (n : Nat) : Prop :=
  (n ≠ 1) ∧ (∀a b : Nat, n | a*b → n | a ∨ n | b)

def infinitely_many_primes : Prop :=
  ∀n : Nat, ∃m : Nat, prime m ∧ m > n

def Fermat_prime (n : Nat) : Prop :=
  fermat_number n ∧ prime n

def infinitely_many_Fermat_primes : Prop :=
  ∀n : Nat, ∃m : Nat, Fermat_prime m ∧ m > n

def goldbach_conjecture : Prop :=
  ∀ n : Nat, n > 2 →
    (∃ x y : Nat, prime x ∧ prime y ∧ x + y = n)

def Goldbach's_weak_conjecture : Prop :=
  ∀ n : Nat, odd n ∧ n > 5 →
    (
      ∃ x y z : Nat, prime x ∧ prime y ∧ prime z
      ∧ x + y + z = n
    )

def Fermat's_last_theorem : Prop :=
  ¬∃ x y z n : Nat, n > 2
    ∧ (x ^ n) + (y ^ n) + (z ^ n) = n
end

section

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r :=
  fun h : ∃ _: α, r =>
    Exists.elim h
    (fun _ : α => fun hr : r => hr)

example (a : α) : r → (∃ _ : α, r) :=
  fun h : r => Exists.intro a h

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
  (fun h : ∃ x, p x ∧ r =>
    Exists.elim h
    (fun x : α => fun h : p x ∧ r =>
      And.intro
      (Exists.intro x h.left)
      (h.right)
    )
  )
  (fun h : (∃ x, p x) ∧ r =>
    Exists.elim h.left
    (fun x : α => fun hpx : p x =>
      Exists.intro x (And.intro hpx h.right)
    )
  )

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
  (fun h : ∃ x, p x ∨ q x =>
    Exists.elim h
    (fun x : α => fun h : p x ∨ q x =>
      Or.elim h
      (fun hpx : p x => Or.inl (Exists.intro x hpx))
      (fun hqx : q x => Or.inr (Exists.intro x hqx))
    )
  )
  (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
    Or.elim h
    (fun hexpx : ∃ x, p x =>
      Exists.elim hexpx
      (fun x : α => fun hpx : p x =>
        Exists.intro x (Or.inl hpx)
      )
    )
    (fun hexqx : ∃ x, q x =>
      Exists.elim hexqx
      (fun x : α => fun hqx : q x =>
        Exists.intro x (Or.inr hqx)
      )
    )
  )

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
  (fun h : ∀ x, p x =>
    fun hxpx : ∃ x, ¬ p x =>
      Exists.elim hxpx
      (fun x : α => fun hnpx : ¬ p x =>
        False.elim (hnpx (h x))
      )
  )
  (fun h : ¬ (∃ x, ¬ p x) =>
    fun x : α =>
      Or.elim (Classical.em (p x))
      (id)
      (fun hnpx : ¬ p x =>
        False.elim (h (Exists.intro x hnpx))
      )
  )

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
  (fun h : ∃ x, p x =>
    fun hfa : ∀ x, ¬ p x =>
      Exists.elim h
      (fun (x : α) (hpx : p x) =>
        False.elim ((hfa x) hpx)
      )
  )
  (fun h : ¬ (∀ x, ¬ p x) =>
    Classical.byContradiction
    (fun hnex : ¬ (∃ x, p x) =>
      have hfax : ∀ x, ¬ p x :=
        fun x : α =>
          Or.elim (Classical.em (p x))
          (fun hpx : p x =>
            False.elim (hnex (Exists.intro x hpx) )
          )
          (id)
      False.elim (h hfax)
    )
  )

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
  (fun h : ¬ ∃ x, p x =>
    fun x : α =>
      Or.elim (Classical.em (p x))
      (fun hpx : p x =>
        False.elim (h (Exists.intro x hpx)))
      (id)
  )
  (fun h : ∀ x, ¬ p x =>
    fun hxpx : ∃ x, p x =>
      Exists.elim hxpx
      (fun (x : α) (hpx : p x) =>
        False.elim (h x (hpx))
      )
  )

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
  (fun h : ¬ ∀ x, p x =>
    Classical.byContradiction
    (fun hne : ¬ (∃ x, ¬ p x) =>
      have hnfann : ∀ x, ¬ ¬ p x :=
        fun (x : α) (hnpx : ¬ p x) =>
          False.elim (hne (Exists.intro x hnpx))

      have hnfa : ∀ x, p x :=
        fun x : α => Classical.not_not.mp (hnfann x)

      False.elim (h hnfa)
    )
  )
  (fun h : ∃ x, ¬ p x =>
    fun hfaxpx : ∀ x, p x =>
      Exists.elim h
      (fun (x : α) (hnpx : ¬ p x) =>
        hnpx (hfaxpx x)
      )
  )

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
  (fun h : ∀ x, p x → r =>
    fun hexpx : ∃ x, p x =>
      Exists.elim hexpx
      (fun (x : α) (hpx : p x) =>
        (h x) hpx
      )
  )
  (fun h : (∃ x, p x) → r =>
    fun x : α => fun hpx : p x =>
      h (Exists.intro x hpx)
  )

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
  (fun (h : ∃x, p x → r) (h2 : ∀ x, p x) =>
    Exists.elim h
    (fun (x : α) (hpxr : p x → r) => hpxr (h2 x))
  )
  (fun (h : (∀ x, p x) → r) =>
    Or.elim (Classical.em (∀ x, p x))
    (fun faxpx : ∀ x, p x =>
      have hr : r := h faxpx
      Exists.intro a (fun _ : p a => hr)
    )
    (fun nfaxpx : ¬∀ x, p x =>
      Exists.elim ((Iff.mp Classical.not_forall) nfaxpx)
      (fun (x : α) (hnpx : ¬p x) =>
        Exists.intro x (False.elim ∘ hnpx)
      )
    )
  )
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
  (fun h : ∃ x, r → p x =>
    fun hr : r =>
      Exists.elim h
      (fun (x : α) (hrpx : r → p x) =>
        Exists.intro x (hrpx hr)
      )
  )
  (fun h : r → ∃ x, p x =>
    Or.elim (Classical.em r)
    (fun hr : r =>
      have expx : ∃x, p x := h hr
      Exists.elim (expx)
      (fun (x : α) (hpx : p x) =>
        Exists.intro x (fun _ : r => hpx)
      )
    )
    (fun hnr : ¬r =>
      Exists.intro a (fun hr : r => False.elim (hnr hr))
    )
  )

end
