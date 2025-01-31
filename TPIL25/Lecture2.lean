import Mathlib.Tactic

/-
# Recap from last time

By now, you should:
- have logged into Zulip and have access to the **Chalmers TPIL 2025** stream
- have Lean installed
- have Mathlib installed
- have fetched the course repository

Any problems, let me know!

# Questions that came up from last time

- Break time 13:50-14:00
- If you get a message saying to "Restart File",
  note the button in the bottom right corner ↘ of the Infoview
  - note for folks watching the video, the button is covered by my face
  - But if it looks like mathlib is building
    (there are 2000+ files building or it takes more than a minute)
    then you probably forgot to `lake exe cache get`

# Agenda

- Hole based development (term mode proofs)
- Introduction to tactics

-/

-- # Theorem command
def foo : Nat := 1
def bar : True := trivial

theorem bar' : True := trivial
-- theorem foo' : Nat := 1

-- # Hole filling

example : (True → True) ∧ (False → True) :=
  ⟨fun h : True => h, fun _ => trivial⟩

example : (True → True) ∧ (False → True) :=
  ⟨fun h => h, fun _h => trivial⟩

example : (True → True) ∧ (False → True) :=
  ⟨fun h => h, nofun⟩

section
variable (P Q R : ℕ → Prop)

example (a : ℕ) (h1 : ∀ x, P x → Q x)
    (h2 : ∀ x, Q x → R x)
    (h3 : P a) :
    R a :=
  h2 _ (h1 _ h3)

-- # TACTICS

-- # refine
example (a : ℕ) (h1 : ∀ x, P x → Q x)
    (h2 : ∀ x, Q x → R x)
    (h3 : P a) :
    R a := by
  refine h2 a ?_
  refine h1 _ ?_
  refine h3

-- # exact
example (a : ℕ) (h1 : ∀ x, P x → Q x)
    (h2 : ∀ x, Q x → R x)
    (h3 : P a) :
    R a := by
  refine h2 _ ?_
  refine h1 _ ?_
  exact h3

-- # apply
example (a : ℕ) (h1 : ∀ x, P x → Q x)
    (h2 : ∀ x, Q x → R x)
    (h3 : P a) :
    R a := by
  apply h2
  apply h1
  apply h3

-- # show_term
example (a : ℕ) (h1 : ∀ x, P x → Q x)
    (h2 : ∀ x, Q x → R x)
    (h3 : P a) :
    R a := by
  show_term apply h2
  show_term apply h1
  show_term assumption

example (a : ℕ) (h1 : ∀ x, P x → Q x)
    (h2 : ∀ x, Q x → R x)
    (h3 : P a) :
    R a := by?
  apply h2
  apply h1
  assumption

-- # forward reasoning: have
example (a : ℕ) (h1 : ∀ x, P x → Q x)
    (h2 : ∀ x, Q x → R x)
    (h3 : P a) :
    R a := by
  have hQ : Q a := h1 _ h3
  have : R a := by
    apply h2
    exact hQ
  exact this

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

#print test

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · exact hp
  · apply And.intro
    · exact hq
    · exact hp

-- # assumption
example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · assumption
  · apply And.intro
    · assumption
    · assumption

-- # constructor
example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  constructor
  · assumption
  · constructor
    · assumption
    · assumption

-- # intro
example : (True → True) ∧ (False → True) := by?
  apply And.intro
  · intro h
    assumption
  · intro h
    exact trivial

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · intro h
    apply Or.elim (And.right h)
    · intro hq
      apply Or.inl
      apply And.intro
      · exact And.left h
      · exact hq
    · intro hr
      apply Or.inr
      apply And.intro
      · exact And.left h
      · exact hr
  · intro h
    apply Or.elim h
    · intro hpq
      apply And.intro
      · exact And.left hpq
      · apply Or.inl
        exact And.right hpq
    · intro hpr
      apply And.intro
      · exact And.left hpr
      · apply Or.inr
        exact And.right hpr

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩

-- ## multiple/pattern intro
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁

example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩

example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩

-- # show
example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2
  exists a

end

-- # tactic combinators
example (p q : Prop) (hp : p) : p ∨ q := by
  apply Or.inl; assumption

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · assumption
  · assumption

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption

example (p q : Prop) (hp : p) : p ∨ q := by
  first
  | apply Or.inl; assumption
  | apply Or.inr; assumption

example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  repeat
    first
    | constructor
    | assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat any_goals constructor
  all_goals assumption

example (f : ℕ → ℕ) (x : ℕ) : f x = f x := by
  cases e : f x with
  | zero => rfl
  | succ n => rfl

def double' (f : ℕ → ℕ) (x : ℕ) : ℕ := by
  apply f
  apply f
  exact x
#print double'

-- # Rewriting

-- ## rw (rewrite) tactic

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]

example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq]; assumption

example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h]
  · assumption
  · exact hq

example (f : Nat → Nat) (a b : Nat) (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [← h₁, h₂]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]

example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]

def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example {α : Type} (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t


-- ## simp

example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption

example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp?

example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp only [add_zero, mul_one, zero_add, mul_zero]

example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  rw [add_zero, mul_one, zero_add, mul_zero, add_zero]

open List
example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp

example {α} (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [Nat.add_comm]

example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption

-- ### AC rewriting
section
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at *; constructor <;> assumption

example (w x y z : Nat)
        : x * y + z * w * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp; simp at h; assumption

-- ### more simp options

def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ← h', f] -- simp backward with h'

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*] -- simp using all local hypotheses

example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

-- ### propositional rewriting
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]

example (x y : ℕ) : if x = 0 then y + x = y else x ≠ 0 := by
  simp (config := { contextual := true })

end

example (a b c d e : ℕ) (h1 : a = b + 1)
    (h2 : d = c + a) (h3 : e = b + c) :
    d = e + 1 :=
  calc
    d = c + a       := by rw [h2]
    _ = c + (b + 1) := by rw [h1]
    _ = e + 1       := by rw [h3, add_comm b c, add_assoc]

section

variable {G : Type*} [Group G]

#check inv_mul_cancel
#check mul_one
#check one_mul
#check mul_assoc

example (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = z * y := by
  have h1 : y * z = y * (y * z) * (y * z) * z := by
    rw [mul_assoc y, h, mul_one]
  have h2 : z * y = y * (y * z) * (y * z) * z := by
    rw [← mul_assoc y, h, one_mul, mul_assoc, mul_assoc, h, mul_one]
  rw [h1, h2]

end

-- # decision procedure tactics

variable (a b c d e : ℝ)

example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring


example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

open Real
example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']

example {a b c d e : ℕ} (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  omega
