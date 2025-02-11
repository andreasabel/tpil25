import Mathlib.Tactic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

/-
# Recap from last time

We covered inductive types, structures and typeclasses:
- Inductive types
  - are introduced with `inductive` keyword
  - can be `Prop` or `Type`
  - can have parameters and indices
- Working with inductive types
  - Pattern matching definitions
  - `match` in term and tactic mode
  - `fun`-match in term mode or `intro`-match in tactic mode
  - `cases` and `induction` in tactic mode
  - `have` and `let` also do pattern matching
- Structures
  - are syntax for one-constructor inductives
  - have "projection" functions
  - can be introduced using `{ x := 0, y := 1 }` notation
  - have `extends` syntax for composing structures
- Typeclasses
  - are structures with an annotation to make them inferred automatically
  - use `[Foo]` binders to get inferred
  - are used in mathlib to manage the algebraic hierarchy

# Addenda to the previous class

- `rcases`, `obtain`, `rintro` tactics

# Agenda

- Searching for theorems in lean and mathlib
  - grep
  - autocomplete
  - Loogle: https://loogle.lean-lang.org
  - Moogle: https://moogle.ai
  - LeanSearch: https://leansearch.net
  - Zulip
- Live formalization demo

-/

-- ## rcases, rintro, obtain

example (p q : Prop) (h : p ∧ q) : True := by
  cases h with
  | intro a b => trivial

example (p q : Prop) (h : p ∨ q) : True := by
  cases h with
  | inl a => trivial
  | inr a => trivial

example (p : ℕ → Prop) (h : ∃ a : ℕ, p a) : True := by
  cases h with
  | intro a ha => trivial

example (p : ℕ → Prop) (h : ∃ a b c : ℕ, p a ∧ p b ∧ p c) : True := by
  cases h with
  | intro a h =>
    cases h with
    | intro b h =>
      cases h with
      | intro c h =>
        cases h with
        | intro ha h =>
          cases h with
          | intro hb hc =>
            trivial

example (p : ℕ → Prop) (h : ∃ a b c : ℕ, p a ∧ p b ∧ p c) : True := by
  rcases h with ⟨a, b, c, ha, hb, hc⟩
  trivial

example (p : ℕ → Prop) (h : ∃ a b c : ℕ, p a ∧ p b ∧ p c) : True := by
  obtain ⟨a, b, c, ha, hb, hc⟩ := h
  trivial

example (p : ℕ → Prop) (h : ∃ a b c : ℕ, p a ∧ p b ∧ p c) : True := by
  have ⟨a, b, c, ha, hb, hc⟩ := h
  trivial

example (p : ℕ → Prop) (h : ∃ a b c : ℕ, p a ∧ p b ∧ p c) : True := by
  match h with
  | ⟨a, b, c, ha, hb, hc⟩ =>
    trivial

example (p : ℕ → Prop) (h : ∃ a b c : ℕ, p a ∨ p b ∨ p c) : True := by
  obtain ⟨a, b, c, ha | hb | hc⟩ := h
  · trivial
  · trivial
  · trivial

example (p : ℕ → Prop) (h : ∃ a b c : ℕ, p a ∨ p b ∨ p c) : True := by
  match h with
  | ⟨a, b, c, .inl ha⟩ => trivial
  | ⟨a, b, c, .inr (.inl ha)⟩ => trivial
  | ⟨a, b, c, .inr (.inr ha)⟩ => trivial

example (p : ℕ → Prop) : (∃ a b c : ℕ, p a ∨ p b ∨ p c) → True := by
  rintro ⟨a, b, c, ha | hb | hc⟩
  · trivial
  · trivial
  · trivial

section «recall our previous proof of IsEven»

inductive IsEven : ℕ → Prop
  | zero : IsEven 0
  | add2 (n : ℕ) : IsEven n → IsEven (n + 2)

example (n : ℕ) : (∃ k, n = 2 * k) → IsEven n := by
  intro ⟨k, eq⟩
  rw [eq]
  clear eq
  induction k with
  | zero =>
    show IsEven 0
    constructor
  | succ k ih =>
    rw [show 2*(k+1) = 2*k + 2 by ring]
    constructor
    apply ih

end «recall our previous proof of IsEven»

example (n : ℕ) : (∃ k, n = 2 * k) → IsEven n := by
  intro ⟨k, eq⟩
  rw [eq]
  clear eq
  induction k with
  | zero =>
    show IsEven 0
    constructor
  | succ k ih =>
    rw [show 2*(k+1) = 2*k + 2 by ring]
    constructor
    exact ih

example (n : ℕ) : (∃ k, n = 2 * k) → IsEven n := by
  rintro ⟨k, rfl⟩
  induction k with
  | zero =>
    show IsEven 0
    constructor
  | succ k ih =>
    rw [show 2*(k+1) = 2*k + 2 by ring]
    constructor
    exact ih

example (n : ℕ) : (∃ k, n = 2 * k) → IsEven n := by
  intro h
  cases h with
  | intro k eq =>
    subst eq
    induction k with
    | zero =>
      show IsEven 0
      constructor
    | succ k ih =>
      rw [show 2*(k+1) = 2*k + 2 by ring]
      constructor
      exact ih

-- # Ways to search

-- ## 1. grep
-- * Git clone mathlib
-- * "Find in files"
-- * Search for words or symbols related to the query,
--   then browse the nearby theorems

-- It is very low-tech but useful for learning what is available
-- when you don't have a precise question

-- You can also ctrl-click on any declaration to go to it:
#print TopologicalSpace


-- ## 2. autocomplete
-- * Type part of an identifier name
-- * ctrl-space (sometimes this is not needed) to bring up completions

-- This is most useful in conjunction with
-- **learning the naming convention**:
-- - https://leanprover-community.github.io/contribute/naming.html

-- * Common "axiomatic" properties of an operation like conjunction or
--   disjunction are put in a namespace that begins with the name of the operation:
#check And.comm
#check Or.comm

-- * In particular, this includes `intro` and `elim` operations for logical
--   connectives, and properties of relations:
#check And.intro
#check And.elim
#check Or.intro_left
#check Or.intro_right
#check Or.elim

#check Eq.refl
#check Eq.symm
#check Eq.trans

-- * Note however we do not do this for axiomatic logical and arithmetic operations.
#check and_assoc
#check mul_comm
#check mul_assoc
#check mul_left_cancel  -- multiplication is left cancelative

-- * For the most part, however, we rely on descriptive names.
--   Often the name of theorem simply describes the conclusion:
#check Nat.succ_ne_zero
#check Nat.mul_zero
#check Nat.mul_one
#check sub_add_eq_add_sub
#check Nat.le_iff_lt_or_eq

-- * If only a prefix of the description is enough to convey the meaning,
--   the name may be made even shorter:
#check neg_neg
#check Nat.pred_succ

-- * When an operation is written as infix, the theorem names follow suit.
--   For example, we write `neg_mul_neg` rather than `mul_neg_neg`
--   to describe the pattern `-a * -b`.

-- * Sometimes, to disambiguate the name of theorem or better convey the
--   intended reference, it is necessary to describe some of the hypotheses.
--   The word "of" is used to separate these hypotheses:
#check Nat.lt_of_succ_le
#check Nat.lt_of_not_ge
#check Nat.lt_of_le_of_ne
#check Nat.add_lt_add_of_lt_of_le

-- * The hypotheses are listed in the order they appear, *not* reverse order.
--   For example, the theorem `A → B → C` would be named `C_of_A_of_B`.

-- * Sometimes abbreviations or alternative descriptions are easier to work with.
--   For example, we use `pos`, `neg`, `nonpos`, `nonneg` rather than
--   `zero_lt`, `lt_zero`, `le_zero`, and `zero_le`.
#check mul_pos
#check mul_nonpos_of_nonneg_of_nonpos
#check add_lt_of_lt_of_nonpos
#check add_lt_of_nonpos_of_lt

-- * These conventions are not perfect. They cannot distinguish
--   compound expressions up to associativity, or repeated
--   occurrences in a pattern. For that, we make do as best we can.
--   For example, `a + b - b = a` could be named either
--   `add_sub_self` or `add_sub_cancel`.

-- * Sometimes the word "left" or "right" is helpful to describe
--   variants of a theorem.
#check add_le_add_left
#check add_le_add_right
#check le_of_mul_le_mul_left
#check le_of_mul_le_mul_right

-- * Mathlib takes this naming convention very seriously,
--   and will use it even for famous theorems:
recall EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two
  {V P} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
  (p1 p2 p3 : P) :
  dist p1 p3 * dist p1 p3 = dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 ↔
    EuclideanGeometry.angle p1 p2 p3 = Real.pi / 2

-- * Occasionally famous theorems will be provided
--   in both "symbol reading" and vernacular form.
#check Nat.exists_prime_lt_and_le_two_mul
#check Nat.bertrand

-- ## 3. `exact?`, `apply?`

-- * The `exact?` tactic tries to close the goal as an instantiation
--   of any single theorem in the library. As such, it can be used as a
--   search tool by typing the theorem you want and using `exact?` to prove it

example (a b : ℤ) : a + b - b = a := by exact?


-- * There is also `apply?`, which allows some subgoals to be generated
--   example (a b : ℕ) : a - b + b = a := by exact?
example (a b : ℕ) : a - b + b = a := by apply?

-- ## 4. `#loogle`
-- * https://loogle.lean-lang.org

-- There is also an older version of loogle called `#find`
#find _ + _ = _ + _
#find Nat → Nat
#find List String → String


#loogle "add", _ - _

#loogle Real.sin -- theorems using `Real.sin`
#loogle "differ" -- theorems whose names contain `differ`
-- #loogle _ * (_ ^ _) -- theorems with a subexpression
-- s#loogle ?a * ?b = ?b * ?a -- nonlinear patterns
#loogle ⊢ tsum _ = _ * tsum _ -- search only in the conclusion

-- ## 5. `#moogle`
-- * https://moogle.ai

#moogle "Hausdorff dimension."

-- ## 6. `#leansearch`
-- * https://leansearch.net

#leansearch "Hausdorff dimension."

-- ## 7. Zulip > Is there code for X?
-- * https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F



-- # Formalization demo: STLC is strongly normalizing

inductive Typ
  | nat : Typ
  | fn : Typ → Typ → Typ

inductive Term
  | nat : Nat → Term
  | var : Term
  | app : Term → Term → Term
  | lam : Typ → Term → Term
