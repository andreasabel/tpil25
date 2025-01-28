import Mathlib.Tactic

/-
# Agenda

- Interactive theorem proving
- Course requirements
- Getting set up
- Introduction to Lean

# Introductions

Mario Carneiro
Magnus Myreen
Ana Bove

# Interactive theorem proving

- https://leanprover-community.github.io/
  statistics: https://leanprover-community.github.io/mathlib_stats.html
  API: https://leanprover-community.github.io/mathlib4_docs/
- https://lean-lang.org/
- https://www.scientificamerican.com/article/ai-will-become-mathematicians-co-pilot/
- https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/

Why?

- verification
- libraries, reference, search
- collaboration
- teaching / learning
- exploring / doing mathematics
- automation and machine learning

# Requirements

This course is unusual:
- Goal: learn to formalize mathematics
- Format: project course, no exams
- Lectures: in an editor

Plan:
- First 3 weeks: lectures
- After that: self-selected projects in groups of 1 or 2

Warnings:
- requires independence
- requires time management / discipline

Information will be posted on the Lean Zulip chat:
- https://leanprover.zulipchat.com/#narrow/channel/481399-Chalmers-TPIL-2025

Your first assignment is to sign up for zulip and DM me
- https://leanprover.zulipchat.com/#narrow/dm/110049-Mario-Carneiro
so that I can add you to the private stream above.

Lectures will be recorded and put on YouTube; I will post them on Zulip
as they become available.

You will use Github to pull assignments and lectures.

We will be mainly using two textbooks:
- Theorem Proving in Lean
  - book: https://lean-lang.org/theorem_proving_in_lean4/
- Mathematics in Lean
  - book: https://leanprover-community.github.io/mathematics_in_lean/
  - code: https://github.com/leanprover-community/mathematics_in_lean

- Course website: https://www.cse.chalmers.se/~marioc/courses/tpil25/
- Course repository: https://github.com/digama0/tpil25/

# Getting set up

- Install lean:
  https://github.com/leanprover/lean4/blob/master/doc/quickstart.md
- Install Git

```
git clone https://github.com/digama0/tpil25.git
cd tpil25
lake exe cache get
lake build
```

# Getting started with Lean

In Lean, there is a single language for:
- defining data types
- defining objects
- stating claims
- writing proofs

Two fundamental facts:
- Everything is an expression.
- Every expression has a type.

Two fundamental operations:
- Check that an expression is well-formed and infer/check its type.
- Evaluate an expression.
-/

/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

example := m
example : Nat := m

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false

#reduce b1 && b2    -- false

-- # Simple type theory

#check Nat → Nat      -- type the arrow as "\to" or "\r"
#check Nat -> Nat     -- alternative ASCII notation

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9

#check 2 + 2
#check (2 : ℝ) + 2
#check (2 + 2 : ℝ)

#eval 2 + 2
#eval 2343242 * 4435
#eval (17 : ℚ) / 5 + 5
#eval 17 % 5

-- # Types as objects
#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat


-- # Defining types
def A : Type := Nat
def B : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check A        -- Type
#check F A      -- Type
#check F Nat    -- Type
#check G A      -- Type → Type
#check G A B    -- Type
#check G A Nat  -- Type


-- # The type of types
#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5

/-
|:------:|:-------------:|:-------------:|:---------------:|:----------------------:|:---:|
| sort   | Prop (Sort 0) | Type (Sort 1) | Type 1 (Sort 2) | Type 2 (Sort 3)        | ... |
| type   | True          | Bool          |   Nat -> Type   | Type -> Type 1         | ... |
| term   | trivial       | true          | fun n => Fin n  | fun (_ : Type) => Type | ... |
-/


-- # Universe parametricity
#check List     -- List.{u} (α : Type u) : Type u
#check List.{0} -- List : Type → Type

#check Prod    -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)


-- # Function abstraction and evaluation
#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ and fun mean the same thing
#check fun x => x + 5     -- Nat inferred
#check λ x => x + 5       -- Nat inferred

#eval (λ x : Nat => x + 5) 10    -- 15


-- # Types as parameters
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)


-- # Propositions as types
#check True
#check False
#check 2 + 2 = 4
#check 2 + 2 = 5

#check ∀ x y z n : ℕ, x * y * z ≠ 0 → n > 2 →
  x^n + y^n ≠ z^n

#check trivial
#check (rfl : 2 + 2 = 4)
#check (sorry : 2 + 2 = 5) -- can't fill the sorry

-- #check (by decide : 2 + 2 = 5)
-- -- tactic 'decide' proved that the proposition
-- --   2 + 2 = 5
-- -- is false

#check true         -- true : Bool
#check True         -- True : Prop
#check false → true -- false = true → true = true : Prop

-- # Definitions

def double (x : Nat) : Nat :=
  x + x

def double' : Nat → Nat :=
  fun (x : Nat) => x + x

def double'' :=
  fun (x : Nat) => x + x

#eval double 3   -- 6


def add (x y : Nat) :=
  x + y

#eval add 3 2  -- 5


def greater (x y : Nat) :=
  if x > y then
    x
  else
    y


def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2   -- 8


def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

-- # Local declarations (let)
#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

#eval
  let y := 2 + 2;
  y * y

#eval
  let y := 2 + 2 -- look ma, no semicolon
  y * y

example := let a := Nat; fun x : a => Nat.succ x  -- ok
-- example := (fun a => fun x : a => Nat.succ x) Nat -- fail

-- # variable declarations

section

variable (α β γ : Type)

def compose' (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice' (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (h : α → α) (x : α) : α :=
  h (h (h x))

end

-- # Auto-implicits
section
set_option autoImplicit true

def identity : α → α :=
  fun x => x

example (h : nat → nat) (x : nat) : nat :=
  h (h x)

end

-- -- unknown identifier 'nat'
-- example (h : nat → nat) (x : nat) : nat :=
--   h (h x)

-- # Sections
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose'' := g (f x)
  def doTwice'' := h (h x)
  def doThrice'' := h (h (h x))
end useful


-- # Namespaces
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check Foo.fa



-- # Dependent types

#check @List.cons    -- {α : Type u_1} → α → List α → List α
#check @List.nil     -- {α : Type u_1} → List α
#check @List.length  -- {α : Type u_1} → List α → Nat
#check @List.append  -- {α : Type u_1} → List α → List α → List α

universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5 -- 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5 -- 5

-- # Implicit arguments

def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil

#check Lst.cons Nat 0 (Lst.nil Nat)
#check Lst.cons _ 0 (Lst.nil _)

def Lst.cons' {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil' {α : Type u} : Lst α := List.nil

#check Lst.cons' 0 (Lst.nil')

#check List.cons 0 (List.nil)

#check @Lst.cons    -- (α : Type u_1) → α → Lst α → Lst α
#check @Lst.nil     -- (α : Type u_1) → Lst α
#check @List.cons    -- {α : Type u_1} → α → List α → List α
#check @List.nil     -- {α : Type u_1} → List α


#check @Lst.cons' _ 0 (@Lst.nil' _)
#check @Lst.cons' Nat 0 (@Lst.nil' Nat)
#check Lst.cons' (α := Nat) 0 (Lst.nil' (α := Nat))
