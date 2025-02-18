import Mathlib.Tactic

/-
# Recap from last time

We covered tactic mode, along with the tactics:
- exact, refine, apply
- assumption
- constructor
- cases
- have, let, show
- goal structuring using `case` and bullets
- first, repeat, all_goals, any_goals, try, `<;>`
- rw, simp
- ring, linarith, omega

We covered a lot of stuff, so please ask questions if anything is
confusing. We will keep seeing these tactics in the future, so we will
get more practice with them "on the job".

# Addenda to the previous class

- Some structural commands I forgot to mention: `skip`, `fail`, `done`
- Show of hands, who has some experience with agda?

# Agenda

- Inductive types
  - pattern matching in `def` and `fun`
  - cases, induction
  - rcases, rintro, obtain
  - match, nomatch, nofun
- break
- Structures
  - structure instances
  - Typeclasses

-/

-- # more structural commands

section
-- I will explain these afterward
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

-- ## skip and fail
example : True := by
  skip
  trivial

-- example : True := by
--   fail "oh no"

example : True := by
  try (skip; trace_state)
  try (fail "oh no"; trace_state)
  trace_state
  trivial

-- ## done

-- syntax error, note the bad error message
-- example : True := by

-- example : True := by
--   done

example : True := by
  trivial
  done -- note the lightbulb

end


-- # Inductive types

inductive Trool
  | protected true
  | protected false
  | trelse

inductive Trool' : Type
  | true : Trool'
  | false : Trool'
  | trelse : Trool'


#check Trool.true

def toBool : Trool → Option Bool
  | Trool.true => some true
  | Trool.false => some false
  | Trool.trelse => none

namespace Trool

def toBool : Trool → Option Bool
  | .true => some true
  | .false => some false
  | trelse => none

def toBool' : Trool → Option Bool
  | .true => some Bool.true
  | .false => some Bool.false
  | trelse => none

def toBool'' : Trool → Option Bool
  | .true => some .true
  | .false => some .false
  | trelse => none

-- protected true, false

end Trool

def toBool' : Trool → Option Bool
  | .true => some true
  | .false => some false
  | .trelse => none


                 -- ↓ parameter
inductive MyOption (α : Type) : Type
  | none : MyOption α
  | some (a : α) : MyOption α

def toOption {α} : MyOption α → Option α
  | .none => none
  | .some a => some a


inductive MyList (α : Type) : Type
  | nil : MyList α
  | cons (head : α) (tail : MyList α) : MyList α

def MyList.map {α β} (f : α → β) : MyList α → MyList β
  | nil => nil
  | cons a b => cons (f a) (map f b)

-- note the namespace above

#eval (.cons 1 (.cons 4 (.cons 0 .nil)) : MyList ℕ)
#eval (.cons 1 (.cons 4 (.cons 0 .nil)) : MyList ℕ)
        |>.map fun n => n * 10
        -- |> MyList.map fun n => n * 10


-- ## What does an `inductive` declaration actually do?
#print MyList
#print MyList.nil
#print MyList.cons
#print MyList.rec

noncomputable
section

variable
  {α : Type} {motive : MyList α → Type}
  (H0 : motive MyList.nil)
  (H1 : (head : α) → (tail : MyList α) →
    motive tail → motive (MyList.cons head tail))

example (t : MyList α) : motive t := MyList.rec H0 H1 t

example : motive .nil := MyList.rec H0 H1 .nil

example : motive .nil := H0

example : MyList.rec H0 H1 .nil = H0 := rfl

example (a : α) (b : MyList α) :
  MyList.rec H0 H1 (.cons a b) =
  H1 a b (MyList.rec H0 H1 b) := rfl

def MyList.map' {α β} (f : α → β) : MyList α → MyList β :=
  fun list =>
    list.rec
      nil
      fun a _ IH => cons (f a) IH

end

-- ## Proofs by induction are also definitions by recursion

namespace MyList

def length {α} : MyList α → ℕ
  | .nil => 0
  | .cons _ b => b.length + 1

theorem length_map {α β} (f : α → β) (l : MyList α) :
    (map f l).length = l.length :=
  match l with
  | .nil => rfl
  | .cons _ l => congrArg Nat.succ (length_map f l)

theorem length_map' {α β} (f : α → β) (l : MyList α) :
    (map f l).length = l.length :=
  match l with
  | nil => by
    simp [map]
    rfl
  | cons _ l => by
    simp [map, length]
    exact (length_map' f l)

end MyList


-- ## Tactics for case splitting

example (n : ℕ) : n + 1 - 1 = n := rfl
-- example (n : ℕ) : n - 1 + 1 = n := rfl

#eval (0 - 1 + 1, 0)

example (n : ℕ) : n ≠ 0 → n - 1 + 1 = n := by
  intro h0
  cases n
  · exfalso
    apply h0
    rfl
  · rfl

example (n : ℕ) : n ≠ 0 → n - 1 + 1 = n := by
  intro h0
  induction n
  · exfalso
    apply h0
    rfl
  case succ n IH =>
    rfl

def foo : ℕ → ℕ
  | 0 => 0
  | n + 1 => foo n + 1

example (n : ℕ) : foo n = n := by
  induction n with
  | zero =>
    simp [foo]
  | succ n ih =>
    simp [foo]
    exact ih

example (n : ℕ) : foo n = n := by
  induction n with
  | zero =>
    simp [foo]
  | succ n ih =>
    simp [foo, *]

example (n : ℕ) : foo n = n := by
  induction n <;> simp [foo, *]

theorem MyList.length_map''' {α β} (f : α → β) (l : MyList α) :
    (map f l).length = l.length := by
  induction l <;> simp [map, length, *]

example {p q} (h : p ∨ p) (h2 : q ∨ q) : 1 = 1 ∨ 0 = 0 := by
  casesm* _ ∨ _
  all_goals trivial

-- ## match

theorem MyList.length_map'' {α β} (f : α → β) (l : MyList α) :
    (map f l).length = l.length := by
  match l with
  | .nil => rfl
  | .cons _ l => exact congrArg Nat.succ (length_map f l)

def firstOpt {α} (a b : Option α) : Option α :=
  match a, b with
  | some x, _ => some x
  | _, some x => some x
  | none, none => none

def firstOpt' {α} (a b : Option α) : Option α :=
  match a, b with
  | some x, _
  | _, some x => some x
  | _, _ => none

def firstOpt'' {α} : (a b : Option α) → Option α :=
  fun
  | some x, _ | _, some x => some x
  | none, none => none

def firstOpt''' {α} : (a b : Option α) → Option α := by
  intro
  | some x, _ | _, some x => exact some x
  | none, none => exact none

theorem firstOpt_some1 {α} (a : α) (s : Option α) :
  firstOpt (some a) s = some a := by
    simp [firstOpt]

theorem firstOpt_some2 {α} (s : Option _) (b : α) :
  firstOpt s (some b) = some b := by
    simp [firstOpt]
    done

-- ## Inductive propositions

inductive MyInhabited (α : Type) : Type
  | mk (a : α) : MyInhabited α

inductive MyNonempty (α : Type) : Prop
  | mk (a : α) : MyNonempty α

def MyInhabited.get {α} : MyInhabited α → α
  | .mk a => a

example {α} (a : α) : (MyInhabited.mk a).get = a := rfl

-- def MyNonempty.get {α} : MyNonempty α → α
--   | .mk a => a

#print MyInhabited.rec
#print MyNonempty.rec

theorem MyNonempty.exists {α} : MyNonempty α → ∃ x : α, x = x
  | .mk a => ⟨a, rfl⟩

set_option pp.proofs true
example (get : MyNonempty ℕ → ℕ)
    (hget : ∀ (n : ℕ), get (MyNonempty.mk n) = n)
    : False := by
  let a := MyNonempty.mk 0
  let b := MyNonempty.mk 1
  have : a = b := rfl
  have H0 : get a = 0 := hget 0
  have H1 : get b = 1 := hget 1
  have : 0 = 1 := by rw [← H0, H1]
  cases this
  done

#check Classical.choice

-- example {α} (a : α) : Classical.choice (Nonempty.intro a) = a := rfl

-- ## Inductive predicates

                -- ↓ index
inductive IsEven : ℕ → Prop
  | zero : IsEven 0
  | add2 (n : ℕ) : IsEven n → IsEven (n + 2)

example (n : ℕ) : IsEven n ↔ ∃ k, n = 2 * k := by
  constructor
  · intro H
    induction H with
    | zero => exists 0
    | add2 n _ ih =>
      let ⟨k, eq⟩ := ih
      exists k+1
      rw [eq]
      ring
  · intro ⟨k, eq⟩
    rw [eq]
    clear eq -- needed to get the correct induction hypothesis
    induction k with
    | zero =>
      show IsEven 0
      constructor
    | succ k ih =>
      rw [show 2*(k+1) = 2*k + 2 by ring]
      constructor
      apply ih

#print Or
#print Exists
#print True
#print False

#print And


-- # Structures

structure Point where
  x : ℕ
  y : ℕ

inductive Point' where
  | mk
    (x : ℕ)
    (y : ℕ)
    : Point'

structure Point'' : Type where
  make ::
  x : ℕ
  y : ℕ

example : Point := Point.mk 0 1

-- structure Exists'.{u} {α : Sort u} (p : α → Prop) : Prop where
--   w : α
--   h : p w

def toProd (p : Point) : ℕ × ℕ :=
  match p with
  | .mk a b => (a, b)

#check Point.x
#check Point.y

def Point'.x : Point → ℕ
  | .mk x _ => x

def Point'.y : Point → ℕ
  | .mk _ y => y

def pt : Point := { x := 0, y := 1 }
def pt' : Point := ⟨0, 1⟩

def foo' : Point := {
  x := 0
  y := 1
}

structure Point3 extends Point where
  z : ℕ

structure Point3' where
  toPoint : Point
  z : ℕ

def pt3 : Point3 := ⟨⟨0, 1⟩, 2⟩
def pt3' : Point3 := { x := 0, y := 1, z := 2 }
def pt3'' : Point3 := { toPoint := ⟨0, 1⟩, z := 2 }

#check pt3.toPoint.x


structure CheckerPoint where
  x : ℕ
  y : ℕ
  even : IsEven (x + y)

example : CheckerPoint where
  x := 1
  y := 1
  even := .add2 _ .zero

#print And
#print Subtype

example : {n : ℕ // n > 3} := ⟨5, by decide⟩
example (a : {n // n > 3}) : a.val ≠ 0 := by linarith [a.property]

-- # Typeclasses

class Origin where
  x : ℕ
  y : ℕ

@[class] structure Origin' where
  x : ℕ
  y : ℕ

def originX : [_o : Origin] → ℕ
  | .mk x _ => x

def myOrigin : Origin := { x := 0, y := 0 }

#check Point.x
#check originX

-- example : ℕ := originX myOrigin
example : ℕ := @originX myOrigin
example : ℕ := @Point.x pt

-- example : ℕ := @originX _
-- example : ℕ := @Point.x _

example [_o : Origin] : ℕ := originX
example [_o : Origin] : ℕ := @originX _
-- example (_pt : Point) : ℕ := @Point.x _

instance myOrigin' : Origin := { x := 0, y := 0 }

@[instance] def myOrigin'' : Origin := { x := 0, y := 0 }

example : ℕ := @originX _
example : ℕ := originX

-- ### using instances for proof search
attribute [class] IsEven
attribute [instance] IsEven.zero
instance IsEven.add2' (n : ℕ) [h : IsEven n] : IsEven (n + 2) := IsEven.add2 n h

def T : IsEven 42 := inferInstance

-- ### using instances for algebraic laws

#print Mul -- <- goto def

example {α} [Mul α] (a b : α) : a * b = a * b := rfl

class MySemigroup (α : Type) extends Mul α where
  assoc (a b c : α) : (a * b) * c = a * (b * c)

instance : MySemigroup Nat where
  assoc a b c := Nat.mul_assoc a b c

theorem assoc4 {α} [MySemigroup α] (a b c d : α) :
    ((a * b) * c) * d = a * (b * (c * d)) := by
  rw [MySemigroup.assoc, MySemigroup.assoc]

example (x y : ℕ) :
    ((5 * x) * (2+y)) * y = 5 * (x * ((2+y) * y)) :=
  assoc4 ..

#print Monoid -- <- goto def


/-!
# Summary

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
  - `rcases`, `obtain`, `rintro`
- Structures
  - are syntax for one-constructor inductives
  - have "projection" functions
  - can be introduced using `{ x := 0, y := 1 }` notation
  - have `extends` syntax for composing structures
- Typeclasses
  - are structures with an annotation to make them inferred automatically
  - use `[Foo]` binders to get inferred
  - are used in mathlib to manage the algebraic hierarchy

-/
