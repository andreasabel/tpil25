import Lean
import Batteries

/-
# Recap from last time

- Searching for theorems in lean and mathlib
  - grep
  - autocomplete
  - Loogle: https://loogle.lean-lang.org
  - Moogle: https://moogle.ai
  - LeanSearch: https://leansearch.net
  - Zulip
- STLC formalization demo
  - If you want you can finish this as a project idea

# Agenda

- Project ideas
- Programming in lean
- Tactic writing
  - NB: writing a tactic is a possible project idea

-/

-- # Project ideas

-- * Library overview:
--   https://leanprover-community.github.io/mathlib-overview.html

-- * Undergrad mathematics in mathlib:
--   https://leanprover-community.github.io/undergrad.html
-- * Undergrad mathematics not in mathlib:
--   https://leanprover-community.github.io/undergrad_todo.html
-- * Undergrad low hanging fruits (out of date)
--   https://github.com/leanprover-community/mathlib3/wiki/Undergrad-low-hanging-fruits

-- * Tactic porting tracking issue:
--   https://github.com/leanprover-community/mathlib4/issues/430

-- * 1000+ theorems list:
--   https://leanprover-community.github.io/1000.html

-- * Mathlib active project list:
--   https://github.com/leanprover-community/mathlib4/projects?query=is%3Aopen

-- On tuesday we will not have a class, instead we will have meetings
-- to talk about your project ideas. DM me (in a group with your partner
-- if you are doing a pair project) sometime between now and Tue
-- and we will set a time to meet.
-- (If you are auditing / don't plan to do a project you can skip this)

-- # Programming in lean

-- We have already seen that you can define functions and run them:

def foo (x y : Nat) := x + y
#eval foo 2 2

-- Lean uses `Monad`s to organize imperative calculations

def bar : IO Unit := IO.print "hello world"

#eval bar

-- recall: monads

example {α} (a : α) : IO α := pure a
example {α β} (x : IO α) (f : α → IO β) : IO β := bind x f

def twoRandomNumbers : IO (Nat × Nat) :=
  bind (IO.rand 0 10) fun a =>
  bind (IO.rand 0 100) fun b =>
  pure (a, b)

#eval twoRandomNumbers

-- ## do notation

def twoRandomNumbers' : IO (Nat × Nat) := do
  let a ← IO.rand 0 10
  let b ← IO.rand 0 100
  return (a, b)

def twoRandomNumbers'' : IO (Nat × Nat) := do
  return (← IO.rand 0 10, ← IO.rand 0 100)

def findFirstIdx {α} [Inhabited α] [BEq α]
    (arr : Array α) (a : α) : Option Nat := do
  for i in [0:arr.size] do
    let a' := arr[i]!
    if a' == a then
      return i
  none

#print findFirstIdx

def findFirstIdx' {α} [Inhabited α] [BEq α]
    (arr : Array α) (a : α) : Option Nat :=
  bind (
    forIn [0:arr.size] none fun i _ =>
      let a' := arr[i]!
      if a' == a then
        pure (.done (some i))
      else pure (.yield none)
  ) fun r => r


def sumArray (arr : Array Nat) : Nat := Id.run do
  let mut sum := 0
  for i in [0:arr.size] do
    let a' := arr[i]!
    sum := sum + a'
  return sum

#eval sumArray #[1,2,3]

def sumArray' (arr : Array Nat) : Nat := Id.run do
  let mut sum := 0
  for _h : i in [0:arr.size] do
    let a' := arr[i]
    sum := sum + a'
  return sum

def sumArray'' (arr : Array Nat) : Nat := Id.run do
  let mut sum := 0
  for a' in arr do
    sum := sum + a'
  return sum

def sumArray''' (arr : Array Nat) : Nat :=
  arr.foldl (· + ·) 0

-- see the [lakefile](../lakefile.toml)

def main : IO Unit := do
  println! "{foo 2 2}"
  println! "{← bar}"
  println! "two random numbers: {← twoRandomNumbers}"
  println! "sum of #[1,2,3] is {sumArray #[1,2,3]}"

-- ## destructive updates

def fastNumbers (sz : Nat) : Array Nat :=
  go sz (mkArray sz 0)
where
  go (i : Nat) (arr : Array Nat) :=
    match i with
    | 0 => arr
    | i+1 => go i (arr.set! i i)

-- #time
-- #eval sumArray (fastNumbers 100000)

def slowNumbers (sz : Nat) : Array Nat :=
  let arr := mkArray sz 0
  go sz arr arr
where
  go (i : Nat) (arr _ : Array Nat) :=
    match i with
    | 0 => arr
    | i+1 => go i (arr.set! i i) arr

-- #time
-- #eval sumArray (slowNumbers 100000)


-- # Tactic writing in lean

-- ## Macro tactics

macro "easy" : tactic => `(tactic| trivial)

example : True := by
  easy

syntax term_list := "[" term,* "]"
macro "mysimp" "[" tm:term,* "]" : tactic =>
  `(tactic| simp [Nat.add_left_comm, $[$tm:term],*])

example (x y z : Nat) : x + y + z = y + (x + z) := by
  mysimp [Nat.add_assoc]

-- `syntax` declarations use a special DSL for writing parsers
-- * `"foo"` means the literal token `foo`
-- * `term` or another named parser refers to the objects
--   produced by that parser
-- * `p,*` parses 0 or more `p`'s separated by commas
-- * `p*` parses 0 or more `p`'s
-- * `p,+` and `p+` parse 1 or more `p`'s
-- * `p,*,?` allows optional trailing comma
-- * `p q` is a sequence of parsers (**not** application!)
-- * `p <|> q` parses `p` or `q`

-- There are also two ways to write a syntax declaration:

syntax closed_class := "foo!" <|> "bar!" <|> "baz?"

declare_syntax_cat open_class
syntax "foo1!" : open_class
syntax "foo2!" : open_class

macro "mytac " open_class ", " closed_class : tactic => `(tactic| skip)

example : True := by
  mytac foo1!, foo!
  mytac foo2!, baz?
  trivial

syntax "foo3!" : open_class

example : True := by
  mytac foo1!, foo!
  mytac foo2!, baz?
  mytac foo3!, bar!
  trivial

-- * You don't only need to use this to define tactics, terms work too:

open Lean

macro "boo" c:closed_class : term =>
  match c with
  | `(closed_class| foo!) => `("hello world")
  | `(closed_class| bar!) => `(2 + 2)
  | _ => Macro.throwUnsupported


#eval boo foo!
#eval boo bar!
-- #eval boo baz?

-- * `elab`orators get to do more than just expand to code, they return
--   terms directly (or execute a tactic action in the case of `tactic`)

open Meta Elab Tactic

elab "testme" : tactic => do
  let g ← getMainGoal
  unless ← isDefEq (← g.getType) (mkConst ``True) do
    throwError "I only prove true things"
  g.assignIfDefeq (mkConst ``True.intro)
  replaceMainGoal []

example : True := by
  testme

-- example : False := by
--   testme

-- example : 2 + 2 = 4 := by
--   testme

elab "myexact" t:term : tactic => do
  let g ← getMainGoal
  let e ← elabTerm t (← g.getType)
  g.assignIfDefeq e
  replaceMainGoal []

example : 2 + 2 = 4 := by
  myexact rfl

elab "everything_is_trivial" : tactic => do
  let g ← getMainGoal
  g.assign (mkConst ``trivial)
  replaceMainGoal []

example : True := by
  everything_is_trivial

example : id True := by
  everything_is_trivial

-- example : False := by
--   everything_is_trivial

elab "myassumption" : tactic => do
  let g ← getMainGoal
  let ty ← g.getType
  let lctx ← getLCtx
  for x in lctx do
    if x.userName.toString.startsWith "h" then
      if ← isDefEq x.type ty then
        g.assign (.fvar x.fvarId)
        replaceMainGoal []
        return
  throwError "no assumption matches"

example (a x : Nat) (_ : a = 1) (h : x = 2) : x = 2 := by
  myassumption

-- example (a x : Nat) (_ : a = 1) (y : x = 2) : x = 2 := by
--   myassumption
