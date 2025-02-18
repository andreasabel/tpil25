import Mathlib.Tactic



example (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases eq : f x with
  | true => cases x with
    | true => repeat (rw [eq])
    | false => cases eq1 : f true with
      | true => exact eq1
      | false => exact eq
  | false => _

example (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases x with
  | true => cases eq : f true with
    | true => repeat (rw [eq])
    | false => cases eq1' : f false with
      | true => exact eq
      | false => exact eq1'
  | false => cases eq : f false with
    | true => cases eq1 : f true with
      | true => exact eq1
      | false => exact eq
    | false => repeat (rw [eq])
  done

example (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  match x, f1 : f true, f0 : f false with
  | true , true, b2 => repeat (rw [f1])
  | true , false, true => rw [f1]; rw [f0]; exact f1
  | true , false, false => rw [f1]; rw [f0]; exact f0
  | false, true, true => rw [f0]; repeat (rw [f1])
  | false, true, false => repeat (rw [f0])
  | false, false, b2 => repeat (rw [f0])
  done

example (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
    revert f; revert x; decide

example (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases x <;> cases e1 : f true <;> cases e2 : f false <;> simp [e1, e2]

variable (p : Prop)

example : ¬(p ↔ ¬p) := by
  intro h
  have np : ¬p := fun hp => h.mp hp hp
  have yp : p := h.mpr np
  exact np yp
