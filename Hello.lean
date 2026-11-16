#eval 1 + 1

def greeting : String := "Hello Lean!"
#eval! greeting

def f (x : Nat) : Nat :=
  x^2 + 1

#eval f 3
#eval f 10

def double : Nat → Nat :=
  fun x ↦ x * 2

#eval double 7

def square : Nat → Nat :=
  fun x ↦ x^2

#eval square 6

example : double 5 = 10 := by
  rfl

example : square 6 = 36 := by
  rfl

example (x : Nat) : double x = x * 2 := by
  rfl

def triple (x : Nat) : Nat :=
  3 * x

example (x : Nat) : triple x = 3 * x := by
  rfl
