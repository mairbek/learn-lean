/- This is the first assignment. These assignments are intended for practice and
should be completed after each lecture to help with understanding. -/

/-- Q1: Define a function that calculates the cube of an integer.
Use `sorry` to mark a value that you will fill in later.
-/
def cube (x : Nat) := x * x * x
-- outputs 125
#eval cube 5

/-- Q2: Define the step function in Collatz's conjecture. i.e.
`f x = x / 2` if `x` is even
`f x = (3 x + 1) / 2` if `x` is even

Hint: The remainder function is `%`. (e.g. `5 % 2`)
-/
def collatz (x : Nat) : Nat :=
  if x % 2 == 0 then x / 2 else (3 * x + 1) / 2

#eval collatz 6
