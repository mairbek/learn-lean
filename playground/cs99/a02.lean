/-- Q1:
Did you know that you can match on Strings too? Modify the function below so the
wildcard case prints out the input string length
-/
def count : String → String
  | "" => "Empty string"
  -- The `_` prefix prevents the compiler from complaining about unused
  -- variables.
  | x => s!"The length is { x.length }"

#eval count ""
#eval count "pepe"

/-- Q2:
Define a recursive function to evaluate the Collatz conjecture. i.e. it repeats

`f x = x / 2` if `x` is even
`f x = (3 x + 1) / 2` if `x` is even

Until `x` reaches 1.
-/
partial def collatz (x : Nat) : Nat :=
  if x == 1 then
    1
  else
    if x % 2 == 0 then
      let x' := x / 2;
      collatz x'
    else
      let x' := (3 * x + 1) / 2;
      collatz x'


#eval collatz 10

/-- Q3:
Create a function that generates a variable-sized Christmas tree. Below is an
example of tree size being 3.
```
  *
 ***
*****
  *
  *
```
-/
def christmasTree (n : Nat) : String := sorry

structure Point3 where
  x : Nat
  y : Nat
  z : Nat

/-- Q4:
Define a function that sorts the elements of a `Point3`.
-/
def Point3.sort (p : Point3) : Point3 :=
  let { x, y, z } := p
  sorry

inductive Tree where
  | leaf (x : Nat)
  | branch (x : Nat) (left right : Tree)

/-- Q5:
Define an infix traversal function of `Tree`
Hint: Use `++` to concatenate two lists.
-/
def Tree.infixTraverse : Tree → List Nat := sorry

-- Should output [2, 5, 0]
#eval (Tree.branch 5 (.leaf 2) (.leaf 0)).infixTraverse

/-- Q6: Represents the result of a computation -/
inductive Result where
  | ok (x : Nat)
  | error (message : String)

/-- Q6.1:
Define a function which has the following behaviour: Given a `Result.ok x`, it
returns `x`. Given a `Result.error message`, it returns `0`.
-/
def Result.unwrapD : Result → Nat := sorry

/-- Q6.2:
Define the same function but use the recursor `Result.casesOn` instead.
-/
def Result.unwrapD' : Result → Nat := sorry
