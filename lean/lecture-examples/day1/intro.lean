def double (n: Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => double n' + 1 + 1

#eval double 5
#eval double 9
#eval double 921

#check double

def double' : Nat -> Nat
  | 0 => 0
  | n + 1 => double' n + 2

def multiply (k : Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => multiply k n  + k

#eval multiply 4 9

/-
Not doing implicit tupling like in ml
-/
def append : List a -> List a -> List a
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys


/-
The alpha is important for typing as part of the structure
We cannot omit it because the structure is underspecified
-/
inductive Tree (α : Type) where
  | leaf : Tree α
  | branch (left: Tree α) (val : α) (right: Tree α): Tree α

def Tree.toList : Tree α -> List α
  | leaf => []
  | branch l x r => toList l ++ [x] ++ toList r

#eval (Tree.branch Tree.leaf 1 Tree.leaf).toList

/- Knows that it's a nat because of the 1 in the tree structure

-/
#check fun (β: Type) (x: β) => (Tree.branch Tree.leaf x Tree.leaf).toList

/- Prop (proposition) - some sort of meaningful statement -/
inductive Even: Nat -> Prop where
  | isEven (n: Nat) : Even (n + n)
example : Even 6 := .isEven 3

inductive Repeats (x : α) : List α → Prop where
  | nil : Repeats x []
  | cons : Repeats x xs → Repeats x (x :: xs) -- here xs is implicitly an argument

example : Repeats "yes!" ["yes!","yes!","yes!"] := .cons (.cons (.cons .nil))

def Both (p q : α -> Prop) : α -> Prop :=
  fun x => p x ∧ q x
