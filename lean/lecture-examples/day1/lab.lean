def append_two_list (a: List α) (b: List α): List α :=
  match a with
    | [] => b
    | y :: a' => y :: append_two_list a' b

#eval append_two_list [1, 2, 3] [4, 5, 6]

def append_length : (append_two_list xs ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp [append_two_list]
  | cons x xs ih => simp [append_two_list, ih]
                    omega -- There are other ways to handle this, but this shows  --

def map {α β: Type} (a: List α) (b: α -> β) : List β :=
  match a with
  | [] => []
  | x :: a' => b x :: map a' b

#eval map [1, 2, 3] (fun (n : Nat) => n + 1) -- Make sure you have commas in the list items --

def map_proof_len : (map xs func).length = xs.length := by
  induction xs with
  | nil => simp [map]
  | cons _ xs ih => simp [map, ih]


-- def map_proof_type {α : Type} : ∀ (l : List α) you cannot do this in lean, church style vs curry style?

inductive Tree (α: Type) where
  | leaf: Tree α
  | branch (name: string) (left: Tree α) (val: α) (right: Tree α): Tree α

inductive All (p: α -> Prop) -> Tree α -> Prop where
