namespace Filter.List
/- DecidablePred p means that we can use if to check whether a value satisfies p -/
def filter (p : α -> Prop) [DecidablePred p] (xs: List α):
  List α :=
    match xs with
     | [] => []
     | x' :: xs =>
      if p x' then x' :: filter p xs else filter p xs

-- theorem filter_length (p : α -> Prop) [DecidablePred p]
--   : (filter p xs).length <= xs.length := by
--     induction xs with
--       | nil => simp [filter]
--       | cons x xs ih =>
--         simp [filter]
--         split
--         next h =>
--           simp
--           assumption
--         next =>
--           apply Nat.le_succ_of_le ih
--           assumption

def filter_length (p : α → Prop) [DecidablePred p] : (filter p xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [filter]
  | cons x xs ih =>
    simp only [filter]
    split
    . simp only [List.length];
      exact Nat.add_le_add_right ih 1
    . exact Nat.le_succ_of_le ih

inductive All (p : α -> Prop) : List α -> Prop where
  | nil : All p []
  | cons : p x -> All p xs -> All p (x :: xs)

theorem filter_all (p : α -> Prop) [DecidablePred p]
  : All p (filter p xs) := by
  induction xs with
    | nil => apply All.nil
    | cons x xs ih =>
      simp [filter]
      split
      . apply All.cons <;> assumption
      . assumption
