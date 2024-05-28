namespace Filter.Array

def filter1 (p : α -> Prop) [DecidablePred p] (xs: Array α) : Array α := Id.run do
  let mut out := #[]
  for x in xs do
    if p x then out:= out.push x
  return out

def filter (p : α -> Prop) [DecidablePred p] (xs: Array α)
  : Array α :=
    let rec go (i : Nat) (acc: Array α) : Array α :=
      if h : i < xs.size then
        if p xs[i] then
          go (i + 1) (acc.push xs[i])
        else
          go (i + 1) acc
        else acc
      go 0 #[]

def All (p : α -> prop) (xs: Array α) :=
  ∀ (i: Nat) (lt : i < xs.size), p xs[i]

theorem filter_go_all (p: α -> prop) [DecidablePred p]
  : All p acc -> All p (filter.go p xs i acc) := by
    induction i, acc using filter.go.induct p xs

theorem filter_all (p: α -> Prop) [DecidablePred p]
  : All p (filter p xs) := by
    simp [filter]
