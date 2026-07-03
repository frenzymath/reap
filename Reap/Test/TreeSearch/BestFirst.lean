import Reap.TreeSearch.BestFirst

set_option linter.unusedSimpArgs false

def bestFirstSmoke : Option Nat × Nat :=
  let (solution, nodes) := TreeSearch.bestFirstSearch (m := Id)
    (priority := fun n : Nat => n.toFloat)
    (isTerminal := fun n => n == 3)
    (expand := fun n => if n < 3 then #[("next", n + 1)] else #[])
    0
    (maxNodes := 10)
  (solution, nodes.size)

#guard bestFirstSmoke == (some 3, 4)
