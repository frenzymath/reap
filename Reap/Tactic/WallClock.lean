module
public meta import Lean

public meta section

open Lean Elab Tactic

namespace Reap.WallClock

initialize cumulativeWallClockTimes : IO.Ref (Std.HashMap String Nat) ←
  IO.mkRef {}

def withCumulativeWallClockTime {m : Type _ → Type _} {α : Type _} [Monad m]
    [MonadLiftT BaseIO m] [MonadFinally m] (name : String) (act : m α) : m α := do
  let start ← liftM (m := BaseIO) IO.monoNanosNow
  try
    act
  finally
    let stop ← liftM (m := BaseIO) IO.monoNanosNow
    discard <| liftM (m := BaseIO) <| cumulativeWallClockTimes.modify fun stats =>
      stats.insert name <| stats.getD name 0 + (stop - start)

def printCumulativeWallClockTimes : TacticM Unit := do
  let stats := (← liftM (m := BaseIO) cumulativeWallClockTimes.get).toArray.qsort fun a b => a.1 < b.1
  unless stats.isEmpty do
    IO.println "cumulative wall-clock times:"
    for (name, nanos) in stats do
      IO.println s!"\t{name} took {nanos.toFloat / 1000000000} s"

end Reap.WallClock
