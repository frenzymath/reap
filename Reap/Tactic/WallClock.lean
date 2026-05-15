module
public meta import Lean

public meta section

open Lean Elab Tactic

namespace Reap.WallClock

initialize cumulativeWallClockTimes : IO.Ref (Std.HashMap String Nat) ←
  IO.mkRef {}

variable {m : Type _ → Type _} [Monad m] [MonadLiftT BaseIO m]

def withCumulativeWallClockTime {α : Type _} (name : String) (act : m α) : m α := do
  let start ← IO.monoNanosNow
  let result ← act
  let stop ← IO.monoNanosNow
  discard <| liftM (m := BaseIO) <| cumulativeWallClockTimes.modify fun stats =>
    stats.insert name <| (stats.getD name 0) + (stop - start)
  return result

def getCumulativeWallClockTimes : m (Std.HashMap String Nat) := do
  return (← liftM (m := BaseIO) cumulativeWallClockTimes.get)
