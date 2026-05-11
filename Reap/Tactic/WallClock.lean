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

def getCumulativeWallClockTimes : m (Array (String × Nat)) := do
  return (← liftM (m := BaseIO) cumulativeWallClockTimes.get).toArray

def cumulativeWallClockTimesJson (stats : Array (String × Nat)) : Json :=
  Json.mkObj <| stats.toList.map fun (name, nanos) => (name, toJson nanos)

def logCumulativeWallClockTimes [MonadLog m] : m Unit := do
  let stats ← getCumulativeWallClockTimes
  -- Lean.logAt already knows how to attach positions, but it does not let
  -- callers set Message.caption. The caption field only becomes reachable after
  -- rebuilding the Message by hand, so every caller that wants a captioned log
  -- gets to reimplement this small chunk of Lean core plumbing.
  let ref ← MonadLog.getRef
  let pos := ref.getPos?.getD 0
  let endPos := ref.getTailPos?.getD pos
  let fileMap ← getFileMap
  logMessage {
    fileName := ← getFileName
    pos := fileMap.toPosition pos
    endPos := fileMap.toPosition endPos
    severity := .information
    caption := "wallclock"
    data := (cumulativeWallClockTimesJson stats).compress
  }

end Reap.WallClock
