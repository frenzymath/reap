module
public meta import Lean

public meta section

open Lean Elab Tactic

namespace Reap.WallClock

initialize wallClockLogFile : IO.Ref (Option IO.FS.Handle) ← IO.mkRef none

variable {m : Type _ → Type _} [Monad m] [MonadLiftT IO m]

def appendLogRecord (record : Json) : m Unit := liftM (m := IO) do
  if let some f ← wallClockLogFile.get then
    f.putStrLn record.compress
    f.flush

def openLogFile (path : System.FilePath) : m Unit := liftM (m := IO) do
  let f ← IO.FS.Handle.mk path .append
  wallClockLogFile.set f

def withLogWallClockTime {α : Type _} (name : String) (extraFun : α → Json) (act : m α) : m α := do
  let start ← IO.monoNanosNow.toIO
  let result ← act
  let stop ← IO.monoNanosNow.toIO
  let record := json%{
    name: $name,
    start: $start,
    stop: $stop,
    extra: $(extraFun result)
  }
  appendLogRecord record
  return result
