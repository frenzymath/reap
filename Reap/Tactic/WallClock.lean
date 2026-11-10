module
public meta import Lean
public meta import Reap.Options

public meta section

open Lean Elab Tactic

namespace Reap.WallClock

variable {m : Type _ → Type _} [Monad m] [MonadLiftT IO m]

def appendLogRecord (logConfig : ReapLogConfig) (record : Json) : m Unit := liftM (m := IO) do
  if let some f := logConfig.wallClock then
    f.putStrLn record.compress
    f.flush

def withLogWallClockTime {α : Type _} (logConfig : ReapLogConfig) (name : String)
    (extraFun : α → Json) (act : m α) : m α := do
  let start ← IO.monoNanosNow.toIO
  let result ← act
  let stop ← IO.monoNanosNow.toIO
  let record := json%{
    name: $name,
    start: $start,
    stop: $stop,
    extra: $(extraFun result)
  }
  appendLogRecord logConfig record
  return result
