module
public import Lean
public meta section
open Lean
namespace Array

def mapIdxM' {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : Nat → α → m β) (as : Array α) : m (Array β) :=
  as.mapIdxM fun i a => f i a

def mapIdx' {α : Type u} {β : Type v} (f : Nat → α → β) (as : Array α) : Array β :=
  Id.run <| as.mapIdxM' f

end Array
