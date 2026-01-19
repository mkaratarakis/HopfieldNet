import NeuralNetwork.NeuralNetwork.FastStateEnum
import NeuralNetwork.NeuralNetwork.FastSampling

/-!
# Compute-layer trace utilities

This module turns the compute-layer index trajectories into readable configurations:

- `stateAt? i` retrieves the `i`th state in the explicit enumeration.
- `stateToActList` renders a state as a list of activations in explicit site order.
- `traceToActLists?` maps a trajectory of indices to a trajectory of activation lists.
-/

namespace NeuralNetwork
namespace FastTrace

open NeuralNetwork.FastFiniteEvalExplicit
open NeuralNetwork.FastStateEnum
open TwoState

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]
variable [FiniteEnum U]

abbrev NNQ : NeuralNetwork ℚ U ℚ := TwoState.SymmetricBinary ℚ U

def enumSites : List U :=
  FiniteEnum.enum (α := U)

def enumStates : List (NNQ (U := U)).State :=
  FiniteEnum.enum (α := (NNQ (U := U)).State)

/-- A computable fallback state (all activations = 1). -/
def defaultState : (NNQ (U := U)).State :=
{ act := fun _ => (1 : ℚ)
  hp := by
    intro _u
    -- `pact a := a = 1 ∨ a = -1` for SymmetricBinary
    simp [NNQ, TwoState.SymmetricBinary] }

def stateAt? (i : Nat) : Option (NNQ (U := U)).State :=
  let es := enumStates (U := U)
  if _h : i < es.length then
    some (es.getD i (defaultState (U := U)))
  else
    none

/-- Render a state as a list of activations in `enumSites` order. -/
def stateToActList (s : (NNQ (U := U)).State) : List ℚ :=
  (enumSites (U := U)).map (fun u => s.act u)

def traceToActLists? (idxs : List Nat) : Option (List (List ℚ)) := do
  idxs.mapM (fun i => do
    let s ← stateAt? (U := U) i
    pure (stateToActList (U := U) s))

end FastTrace
end NeuralNetwork
