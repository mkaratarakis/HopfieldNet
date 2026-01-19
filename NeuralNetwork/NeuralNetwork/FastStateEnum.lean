import NeuralNetwork.NeuralNetwork.FastFiniteEvalExplicit
import NeuralNetwork.NeuralNetwork.TwoState

/-!
# Computable state enumeration for TwoState networks

For the **compute layer**, we avoid relying on `Fintype` enumeration (which can be classical).
Instead, we build explicit lists of configurations from an explicit site enumeration.

In this file we provide:
- an enumeration of Boolean assignments `U → Bool`, built by recursion over an explicit `List U`,
- an enumeration of states for `TwoState.SymmetricBinary ℚ U` by mapping `Bool` to `{ -1, 1 }`.
-/

namespace NeuralNetwork
namespace FastStateEnum

open TwoState
open NeuralNetwork.FastFiniteEvalExplicit

variable {U : Type} [DecidableEq U]

/-- Enumerate all Boolean assignments on a finite site list, by recursion. -/
def enumBoolFuns (sites : List U) : List (U → Bool) :=
  match sites with
  | [] => [fun _ => false]
  | u :: us =>
      let rest := enumBoolFuns us
      rest.flatMap (fun f => [Function.update f u false, Function.update f u true])

/-!
## SymmetricBinary ℚ states

We construct the `State` record (including the `pact` proof) from a `Bool` assignment.
-/

variable [Fintype U] [Nonempty U]

abbrev NNQ : NeuralNetwork ℚ U ℚ := TwoState.SymmetricBinary ℚ U

def actOfBool (b : Bool) : ℚ := if b then (1 : ℚ) else (-1 : ℚ)

def stateOfBoolFun (f : U → Bool) : (NNQ (U := U)).State :=
{ act := fun u => actOfBool (f u)
  hp := by
    intro u
    -- `pact a := a = 1 ∨ a = -1` for SymmetricBinary
    by_cases h : f u
    · simp [NNQ, TwoState.SymmetricBinary, actOfBool, h]
    · simp [NNQ, TwoState.SymmetricBinary, actOfBool, h] }

instance instFiniteEnumStateSymmetricBinaryQ [FiniteEnum U] :
    FiniteEnum (NNQ (U := U)).State where
  enum :=
    let sites := (FiniteEnum.enum (α := U))
    (enumBoolFuns (U := U) sites).map stateOfBoolFun

end FastStateEnum
end NeuralNetwork
