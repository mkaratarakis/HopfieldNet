import NeuralNetwork.NeuralNetwork.FastFiniteEvalExplicit
import NeuralNetwork.NeuralNetwork.FastHopfieldEnergy
import NeuralNetwork.NeuralNetwork.FastStateEnum

/-!
# Executable partition function and Boltzmann probabilities (TwoState SymmetricBinary ℚ)

This is the compute-layer counterpart of the proof-layer Boltzmann distribution.

Given:
- an explicit enumeration of sites (`FiniteEnum U`),
- the computable Hopfield Hamiltonian over `ℚ`,

we can compute:
- the partition function \(Z\),
- the Boltzmann probability \(π(s)\),

as certified `FastReal` enclosures (`Option Ball` at a requested precision).
-/

namespace NeuralNetwork
namespace FastBoltzmannEval

open Computable.Fast
open NeuralNetwork.FastFiniteEvalExplicit
open NeuralNetwork.FastHopfieldEnergy
open NeuralNetwork.FastStateEnum
open TwoState

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

abbrev NNQ : NeuralNetwork ℚ U ℚ := TwoState.SymmetricBinary ℚ U

variable [FiniteEnum U]

/-- Energy as a `FastReal` (via `ℚ ↪ FastReal`). -/
def energyFast (p : Params (NNQ (U := U))) (s : (NNQ (U := U)).State) : FastReal :=
  Computable.Fast.FastReal.ofRat (hamiltonianQ (U := U) p s)

/-- Partition function \(Z = \sum_s \exp(-β E(s))\). -/
def partitionFunction (β : FastReal) (p : Params (NNQ (U := U))) : FastReal :=
  FastFiniteEvalExplicit.partitionFunction (ι := (NNQ (U := U)).State) β (energyFast (U := U) p)

/-- Boltzmann probability \(π(s)\) as a partial certified enclosure. -/
def probability? (β : FastReal) (p : Params (NNQ (U := U))) (s : (NNQ (U := U)).State) :
    ℕ → Option Ball :=
  FastFiniteEvalExplicit.probability? (ι := (NNQ (U := U)).State) β (energyFast (U := U) p) s

end FastBoltzmannEval
end NeuralNetwork
