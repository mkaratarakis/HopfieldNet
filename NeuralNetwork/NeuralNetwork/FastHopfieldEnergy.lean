import NeuralNetwork.NeuralNetwork.FastRat
import NeuralNetwork.NeuralNetwork.FastTwoStateGibbs
import NeuralNetwork.NeuralNetwork.TwoState

/-!
# Executable Hopfield energy backend for Gibbs sampling (ℚ → FastReal)

This file provides a fully **computable** `FastEnergyAtSite` instance for the standard
`TwoState.SymmetricBinary` network over `ℚ`.

Design:
- Define the Hopfield Hamiltonian `E : Params NN → NN.State → ℚ` *computably* (no `noncomputable`).
- Embed `ℚ` into `FastReal` via `FastReal.ofRat`.
- Use `updPos`/`updNeg` to produce the two candidate energies at a site.

This avoids relying on the `noncomputable` energy spec in `BoltzmannMachine.lean`.
-/

namespace NeuralNetwork
namespace FastHopfieldEnergy

open Classical
open Finset Matrix NeuralNetwork TwoState
open Computable.Fast

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

local notation "NNQ" => TwoState.SymmetricBinary ℚ U

/-!
## Computable Hopfield Hamiltonian over ℚ

E(s) = -1/2 * ∑ᵢ sᵢ (W s)ᵢ + ∑ᵢ θᵢ sᵢ

where `θᵢ = (p.θ i).get fin0`.
-/

def hamiltonianQ (p : Params NNQ) (s : (TwoState.SymmetricBinary ℚ U).State) : ℚ :=
  let quad : ℚ := ∑ i : U, s.act i * (p.w.mulVec s.act i)
  let θ : U → ℚ := fun i => (p.θ i).get fin0
  (- (1/2 : ℚ) * quad) + ∑ i : U, θ i * s.act i

/-!
## FastEnergyAtSite instance

This immediately makes `FastTwoStateGibbs.probPos?` runnable for SymmetricBinary ℚ.
-/

instance instFastEnergyAtSiteSymmetricBinaryQ :
    FastTwoStateGibbs.FastEnergyAtSite (NN := NNQ) where
  Epos p s u :=
    Computable.Fast.FastReal.ofRat (hamiltonianQ p (TwoState.updPos (NN := NNQ) s u))
  Eneg p s u :=
    Computable.Fast.FastReal.ofRat (hamiltonianQ p (TwoState.updNeg (NN := NNQ) s u))

end FastHopfieldEnergy
end NeuralNetwork
