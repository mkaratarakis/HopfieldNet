import NeuralNetwork.NeuralNetwork.FastRat
import NeuralNetwork.NeuralNetwork.FastTwoStateGibbs

/-!
# From `EnergySpec'` over `ℚ` to executable `FastEnergyAtSite`

This provides the first concrete, end-to-end runnable bridge:

- proofs can be done over `ℚ` (or lifted to `ℝ` via coercions),
- computation of Gibbs probabilities uses `FastReal` interval arithmetic.
-/

namespace NeuralNetwork
namespace FastEnergySpec

open Classical
open Computable.Fast
open NeuralNetwork.FastTwoStateGibbs
open TwoState

variable {U σ : Type}
variable [Fintype U] [DecidableEq U] [Nonempty U]

/-!
## Default instance: any TwoState energy spec on `ℚ`

Given `spec : TwoState.EnergySpec' (NN := NN)` with scalar `R = ℚ`,
we define the executable candidate energies by embedding the exact rationals into `FastReal`.
-/

variable (NN : NeuralNetwork ℚ U σ) [TwoStateNeuralNetwork NN]

instance (spec : TwoState.EnergySpec' (NN := NN)) :
    FastEnergyAtSite (NN := NN) where
  Epos p s u := Computable.Fast.FastReal.ofRat (spec.E p (TwoState.updPos (NN := NN) s u))
  Eneg p s u := Computable.Fast.FastReal.ofRat (spec.E p (TwoState.updNeg (NN := NN) s u))

end FastEnergySpec
end NeuralNetwork
