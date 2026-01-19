import NeuralNetwork.NeuralNetwork.FastFiniteEvalExplicit
import NeuralNetwork.NeuralNetwork.FastRat
import NeuralNetwork.NeuralNetwork.FastTwoStateGibbs

/-!
# Fully executable random-scan Gibbs transition entry (FastReal)

Given:
- an explicit `FiniteEnum U` of sites,
- a `FastEnergyAtSite` instance for the model,

we compute the **random-scan** (uniform-site) one-step transition probability entry
`P(s → s')` as a partial interval enclosure (`ℕ → Option Ball`).

This is computable and avoids any `Fintype`/`Finset.toList` classical machinery.
-/

namespace NeuralNetwork
namespace FastRandomScan

open Classical
open Computable.Fast
open NeuralNetwork.FastFiniteEvalExplicit
open NeuralNetwork.FastTwoStateGibbs

variable {R U σ : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [DecidableEq U] [Nonempty U] [Fintype U]
variable (NN : NeuralNetwork R U σ) [TwoStateNeuralNetwork NN]
variable [FiniteEnum U]
variable [DecidableEq σ]
variable [FastEnergyAtSite (NN := NN)]

/-!
We return an `Option Ball` because the underlying one-site probabilities are partial (`inv?`).
-/

def randomScanEntry? (β : FastReal) (p : Params NN) (s s' : NN.State) : ℕ → Option Ball :=
  fun n => do
    let prec : Int := -((n : Int) + 2)
    let sites : List U := FiniteEnum.enum (α := U)
    let denom : Nat := sites.length
    if _h0 : denom = 0 then
      -- invalid enumeration; treat as failure
      none
    else
      -- accumulate the sum of the one-site transition probabilities
      let sumBall ←
        sites.foldlM
          (fun acc u => do
            let pu ← (gibbsEntry? (NN := NN) β p s u s') n
            return Ball.add acc pu prec)
          Ball.zero
      -- multiply by uniform weight 1/denom
      let w : FastReal := Computable.Fast.FastReal.ofRat ((1 : ℚ) / (denom : ℚ))
      return Ball.mul (w n) sumBall prec

end FastRandomScan
end NeuralNetwork
