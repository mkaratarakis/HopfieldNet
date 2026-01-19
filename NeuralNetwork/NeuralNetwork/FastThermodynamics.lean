import NeuralNetwork.NeuralNetwork.FastBoltzmannEval
import NeuralNetwork.NeuralNetwork.FastMarkovMatrix

/-!
# Executable thermodynamics (FastReal / Ball)

This module provides **computable**, interval-certified enclosures for:

- `log Z` (log partition function),
- free energy in the normalized units \(F = -kBT \log Z\) (user supplies `kBT`), and
- Shannon entropy in units \(k_B = 1\): \(S = -\sum_s p(s)\log p(s)\).

All functions are *partial* (`Option`) because `log` requires certified positivity
and division requires certified separation from `0`.
-/

namespace NeuralNetwork
namespace FastThermodynamics

open Computable.Fast
open NeuralNetwork.FastFiniteEvalExplicit

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U] [FiniteEnum U]

abbrev NNQ : NeuralNetwork ℚ U ℚ := TwoState.SymmetricBinary ℚ U

/-- `log Z` where `Z = ∑ exp(-β E(s))` is computed via `FastBoltzmannEval.partitionFunction`. -/
def logPartition? (β : FastReal) (p : Params (NNQ (U := U))) : ℕ → Option Ball :=
  FastReal.log? (NeuralNetwork.FastBoltzmannEval.partitionFunction (U := U) β p)

/-- Free energy in "kBT units": \(F = -(kBT)\log Z\). -/
def freeEnergyKBT? (β : FastReal) (p : Params (NNQ (U := U))) (kBT : FastReal) :
    ℕ → Option Ball := fun n => do
  let prec : Int := -((n : Int) + 2)
  let lZ ← logPartition? (U := U) β p n
  pure (Ball.neg (Ball.mul (kBT (n + 10)) lZ prec))

/-- Free energy in "β units": \(F = -\log Z / β\) (i.e. `kB = 1`, `T = 1/β`). -/
def freeEnergyBeta? (β : FastReal) (p : Params (NNQ (U := U))) : ℕ → Option Ball := fun n => do
  let prec : Int := -((n : Int) + 2)
  let lZ ← logPartition? (U := U) β p n
  let invβ ← FastReal.inv? β n
  pure (Ball.neg (Ball.mul lZ invβ prec))

/-- Shannon entropy (in units `kB = 1`): \(S = -\sum_s p(s)\log p(s)\). -/
def shannonEntropy? (β : FastReal) (p : Params (NNQ (U := U))) : ℕ → Option Ball := fun n => do
  let ps ← NeuralNetwork.FastMarkovMatrix.boltzmannVec? (U := U) β p n
  let prec : Int := -((n : Int) + 2)
  let mut acc : Ball := Ball.zero
  for q in ps do
    let lq ← Ball.log? q prec
    acc := Ball.add acc (Ball.mul q lq prec) prec
  pure (Ball.neg acc)

end FastThermodynamics
end NeuralNetwork
