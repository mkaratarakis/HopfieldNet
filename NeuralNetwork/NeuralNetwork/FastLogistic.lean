import HopfieldNet.CReals.CRealsFast

/-!
# Executable logistic (FastReal)

`TwoState.logisticProb` is defined over `ℝ` for analysis/proofs. For **computation** we use
`Computable.Fast.FastReal` (dyadic interval arithmetic).

Since reciprocal/division is only partially computable in general, we expose the logistic as a
*partial approximator* returning `Option Ball` at each requested precision.
-/

namespace NeuralNetwork
namespace FastLogistic

open Computable.Fast

/-! ## Logistic as a partial approximator -/

def logisticDenom (x : FastReal) : FastReal :=
  (1 : FastReal) + FastReal.exp (-x)

def logistic? (x : FastReal) : ℕ → Option Ball :=
  FastReal.inv? (logisticDenom x)

/-!
Convenience: logistic applied to an affine form `a * x + b`.
This is useful for Gibbs probabilities which often look like `logistic(β * ΔE)`.
-/

def logisticAffine? (a x b : FastReal) : ℕ → Option Ball :=
  logistic? (a * x + b)

end FastLogistic
end NeuralNetwork
