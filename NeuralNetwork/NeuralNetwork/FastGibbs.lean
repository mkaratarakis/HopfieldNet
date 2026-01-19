import NeuralNetwork.NeuralNetwork.FastLogistic

/-!
# Executable two-state Gibbs step (FastReal)

This module provides a minimal, *backend-agnostic* executable interface for two-state Gibbs
updates on finite state spaces, using `Computable.Fast.FastReal`.

Key idea (standard):

Given two candidate energies `E_pos` and `E_neg` (with all other coordinates fixed),
the conditional probability of choosing the `pos` value is

`P(pos) = exp(-β E_pos) / (exp(-β E_pos) + exp(-β E_neg))
        = 1 / (1 + exp(-β (E_neg - E_pos)))`

So we only need `exp` (total) and reciprocal of `1 + exp(..)` (partial).
-/

namespace NeuralNetwork
namespace FastGibbs

open Computable.Fast

/-! ## Probabilities from energy differences -/

def probPosFromEnergies? (β : FastReal) (Epos Eneg : FastReal) : ℕ → Option Ball :=
  let δ : FastReal := Eneg - Epos
  -- `1 / (1 + exp(-β * δ))`
  FastLogistic.logistic? (β * δ)

def probNegFromEnergies? (β : FastReal) (Epos Eneg : FastReal) : ℕ → Option Ball :=
  fun n => do
    let p ← probPosFromEnergies? β Epos Eneg n
    -- NOTE: `Ball` is an interval. We can compute `1 - p` interval-wise.
    -- `Ball` arithmetic lives in `Computable.Fast` and is total.
    -- Use the same precision index for `1` (as a FastReal constant) and subtract.
    let one : Ball := (1 : FastReal) n
    -- `Ball` doesn't currently expose a dedicated `sub`; use `add` + `neg`.
    -- We round at the *requested* precision `n` (converted to an exponent).
    let prec : Int := -((n : Int) + 2)
    return Ball.add one (Ball.neg p) prec

end FastGibbs
end NeuralNetwork
