import NeuralNetwork.NeuralNetwork.FastGibbs
import NeuralNetwork.NeuralNetwork.TwoState

/-!
# Executable one-site Gibbs step for TwoState networks (FastReal)

This file connects:

- the abstract two-state state update combinatorics (`TwoState.updPos`, `TwoState.updNeg`), with
- the executable probability core (`FastGibbs.probPosFromEnergies?`) based on FastReal interval arithmetic.

We stay **backend-agnostic**: you provide a `FastEnergyAtSite` instance computing the two candidate
energies at a site `u` (all other coordinates fixed), and we derive:

- `probPos?` / `probNeg?` as partial approximators (`ℕ → Option Ball`),
- `gibbsEntry?` giving the interval enclosure for the one-step transition probability
  from `s` to a candidate `s'` under the single-site Gibbs update at `u`.

This is the SOTA pattern:
- proofs in `ℝ`/`CReal` via `toReal`,
- computation in `FastReal` with certified enclosures.
-/

namespace NeuralNetwork
namespace FastTwoStateGibbs

open Computable.Fast

variable {R U σ : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype U] [DecidableEq U] [Nonempty U]
variable (NN : NeuralNetwork R U σ) [TwoStateNeuralNetwork NN]
variable [DecidableEq σ]

/-!
## Computable equality on states (when `U` is finite and `σ` is decidable)

This makes kernels like `gibbsEntry?` computable, avoiding `Classical.propDecidable`.
-/

instance : DecidableEq NN.State := by
  intro s t
  -- decide equality by deciding equality of the `act` function pointwise on finite `U`
  by_cases h : ∀ u : U, s.act u = t.act u
  · exact isTrue (NeuralNetwork.ext (NN := NN) h)
  · refine isFalse ?_
    intro hst
    apply h
    intro u
    simp [hst]

/-!
## Interface: Fast energy-at-site

For a fixed state `s` and site `u`, we need the energies of the two candidate states:
`updPos s u` and `updNeg s u`.
-/

class FastEnergyAtSite (NN : NeuralNetwork R U σ) [TwoStateNeuralNetwork NN] : Type where
  /-- `FastReal` energy of the state where site `u` is forced to `σ_pos`. -/
  Epos : Params NN → NN.State → U → FastReal
  /-- `FastReal` energy of the state where site `u` is forced to `σ_neg`. -/
  Eneg : Params NN → NN.State → U → FastReal

variable [FastEnergyAtSite (NN := NN)]

/-! ## Derived probabilities -/

def probPos? (β : FastReal) (p : Params NN) (s : NN.State) (u : U) : ℕ → Option Ball :=
  FastGibbs.probPosFromEnergies? β
    (FastEnergyAtSite.Epos (NN := NN) p s u)
    (FastEnergyAtSite.Eneg (NN := NN) p s u)

def probNeg? (β : FastReal) (p : Params NN) (s : NN.State) (u : U) : ℕ → Option Ball :=
  FastGibbs.probNegFromEnergies? β
    (FastEnergyAtSite.Epos (NN := NN) p s u)
    (FastEnergyAtSite.Eneg (NN := NN) p s u)

/-!
## Derived transition entry for the one-site kernel

This matches the semantics of `TwoState.gibbsUpdate` but produces executable interval enclosures.
-/

def gibbsEntry? (β : FastReal) (p : Params NN) (s : NN.State) (u : U) (s' : NN.State) :
    ℕ → Option Ball :=
  fun n =>
    if _hpos : s' = TwoState.updPos (NN := NN) s u then
      probPos? (NN := NN) β p s u n
    else if _hneg : s' = TwoState.updNeg (NN := NN) s u then
      probNeg? (NN := NN) β p s u n
    else
      some Ball.zero

end FastTwoStateGibbs
end NeuralNetwork
