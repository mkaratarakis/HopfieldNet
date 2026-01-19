import HopfieldNet.CReals.CRealsFast
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Executable finite-state evaluation (FastReal)

This module is the *execution* counterpart to `ComputableRealsBridge.lean`.

For finite state spaces, all thermodynamic quantities reduce to finite sums. We can therefore
compute *approximations* of partition functions / Boltzmann weights using
`Computable.Fast.FastReal` (dyadic interval arithmetic).

Important:
- Division is exposed as a partial approximator (`div?`) because certifying a denominator
  is separated from `0` is not decidable in general at fixed precision.
- In practice, the partition function is strictly positive, so `div?` should succeed
  once enough precision is requested.
-/

namespace NeuralNetwork
namespace FastFiniteEval

open Computable.Fast

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-!
We intentionally avoid `Finset.sum` here: `FastReal` is an executable interval type with `0` and `+`,
but it does not currently carry the full `AddCommMonoid` instance required by `Finset.sum`.

Instead we fold over the explicit list `Finset.univ.toList`. This does not require commutativity/
associativity typeclass assumptions and stays computable whenever the given `Fintype` instance is.
-/

noncomputable def sum (f : ι → FastReal) : FastReal :=
  (Finset.univ : Finset ι).toList.foldl (fun acc i => acc + f i) 0

def boltzmannWeight (β : FastReal) (E : FastReal) : FastReal :=
  FastReal.exp (-(β * E))

noncomputable def partitionFunction (β : FastReal) (E : ι → FastReal) : FastReal :=
  sum (ι := ι) (fun i => boltzmannWeight β (E i))

/--
Boltzmann probability as a partial approximator.

Returns a function `n ↦ Option Ball` (requested-precision-index ↦ certified interval enclosure).
-/
noncomputable def probability? (β : FastReal) (E : ι → FastReal) (i : ι) : ℕ → Option Ball :=
  let w : FastReal := boltzmannWeight β (E i)
  let Z : FastReal := partitionFunction (ι := ι) β E
  FastReal.div? w Z

end FastFiniteEval
end NeuralNetwork
