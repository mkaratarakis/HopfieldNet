import HopfieldNet.CReals.CRealsFast

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

def finsetSum (s : Finset ι) (f : ι → FastReal) : FastReal :=
  s.fold (fun acc i => acc + f i) 0

@[simp] lemma finsetSum_empty (f : ι → FastReal) :
    finsetSum (ι := ι) (∅ : Finset ι) f = 0 := by
  simp [finsetSum]

def sum (f : ι → FastReal) : FastReal :=
  finsetSum (ι := ι) Finset.univ f

def boltzmannWeight (β : FastReal) (E : FastReal) : FastReal :=
  FastReal.exp (-(β * E))

def partitionFunction (β : FastReal) (E : ι → FastReal) : FastReal :=
  sum (ι := ι) (fun i => boltzmannWeight β (E i))

/--
Boltzmann probability as a partial approximator.

Returns a function `n ↦ Option Ball` (requested-precision-index ↦ certified interval enclosure).
-/
def probability? (β : FastReal) (E : ι → FastReal) (i : ι) : ℕ → Option Ball :=
  let w : FastReal := boltzmannWeight β (E i)
  let Z : FastReal := partitionFunction (ι := ι) β E
  FastReal.div? w Z

end FastFiniteEval
end NeuralNetwork

