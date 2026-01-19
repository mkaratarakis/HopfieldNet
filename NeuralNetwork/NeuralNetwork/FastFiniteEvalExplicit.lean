import HopfieldNet.CReals.CRealsFast
import Mathlib.Data.List.FinRange

/-!
# Executable finite evaluation with an explicit enumeration

Mathlib's `Finset.toList` / `Fintype.elems` can be non-executable (classical) in general.

To get a truly **computable** evaluator, we require the user to provide an explicit `List` enumerating
the finite type. This is the SOTA separation:

- `Fintype` is great for proofs.
- computation needs an *explicit enumeration*.
-/

namespace NeuralNetwork
namespace FastFiniteEvalExplicit

open Computable.Fast

class FiniteEnum (α : Type) : Type where
  enum : List α

namespace FiniteEnum

instance (n : Nat) : FiniteEnum (Fin n) where
  enum := List.finRange n

end FiniteEnum

variable {ι : Type} [FiniteEnum ι]

def sum (f : ι → FastReal) : FastReal :=
  (FiniteEnum.enum (α := ι)).foldl (fun acc i => acc + f i) 0

def boltzmannWeight (β : FastReal) (E : FastReal) : FastReal :=
  FastReal.exp (-(β * E))

def partitionFunction (β : FastReal) (E : ι → FastReal) : FastReal :=
  sum (ι := ι) (fun i => boltzmannWeight β (E i))

def probability? (β : FastReal) (E : ι → FastReal) (i : ι) : ℕ → Option Ball :=
  let w : FastReal := boltzmannWeight β (E i)
  let Z : FastReal := partitionFunction (ι := ι) β E
  FastReal.div? w Z

end FastFiniteEvalExplicit
end NeuralNetwork
