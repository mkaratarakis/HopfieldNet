import NeuralNetwork.NeuralNetwork.FastBoltzmannEval
import NeuralNetwork.NeuralNetwork.FastRandomScan
import NeuralNetwork.NeuralNetwork.FastStateEnum

/-!
# Executable Markov matrices and probability vectors (FastReal)

This file packages the compute-layer objects into explicit finite tables:

- a transition matrix as `List (List Ball)` (rows/cols ordered by an explicit enumeration),
- a probability vector as `List Ball`.

Everything here is **computable** provided the underlying kernels return `Option Ball`
at a requested precision.
-/

namespace NeuralNetwork
namespace FastMarkovMatrix

open Computable.Fast
open NeuralNetwork.FastFiniteEvalExplicit

variable {α : Type} [FiniteEnum α]

def enum : List α := FiniteEnum.enum (α := α)

def matrixOfKernel? (k : α → α → ℕ → Option Ball) (n : ℕ) : Option (List (List Ball)) :=
  (enum (α := α)).mapM (fun a =>
    (enum (α := α)).mapM (fun b => k a b n))

def vectorOfPMF? (p : α → ℕ → Option Ball) (n : ℕ) : Option (List Ball) :=
  (enum (α := α)).mapM (fun a => p a n)

/-!
## Specialization: SymmetricBinary ℚ
-/

open TwoState
open NeuralNetwork.FastRandomScan
open NeuralNetwork.FastBoltzmannEval
open NeuralNetwork.FastStateEnum

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U] [FiniteEnum U]

abbrev NNQ : NeuralNetwork ℚ U ℚ := TwoState.SymmetricBinary ℚ U

/-- Explicit (computable) enumeration of states. -/
def enumStates : List (NNQ (U := U)).State :=
  FiniteEnum.enum (α := (NNQ (U := U)).State)

/-- Random-scan transition matrix (Ball enclosures) at precision `n`. -/
def randomScanMatrix? (β : FastReal) (p : Params (NNQ (U := U))) (n : ℕ) :
    Option (List (List Ball)) :=
  matrixOfKernel? (α := (NNQ (U := U)).State)
    (fun s s' => NeuralNetwork.FastRandomScan.randomScanEntry? (NN := NNQ (U := U)) β p s s') n

/-- Boltzmann probability vector π(s) (Ball enclosures) at precision `n`. -/
def boltzmannVec? (β : FastReal) (p : Params (NNQ (U := U))) (n : ℕ) :
    Option (List Ball) :=
  vectorOfPMF? (α := (NNQ (U := U)).State)
    (fun s => NeuralNetwork.FastBoltzmannEval.probability? (U := U) β p s) n

end FastMarkovMatrix
end NeuralNetwork
