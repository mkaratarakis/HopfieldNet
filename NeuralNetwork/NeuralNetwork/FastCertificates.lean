import NeuralNetwork.NeuralNetwork.FastChecks
import NeuralNetwork.NeuralNetwork.FastMarkovMatrix
import NeuralNetwork.NeuralNetwork.FastFiniteEvalExplicit

/-!
# Compute-layer certificates

This file defines a small **executable certificate object** packaging:
- a finite-state transition matrix `P` (as `List (List Ball)`),
- a candidate stationary distribution `π` (as `List Ball`),
- a precision index `n` and a tolerance exponent `k` (meaning tolerance \(2^{-k}\)),
- executable verification booleans.

This is not a proof artifact; it is a runtime-checkable certificate for concrete instances.
-/

namespace NeuralNetwork
namespace FastCertificates

open Computable.Fast
open NeuralNetwork.FastChecks
open NeuralNetwork.FastMarkovMatrix
open NeuralNetwork.FastFiniteEvalExplicit
open TwoState

structure StationaryWitness where
  n : ℕ
  k : ℕ
  P : List (List Ball)
  π : List Ball
  rowSumsOk : Bool
  stationaryOk : Bool
deriving Repr

def mkWitness (P : List (List Ball)) (π : List Ball) (n k : ℕ) : StationaryWitness :=
  let tol : Computable.Fast.Dyadic := dyadicTwoPow (-(k : Int))
  let rowSumsOk := (rowSumsWithin P n tol).all (fun b => b)
  let stationaryOk := (invarianceDeltaWithin π P n tol).all (fun b => b)
  { n := n, k := k, P := P, π := π, rowSumsOk := rowSumsOk, stationaryOk := stationaryOk }

def isValid (w : StationaryWitness) : Bool :=
  w.rowSumsOk && w.stationaryOk

/-!
## Specialization: SymmetricBinary ℚ random-scan vs Boltzmann
-/

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]
variable [NeuralNetwork.FastFiniteEvalExplicit.FiniteEnum U]

def witnessAt?
    (β : FastReal) (p : Params (NeuralNetwork.FastMarkovMatrix.NNQ (U := U))) (n k : ℕ) :
    Option StationaryWitness := do
  let P ← randomScanMatrix? (U := U) β p n
  let π ← boltzmannVec? (U := U) β p n
  let w := mkWitness P π n k
  if isValid w then
    some w
  else
    none

def findWitness?
    (β : FastReal) (p : Params (NeuralNetwork.FastMarkovMatrix.NNQ (U := U))) (n0 steps k : ℕ) :
    Option StationaryWitness := do
  let nRow ← findRowSumPrecision?
    (fun n => randomScanMatrix? (U := U) β p n) n0 steps k
  let nStat ← findStationaryPrecision?
    (fun n => boltzmannVec? (U := U) β p n)
    (fun n => randomScanMatrix? (U := U) β p n) n0 steps k
  -- choose the larger precision requirement
  let n := Nat.max nRow nStat
  witnessAt? (U := U) β p n k

end FastCertificates
end NeuralNetwork
