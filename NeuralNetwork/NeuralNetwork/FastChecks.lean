import NeuralNetwork.NeuralNetwork.FastMarkovMatrix

/-!
# Executable sanity checks (FastReal / Ball)

This file provides small computable “checkers” over the explicit matrix/vector tables:

- row-sum enclosures (does a row sum enclose 1?),
- basic invariance check for a probability vector: compute `(πP - π)` as `Ball`s.

These are **not proofs**; they are executable diagnostics / certificates for concrete instances.
-/

namespace NeuralNetwork
namespace FastChecks

open Computable.Fast

/-- Compute `prec` used by FastReal evaluation at index `n`. -/
@[inline] def precOf (n : ℕ) : Int := -((n : Int) + 2)

@[inline] def dyadicTwoPow (e : Int) : Computable.Fast.Dyadic :=
  ⟨1, e⟩

@[inline] def dyadicZero : Computable.Fast.Dyadic :=
  ⟨0, 0⟩

def ballSub (x y : Ball) (prec : Int) : Ball :=
  Ball.add x (Ball.neg y) prec

def ballSum (xs : List Ball) (prec : Int) : Ball :=
  xs.foldl (fun acc b => Ball.add acc b prec) Ball.zero

/-- Does the interval enclosure for `x` contain the point value `q`? -/
def ballContainsDyadic (x : Ball) (q : Computable.Fast.Dyadic) : Bool :=
  (x.lo ≤ q) && (q ≤ x.hi)

def ballContainsOne (x : Ball) : Bool :=
  ballContainsDyadic x (⟨1, 0⟩ : Computable.Fast.Dyadic)

def ballContainsZero (x : Ball) : Bool :=
  ballContainsDyadic x dyadicZero

def ballAbsUpperLe (x : Ball) (tol : Computable.Fast.Dyadic) : Bool :=
  x.absUpper ≤ tol

/-- Check `|x - target| ≤ tol` using `Ball.absUpper`. -/
def ballWithin (x target : Ball) (prec : Int) (tol : Computable.Fast.Dyadic) : Bool :=
  ballAbsUpperLe (ballSub x target prec) tol

/-- Row sum enclosures for a matrix table. -/
def rowSums (M : List (List Ball)) (n : ℕ) : List Ball :=
  let prec := precOf n
  M.map (fun row => ballSum row prec)

/-- For each row, check whether its sum encloses 1. -/
def rowSumsContainOne (M : List (List Ball)) (n : ℕ) : List Bool :=
  (rowSums M n).map ballContainsOne

def rowSumsWithin (M : List (List Ball)) (n : ℕ) (tol : Computable.Fast.Dyadic) : List Bool :=
  let prec := precOf n
  (rowSums M n).map (fun s => ballWithin s Ball.one prec tol)

/-!
## Invariance checker for `π` against a transition matrix `P`

Given a probability vector `π` and a row-stochastic matrix `P`, we compute:
`(πP)_j = ∑_i π_i * P_{i,j}` and then return the list of enclosures for `(πP - π)`.
-/

def dotRow (πrow : List Ball) (col : List Ball) (prec : Int) : Ball :=
  (List.zipWith (fun a b => Ball.mul a b prec) πrow col).foldl (fun acc x => Ball.add acc x prec) Ball.zero

def transpose (M : List (List Ball)) : List (List Ball) :=
  match M with
  | [] => []
  | row0 :: _ =>
      let m := row0.length
      (List.finRange m).map (fun j => M.map (fun row => row.getD j Ball.zero))

def mulVec (π : List Ball) (P : List (List Ball)) (prec : Int) : List Ball :=
  let cols := transpose P
  cols.map (fun col => dotRow π col prec)

def invarianceDelta (π : List Ball) (P : List (List Ball)) (n : ℕ) : List Ball :=
  let prec := precOf n
  let πP := mulVec π P prec
  List.zipWith (fun a b => ballSub a b prec) πP π

def invarianceDeltaWithin (π : List Ball) (P : List (List Ball)) (n : ℕ) (tol : Computable.Fast.Dyadic) : List Bool :=
  let prec := precOf n
  (invarianceDelta π P n).map (fun d => ballWithin d Ball.zero prec tol)

/-- Search for the first `n` in `[n0, n0+steps]` where all row sums are within `2^{-k}` of 1. -/
def findRowSumPrecision?
    (getM : ℕ → Option (List (List Ball))) (n0 steps k : ℕ) : Option ℕ :=
  let tol : Computable.Fast.Dyadic := dyadicTwoPow (-(k : Int))
  let rec go (i : ℕ) : Option ℕ :=
    if _h : i ≥ steps then none
    else
      let n := n0 + i
      match getM n with
      | none => go (i + 1)
      | some M =>
          if (rowSumsWithin M n tol).all (fun b => b) then some n else go (i + 1)
  termination_by steps - i
  decreasing_by
    have hi : i < steps := Nat.lt_of_not_ge _h
    exact Nat.sub_lt_sub_left hi (Nat.lt_succ_self i)
  go 0

/-- Search for the first `n` in `[n0, n0+steps]` where all entries of `(πP-π)` are within `2^{-k}` of 0. -/
def findStationaryPrecision?
    (getπ : ℕ → Option (List Ball)) (getP : ℕ → Option (List (List Ball))) (n0 steps k : ℕ) : Option ℕ :=
  let tol : Computable.Fast.Dyadic := dyadicTwoPow (-(k : Int))
  let rec go (i : ℕ) : Option ℕ :=
    if _h : i ≥ steps then none
    else
      let n := n0 + i
      match getπ n, getP n with
      | some π, some P =>
          if (invarianceDeltaWithin π P n tol).all (fun b => b) then some n else go (i + 1)
      | _, _ => go (i + 1)
  termination_by steps - i
  decreasing_by
    have hi : i < steps := Nat.lt_of_not_ge _h
    exact Nat.sub_lt_sub_left hi (Nat.lt_succ_self i)
  go 0

end FastChecks
end NeuralNetwork
