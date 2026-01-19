import NeuralNetwork.NeuralNetwork.FastCertificates

/-!
# Compute-layer sampling (interval-certified)

We expose a *partial* sampler:

- input: a uniform dyadic `u ∈ [0,1)` and a list of probability enclosures (`Ball`s)
- output: `Option Nat` (the chosen index) or `none` if the intervals are too wide to decide.

This is the right SOTA shape:
- increase precision until sampling becomes decidable,
- keep the proof layer separate.
-/

namespace NeuralNetwork
namespace FastSampling

open Computable.Fast

/-!
## Uniform dyadic from a seed

This is a tiny deterministic RNG adapter: it maps a seed to a dyadic in `[0,1)` with `bits` bits.
It is *not* cryptographically secure; it’s just a reproducible source for demos/tests.
-/

def uniformDyadic (seed bits : Nat) : Computable.Fast.Dyadic :=
  let m : Nat := seed % (Nat.pow 2 bits)
  { man := (Int.ofNat m), exp := -((bits : Int)) }

/-!
## Certified discrete choice from interval weights

Sufficient condition to *certify* that index `i` is selected:
let `Hi_prev = sum_{j<i} hi_j` and `Lo_i = sum_{j≤i} lo_j`.
If `Hi_prev ≤ u < Lo_i`, then **for all exact distributions inside the balls**
the mass before `i` is ≤ `Hi_prev` and the mass up to `i` is ≥ `Lo_i`,
so the inverse-CDF must select `i`.
-/

def sampleIndexAux? (u : Computable.Fast.Dyadic) (ws : List Ball) (i : Nat)
    (lo hi : Computable.Fast.Dyadic) : Option Nat :=
  match ws with
  | [] => none
  | b :: bs =>
      let lo' := lo + b.lo
      let hi' := hi + b.hi
      if (hi ≤ u) && (u < lo') then
        some i
      else
        sampleIndexAux? u bs (i + 1) lo' hi'

def sampleIndex? (u : Computable.Fast.Dyadic) (ws : List Ball) : Option Nat :=
  sampleIndexAux? u ws 0 0 0

def sampleFromEnum? (enum : List α) (ws : List Ball) (u : Computable.Fast.Dyadic) : Option α := do
  match enum with
  | [] => none
  | a0 :: as =>
      if _h : (a0 :: as).length = ws.length then
        let idx ← sampleIndex? u ws
        if _hidx : idx < (a0 :: as).length then
          -- `getD` exists on this Mathlib version; use head as safe fallback
          some ((a0 :: as).getD idx a0)
        else
          none
      else
        none

/-!
## Sampling with a `StationaryWitness`
-/

open NeuralNetwork.FastCertificates

def sampleInitIndex? (w : StationaryWitness) (seed bits : Nat) : Option Nat :=
  sampleIndex? (uniformDyadic seed bits) w.π

def stepIndex? (w : StationaryWitness) (i : Nat) (seed bits : Nat) : Option Nat := do
  if _hi : i < w.P.length then
    let row := w.P.getD i []
    sampleIndex? (uniformDyadic seed bits) row
  else
    none

/-!
## Retry wrappers

If intervals are too wide to decide a sample, we increase the number of bits used for the dyadic
uniform `u` (and keep the witness fixed). This is the intended compute-layer workflow:
increase precision / randomness until the choice becomes unambiguous.
-/

def sampleInitIndexRetryAux (w : StationaryWitness) (seed bits : Nat) : Nat → Option Nat
  | 0 => sampleInitIndex? w seed bits
  | Nat.succ t =>
      match sampleInitIndex? w seed bits with
      | some i => some i
      | none => sampleInitIndexRetryAux w seed (bits + 1) t

def sampleInitIndexRetry? (w : StationaryWitness) (seed bits0 maxIncr : Nat) : Option Nat :=
  sampleInitIndexRetryAux w seed bits0 maxIncr

def stepIndexRetryAux (w : StationaryWitness) (i : Nat) (seed bits : Nat) : Nat → Option Nat
  | 0 => stepIndex? w i seed bits
  | Nat.succ t =>
      match stepIndex? w i seed bits with
      | some j => some j
      | none => stepIndexRetryAux w i seed (bits + 1) t

def stepIndexRetry? (w : StationaryWitness) (i : Nat) (seed bits0 maxIncr : Nat) : Option Nat :=
  stepIndexRetryAux w i seed bits0 maxIncr

/-!
## Multi-step simulation (indices)

We expose a simple simulator that returns a trajectory of indices in the explicit state enumeration.
It is deterministic given the seeds.
-/

@[inline] def seedAt (seed0 : Nat) (t : Nat) : Nat :=
  seed0 + 9973 * t

def simulateIndices? (w : StationaryWitness)
    (steps : Nat)
    (seedInit seedStep : Nat)
    (bits0 maxIncr : Nat) : Option (List Nat) := do
  let i0 ← sampleInitIndexRetry? w seedInit bits0 maxIncr
  let rec go (t : Nat) (i : Nat) : Option (List Nat) :=
    match t with
    | 0 => some [i]
    | Nat.succ t' => do
        let j ← stepIndexRetry? w i (seedAt seedStep t') bits0 maxIncr
        let rest ← go t' j
        return i :: rest
  go steps i0

end FastSampling
end NeuralNetwork
