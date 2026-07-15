/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.NN
import HopfieldNet.CReals.CRealsFast

/-!
# Minimal API: neural-network computations over computable reals

This folder is the minimal executable surface for running the repository's
neural-network tests over **computable reals** (`Computable.Fast.FastReal`,
ball arithmetic over dyadics) instead of `ℚ`.

Comparison of computable reals is undecidable, so a `Decidable (θ ≤ net)`
instance — what the `ℚ` dynamics use — cannot exist. Instead:

* activations are computed with the total, fuel-based `FastReal.compare`:
  balls either separate (strict inequality), are exact radius-`0` points and
  get compared exactly (this decides *ties* such as `net = θ`), or fuel runs
  out and the neuron keeps its current activation;
* every run can be accompanied by an executable **decidedness certificate**
  showing the fuel-exhaustion fallback was never taken (`isStableF`,
  `stabilizeF` report this, `NNtest.decidedRun` checks it per update);
* with integer/dyadic weights and `{0,1}` or `{±1}` activations, every net
  input is an exact dyadic, so every comparison — ties included — is decided
  at the first probe.

`Basic.lean` provides the shared helpers and a generic fueled stabilization
loop for any `NeuralNetwork FastReal (Fin n)`; `NNtest.lean` and `HNtest.lean`
port the two test suites.
-/

open Computable.Fast

namespace Computable.Fast.API

/-- Default fuel for fueled comparisons. Irrelevant for exact (radius-`0`)
inputs, which are decided at the first probe. -/
def defaultFuel : ℕ := 60

/-- Fueled equality test: `some true`/`some false` if decided, `none` if the
balls neither separate nor become exact points within fuel. -/
def eqF (x y : FastReal) (fuel : ℕ := defaultFuel) : Option Bool :=
  (FastReal.compare x y fuel).map (· == Ordering.eq)

/-- Fueled `x ≤ y` test. -/
def leF (x y : FastReal) (fuel : ℕ := defaultFuel) : Option Bool :=
  (FastReal.compare x y fuel).map (· != Ordering.gt)

/-- Binary threshold activation, executable: `1` if `0 ≤ net`, `0` if
`net < 0`, current activation if undecided within fuel. -/
def binaryStep (curr net : FastReal) (fuel : ℕ := defaultFuel) : FastReal :=
  match FastReal.compare net 0 fuel with
  | some Ordering.lt => 0
  | some _ => 1
  | none => curr

/-- Hopfield (`±1`) threshold activation, executable: `1` if `θ ≤ net`,
`-1` if `net < θ`, current activation if undecided within fuel.
This is the fueled twin of `ℚ`'s `if θ ≤ net then 1 else -1`. -/
def signStep (curr net θ : FastReal) (fuel : ℕ := defaultFuel) : FastReal :=
  match FastReal.compare net θ fuel with
  | some Ordering.lt => -1
  | some _ => 1
  | none => curr

/-- Render an activation vector as integers (via fueled sign), for readable
`#eval` output: `some [1, -1, ...]`, or `none` if some sign is undecided. -/
def actsToInts {n : ℕ} (act : Fin n → FastReal) (fuel : ℕ := defaultFuel) :
    Option (List Int) :=
  (List.finRange n).mapM (fun u => FastReal.sign (act u) fuel)

variable {n : ℕ} {NN : NeuralNetwork FastReal (Fin n)}

/-- Fueled stability test: `some true` iff every neuron's update provably
keeps its activation (all comparisons decided). `none` propagation means the
answer is honest — we never claim stability from an undecided comparison. -/
def isStableF (p : Params NN) (s : NN.State) (fuel : ℕ := defaultFuel) :
    Option Bool :=
  (List.finRange n).foldl
    (fun acc u => do
      let b ← acc
      let e ← eqF ((s.Up p u).act u) (s.act u) fuel
      pure (b && e))
    (some true)

/-- Fueled stabilization along the cyclic update sequence `0, 1, …, n-1, 0, …`
(the twin of `ℚ`'s `HopfieldNet_stabilize` with `useq_Fin`).

Returns `(final state, steps taken, certified)`. `certified = true` means the
loop stopped because `isStableF` returned `some true` — i.e. the state is
provably stable with every comparison decided; `false` means `maxSteps` ran
out first. The step count is the twin of `HopfieldNet_conv_time_steps`. -/
def stabilizeF [NeZero n] (p : Params NN) (maxSteps : ℕ) (s : NN.State)
    (steps : ℕ := 0) (fuel : ℕ := defaultFuel) : NN.State × ℕ × Bool :=
  match maxSteps with
  | 0 => (s, steps, false)
  | maxSteps' + 1 =>
    if isStableF p s fuel = some true then
      (s, steps, true)
    else
      stabilizeF p maxSteps'
        (s.Up p ⟨steps % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩)
        (steps + 1) fuel

end Computable.Fast.API
