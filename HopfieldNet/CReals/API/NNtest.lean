/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.CReals.API.Basic
import Mathlib.Tactic.FinCases

/-!
# The `NNCReal` 3-neuron test, executable over computable reals

`NNCReal.lean` defines this network over the *specification* model
`Computable.CReal`; its activation needs `Decidable (0 ≤ input)`, which is
undecidable there, so it cannot be `#eval`ed. This file is the executable
twin over `FastReal`: same weight matrix, same update sequences.

Note that the second update of the first run hits the **exact tie**
`net = 0`: interval refinement alone could never decide it; the exact-point
branch of `FastReal.compare` does.
-/

open Computable.Fast Computable.Fast.API

namespace Computable.Fast.API.NNtest

/-- Weight matrix of the 3-neuron example network (as `test.M` in
`NNCReal.lean`, read over `FastReal`). -/
def M : Matrix (Fin 3) (Fin 3) FastReal :=
  Matrix.of ![![0, 0, 4], ![1, 0, 0], ![(-2), 3, 0]]

/-- The executable twin of the 3-neuron network `test` from `NNCReal.lean`. -/
abbrev NNtestF : NeuralNetwork FastReal (Fin 3) where
  Adj u v := M u v ≠ 0
  Ui := {0, 1}
  Uo := {2}
  Uh := ∅
  hU := by ext x; fin_cases x <;> simp
  hUi := Set.Nonempty.ne_empty ⟨0, Set.mem_insert 0 {1}⟩
  hUo := Set.Nonempty.ne_empty ⟨2, rfl⟩
  hhio := Set.empty_inter _
  κ1 _ := 0
  κ2 _ := 1
  fnet _ w pred _ := w 0 * pred 0 + w 1 * pred 1 + w 2 * pred 2
  fact _ curr net _ := binaryStep curr net
  fout _ act := act
  pact _ := True
  pw _ := True
  hpact _ _ _ _ _ _ _ _ := trivial

/-- Parameters: weights `M`; the threshold (comparison against `0`) is baked
into `binaryStep`; `σ` and `θ` are unused. -/
def pF : Params NNtestF where
  w := M
  hw _ _ h := not_not.mp h
  hw' := trivial
  σ _ := Vector.emptyWithCapacity 0
  θ _ := ⟨#[1], rfl⟩

/-- Initial state `[1, 0, 0]`, as in `NNCReal.lean`. -/
def s0 : NNtestF.State where
  act := ![1, 0, 0]
  hp _ := trivial

lemma s0_onlyUi : s0.onlyUi := by
  intro u hu
  fin_cases u
  · exact absurd (by simp) hu
  · exact absurd (by simp) hu
  · rfl

/-- Run the updates in `order` while checking that every activation
comparison was decided (`some _`) — i.e. that the `none` fallback of
`binaryStep` was never taken. -/
def decidedRun (s : NNtestF.State) (order : List (Fin 3)) : Bool × NNtestF.State :=
  order.foldl
    (fun acc u =>
      let net := acc.2.net pF u
      (acc.1 && (FastReal.compare net 0 defaultFuel).isSome, acc.2.Up pF u))
    (true, s)

/-! ## The runs (update sequences from `NNCReal.lean`) -/

-- Asynchronous updates `u3, u1, u2, u3, u1, u2, u3` (balls, then as integers):
#eval List.ofFn (NeuralNetwork.State.workPhase pF s0 s0_onlyUi [2, 0, 1, 2, 0, 1, 2]).act
#eval actsToInts (NeuralNetwork.State.workPhase pF s0 s0_onlyUi [2, 0, 1, 2, 0, 1, 2]).act

-- Asynchronous updates `u3, u2, u1, u3, u2, u1, u3` (balls, then as integers):
#eval List.ofFn (NeuralNetwork.State.workPhase pF s0 s0_onlyUi [2, 1, 0, 2, 1, 0, 2]).act
#eval actsToInts (NeuralNetwork.State.workPhase pF s0 s0_onlyUi [2, 1, 0, 2, 1, 0, 2]).act

-- Decidedness certificates: every comparison during the runs was decided.
#eval (decidedRun s0 [2, 0, 1, 2, 0, 1, 2]).1  -- expect `true`
#eval (decidedRun s0 [2, 1, 0, 2, 1, 0, 2]).1  -- expect `true`

/-! ## Exact ties, demonstrated directly -/

#eval FastReal.compare ((2 : FastReal) - 2) 0 5   -- expect `some Ordering.eq`
#eval FastReal.compare ((1 : FastReal) + 1) 2 5   -- expect `some Ordering.eq`
#eval FastReal.compare (1 : FastReal) 2 5         -- expect `some Ordering.lt`

end Computable.Fast.API.NNtest
