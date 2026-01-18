import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import NeuralNetwork.TwoState
import NeuralNetwork.TSAux
import PhysLean.Thermodynamics.Temperature.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

/-!
# Zero-temperature limit for Two-state Hopfield networks with Gibbs update

This file proves convergence of this kernel to a deterministic zero-temperature
limit as `β → ∞` (equivalently, `T → 0+`).

## Overview

- Zero-temperature limit:
  * `scale_pos f` shows `scale f > 0` for an injective order-embedding `f`.
  * `zeroTempLimitPMF p s u` is the limiting one-step kernel at `T = 0+`, which:
    - moves deterministically to `updPos` if local field is positive,
    - to `updNeg` if negative,
    - and splits 1/2–1/2 between them on a tie.
  * Main theorem:
      `gibbs_update_tends_to_zero_temp_limit f hf p s u`
    states the PMF `gibbsUpdate f p (tempOfBeta b) s u` converges (as `b → ∞`)
    to `zeroTempLimitPMF p s u`, pointwise on states.

## Key definitions and lemmas

- Convergence to zero temperature:
  * `scale_pos f`: positivity of `scale f` under an injective order embedding.
  * `zeroTempLimitPMF p s u : PMF State`: the `T → 0+` limit kernel.
  * Pointwise convergence on the only two reachable states:
      - `gibbs_update_tends_to_zero_temp_limit_apply_updPos`
      - `gibbs_update_tends_to_zero_temp_limit_apply_updNeg`
    and zero limit on any other target state
      - `gibbs_update_tends_to_zero_temp_limit_apply_other`.
  * Main PMF convergence:
      `gibbs_update_tends_to_zero_temp_limit f hf p s u`.

-/

open Finset Matrix NeuralNetwork State Constants Temperature Filter Topology
open scoped ENNReal NNReal BigOperators
open NeuralNetwork

--variable {R U σ : Type}
--variable {R U σ : Type*}
universe uR uU uσ

-- We can also parametrize earlier variables with these universes if desired:
variable {R : Type uR} {U : Type uU} {σ : Type uσ}

/-! ### Convergence
As β → ∞ (i.e., T → 0+), the one–site Gibbs update PMF converges pointwise to the
zero–temperature limit kernel, for any TwoState NN and any order-embedding f. -/

open scoped Topology Filter
open PMF Filter

namespace TwoState
/-
  Reintroduce all required instances (they were shadowed when reopening the namespace),
  so that `U` and `NN` are fixed consistently for `updPos`, `updNeg`, `θ0`, etc.
-/
variable {R U σ : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [DecidableEq U] [Fintype U] [Nonempty U]
variable {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]

/-- Rewrite the 1/0/1/2 piecewise expression by dropping the positive `1/kB` factor
in front of its argument. This aligns the “zero-temperature target” with the
real-limit expression using `c0 := κ * f L`. -/
lemma sign_piecewise_rewrite_with_c0
    {F} [FunLike F R ℝ]
    (f : F)
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (L : R) :
    let κ := scale (R:=R) (U:=U) (σ:=σ) (NN := NN) (f:=f)
    (if 0 < ((κ / kB) * (f L)) then 1
     else if ((κ / kB) * (f L)) < 0 then 0 else (1/2 : ℝ))
    =
    (if 0 < (κ * (f L)) then 1
     else if (κ * (f L)) < 0 then 0 else (1/2 : ℝ)) := by
  intro κ
  have ha : 0 < (kB : ℝ)⁻¹ := inv_pos.mpr kB_pos
  have hrewrite :
      ((κ / kB) * (f L)) = (kB : ℝ)⁻¹ * (κ * (f L)) := by
    simp [div_eq_mul_inv, mul_left_comm, mul_assoc]
  have h := piecewise01half_sign_mul_left_pos
              (a := (kB : ℝ)⁻¹) (v := κ * (f L)) ha
  simpa [hrewrite] using h

/-- κ := scale between the two numeric states (pushed along f) is positive
    under a strictly monotone embedding and the class `m_order`. -/
lemma scale_pos
    {F} [FunLike F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f)
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN] :
    0 < scale (R:=R) (U:=U) (σ:=σ) (NN := NN) (f:=f) := by
  -- TwoStateNeuralNetwork.m_order : m σ_neg < m σ_pos
  have h := (strictMono_of_injective_orderHom (R:=R) (f:=f) hf)
  have himg :
      f (NN.m (TwoStateNeuralNetwork.σ_neg (NN := NN))) <
        f (NN.m (TwoStateNeuralNetwork.σ_pos (NN := NN))) :=
    h (TwoStateNeuralNetwork.m_order (NN := NN))
  exact sub_pos.mpr himg

/-- One-step zero-temperature limit kernel (tie -> 1/2 mixture of updPos/updNeg). -/
noncomputable def zeroTempLimitPMF
    (p : Params NN) (s : NN.State) (u : U) : PMF NN.State :=
  let net := s.net p u
  let θ   := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)
  if h : θ < net then
    PMF.pure (updPos (s:=s) (u:=u))
  else if h' : net < θ then
    PMF.pure (updNeg (s:=s) (u:=u))
  else
    -- tie: 1/2 – 1/2 Bernoulli mixture
    let pHalf : ℝ≥0 := (1/2 : ℝ≥0)
    have hp : pHalf ≤ 1 := by norm_num
    PMF.bernoulli pHalf hp >>= fun b =>
      if b then PMF.pure (updPos (s:=s) (u:=u))
           else PMF.pure (updNeg (s:=s) (u:=u))

/-- Helper: the two updated states differ. -/
private lemma updPos_ne_updNeg (s : NN.State) (u : U) :
    updPos (s:=s) (u:=u) ≠ updNeg (s:=s) (u:=u) := by
  intro h
  have := congrArg (fun st => st.act u) h
  simp [updPos, updNeg, Function.update, TwoStateNeuralNetwork.h_pos_ne_neg] at this

/-
  General limit lemmas for reals, used to analyze the zero-temperature limit.
  These are independent of the neural-network context.
-/
open Real Filter Topology Monotone

/-- As `x → +∞`, `logisticProb x → 1`. -/
lemma logisticProb_tendsto_atTop :
    Tendsto logisticProb atTop (𝓝 (1 : ℝ)) := by
  -- logisticProb x = 1/(1 + exp(-x)); as x→+∞, -x→-∞, so exp(-x)→0, then 1/(1+r)→1
  have hx_neg : Tendsto (fun x : ℝ => -x) atTop atBot :=
    (tendsto_neg_atBot_iff).mpr tendsto_id
  have h_exp : Tendsto (fun x => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hx_neg
  have h_cont : ContinuousAt (fun r : ℝ => (1 : ℝ) / (1 + r)) 0 :=
    (continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num))
  have h_comp :
      Tendsto (fun x => (1 : ℝ) / (1 + Real.exp (-x))) atTop (𝓝 ((1 : ℝ) / (1 + 0))) :=
    h_cont.tendsto.comp h_exp
  unfold logisticProb
  simpa [Real.exp_zero] using h_comp

/-- As `x → -∞`, `logisticProb x → 0`. -/
lemma logisticProb_tendsto_atBot :
    Tendsto logisticProb atBot (𝓝 (0 : ℝ)) := by
  -- 0 ≤ logistic ≤ exp, and exp x → 0 as x→-∞
  have h_le_exp : ∀ x : ℝ, logisticProb x ≤ Real.exp x := by
    intro x
    unfold logisticProb
    have hxpos : 0 < Real.exp (-x) := Real.exp_pos _
    have hz_le : Real.exp (-x) ≤ 1 + Real.exp (-x) := by linarith
    have : (1 : ℝ) / (1 + Real.exp (-x)) ≤ (1 : ℝ) / Real.exp (-x) :=
      one_div_le_one_div_of_le hxpos hz_le
    simpa [one_div, Real.exp_neg] using this
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds) (Real.tendsto_exp_atBot)
      (fun x => logisticProb_nonneg x)
      (fun x => h_le_exp x)

/-- As `T → 0+`, if `c > 0` then `logisticProb (c/T) → 1`. -/
lemma tendsto_logistic_scaled_of_pos {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℝ => logisticProb (c / T)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
  logisticProb_tendsto_atTop.comp (tendsto_c_div_atTop_of_pos hc)

/-- As `T → 0+`, if `c < 0` then `logisticProb (c/T) → 0`. -/
lemma tendsto_logistic_scaled_of_neg {c : ℝ} (hc : c < 0) :
    Tendsto (fun T : ℝ => logisticProb (c / T)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
  logisticProb_tendsto_atBot.comp (tendsto_c_div_atBot_of_neg hc)

/-- As `T → 0+`, if `c = 0` then `logisticProb (c/T)` is constantly `1/2`. -/
lemma tendsto_logistic_scaled_of_eq_zero {c : ℝ} (hc : c = 0) :
    Tendsto (fun T : ℝ => logisticProb (c / T)) (𝓝[>] (0 : ℝ)) (𝓝 ((1 : ℝ) / 2)) := by
  have : (fun T : ℝ => logisticProb (c / T)) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => 1 / 2 := by
    filter_upwards [self_mem_nhdsWithin] with T _
    simp [logisticProb, hc, Real.exp_zero, one_add_one_eq_two]
  exact (tendsto_congr' this).mpr tendsto_const_nhds

/-- As `T → 0+`, `logisticProb (c / T)` tends to `1` if `c > 0`, to `0` if `c < 0`,
and to `1/2` if `c = 0`. -/
lemma tendsto_logistic_scaled
    (c : ℝ) :
    Tendsto (fun T : ℝ => logisticProb (c / T)) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (if 0 < c then 1 else if c < 0 then 0 else 1/2)) := by
  by_cases hcpos : 0 < c
  · simpa [hcpos] using (tendsto_logistic_scaled_of_pos (c:=c) hcpos)
  · by_cases hcneg : c < 0
    · have := tendsto_logistic_scaled_of_neg (c:=c) hcneg
      simpa [hcpos, hcneg] using this
    · have hc0 : c = 0 := le_antisymm (le_of_not_gt hcpos) (le_of_not_gt hcneg)
      simpa [hcpos, hcneg, hc0] using (tendsto_logistic_scaled_of_eq_zero (c:=c) hc0)

/-- On ℝ≥0: as `b → ∞`, `logisticProb (c * b) → 1/0/1/2` depending on the sign of `c`. -/
lemma tendsto_logistic_const_mul_coeNNReal
    (c : ℝ) :
    Tendsto (fun b : ℝ≥0 => logisticProb (c * (b : ℝ))) atTop
      (𝓝 (if 0 < c then 1 else if c < 0 then 0 else 1/2)) := by
  have h_coe : Tendsto (fun b : ℝ≥0 => (b : ℝ)) atTop atTop := by
    refine (Filter.tendsto_atTop_atTop).2 ?_
    intro M
    refine ⟨⟨max 0 (M + 1), by have : 0 ≤ max 0 (M + 1) := le_max_left _ _; exact this⟩, ?_⟩
    intro b hb
    have hBR : (max 0 (M + 1) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have hM1 : (M + 1 : ℝ) ≤ (b : ℝ) := le_trans (le_max_right _ _) hBR
    have : (M : ℝ) ≤ (b : ℝ) := by linarith
    exact this
  by_cases hcpos : 0 < c
  · have hmul := tendsto_mul_const_atTop_atTop_of_pos (c:=c) hcpos
    simpa [hcpos, Function.comp] using
      logisticProb_tendsto_atTop.comp (hmul.comp h_coe)
  · by_cases hcneg : c < 0
    · have hmul := tendsto_mul_const_atTop_atBot_of_neg (c:=c) hcneg
      simpa [hcpos, hcneg, Function.comp] using
        logisticProb_tendsto_atBot.comp (hmul.comp h_coe)
    · have hc0 : c = 0 := le_antisymm (le_of_not_gt hcpos) (le_of_not_gt hcneg)
      have hconst :
          (fun b : ℝ≥0 => logisticProb (c * (b : ℝ))) = fun _ => (1/2 : ℝ) := by
        funext b; simp [hc0, logisticProb, Real.exp_zero, one_add_one_eq_two]
      aesop

/-- Real-valued probability limit P(T) for our model as T → 0+. -/
lemma tendsto_probPos_at_zero
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (_ : Function.Injective f)
    (p : Params NN) (s : NN.State) (u : U) :
    let L : R := (s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)
    Tendsto (fun T : ℝ => probPos (NN := NN) f p ⟨Real.toNNReal T⟩ s u)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (let κ := scale (NN := NN) (f:=f); let c := (κ / kB) * (f L);
          if 0 < c then 1 else if c < 0 then 0 else 1/2)) := by
  intro L
  have h_event :
      (fun T : ℝ => probPos (NN := NN) f p ⟨Real.toNNReal T⟩ s u)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun T : ℝ =>
        logisticProb (((scale (NN := NN) (f:=f)) / kB) * (f L) / T)) := by
    filter_upwards [self_mem_nhdsWithin] with T hTpos
    have hT0 : 0 ≤ T := le_of_lt hTpos
    have : (β ⟨Real.toNNReal T⟩ : ℝ) = 1 / (kB * T) := by
      simp [Temperature.β, Temperature.toReal, Real.toNNReal_of_nonneg hT0, one_div]
    unfold probPos
    simp [this, logisticProb, mul_comm, mul_assoc, div_eq_mul_inv]
    simp_all only [Set.mem_Ioi, one_div, mul_inv_rev, map_sub, true_or, L]
  have hlim :
      Tendsto (fun T : ℝ =>
        logisticProb (((scale (NN := NN) (f:=f)) / kB) * (f L) / T))
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (let κ := scale (NN := NN) (f:=f); let c := (κ / kB) * (f L);
             if 0 < c then 1 else if c < 0 then 0 else 1/2)) :=
    tendsto_logistic_scaled _
  exact (tendsto_congr' h_event).mpr hlim

open PMF

/-- Pointwise evaluation at `updPos`: exact equality with `probPos`. (Fixed bernoulli usage.) -/
lemma gibbsUpdate_apply_updPos
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ]
    (f : F) (p : Params NN) (T : Temperature) (s : NN.State) (u : U) :
    (gibbsUpdate (NN := NN) f p T s u) (updPos (s:=s) (u:=u))
      = ENNReal.ofReal (probPos (NN := NN) f p T s u) := by
  unfold gibbsUpdate
  set pPos : ℝ := probPos (NN := NN) f p T s u
  have hPos_nonneg : 0 ≤ pPos := probPos_nonneg (NN := NN) f p T s u
  have hPos_le_one : pPos ≤ 1 := probPos_le_one (NN := NN) f p T s u
  set q : ℝ≥0 := ⟨pPos, hPos_nonneg⟩
  have hq_le : q ≤ 1 := by
    exact_mod_cast hPos_le_one
  have hne := updPos_ne_updNeg (s:=s) (u:=u)
  have hcoe : (q : ℝ≥0∞) = ENNReal.ofReal pPos := by
    simp [q, pPos, ENNReal.ofReal]
    simp_all only [ne_eq, pPos, q]
    ext : 1
    simp_all only [NNReal.coe_mk, coe_toNNReal', left_eq_sup]
    exact hPos_nonneg
  simp [q, hcoe, PMF.bernoulli_bind_pure_apply_left_of_ne (α:=NN.State) hq_le hne,
        pPos]

/-- Pointwise evaluation at `updNeg`: exact equality with `1 - probPos`. -/
lemma gibbsUpdate_apply_updNeg
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ]
    (f : F) (p : Params NN) (T : Temperature) (s : NN.State) (u : U) :
    (gibbsUpdate (NN := NN) f p T s u) (updNeg (s:=s) (u:=u))
      = ENNReal.ofReal (1 - probPos (NN := NN) f p T s u) := by
  unfold gibbsUpdate
  set pPos : ℝ := probPos (NN := NN) f p T s u
  have hPos_nonneg : 0 ≤ pPos := probPos_nonneg (NN := NN) f p T s u
  have hPos_le_one : pPos ≤ 1 := probPos_le_one (NN := NN) f p T s u
  set q : ℝ≥0 := ⟨pPos, hPos_nonneg⟩
  have hq_le : q ≤ 1 := by
    exact_mod_cast hPos_le_one
  have hne := updPos_ne_updNeg (s:=s) (u:=u)
  have hcoe : (q : ℝ≥0∞) = ENNReal.ofReal pPos := by
    simp [q, pPos, ENNReal.ofReal]
    simp_all only [ne_eq, pPos, q]
    ext : 1
    simp_all only [NNReal.coe_mk, coe_toNNReal', left_eq_sup]
    exact hPos_nonneg
  have hEval :
      ((PMF.bernoulli q hq_le) >>= fun b =>
        if b then PMF.pure (updPos (s:=s) (u:=u)) else PMF.pure (updNeg (s:=s) (u:=u)))
        (updNeg (s:=s) (u:=u))
      = ((1 : ℝ≥0) - q : ℝ≥0) :=
    PMF.bernoulli_bind_pure_apply_right_of_ne (α:=NN.State) hq_le hne
  have h_sub :
      ((1 : ℝ≥0) - q : ℝ≥0) = ⟨1 - pPos, by
        have : 0 ≤ 1 - pPos := sub_nonneg.mpr hPos_le_one
        simpa [q] using this⟩ := by
          simp_all only [ne_eq, not_false_eq_true, bernoulli_bind_pure_apply_right_of_ne,
            ENNReal.coe_sub, ENNReal.coe_one, q, pPos]
          simp_all only [q, pPos]
          ext : 1
          simp_all only [NNReal.coe_sub, NNReal.coe_one, NNReal.coe_mk]
  have hENN :
      ((1 : ℝ≥0) - (q : ℝ≥0) : ℝ≥0∞)
        = ENNReal.ofReal (1 - pPos) := by
    have h1 : 0 ≤ 1 - pPos := sub_nonneg.mpr hPos_le_one
    simp [q, ENNReal.ofReal, pPos]
    rfl
  simpa [q, h_sub, hENN, pPos]

/-- Eventual equality rewriting Gibbs mass at updPos along β → ∞ to ENNReal.ofReal (probPos at T). -/
lemma eventually_eval_updPos_eq_ofReal_probPos
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ]
    (f : F) (p : Params NN) (s : NN.State) (u : U) :
    (fun b : ℝ≥0 => (gibbsUpdate (NN := NN) f p (Temperature.ofβ b) s u) (updPos (s:=s) (u:=u)))
      =ᶠ[atTop]
    (fun b : ℝ≥0 => ENNReal.ofReal (probPos (NN := NN) f p (Temperature.ofβ b) s u)) := by
  refine Filter.Eventually.of_forall ?_
  intro b; simp [gibbsUpdate_apply_updPos]

/-- Eventual equality rewriting Gibbs mass at updNeg along β → ∞ to ENNReal.ofReal (1 - probPos). -/
lemma eventually_eval_updNeg_eq_ofReal_one_sub_probPos
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ]
    (f : F) (p : Params NN) (s : NN.State) (u : U) :
    (fun b : ℝ≥0 => (gibbsUpdate (NN := NN) f p (Temperature.ofβ b) s u) (updNeg (s:=s) (u:=u)))
      =ᶠ[atTop]
    (fun b : ℝ≥0 => ENNReal.ofReal (1 - probPos (NN := NN) f p (Temperature.ofβ b) s u)) := by
  refine Filter.Eventually.of_forall ?_
  intro b; simp [gibbsUpdate_apply_updNeg]

lemma zeroTempLimitPMF_updPos_eval_pos
    (p : Params NN) (s : NN.State) (u : U)
    {net θ : R} (h : θ < net)
    (hnet : net = s.net p u)
    (hθ : θ = (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)) :
    (zeroTempLimitPMF (NN := NN) p s u) (updPos (s:=s) (u:=u)) = 1 := by
  subst hnet; subst hθ
  unfold zeroTempLimitPMF
  simp [h]

lemma zeroTempLimitPMF_updPos_eval_neg
    (p : Params NN) (s : NN.State) (u : U)
    {net θ : R} (h : net < θ)
    (hnet : net = s.net p u)
    (hθ : θ = (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)) :
    (zeroTempLimitPMF (NN := NN) p s u) (updPos (s:=s) (u:=u)) = 0 := by
  subst hnet; subst hθ
  unfold zeroTempLimitPMF
  have h₁ : ¬ ((p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u) < s.net p u) :=
    not_lt.mpr h.le
  have hne : updPos (s:=s) (u:=u) ≠ updNeg (s:=s) (u:=u) :=
    updPos_ne_updNeg (s:=s) (u:=u)
  simp [h, h₁, hne]

lemma zeroTempLimitPMF_updPos_eval_tie
    (p : Params NN) (s : NN.State) (u : U)
    {net θ : R} (h : net = θ)
    (hnet : net = s.net p u)
    (hθ : θ = (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)) :
    (zeroTempLimitPMF (NN := NN) p s u) (updPos (s:=s) (u:=u)) = (1/2 : ℝ≥0∞) := by
  subst hnet; subst hθ
  have h' : s.net p u = (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u) := h
  unfold zeroTempLimitPMF
  have hlt1 : ¬ ((p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u) < s.net p u) := by
    simp [h']
  have hlt2 : ¬ (s.net p u < (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)) := by
    simp [h']
  have hne : updPos (s:=s) (u:=u) ≠ updNeg (s:=s) (u:=u) :=
    updPos_ne_updNeg (s:=s) (u:=u)
  have hp : ( (1/2 : ℝ≥0) ≤ 1 ) := by norm_num
  simp [h', hne]

variable {F} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [DecidableEq U] [Fintype U] [Nonempty U]
variable {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
variable [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]

/-- Core algebra: under θ < net, the scaled difference is positive. -/
lemma pos_of_theta_lt_net
    (f : F) (hf : Function.Injective f)
    (net θ : R) (h : θ < net) :
    0 < ((scale (NN := NN) (f:=f)) / kB) * (f net - f θ) := by
  have hκ : 0 < scale (NN := NN) (f:=f) :=
    scale_pos (R:=R) (U:=U) (σ:=σ) (NN := NN) (f:=f) hf
  have hκdiv : 0 < scale (NN := NN) (f:=f) / kB := div_pos hκ kB_pos
  have hsub : 0 < net - θ := sub_pos.mpr h
  have hfsub : 0 < f (net - θ) := map_pos_of_pos (R:=R) (f:=f) hf hsub
  simpa [map_sub f] using mul_pos hκdiv hfsub

/-- Core algebra: under net<θ, the scaled difference is negative. -/
lemma neg_of_net_lt_theta
    (f : F) (hf : Function.Injective f)
    (net θ : R) (h : net < θ) :
    ((scale (NN := NN) (f:=f)) / kB) * (f net - f θ) < 0 := by
  have hκ : 0 < scale (NN := NN) (f:=f) :=
    scale_pos (R:=R) (U:=U) (σ:=σ) (NN := NN) (f:=f) hf
  have hκdiv : 0 < scale (NN := NN) (f:=f) / kB := div_pos hκ kB_pos
  have hsub : net - θ < 0 := sub_lt_zero.mpr h
  have hfsub : f (net - θ) < 0 := map_neg_of_neg (R:=R) (f:=f) hf hsub
  simpa [map_sub f] using mul_neg_of_pos_of_neg hκdiv hfsub

/-- Tie algebra: equality case. -/
lemma zero_of_net_eq_theta
    (f : F) (net θ : R) (h : net = θ) :
    ((scale (NN := NN) (f:=f)) / kB) * (f net - f θ) = 0 := by
  simp [h]

lemma zeroTemp_target_updPos_as_ofReal_sign
    (f : F) (hf : Function.Injective f)
    (p : Params NN) (s : NN.State) (u : U) :
    let net := s.net p u
    let θ   := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)
    (zeroTempLimitPMF (NN := NN) p s u) (updPos (s:=s) (u:=u)) =
      ENNReal.ofReal
        (if 0 < ((scale (NN := NN) (f:=f)) / kB) * (f net - f θ)
         then 1
         else if ((scale (NN := NN) (f:=f)) / kB) * (f net - f θ) < 0
              then 0
              else (1/2 : ℝ)) := by
  intro net θ
  rcases lt_trichotomy θ net with hlt | heq | hgt
  · -- Case 1: θ < net (positive local field)
    have h_lhs := zeroTempLimitPMF_updPos_eval_pos (NN := NN) p s u hlt rfl rfl
    have h_rhs_arg := pos_of_theta_lt_net (NN := NN) (f:=f) hf net θ hlt
    simp [h_lhs, h_rhs_arg]
  · -- Case 2: θ = net (tie)
    have h_lhs := zeroTempLimitPMF_updPos_eval_tie (NN := NN) p s u heq.symm rfl rfl
    have h_rhs_arg := zero_of_net_eq_theta (NN := NN) (f:=f) net θ heq.symm
    have hhalf : ENNReal.ofReal ((2 : ℝ)⁻¹) = (2 : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      simp
    simp [h_lhs, h_rhs_arg]; ring_nf; aesop
  · -- Case 3: net < θ (negative local field)
    have h_lhs := zeroTempLimitPMF_updPos_eval_neg (NN := NN) p s u hgt rfl rfl
    have h_rhs_arg := neg_of_net_lt_theta (NN := NN) (f:=f) hf net θ hgt
    simp [h_lhs, h_rhs_arg, not_lt.mpr h_rhs_arg.le]

lemma zeroTemp_target_updNeg_as_ofReal_one_sub_sign_pos
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f)
    (p : Params NN) (s : NN.State) (u : U)
    {net θ : R} (hpos : θ < net)
    (hnet : net = s.net p u) (hθ : θ =
      (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)) :
    (zeroTempLimitPMF (NN := NN) p s u) (updNeg (s:=s) (u:=u)) =
      ENNReal.ofReal
        (1 - (if 0 < ((scale (NN := NN) (f:=f)) / kB) * f (net - θ) then 1
              else if ((scale (NN := NN) (f:=f)) / kB) * f (net - θ) < 0 then 0
              else (1/2 : ℝ))) := by
  subst hnet; subst hθ
  have hLpos : 0 < (s.net p u) - (p.θ u).get _ := sub_pos.mpr hpos
  have hfpos : 0 < f ((s.net p u) - (p.θ u).get _) :=
    map_pos_of_pos (R:=R) (f:=f) hf hLpos
  have hκpos : 0 < (scale (NN := NN) (f:=f)) / kB :=
    div_pos (scale_pos (R:=R) (U:=U) (σ:=σ) (NN := NN) (f:=f) hf) kB_pos
  have hprod : 0 <
      ((scale (NN := NN) (f:=f)) / kB) * f ((s.net p u) - (p.θ u).get _) :=
    mul_pos hκpos hfpos
  have hne := updPos_ne_updNeg (s:=s) (u:=u)
  have hnot : ¬ s.net p u < (p.θ u).get _ := not_lt.mpr hpos.le
  simp [zeroTempLimitPMF, hpos]
  simp_all only [sub_pos, map_sub, mul_pos_iff_of_pos_left, ne_eq, not_lt, ↓reduceIte, sub_self, ENNReal.ofReal_zero,
    ite_eq_right_iff, one_ne_zero, imp_false]
  apply Aesop.BuiltinRules.not_intro
  intro a
  simp_all only [not_true_eq_false]

/-! ### Helpers for the `updNeg` zero-temperature targets -/

open scoped ENNReal

/-- Abbreviation: the scaled, pushed-along local-field appearing in the RHS
     of the `updNeg` lemmas. -/
noncomputable def scaledField (f : F) (p : Params NN) (s : NN.State) (u : U) : ℝ :=
  let κ := scale  (NN := NN) (f:=f)
  let L := (s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)
  (κ / kB) * f L

/-- If the scaled field is negative, the inner {1,0,½} collapses to `0`. -/
lemma scaledField_neg_imp_piece_zero
    (_ : F) {x : ℝ} (hx : x < (0 : ℝ)) :
    (if 0 < x then 1 else if x < 0 then 0 else (1/2 : ℝ)) = 0 := by
  have : ¬ 0 < x := not_lt.mpr hx.le
  simp [this, hx]

/-- If the scaled field is exactly `0`, the inner {1,0,½} collapses to `½`. -/
lemma scaledField_zero_imp_piece_half
    {x : ℝ} (hx : x = 0) :
    (if 0 < x then 1 else if x < 0 then 0 else (1/2 : ℝ)) = (1/2 : ℝ) := by
  simp [hx]

/-!  Focused evaluation lemmas for zeroTempLimitPMF at `updNeg`.  -/
lemma zeroTempLimitPMF_updNeg_eval_neg
    (p : Params NN) (s : NN.State) (u : U)
    {net θ : R} (hneg : net < θ)
    (hnet : net = s.net p u)
    (hθ : θ = (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)) :
    (zeroTempLimitPMF (NN := NN) p s u) (updNeg (s:=s) (u:=u)) = 1 := by
  subst hnet; subst hθ
  unfold zeroTempLimitPMF
  have : ¬ ((p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u) < s.net p u) :=
    not_lt.mpr hneg.le
  simp [this, hneg]

lemma zeroTempLimitPMF_updNeg_eval_pos
    (p : Params NN) (s : NN.State) (u : U)
    {net θ : R} (hpos : θ < net)
    (hnet : net = s.net p u)
    (hθ : θ = (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)) :
    (zeroTempLimitPMF (NN := NN) p s u) (updNeg (s:=s) (u:=u)) = 0 := by
  subst hnet; subst hθ
  unfold zeroTempLimitPMF
  have hne : updNeg (NN := NN) (s:=s) (u:=u) ≠ updPos (NN := NN) (s:=s) (u:=u) := by
    have h := updPos_ne_updNeg (NN := NN) (s:=s) (u:=u)
    simpa [ne_comm] using h
  simp [hpos, hne]

lemma zeroTempLimitPMF_updNeg_eval_tie
    (p : Params NN) (s : NN.State) (u : U)
    {net θ : R} (htie : net = θ)
    (hnet : net = s.net p u)
    (hθ : θ = (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)) :
    (zeroTempLimitPMF (NN := NN) p s u) (updNeg (s:=s) (u:=u)) = (1/2 : ℝ≥0∞) := by
  subst hnet; subst hθ
  unfold zeroTempLimitPMF
  have h1 : ¬ ((p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u) <
              s.net p u) := by simp [htie]
  have h2 : ¬ (s.net p u <
              (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)) := by simp [htie]
  have hne := updPos_ne_updNeg (s:=s) (u:=u)
  have hp : ((1/2 : ℝ≥0) ≤ 1) := by norm_num
  simp [htie, hne]

lemma zeroTemp_target_updNeg_as_ofReal_one_sub_sign_neg
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f)
    (p : Params NN) (s : NN.State) (u : U)
    {net θ : R} (hneg : net < θ)
    (hnet : net = s.net p u)
    (hθ : θ = (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)) :
    (zeroTempLimitPMF (NN := NN) p s u) (updNeg (s:=s) (u:=u)) =
      ENNReal.ofReal
        (1 - (if 0 < ((scale (NN := NN) (f:=f)) / kB) * f (net - θ) then 1
              else if ((scale (NN := NN) (f:=f)) / kB) * f (net - θ) < 0 then 0
              else (1/2 : ℝ))) := by
  have hLHS := zeroTempLimitPMF_updNeg_eval_neg (NN := NN) p s u hneg hnet hθ
  subst hnet; subst hθ
  let θ0 := TwoStateNeuralNetwork.θ0 (NN := NN) u
  let κ  := scale (NN := NN) (f:=f)
  let L  : R := s.net p u - (p.θ u).get θ0
  have hL_neg : L < 0 := sub_lt_zero.mpr hneg
  have hfL_neg : f L < 0 := map_neg_of_neg (R:=R) (f:=f) hf hL_neg
  have hκ_pos : 0 < κ := scale_pos (R:=R) (U:=U) (σ:=σ) (NN := NN) (f:=f) hf
  have hκdiv_pos : 0 < κ / kB := div_pos hκ_pos kB_pos
  have hprod_neg : (κ / kB) * f L < 0 := mul_neg_of_pos_of_neg hκdiv_pos hfL_neg
  have hPiece :
      (if 0 < (κ / kB) * f L then 1
       else if (κ / kB) * f L < 0 then 0
       else (1/2 : ℝ)) = 0 :=
    scaledField_neg_imp_piece_zero f hprod_neg
  have hPiece'' :
      (if 0 < (κ / kB) * f (s.net p u - (p.θ u).get θ0) then 1
       else if (κ / kB) * f (s.net p u - (p.θ u).get θ0) < 0 then 0
       else (1/2 : ℝ)) = 0 := by
    simpa [L] using hPiece
  have : (zeroTempLimitPMF (NN := NN) p s u) (updNeg (s:=s) (u:=u)) = 1 := hLHS
  rw [this, hPiece'']
  simp

lemma zeroTemp_target_updNeg_as_ofReal_one_sub_sign_tie
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (_ : Function.Injective f) -- (hf kept for uniform signature; unused here)
    (p : Params NN) (s : NN.State) (u : U)
    {net θ : R} (htie : net = θ)
    (hnet : net = s.net p u)
    (hθ : θ = (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)) :
    (zeroTempLimitPMF (NN := NN) p s u) (updNeg (s:=s) (u:=u)) =
      ENNReal.ofReal
        (1 - (if 0 < ((scale (NN := NN) (f:=f)) / kB) * f (net - θ) then 1
              else if ((scale (NN := NN) (f:=f)) / kB) * f (net - θ) < 0 then 0
              else (1/2 : ℝ))) := by
  have hLHS := zeroTempLimitPMF_updNeg_eval_tie (NN := NN) p s u htie hnet hθ
  subst hnet; subst hθ
  let θ0 := TwoStateNeuralNetwork.θ0 (NN := NN) u
  let κ  := scale (NN := NN) (f:=f)
  let L  : R := s.net p u - (p.θ u).get θ0
  have hL0 : L = 0 := by
    unfold L; simpa using (sub_eq_zero.mpr htie)
  have hPiece :
      (if 0 < (κ / kB) * f L then 1
       else if (κ / kB) * f L < 0 then 0
       else (1/2 : ℝ)) = (1/2 : ℝ) := by
    have : (κ / kB) * f L = 0 := by simp [hL0]
    exact scaledField_zero_imp_piece_half (x := (κ / kB) * f L) this
  have hPiece' :
      (if 0 < (κ / kB) * f (s.net p u - (p.θ u).get θ0) then 1
       else if (κ / kB) * f (s.net p u - (p.θ u).get θ0) < 0 then 0
       else (1/2 : ℝ)) = (1/2 : ℝ) := by
    simpa [L] using hPiece
  have hxArg :
      (κ / kB) * f (s.net p u - (p.θ u).get θ0) = 0 := by
    simp
    simp_all only [one_div, sub_self, map_zero, mul_zero, lt_self_iff_false, ↓reduceIte, or_true,
      L, θ0, κ]
  have hRHS_simp :
      ENNReal.ofReal
        (1 -
          (if 0 < (κ / kB) * f (s.net p u - (p.θ u).get θ0) then 1
           else if (κ / kB) * f (s.net p u - (p.θ u).get θ0) < 0 then 0
           else (1/2 : ℝ)))
        = (1/2 : ℝ≥0∞) :=
    ENNReal.ofReal_one_sub_signPiece_of_zero hxArg
  exact hLHS.trans hRHS_simp.symm

/-- main lemmas. -/
lemma zeroTemp_target_updNeg_as_ofReal_one_sub_sign
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f)
    (p : Params NN) (s : NN.State) (u : U) :
    let net := s.net p u
    let θ := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)
    (zeroTempLimitPMF (NN := NN) p s u) (updNeg (s:=s) (u:=u)) =
      ENNReal.ofReal
        (1 - (if 0 < ((scale (NN := NN) (f:=f)) / kB) * (f (net - θ))
              then 1 else if ((scale (NN := NN) (f:=f)) / kB) *
                (f (net - θ)) < 0 then 0 else (1/2 : ℝ))) := by
  intro net θ
  rcases lt_trichotomy θ net with hpos | hEq | hneg
  · -- positive field
    exact zeroTemp_target_updNeg_as_ofReal_one_sub_sign_pos
            (NN := NN) f hf p s u hpos rfl rfl
  · -- tie (θ = net)
    have : net = θ := hEq.symm
    exact zeroTemp_target_updNeg_as_ofReal_one_sub_sign_tie
            (NN := NN) f hf p s u this rfl rfl
  · -- negative field (net < θ)
    exact zeroTemp_target_updNeg_as_ofReal_one_sub_sign_neg
            (NN := NN) f hf p s u hneg rfl rfl

/-- Real-valued limit along `β (ofβ b) = b`: `probPos` tends to 1/0/1/2 by the sign of `c0`. -/
lemma tendsto_probPos_along_ofβ_to_piecewise
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (p : Params NN) (s : NN.State) (u : U) :
    let L := (s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)
    let c0 : ℝ := (scale (NN := NN) (f:=f)) * (f L)
    Tendsto (fun b : ℝ≥0 => probPos (NN := NN) f p (Temperature.ofβ b) s u)
      atTop
      (𝓝 (if 0 < c0 then 1 else if c0 < 0 then 0 else 1/2)) := by
  intro L c0
  have hβ : ∀ b, (β (Temperature.ofβ b) : ℝ) = b := by intro b; simp
  have h_form :
      ∀ b, probPos (NN := NN) f p (Temperature.ofβ b) s u
            = logisticProb (c0 * (b : ℝ)) := by
    intro b; unfold probPos; simp [L, c0, mul_comm, logisticProb]
  simpa [h_form] using tendsto_logistic_const_mul_coeNNReal c0

/-- Convergence on `updPos`: short proof using the split helpers. -/
lemma gibbs_update_tends_to_zero_temp_limit_apply_updPos
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f)
    (p : Params NN) (s : NN.State) (u : U) :
    Tendsto (fun b : ℝ≥0 =>
      (gibbsUpdate (NN := NN) f p (Temperature.ofβ b) s u) (updPos (s:=s) (u:=u)))
      atTop (𝓝 ((zeroTempLimitPMF (NN := NN) p s u) (updPos (s:=s) (u:=u)))) := by
  have h_target := zeroTemp_target_updPos_as_ofReal_sign (NN := NN) f hf p s u
  have hev := eventually_eval_updPos_eq_ofReal_probPos (NN := NN) f p s u
  set net := s.net p u
  set θ := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)
  set L : R := net - θ
  set c0 : ℝ := (scale (NN := NN) (f:=f)) * (f L)
  have h_real := tendsto_probPos_along_ofβ_to_piecewise (NN := NN) f p s u
  have h_rewrite := sign_piecewise_rewrite_with_c0 (R:=R) (U:=U) (σ:=σ) (NN := NN) (f:=f) L
  have hlim := ENNReal.tendsto_ofReal (by simpa [L, c0, h_rewrite] using h_real)
  have h := (tendsto_congr' hev).mpr hlim
  have h' : Tendsto (fun b : ℝ≥0 =>
      (gibbsUpdate (NN := NN) f p (Temperature.ofβ b) s u) (updPos (s:=s) (u:=u)))
      atTop (𝓝 (ENNReal.ofReal
        (if 0 < ((scale (NN := NN) (f:=f)) / kB) * (f (net - θ))
         then 1 else if ((scale (NN := NN) (f:=f)) / kB) * (f (net - θ)) < 0 then 0 else (1/2 : ℝ)))) := by
    simp_all only [one_div, map_sub, net, θ, L]
  simpa [h_target, net, θ] using h'

/-- Convergence on `updNeg`: short proof using the split helpers. -/
lemma gibbs_update_tends_to_zero_temp_limit_apply_updNeg
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f)
    (p : Params NN) (s : NN.State) (u : U) :
    Tendsto (fun b : ℝ≥0 =>
      (gibbsUpdate (NN := NN) f p (Temperature.ofβ b) s u) (updNeg (s:=s) (u:=u)))
      atTop (𝓝 ((zeroTempLimitPMF (NN := NN) p s u) (updNeg (s:=s) (u:=u)))) := by
  have h_target := zeroTemp_target_updNeg_as_ofReal_one_sub_sign (NN := NN) f hf p s u
  have hev := eventually_eval_updNeg_eq_ofReal_one_sub_probPos (NN := NN) f p s u
  set net := s.net p u
  set θ := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)
  set L : R := net - θ
  set c0 : ℝ := (scale (NN := NN) (f:=f)) * (f L)
  have h_real :=
    tendsto_probPos_along_ofβ_to_piecewise (NN := NN) f p s u
  have h_sub :
      Tendsto (fun b : ℝ≥0 =>
        (1 : ℝ) - probPos (NN := NN) f p (Temperature.ofβ b) s u)
        atTop
        (𝓝 (1 - (if 0 < c0 then 1 else if c0 < 0 then 0 else (1/2)))) :=
    tendsto_const_nhds.sub h_real
  have h_lift :
      Tendsto (fun b : ℝ≥0 =>
        ENNReal.ofReal (1 - probPos (NN := NN) f p (Temperature.ofβ b) s u))
        atTop
        (𝓝 (ENNReal.ofReal (1 - (if 0 < c0 then 1 else if c0 < 0 then 0 else (1/2))))) :=
    ENNReal.tendsto_ofReal h_sub
  have h_rewrite :
      (if 0 < ((scale (NN := NN) (f:=f)) / kB) * (f L) then 1
       else if ((scale (NN := NN) (f:=f)) / kB) * (f L) < 0 then 0 else (1/2 : ℝ))
        =
      (if 0 < c0 then 1 else if c0 < 0 then 0 else (1/2 : ℝ)) := by
    simpa [c0, one_div] using
      sign_piecewise_rewrite_with_c0
        (R:=R) (U:=U) (σ:=σ) (NN := NN) (f:=f) L
  have h_conv :
      Tendsto (fun b : ℝ≥0 =>
        (gibbsUpdate (NN := NN) f p (Temperature.ofβ b) s u) (updNeg (s:=s) (u:=u)))
        atTop
        (𝓝 (ENNReal.ofReal
              (1 - (if 0 < ((scale (NN := NN) (f:=f)) / kB) * (f L)
                     then 1 else if ((scale (NN := NN) (f:=f)) / kB) * (f L) < 0
                                   then 0 else (1/2 : ℝ))))) := by
    have := (tendsto_congr' hev).mpr h_lift
    simp_all only [map_sub, one_div, net, θ, c0, L]
  simp_all only [map_sub, one_div, net, θ, c0, L]

/-- Convergence on any “other” state (neither updPos nor updNeg). -/
lemma gibbs_update_tends_to_zero_temp_limit_apply_other
    {F} [FunLike F R ℝ]
    (f : F)
    (p : Params NN) (s : NN.State) (u : U)
    {state : NN.State}
    (hpos : state ≠ updPos (s := s) (u := u))
    (hneg : state ≠ updNeg (s := s) (u := u)) :
    Tendsto (fun b : ℝ≥0 =>
      (gibbsUpdate (NN := NN) f p (Temperature.ofβ b) s u) state)
      atTop (𝓝 ((zeroTempLimitPMF (NN := NN) p s u) state)) := by
  set net := s.net p u
  set θ := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := NN) u)
  have htarget0 :
      (zeroTempLimitPMF (NN := NN) p s u) state = 0 := by
    by_cases hθnet : θ < net
    · simp [zeroTempLimitPMF, net, θ, hθnet, PMF.pure_apply, hpos]
    · by_cases hnetθ : net < θ
      · simp [zeroTempLimitPMF, net, θ, hθnet, hnetθ, PMF.pure_apply, hneg]
      · -- tie case: θ = net
        -- zeroTempLimitPMF tie branch is the Bernoulli(1/2) mixture over updPos / updNeg.
        have hbind_zero :
          ((PMF.bernoulli (1/2 : ℝ≥0) (by norm_num : (1/2 : ℝ≥0) ≤ 1)) >>= fun b =>
            if b then PMF.pure (updPos (s:=s) (u:=u))
                 else PMF.pure (updNeg (s:=s) (u:=u))) state = 0 :=
          PMF.bernoulli_bind_pure_apply_other
            (α:=NN.State) (by norm_num : (1/2 : ℝ≥0) ≤ 1) hpos hneg
        simpa [zeroTempLimitPMF, net, θ, hθnet, hnetθ] using hbind_zero
  have hev :
      (fun b : ℝ≥0 =>
        (gibbsUpdate (NN := NN) f p (Temperature.ofβ b) s u) state)
      =ᶠ[atTop] (fun _ => (0 : ℝ≥0∞)) := by
    refine Filter.Eventually.of_forall ?_
    intro b
    -- In the "other state" case the Gibbs PMF assigns zero mass.
    simp [gibbsUpdate, hpos, hneg]
  have : Tendsto (fun b : ℝ≥0 =>
      (gibbsUpdate (NN := NN) f p (Temperature.ofβ b) s u) state)
      atTop (𝓝 0) :=
    (tendsto_congr' hev).mpr tendsto_const_nhds
  simpa [htarget0] using this

/-- **Theorem** Pointwise convergence of the one–site Gibbs PMF to the zero-temperature limit PMF,
for every state. This wraps the three evaluation lemmas into a single statement.
The proof proceeds by case analysis on whether
the target state is the positive update, negative update, or some other state, applying
the corresponding specialized convergence results.
-/
theorem gibbs_update_tends_to_zero_temp_limit
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f)
    (p : Params NN) (s : NN.State) (u : U) :
    ∀ state : NN.State,
      Tendsto (fun b : ℝ≥0 =>
        (gibbsUpdate (NN := NN) f p (Temperature.ofβ b) s u) state)
        atTop (𝓝 ((zeroTempLimitPMF (NN := NN) p s u) state)) := by
  intro state
  by_cases hpos : state = updPos (s:=s) (u:=u)
  · subst hpos
    exact gibbs_update_tends_to_zero_temp_limit_apply_updPos
            (NN := NN) f hf p s u
  · by_cases hneg : state = updNeg (s:=s) (u:=u)
    · subst hneg
      exact gibbs_update_tends_to_zero_temp_limit_apply_updNeg
              (NN := NN) f hf p s u
    · exact gibbs_update_tends_to_zero_temp_limit_apply_other
              (NN := NN) f p s u (by simpa using hpos) (by simpa using hneg)

end TwoState
