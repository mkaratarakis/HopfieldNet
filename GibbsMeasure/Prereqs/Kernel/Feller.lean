import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Feller kernels and their action on bounded continuous functions

This file adds the minimal infrastructure we need for Georgii-style *quasilocality*:

- `ProbabilityTheory.Kernel.IsFeller κ`: a (Markov) kernel is **Feller** if it sends bounded
  continuous observables `f` to continuous observables via `x ↦ ∫ f d(κ x)`.
- `ProbabilityTheory.Kernel.continuousAction κ f`: the induced bounded continuous function on the
  source, built from the integral. For Markov kernels this action is a contraction in sup-norm,
  hence defines a continuous linear operator `continuousActionCLM`.

Mathlib currently does not provide a bundled "Feller kernel" interface, so this file is a small
shim and *not* a reimplementation of existing API.
-/

open MeasureTheory
open BoundedContinuousFunction
open scoped Topology

namespace ProbabilityTheory

open scoped ProbabilityTheory

namespace Kernel

variable {α β : Type*} {mα : MeasurableSpace α} [MeasurableSpace β]
variable [TopologicalSpace α] [TopologicalSpace β] [OpensMeasurableSpace β]

/-- A kernel `κ : Kernel α β` is **Feller** if, for every bounded continuous `f : β →ᵇ ℝ`, the map
`a ↦ ∫ b, f b ∂(κ a)` is continuous. -/
class IsFeller (κ : Kernel[mα] α β) : Prop where
  continuous_integral (f : β →ᵇ ℝ) : Continuous fun a => ∫ b, f b ∂(κ a)

section Action

variable {κ : Kernel[mα] α β} [IsMarkovKernel κ] [IsFeller κ]

omit [TopologicalSpace α] [κ.IsFeller] in
lemma integrable_boundedContinuousFunction (f : β →ᵇ ℝ) (a : α) :
    Integrable (fun b : β => f b) (κ a) := by
  -- For a Markov kernel, `κ a` is a probability measure.
  haveI : IsProbabilityMeasure (κ a) := (IsMarkovKernel.isProbabilityMeasure (κ := κ) a)
  -- A bounded continuous function is measurable on an `OpensMeasurableSpace`.
  have hf_meas : Measurable (fun b : β => f b) := f.continuous.measurable
  have hf_ae : AEStronglyMeasurable (fun b : β => f b) (κ a) :=
    hf_meas.aestronglyMeasurable
  -- Dominate by the constant `‖f‖`.
  have hconst : Integrable (fun _ : β => (‖f‖ : ℝ)) (κ a) := by
    simp
  have hbound : ∀ᵐ b ∂(κ a), ‖f b‖ ≤ (‖f‖ : ℝ) := by
    filter_upwards with b
    exact f.norm_coe_le_norm b
  exact Integrable.mono' hconst hf_ae hbound

omit [TopologicalSpace α] [OpensMeasurableSpace β] [κ.IsFeller] in
lemma norm_integral_le_norm (f : β →ᵇ ℝ) (a : α) :
    ‖∫ b, f b ∂(κ a)‖ ≤ ‖f‖ := by
  haveI : IsProbabilityMeasure (κ a) := (IsMarkovKernel.isProbabilityMeasure (κ := κ) a)
  have hbound : ∀ᵐ b ∂(κ a), ‖f b‖ ≤ (‖f‖ : ℝ) := by
    filter_upwards with b
    exact f.norm_coe_le_norm b
  -- `‖∫ f‖ ≤ ‖f‖ * μ.real univ = ‖f‖`.
  have h :=
    MeasureTheory.norm_integral_le_of_norm_le_const (μ := κ a) (f := fun b : β => f b)
      (C := ‖f‖) hbound
  simpa [probReal_univ, one_mul] using h

/-- The action of a Feller Markov kernel on bounded continuous observables. -/
noncomputable def continuousAction (κ : Kernel[mα] α β) [IsMarkovKernel κ] [IsFeller κ] (f : β →ᵇ ℝ) :
    α →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun a => ∫ b, f b ∂(κ a))
    (IsFeller.continuous_integral (κ := κ) f)
    ‖f‖
    (fun a => norm_integral_le_norm (κ := κ) f a)

omit [OpensMeasurableSpace β] in
@[simp] lemma continuousAction_apply (f : β →ᵇ ℝ) (a : α) :
    continuousAction (κ := κ) f a = ∫ b, f b ∂(κ a) := by
  simp [continuousAction]

omit [OpensMeasurableSpace β] in
lemma norm_continuousAction_le (f : β →ᵇ ℝ) :
    ‖continuousAction (κ := κ) f‖ ≤ ‖f‖ := by
  -- This is built into `ofNormedAddCommGroup`.
  simpa [continuousAction] using
    (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      (f := fun a => ∫ b, f b ∂(κ a))
      (hfc := IsFeller.continuous_integral (κ := κ) f)
      (hC := norm_nonneg f)
      (hfC := fun a => norm_integral_le_norm (κ := κ) f a))

/-- The action operator as a continuous linear map on `β →ᵇ ℝ`, valued in `α →ᵇ ℝ`. -/
noncomputable def continuousActionCLM (κ : Kernel[mα] α β) [IsMarkovKernel κ] [IsFeller κ] :
    (β →ᵇ ℝ) →L[ℝ] (α →ᵇ ℝ) :=
  -- First build a linear map, then use the contraction estimate to get continuity.
  let T : (β →ᵇ ℝ) →ₗ[ℝ] (α →ᵇ ℝ) :=
    { toFun := fun f => continuousAction (κ := κ) f
      map_add' := by
        intro f g
        ext a
        have hf : Integrable (fun b : β => f b) (κ a) := integrable_boundedContinuousFunction (κ := κ) f a
        have hg : Integrable (fun b : β => g b) (κ a) := integrable_boundedContinuousFunction (κ := κ) g a
        simp [continuousAction, integral_add hf hg]
      map_smul' := by
        intro c f
        ext a
        have hf : Integrable (fun b : β => f b) (κ a) := integrable_boundedContinuousFunction (κ := κ) f a
        -- `integral_smul` works for Bochner integrals.
        simpa [continuousAction] using (integral_smul c (fun b : β => f b) (μ := κ a)) }
  (T.mkContinuous 1 (by
    intro f
    -- `‖T f‖ ≤ ‖f‖` is the contraction estimate.
    simpa [one_mul] using (norm_continuousAction_le (κ := κ) f)))

@[simp] lemma continuousActionCLM_apply (f : β →ᵇ ℝ) :
    continuousActionCLM (κ := κ) f = continuousAction (κ := κ) f :=
  rfl

end Action

end Kernel

end ProbabilityTheory
