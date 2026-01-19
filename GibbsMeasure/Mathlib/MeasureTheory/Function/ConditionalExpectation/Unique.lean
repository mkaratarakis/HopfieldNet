import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
import Mathlib.MeasureTheory.Function.SimpleFunc

open scoped ENNReal

namespace MeasureTheory
variable {α : Type*} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure α}

/-! **Uniqueness of the Lebesgue conditional expectation** -/
theorem ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite' (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {f g : α → ℝ≥0∞}
    (hfg_eq : ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ)
    (hfm : AEStronglyMeasurable[m] f μ) (hgm : AEStronglyMeasurable[m] g μ) : f =ᵐ[μ] g := by
  classical
  -- Reduce to `m`-measurable representatives.
  set f0 : α → ℝ≥0∞ := hfm.mk f
  set g0 : α → ℝ≥0∞ := hgm.mk g
  have hf0_meas : Measurable[m] f0 := hfm.measurable_mk
  have hg0_meas : Measurable[m] g0 := hgm.measurable_mk
  have hf_ae : f =ᵐ[μ] f0 := hfm.ae_eq_mk
  have hg_ae : g =ᵐ[μ] g0 := hgm.ae_eq_mk

  -- First show the set-lintegral identity for `f0` and `g0` w.r.t. `μ`.
  have hfg0_eq :
      ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫⁻ x in s, f0 x ∂μ = ∫⁻ x in s, g0 x ∂μ := by
    intro s hs hμs
    have hs0 : MeasurableSet s := hm s hs
    have hf0_f :
        ∫⁻ x in s, f0 x ∂μ = ∫⁻ x in s, f x ∂μ := by
      refine setLIntegral_congr_fun_ae (μ := μ) (f := f0) (g := f) hs0 ?_
      exact (hf_ae.symm.mono fun _ hx _ => hx)
    have hg_g0 :
        ∫⁻ x in s, g x ∂μ = ∫⁻ x in s, g0 x ∂μ := by
      refine setLIntegral_congr_fun_ae (μ := μ) (f := g) (g := g0) hs0 ?_
      exact (hg_ae.mono fun _ hx _ => hx)
    calc
      ∫⁻ x in s, f0 x ∂μ = ∫⁻ x in s, f x ∂μ := hf0_f
      _ = ∫⁻ x in s, g x ∂μ := hfg_eq s hs hμs
      _ = ∫⁻ x in s, g0 x ∂μ := hg_g0

  -- Transfer the set-lintegral identity to the trimmed measure `μ.trim hm`.
  have hfg0_eq_trim :
      ∀ s, MeasurableSet[m] s → (μ.trim hm) s < ∞ →
        ∫⁻ x in s, f0 x ∂μ.trim hm = ∫⁻ x in s, g0 x ∂μ.trim hm := by
    intro s hs hμs_trim
    have hμs : μ s < ∞ := by
      simpa [trim_measurableSet_eq hm hs] using hμs_trim
    have htrim_f0 : ∫⁻ x in s, f0 x ∂μ.trim hm = ∫⁻ x in s, f0 x ∂μ := by
      -- Convert set integrals to integrals w.r.t. restricted measures, then use `lintegral_trim`.
      change (∫⁻ x, f0 x ∂(@Measure.restrict α m (μ.trim hm) s)) =
        (∫⁻ x, f0 x ∂μ.restrict s)
      rw [restrict_trim (μ := μ) hm hs]
      simpa using (lintegral_trim (μ := μ.restrict s) hm hf0_meas)
    have htrim_g0 : ∫⁻ x in s, g0 x ∂μ.trim hm = ∫⁻ x in s, g0 x ∂μ := by
      change (∫⁻ x, g0 x ∂(@Measure.restrict α m (μ.trim hm) s)) =
        (∫⁻ x, g0 x ∂μ.restrict s)
      rw [restrict_trim (μ := μ) hm hs]
      simpa using (lintegral_trim (μ := μ.restrict s) hm hg0_meas)
    -- Now conclude by rewriting everything to `μ`.
    calc
      ∫⁻ x in s, f0 x ∂μ.trim hm
          = ∫⁻ x in s, f0 x ∂μ := htrim_f0
      _ = ∫⁻ x in s, g0 x ∂μ := hfg0_eq s hs hμs
      _ = ∫⁻ x in s, g0 x ∂μ.trim hm := htrim_g0.symm

  -- Apply the sigma-finite uniqueness result on `μ.trim hm`, then transfer back to `μ`.
  have hfg0_trim : f0 =ᵐ[μ.trim hm] g0 :=
    ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (μ := μ.trim hm)
      (f := f0) (g := g0) hf0_meas hg0_meas hfg0_eq_trim
  have hfg0 : f0 =ᵐ[μ] g0 := ae_eq_of_ae_eq_trim (hm := hm) hfg0_trim
  exact hf_ae.trans (hfg0.trans hg_ae.symm)

end MeasureTheory
