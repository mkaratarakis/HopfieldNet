import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import GibbsMeasure.Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique

open ENNReal NNReal Filter
open scoped Classical Topology

namespace MeasureTheory
variable {α : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α} [SigmaFinite μ] {f g : α → ℝ≥0∞}
  {s : Set α}

variable (m μ f) in
/-- Lebesgue conditional expectation of an `ℝ≥0∞`-valued function. It is defined as `0` if any of
the following conditions holds:
* `m` is not a sub-σ-algebra of `m₀`,
* `μ` is not σ-finite with respect to `m`.

When `m ≤ m₀` and `μ.trim hm` is σ-finite, this is the Radon–Nikodym derivative of the trimmed
measure `((μ.withDensity f).trim hm)` with respect to `μ.trim hm`. -/
noncomputable def lcondExp : α → ℝ≥0∞ :=
  if hm : m ≤ m₀ then
    if _h : SigmaFinite (μ.trim hm) then
      ((μ.withDensity f).trim hm).rnDeriv (μ.trim hm)
    else 0
  else 0

/-- Lebesgue conditional expectation of an `ℝ≥0∞`-valued function. It is defined as `0` if any of
the following conditions holds:
* `m` is not a sub-σ-algebra of `m₀`,
* `μ` is not σ-finite with respect to `m`. -/
scoped notation μ "⁻[" f "|" m "]" => MeasureTheory.lcondExp m μ f

/-! ### `SFinite` is preserved by trimming -/

instance sFinite_trim {α : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α} (hm : m ≤ m₀)
    [SFinite μ] : SFinite (μ.trim hm) := by
  classical
  rcases (SFinite.out' (μ := μ)) with ⟨μn, hμn_fin, rfl⟩
  refine ⟨?_⟩
  refine ⟨fun n => (μn n).trim hm, ?_, ?_⟩
  · intro n
    -- Each summand is finite, and finiteness is preserved by `trim`.
    haveI : IsFiniteMeasure (μn n) := (hμn_fin n)
    infer_instance
  · -- `trim` commutes with `Measure.sum` on measurable sets.
    refine @Measure.ext _ m _ _ (fun s hs => ?_)
    -- `hs : MeasurableSet[m] s`, so it is also measurable for `m₀`.
    have hs₀ : MeasurableSet[m₀] s := hm s hs
    simp [Measure.sum_apply, trim_measurableSet_eq, hs, hs₀]

omit [SigmaFinite μ] in
lemma lcondExp_of_not_le (hm_not : ¬m ≤ m₀) : μ⁻[f|m] = 0 := by rw [lcondExp, dif_neg hm_not]

omit [SigmaFinite μ] in
lemma lcondExp_of_not_sigmaFinite (hm : m ≤ m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) :
    μ⁻[f|m] = 0 := by rw [lcondExp, dif_pos hm, dif_neg hμm_not]

omit [SigmaFinite μ] in
lemma lcondExp_of_sigmaFinite (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] :
    μ⁻[f|m] = ((μ.withDensity f).trim hm).rnDeriv (μ.trim hm) := by
  simp [lcondExp, dif_pos hm, hμm]

omit [SigmaFinite μ] in
lemma lcondExp_of_measurable (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α → ℝ≥0∞}
    (hf : Measurable[m] f) : μ⁻[f|m] =ᵐ[μ] f := by
  classical
  -- If `f` is `m`-measurable, then `(μ.withDensity f).trim hm = (μ.trim hm).withDensity f`.
  have hμf :
      (μ.withDensity f).trim hm = (μ.trim hm).withDensity f := by
    refine @Measure.ext _ m _ _ (fun s hs => ?_)
    have hs₀ : MeasurableSet[m₀] s := hm s hs
    have h_ind : Measurable[m] (s.indicator f) := (Measurable.indicator hf hs)
    -- Expand both sides using `withDensity_apply` and `lintegral_trim`.
    -- Reduce to the equality of set-lintegrals under `μ` and `μ.trim hm`.
    calc
      ((μ.withDensity f).trim hm) s
          = (μ.withDensity f) s := by simp [trim_measurableSet_eq hm hs]
      _ = ∫⁻ x in s, f x ∂μ := by simp [MeasureTheory.withDensity_apply _ hs₀]
      _ = ∫⁻ x, (s.indicator f) x ∂μ := by
            simpa [MeasureTheory.lintegral_indicator] using
              (MeasureTheory.lintegral_indicator (μ := μ) (s := s) (hs := hs₀) (f := f)).symm
      _ = ∫⁻ x, (s.indicator f) x ∂(μ.trim hm) := by
            simp [lintegral_trim hm h_ind]
      _ = ∫⁻ x in s, f x ∂(μ.trim hm) := by
            simpa [MeasureTheory.lintegral_indicator] using
              (MeasureTheory.lintegral_indicator (μ := μ.trim hm) (s := s) (hs := hs) (f := f))
      _ = ((μ.trim hm).withDensity f) s := by simp [MeasureTheory.withDensity_apply _ hs]
  -- Now `lcondExp` is an RN derivative of a `withDensity` measure, hence equals `f` a.e.
  have h_ae_trim :
      (μ⁻[f|m] : α → ℝ≥0∞) =ᵐ[μ.trim hm] f := by
    -- Unfold `lcondExp` under the σ-finiteness assumptions and rewrite with `hμf`.
    have :
        (μ⁻[f|m] : α → ℝ≥0∞) =
          ((μ.trim hm).withDensity f).rnDeriv (μ.trim hm) := by
      simp [lcondExp, dif_pos hm, hμm, hμf]
    -- Apply `rnDeriv_withDensity` on the σ-finite trimmed measure.
    simpa [this] using (Measure.rnDeriv_withDensity (ν := μ.trim hm) (hf := hf))
  exact ae_eq_of_ae_eq_trim (hm := hm) h_ae_trim

omit [SigmaFinite μ] in
lemma lcondExp_const (hm : m ≤ m₀) (c : ℝ≥0∞) [IsFiniteMeasure μ] :
    μ⁻[fun _ : α => c|m] =ᵐ[μ] fun _ => c := lcondExp_of_measurable hm measurable_const

omit [SigmaFinite μ] in
@[simp]
lemma lcondExp_zero : μ⁻[(0 : α → ℝ≥0∞)|m] =ᵐ[μ] 0 := by
  by_cases hm : m ≤ m₀
  swap; · simp [lcondExp_of_not_le (m := m) (μ := μ) (f := (0 : α → ℝ≥0∞)) hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp [lcondExp_of_not_sigmaFinite (m := m) (μ := μ) (f := (0 : α → ℝ≥0∞)) hm hμm]
  haveI : SigmaFinite (μ.trim hm) := hμm
  simpa using
    (lcondExp_of_measurable (μ := μ) (m := m) (m₀ := m₀) (f := (0 : α → ℝ≥0∞)) hm
      (@measurable_zero _ _ _ (_) _))

omit [SigmaFinite μ] in
lemma measurable_lcondExp : Measurable[m] (μ⁻[f|m]) := by
  by_cases hm : m ≤ m₀
  swap; ·
    simp [lcondExp_of_not_le (m := m) (μ := μ) (f := f) hm]
    exact measurable_const
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; ·
    simp [lcondExp_of_not_sigmaFinite (m := m) (μ := μ) (f := f) hm hμm]
    exact measurable_const
  haveI : SigmaFinite (μ.trim hm) := hμm
  -- `rnDeriv` is measurable.
  simpa [lcondExp, dif_pos hm, hμm] using (Measure.measurable_rnDeriv ((μ.withDensity f).trim hm) (μ.trim hm))

lemma lcondExp_congr_ae (h : f =ᵐ[μ] g) : μ⁻[f|m] =ᵐ[μ] μ⁻[g|m] := by
  by_cases hm : m ≤ m₀
  swap; · simp [lcondExp_of_not_le (m := m) (μ := μ) (f := f) hm,
      lcondExp_of_not_le (m := m) (μ := μ) (f := g) hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp [lcondExp_of_not_sigmaFinite (m := m) (μ := μ) (f := f) hm hμm,
      lcondExp_of_not_sigmaFinite (m := m) (μ := μ) (f := g) hm hμm]
  haveI : SigmaFinite (μ.trim hm) := hμm
  -- Work in the trimmed measure `ν := μ.trim hm` on the smaller σ-algebra `m`.
  let ν : Measure[m] α := μ.trim hm
  let μf : Measure[m] α := (μ.withDensity f).trim hm
  let μg : Measure[m] α := (μ.withDensity g).trim hm
  have hwd : μ.withDensity f = μ.withDensity g := withDensity_congr_ae (μ := μ) h
  have hμfg : μf = μg := by
    simpa [μf, μg] using congrArg (fun (m' : Measure[m₀] α) => m'.trim hm) hwd
  have hμf_ac : μf ≪ ν :=
    (withDensity_absolutelyContinuous (μ := μ) (f := f)).trim hm
  have hμg_ac : μg ≪ ν :=
    (withDensity_absolutelyContinuous (μ := μ) (f := g)).trim hm
  -- Set up Lebesgue decompositions so that `withDensity_rnDeriv_eq` applies.
  haveI : SFinite μf := by infer_instance
  haveI : SFinite μg := by infer_instance
  haveI : μf.HaveLebesgueDecomposition ν := Measure.haveLebesgueDecomposition_of_sigmaFinite μf ν
  haveI : μg.HaveLebesgueDecomposition ν := Measure.haveLebesgueDecomposition_of_sigmaFinite μg ν
  have hμf_eq : ν.withDensity (μf.rnDeriv ν) = μf := Measure.withDensity_rnDeriv_eq μf ν hμf_ac
  have hμg_eq : ν.withDensity (μg.rnDeriv ν) = μg := Measure.withDensity_rnDeriv_eq μg ν hμg_ac
  have h_ae_trim :
      (μf.rnDeriv ν : α → ℝ≥0∞) =ᵐ[ν] (μg.rnDeriv ν : α → ℝ≥0∞) := by
    -- Equality of `withDensity` measures implies equality of densities a.e. on a σ-finite measure.
    have haemeas_f : AEMeasurable (μf.rnDeriv ν) ν :=
      (Measure.measurable_rnDeriv μf ν).aemeasurable
    have haemeas_g : AEMeasurable (μg.rnDeriv ν) ν :=
      (Measure.measurable_rnDeriv μg ν).aemeasurable
    have hwith :
        ν.withDensity (μf.rnDeriv ν) = ν.withDensity (μg.rnDeriv ν) := by
      -- Both sides are equal to `μf = μg`.
      simp [hμfg]
    exact (withDensity_eq_iff_of_sigmaFinite (μ := ν) haemeas_f haemeas_g).1 hwith
  -- Lift the a.e. equality from `μ.trim hm` back to `μ`.
  refine ae_eq_of_ae_eq_trim (hm := hm) ?_
  simpa [lcondExp, dif_pos hm, hμm, ν, μf, μg] using h_ae_trim

lemma lcondExp_of_aemeasurable (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f (μ.trim hm)) : μ⁻[f|m] =ᵐ[μ] f := by
  -- Replace `f` by an `m`-measurable representative.
  have hfg : f =ᵐ[μ] hf.mk f := ae_eq_of_ae_eq_trim (hm := hm) hf.ae_eq_mk
  refine (lcondExp_congr_ae (m := m) (μ := μ) (f := f) (g := hf.mk f) hfg).trans ?_
  -- Now `hf.mk f` is `m`-measurable, so `lcondExp` is a fixed point.
  exact (lcondExp_of_measurable (μ := μ) (m := m) (m₀ := m₀) (f := hf.mk f) hm hf.measurable_mk).trans
    hfg.symm

/-- The lintegral of the conditional expectation `μ⁻[f|hm]` over an `m`-measurable set is equal to
the lintegral of `f` on that set. -/
lemma setLIntegral_lcondExp (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet[m] s) :
    ∫⁻ x in s, (μ⁻[f|m]) x ∂μ = ∫⁻ x in s, f x ∂μ := by
  classical
  -- Work on the trimmed measure space.
  let ν : Measure[m] α := μ.trim hm
  let μf : Measure[m] α := (μ.withDensity f).trim hm
  have hμf_ac : μf ≪ ν :=
    (withDensity_absolutelyContinuous (μ := μ) (f := f)).trim hm
  haveI : SFinite μf := by infer_instance
  haveI : μf.HaveLebesgueDecomposition ν := Measure.haveLebesgueDecomposition_of_sigmaFinite μf ν
  have hμf : ν.withDensity (μf.rnDeriv ν) = μf := Measure.withDensity_rnDeriv_eq μf ν hμf_ac
  have hs₀ : MeasurableSet[m₀] s := hm s hs
  -- Rewrite the left-hand side as an integral w.r.t. `ν = μ.trim hm`.
  have hmeas_ce : Measurable[m] (μ⁻[f|m]) := measurable_lcondExp (μ := μ) (m := m) (m₀ := m₀) (f := f)
  have htrim :
      (∫⁻ x in s, (μ⁻[f|m]) x ∂ν) = ∫⁻ x in s, (μ⁻[f|m]) x ∂μ := by
    -- Use `lintegral_trim` for the measurable function `s.indicator (μ⁻[f|m])`.
    have h_ind : Measurable[m] (s.indicator fun x ↦ (μ⁻[f|m]) x) :=
      (hmeas_ce.indicator hs)
    -- Convert both set integrals to integrals of indicators, then use `lintegral_trim`.
    have hs₀ : MeasurableSet[m₀] s := hm s hs
    calc
      (∫⁻ x in s, (μ⁻[f|m]) x ∂ν)
          = ∫⁻ x, s.indicator (fun x ↦ (μ⁻[f|m]) x) x ∂ν := by
              simpa [MeasureTheory.lintegral_indicator] using
                (MeasureTheory.lintegral_indicator (μ := ν) (s := s) (hs := hs)
                  (f := fun x ↦ (μ⁻[f|m]) x)).symm
      _ = ∫⁻ x, s.indicator (fun x ↦ (μ⁻[f|m]) x) x ∂μ := by
            simpa using (lintegral_trim (μ := μ) hm h_ind)
      _ = (∫⁻ x in s, (μ⁻[f|m]) x ∂μ) := by
            simpa [MeasureTheory.lintegral_indicator] using
              (MeasureTheory.lintegral_indicator (μ := μ) (s := s) (hs := hs₀)
                (f := fun x ↦ (μ⁻[f|m]) x))
  -- Evaluate `ν.withDensity (μf.rnDeriv ν) = μf` on `s`.
  have h_eval :
      ∫⁻ x in s, (μf.rnDeriv ν) x ∂ν = μf s := by
    -- This is exactly `withDensity_apply` on `s`.
    simpa [MeasureTheory.withDensity_apply _ hs] using congrArg (fun m' : Measure[m] α => m' s) hμf
  -- Now compute.
  calc
    ∫⁻ x in s, (μ⁻[f|m]) x ∂μ
        = ∫⁻ x in s, (μ⁻[f|m]) x ∂ν := by symm; exact htrim
    _ = ∫⁻ x in s, (μf.rnDeriv ν) x ∂ν := by
          -- unfold `lcondExp` in the σ-finite case
          -- use `lcondExp_of_sigmaFinite` to avoid `simp` getting stuck on the `if`.
          simp [lcondExp_of_sigmaFinite (μ := μ) (m := m) (m₀ := m₀) (f := f) hm, ν, μf]
    _ = μf s := h_eval
    _ = (μ.withDensity f) s := by simp [μf, trim_measurableSet_eq hm hs]
    _ = ∫⁻ x in s, f x ∂μ := by simp [MeasureTheory.withDensity_apply _ hs₀]

lemma lintegral_lcondExp (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] :
    ∫⁻ x, (μ⁻[f|m]) x ∂μ = ∫⁻ x, f x ∂μ := by
  suffices ∫⁻ x in Set.univ, (μ⁻[f|m]) x ∂μ = ∫⁻ x in Set.univ, f x ∂μ by
    simp_rw [setLIntegral_univ] at this; exact this
  exact setLIntegral_lcondExp hm MeasurableSet.univ

/-- Total probability law using `lcondExp` as conditional probability. -/
lemma lintegral_lcondExp_indicator {Y : α → ℝ≥0∞} (hY : Measurable Y)
    [SigmaFinite (μ.trim hY.comap_le)] {A : Set α} (hA : MeasurableSet A) :
    ∫⁻ x, (μ⁻[(A.indicator fun _ ↦ 1) | MeasurableSpace.comap Y inferInstance]) x ∂μ = μ A := by
  rw [lintegral_lcondExp, lintegral_indicator hA, setLIntegral_const, one_mul]

/-- **Uniqueness of the conditional expectation**

If a function is a.e. `m`-measurable, verifies an integrability condition and has same lintegral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ⁻[f|hm]`. -/
lemma ae_eq_lcondExp_of_forall_setLIntegral_eq (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {f g : α → ℝ≥0∞}
    (hg_eq : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫⁻ x in s, g x ∂μ = ∫⁻ x in s, f x ∂μ)
    (hgm : AEStronglyMeasurable[m] g μ) : g =ᵐ[μ] μ⁻[f|m] := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite' hm (fun s hs hμs => ?_) hgm
    (measurable_lcondExp (μ := μ) (m := m) (m₀ := m₀) (f := f)).aestronglyMeasurable
  rw [hg_eq s hs hμs, setLIntegral_lcondExp hm hs]

lemma lcondExp_bot' [hμ : NeZero μ] (f : α → ℝ≥0∞) :
    μ⁻[f|⊥] = fun _ => (μ Set.univ).toNNReal⁻¹ • ∫⁻ x, f x ∂μ := by
  by_cases hμ_finite : IsFiniteMeasure μ
  swap
  · have h : ¬SigmaFinite (μ.trim bot_le) := by rwa [sigmaFinite_trim_bot_iff]
    rw [not_isFiniteMeasure_iff] at hμ_finite
    rw [lcondExp_of_not_sigmaFinite bot_le h]
    simp only [hμ_finite, ENNReal.toNNReal_top, GroupWithZero.inv_zero, zero_smul]
    rfl
  classical
  haveI : IsFiniteMeasure μ := hμ_finite
  -- On the bottom σ-algebra, measurable functions are constant; compute the constant using
  -- the identity `∫ lcondExp = ∫ f`.
  haveI : SigmaFinite (μ.trim (bot_le : (⊥ : MeasurableSpace α) ≤ m₀)) :=
    (sigmaFinite_trim_bot_iff (μ := μ)).2 (by infer_instance)
  -- First show that `μ⁻[f|⊥]` is a constant function.
  have h_meas : Measurable[⊥] (μ⁻[f|⊥]) :=
    measurable_lcondExp (μ := μ) (m := (⊥ : MeasurableSpace α)) (m₀ := m₀) (f := f)
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, μ⁻[f|⊥] = fun _ => c := by
    classical
    cases isEmpty_or_nonempty α with
    | inl hα =>
        refine ⟨0, ?_⟩
        funext x
        exact (hα.elim x)
    | inr hα =>
        let x0 : α := Classical.choice hα
        let c : ℝ≥0∞ := (μ⁻[f|⊥]) x0
        refine ⟨c, ?_⟩
        funext x
        have hpre : MeasurableSet[⊥] ((μ⁻[f|⊥]) ⁻¹' ({c} : Set ℝ≥0∞)) :=
          h_meas (measurableSet_singleton c)
        have hbot :
            ((μ⁻[f|⊥]) ⁻¹' ({c} : Set ℝ≥0∞) = ∅) ∨
              ((μ⁻[f|⊥]) ⁻¹' ({c} : Set ℝ≥0∞) = Set.univ) :=
          (MeasurableSpace.measurableSet_bot_iff (s := (μ⁻[f|⊥]) ⁻¹' ({c} : Set ℝ≥0∞))).1 hpre
        have hx0 : x0 ∈ (μ⁻[f|⊥]) ⁻¹' ({c} : Set ℝ≥0∞) := by
          simp [c]
        have huniv : (μ⁻[f|⊥]) ⁻¹' ({c} : Set ℝ≥0∞) = Set.univ := by
          rcases hbot with h0 | huniv
          · have : x0 ∈ (∅ : Set α) := by simp [h0] at hx0
            cases this
          · exact huniv
        have hx : x ∈ (μ⁻[f|⊥]) ⁻¹' ({c} : Set ℝ≥0∞) := by simp [huniv]
        simpa [Set.mem_preimage, Set.mem_singleton_iff] using hx
  -- Use the identity on `univ` to compute `c`.
  have h_int :
      ∫⁻ x, (μ⁻[f|⊥]) x ∂μ = ∫⁻ x, f x ∂μ :=
    lintegral_lcondExp (μ := μ) (m := (⊥ : MeasurableSpace α)) (m₀ := m₀) (f := f) bot_le
  have hμuniv_ne_top : μ Set.univ ≠ ⊤ := by
    exact (ne_of_lt (IsFiniteMeasure.measure_univ_lt_top (μ := μ)))
  have hμuniv_ne_zero : μ Set.univ ≠ 0 := by
    haveI : NeZero (μ Set.univ) := by infer_instance
    exact NeZero.ne (μ Set.univ)
  have hinv : μ Set.univ * (μ Set.univ)⁻¹ = (1 : ℝ≥0∞) :=
    ENNReal.mul_inv_cancel hμuniv_ne_zero hμuniv_ne_top
  have hc_eq :
      c = (∫⁻ x, f x ∂μ) * (μ Set.univ)⁻¹ := by
    have hconst : ∫⁻ x, (μ⁻[f|⊥]) x ∂μ = c * μ Set.univ := by
      simp [hc, lintegral_const]
    have hcmul : c * μ Set.univ = ∫⁻ x, f x ∂μ := by
      simpa [hconst] using h_int
    -- Multiply by the inverse of `μ univ` on the right.
    have : c = (c * μ Set.univ) * (μ Set.univ)⁻¹ := by
      symm
      calc
        (c * μ Set.univ) * (μ Set.univ)⁻¹ = c * (μ Set.univ * (μ Set.univ)⁻¹) := by ac_rfl
        _ = c * 1 := by simp [hinv]
        _ = c := by simp
    calc
      c = (c * μ Set.univ) * (μ Set.univ)⁻¹ := this
      _ = (∫⁻ x, f x ∂μ) * (μ Set.univ)⁻¹ := by simp [hcmul]
  -- Rewrite the inverse via `toNNReal` and conclude.
  have h_toNN : ((μ Set.univ).toNNReal : ℝ≥0∞) = μ Set.univ := by
    simp [hμuniv_ne_top]
  have h_toNN_ne_zero : (μ Set.univ).toNNReal ≠ 0 := by
    exact (ENNReal.toNNReal_pos hμuniv_ne_zero hμuniv_ne_top).ne'
  have h_inv_toNN : ((μ Set.univ).toNNReal⁻¹ : ℝ≥0∞) = (μ Set.univ)⁻¹ := by
    calc
      ((μ Set.univ).toNNReal⁻¹ : ℝ≥0∞)
          = ((μ Set.univ).toNNReal : ℝ≥0∞)⁻¹ := by
              simp
      _ = (μ Set.univ)⁻¹ := by simp [h_toNN]
  -- `•` on `ℝ≥0∞` is multiplication by the scalar.
  have hc_final :
      c = (μ Set.univ).toNNReal⁻¹ • ∫⁻ x, f x ∂μ := by
    -- Rewrite scalar multiplication via `ENNReal` and use commutativity.
    rw [hc_eq]
    -- Convert the `ℝ≥0`-smul into multiplication in `ℝ≥0∞`.
    rw [ENNReal.smul_def, smul_eq_mul]
    -- Now close by rewriting the scalar as `(μ univ)⁻¹` and commuting multiplication.
    calc
      (∫⁻ x, f x ∂μ) * (μ Set.univ)⁻¹ = (μ Set.univ)⁻¹ * ∫⁻ x, f x ∂μ := by
        simp [mul_comm]
      _ = ((μ Set.univ).toNNReal⁻¹ : ℝ≥0∞) * ∫⁻ x, f x ∂μ := by
        simp [h_inv_toNN.symm]
    subst hc_eq
    simp_all only [measurable_const, lintegral_const, ne_eq, measure_ne_top, not_false_eq_true,
      Measure.measure_univ_eq_zero, coe_toNNReal, coe_inv]
  -- Finish.
  simp [hc, hc_final]
  -- have h_meas : Measurable[⊥] (μ⁻[f|⊥]) := measurable_lcondExp
  -- obtain ⟨c, h_eq⟩ := measurable_bot_iff.mp h_meas
  -- rw [h_eq]
  -- have h_lintegral : ∫⁻ x, (μ⁻[f|⊥]) x ∂μ = ∫⁻ x, f x ∂μ := lintegral_lcondExp bot_le
  -- simp_rw [h_eq, lintegral_const] at h_lintegral
  -- rw [← h_lintegral, ← smul_assoc, smul_eq_mul, inv_mul_cancel, one_smul]
  -- rw [Ne, ENNReal.toReal_eq_zero_iff, not_or]
  -- exact ⟨NeZero.ne _, measure_ne_top μ Set.univ⟩

lemma lcondExp_bot_ae_eq (f : α → ℝ≥0∞) :
    μ⁻[f|⊥] =ᵐ[μ] fun _ => (μ Set.univ).toNNReal⁻¹ • ∫⁻ x, f x ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · rw [ae_zero]; exact eventually_bot
  · exact .of_forall <| congr_fun (lcondExp_bot' f)

lemma lcondExp_bot [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) : μ⁻[f|⊥] = fun _ => ∫⁻ x, f x ∂μ := by
  refine (lcondExp_bot' f).trans ?_; rw [measure_univ, ENNReal.toNNReal_one, inv_one, one_smul]

lemma lcondExp_add (hf : AEMeasurable f μ) (_ : AEMeasurable g μ) :
    μ⁻[f + g|m] =ᵐ[μ] μ⁻[f|m] + μ⁻[g|m] := by
  by_cases hm : m ≤ m₀
  swap; · simp_rw [lcondExp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [lcondExp_of_not_sigmaFinite hm hμm]; simp
  haveI : SigmaFinite (μ.trim hm) := hμm
  classical
  have hmeas_f : Measurable[m] (μ⁻[f|m]) := measurable_lcondExp
  have hmeas_g : Measurable[m] (μ⁻[g|m]) := measurable_lcondExp
  let hfgFun : α → ℝ≥0∞ := fun x => (μ⁻[f|m]) x + (μ⁻[g|m]) x
  have hfgFun_def :
      hfgFun = fun x => (μ⁻[f|m]) x + (μ⁻[g|m]) x := rfl
  have hsum_meas : Measurable[m] hfgFun := by
    simpa [hfgFun_def] using (hmeas_f.add hmeas_g)
  have hsum_aestr : AEStronglyMeasurable[m] hfgFun μ :=
    hsum_meas.aestronglyMeasurable
  refine
    (ae_eq_lcondExp_of_forall_setLIntegral_eq (μ := μ) (m := m) (m₀ := m₀)
        (f := f + g) (g := hfgFun) hm ?_ hsum_aestr).symm.trans ?_
  · intro s hs hμs
    have hs₀ : MeasurableSet s := hm s hs
    have hindicator :
        s.indicator hfgFun =
          s.indicator (μ⁻[f|m]) + s.indicator (μ⁻[g|m]) := by
      funext x
      by_cases hx : x ∈ s
      · simp [Set.indicator_of_mem, hx, hfgFun_def]
      · simp [Set.indicator_of_notMem, hx, hfgFun_def]
    have h_add_indicator :
        ∫⁻ x, s.indicator hfgFun x ∂μ =
            ∫⁻ x, s.indicator (μ⁻[f|m]) x ∂μ +
              ∫⁻ x, s.indicator (μ⁻[g|m]) x ∂μ := by
      have hmeas_ind_f : Measurable fun x => s.indicator (μ⁻[f|m]) x :=
        (hmeas_f.indicator hs).mono hm le_rfl
      have hmeas_ind_g : Measurable fun x => s.indicator (μ⁻[g|m]) x :=
        (hmeas_g.indicator hs).mono hm le_rfl
      simpa [hindicator] using
        (lintegral_add_left (μ := μ) (hf := hmeas_ind_f)
          (g := fun x => s.indicator (μ⁻[g|m]) x))
    have h_add :
        ∫⁻ x in s, hfgFun x ∂μ =
            ∫⁻ x in s, (μ⁻[f|m]) x ∂μ + ∫⁻ x in s, (μ⁻[g|m]) x ∂μ := by
      simpa [MeasureTheory.lintegral_indicator, hs₀] using h_add_indicator
    have h_indicator_fg :
        s.indicator (fun x => (f + g) x) = s.indicator f + s.indicator g := by
      funext x
      by_cases hx : x ∈ s
      · simp [Set.indicator_of_mem, hx]
      · simp [Set.indicator_of_notMem, hx]
    have h_int_fg :
        ∫⁻ x in s, (f + g) x ∂μ =
            ∫⁻ x in s, f x ∂μ + ∫⁻ x in s, g x ∂μ := by
      have hf_ind : AEMeasurable (s.indicator f) μ := hf.indicator hs₀
      have h_add_indicator :
          ∫⁻ x, (s.indicator f + s.indicator g) x ∂μ =
              ∫⁻ x, s.indicator f x ∂μ + ∫⁻ x, s.indicator g x ∂μ := by
        simpa [Pi.add_apply] using
          (lintegral_add_left' (μ := μ) (hf := hf_ind)
            (g := fun x => s.indicator g x))
      calc
        ∫⁻ x in s, (f + g) x ∂μ
            = ∫⁻ x, s.indicator (fun x => (f + g) x) x ∂μ := by
                symm
                simp [MeasureTheory.lintegral_indicator, hs₀]
        _ = ∫⁻ x, (s.indicator f + s.indicator g) x ∂μ := by
                -- rewrite the integrand using `h_indicator_fg`
                refine lintegral_congr (fun x => ?_)
                simpa using congrFun h_indicator_fg x
        _ = ∫⁻ x, s.indicator f x ∂μ + ∫⁻ x, s.indicator g x ∂μ := h_add_indicator
        _ = ∫⁻ x in s, f x ∂μ + ∫⁻ x in s, g x ∂μ := by
                simp [MeasureTheory.lintegral_indicator, hs₀]
    calc
      ∫⁻ x in s, hfgFun x ∂μ =
          ∫⁻ x in s, (μ⁻[f|m]) x ∂μ + ∫⁻ x in s, (μ⁻[g|m]) x ∂μ := h_add
      _ = ∫⁻ x in s, f x ∂μ + ∫⁻ x in s, g x ∂μ := by
          simp [setLIntegral_lcondExp (μ := μ) (m := m) (m₀ := m₀) (hm := hm) hs]
      _ = ∫⁻ x in s, (f + g) x ∂μ := h_int_fg.symm
  · -- `hfgFun` is definitionally `μ⁻[f|m] + μ⁻[g|m]`
    -- (but with our `scoped notation`, we need parentheses for application)
    show (∀ᵐ x ∂μ, (hfgFun x) = (μ⁻[f|m] + μ⁻[g|m]) x)
    -- unfold `hfgFun` using `hfgFun_def`, then it's pointwise `rfl`
    simp [hfgFun_def]
  -- refine (lcondExp_ae_eq_lcondExpL1 hm _).trans ?_
  -- rw [lcondExpL1_add hf hg]
  -- exact (coeFn_add _ _).trans
  --   ((lcondExp_ae_eq_lcondExpL1 hm _).symm.add (lcondExp_ae_eq_lcondExpL1 hm _).symm)

lemma lcondExp_finset_sum {ι : Type*} {s : Finset ι} {f : ι → α → ℝ≥0∞}
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    μ⁻[∑ i ∈ s, f i|m] =ᵐ[μ] ∑ i ∈ s, μ⁻[f i|m] := by
  induction s using Finset.induction_on with
  | empty => simp [lcondExp_zero]
  | @insert a s' h_not_mem ih =>
    rw [Finset.sum_insert h_not_mem, Finset.sum_insert h_not_mem]
    have ha : AEMeasurable (f a) μ := hf _ (by simp [Finset.mem_insert])
    have hs' :
        ∀ i ∈ s', AEMeasurable (f i) μ := by
      intro i hi
      exact hf _ (by simpa [Finset.mem_insert, h_not_mem] using Or.inr hi)
    have hsum_aemeas :
        AEMeasurable (∑ i ∈ s', f i) μ :=
      Finset.aemeasurable_sum (s := s') fun i hi => hs' i hi
    refine
      (lcondExp_add (μ := μ) (m := m) (m₀ := m₀) (f := f a)
          (g := ∑ i ∈ s', f i) ha hsum_aemeas).trans ?_
    exact Filter.EventuallyEq.add Filter.EventuallyEq.rfl (ih hs')

lemma lcondExp_smul (c : ℝ≥0) (_ : AEMeasurable f μ) :
    μ⁻[c • f|m] =ᵐ[μ] c • μ⁻[f|m] := by
  by_cases hm : m ≤ m₀
  swap; · simp_rw [lcondExp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [lcondExp_of_not_sigmaFinite hm hμm]; simp
  haveI : SigmaFinite (μ.trim hm) := hμm
  classical
  have hmeas : Measurable[m] (μ⁻[f|m]) := measurable_lcondExp
  have h_smul_meas : Measurable[m] (c • μ⁻[f|m]) := hmeas.const_smul _
  have h_smul_aestr : AEStronglyMeasurable[m] (c • μ⁻[f|m]) μ :=
    h_smul_meas.aestronglyMeasurable
  refine
    (ae_eq_lcondExp_of_forall_setLIntegral_eq (μ := μ) (m := m) (m₀ := m₀)
        (f := c • f) (g := fun x => c • (μ⁻[f|m]) x) hm ?_ h_smul_aestr).symm
  intro s hs hμs
  have hs₀ : MeasurableSet s := hm s hs
  have h_indicator_smul :
      s.indicator (fun x => (c • μ⁻[f|m]) x) =
        fun x => (c : ℝ≥0∞) * s.indicator (μ⁻[f|m]) x := by
    funext x
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem, hx, ENNReal.smul_def]
    · simp [Set.indicator_of_notMem, hx, ENNReal.smul_def]
  have h_integral_indicator :
      ∫⁻ x, s.indicator (fun x => (c • μ⁻[f|m]) x) x ∂μ =
          (c : ℝ≥0∞) * ∫⁻ x, s.indicator (μ⁻[f|m]) x ∂μ := by
    have hc : ((c : ℝ≥0∞)) ≠ ∞ := by simp
    calc
      ∫⁻ x, s.indicator (fun x => (c • μ⁻[f|m]) x) x ∂μ =
          ∫⁻ x, (c : ℝ≥0∞) * s.indicator (μ⁻[f|m]) x ∂μ := by
            refine lintegral_congr (fun x => ?_)
            simpa using congrFun h_indicator_smul x
      _ = (c : ℝ≥0∞) * ∫⁻ x, s.indicator (μ⁻[f|m]) x ∂μ := by
            simpa using
              (lintegral_const_mul' (μ := μ) (r := (c : ℝ≥0∞))
                (f := fun x => s.indicator (μ⁻[f|m]) x) (hr := by simp))
  have h_set :
      ∫⁻ x in s, (c • μ⁻[f|m]) x ∂μ =
          (c : ℝ≥0∞) * ∫⁻ x in s, (μ⁻[f|m]) x ∂μ := by
    simpa [MeasureTheory.lintegral_indicator, hs₀] using h_integral_indicator
  have h_fg :
      ∫⁻ x in s, (c • f) x ∂μ =
          (c : ℝ≥0∞) * ∫⁻ x in s, f x ∂μ := by
    have hc : ((c : ℝ≥0∞)) ≠ ∞ := by simp
    have hind :
        s.indicator (fun x => (c • f) x) =
          fun x => (c : ℝ≥0∞) * s.indicator f x := by
      funext x
      by_cases hx : x ∈ s
      · simp [Set.indicator_of_mem, hx, ENNReal.smul_def, mul_comm]
      · simp [Set.indicator_of_notMem, hx, ENNReal.smul_def]
    have h_integral_indicator_fg :
        ∫⁻ x, s.indicator (fun x => (c • f) x) x ∂μ =
            (c : ℝ≥0∞) * ∫⁻ x, s.indicator f x ∂μ := by
      calc
        ∫⁻ x, s.indicator (fun x => (c • f) x) x ∂μ =
            ∫⁻ x, (c : ℝ≥0∞) * s.indicator f x ∂μ := by
              refine lintegral_congr (fun x => ?_)
              simpa using congrFun hind x
        _ = (c : ℝ≥0∞) * ∫⁻ x, s.indicator f x ∂μ := by
              simpa using
                (lintegral_const_mul' (μ := μ) (r := (c : ℝ≥0∞))
                  (f := fun x => s.indicator f x) (hr := by simp))
    simpa [MeasureTheory.lintegral_indicator, hs₀] using h_integral_indicator_fg
  calc
    ∫⁻ x in s, (c • μ⁻[f|m]) x ∂μ
        = (c : ℝ≥0∞) * ∫⁻ x in s, (μ⁻[f|m]) x ∂μ := h_set
    _ = (c : ℝ≥0∞) * ∫⁻ x in s, f x ∂μ := by
          congr 1
          simpa using
            (setLIntegral_lcondExp (μ := μ) (m := m) (m₀ := m₀) (f := f) (hm := hm) (hs := hs))
    _ = ∫⁻ x in s, (c • f) x ∂μ := by
          simpa using h_fg.symm
  -- refine (lcondExp_ae_eq_lcondExpL1 hm _).trans ?_
  -- rw [lcondExpL1_smul c f]
  -- refine (@lcondExp_ae_eq_lcondExpL1 _ _ _ _ _ m _ _ hm _ f).mp ?_
  -- refine (coeFn_smul c (lcondExpL1 hm μ f)).mono fun x hx1 hx2 => ?_
  -- simp only [hx1, hx2, Pi.smul_apply]

lemma lcondExp_mono (_ : AEMeasurable f μ) (_ : AEMeasurable g μ)
    (hfg : f ≤ᵐ[μ] g) :
    μ⁻[f|m] ≤ᵐ[μ] μ⁻[g|m] := by
  by_cases hm : m ≤ m₀
  swap; ·
    simp [lcondExp_of_not_le (m := m) (m₀ := m₀) (μ := μ) (f := f) hm,
      lcondExp_of_not_le (m := m) (m₀ := m₀) (μ := μ) (f := g) hm]
    show (∀ᵐ x ∂μ, (0 : ℝ≥0∞) ≤ 0)
    exact Filter.Eventually.of_forall (fun _ => le_rfl)
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; ·
    simp [lcondExp_of_not_sigmaFinite (m := m) (m₀ := m₀) (μ := μ) (f := f) hm hμm,
      lcondExp_of_not_sigmaFinite (m := m) (m₀ := m₀) (μ := μ) (f := g) hm hμm]
    show (∀ᵐ x ∂μ, (0 : ℝ≥0∞) ≤ 0)
    exact Filter.Eventually.of_forall (fun _ => le_rfl)
  haveI : SigmaFinite (μ.trim hm) := hμm
  classical
  have hmeas_f : Measurable[m] (μ⁻[f|m]) := measurable_lcondExp
  have hmeas_g : Measurable[m] (μ⁻[g|m]) := measurable_lcondExp
  have h_trim :
      μ⁻[f|m] ≤ᵐ[μ.trim hm] μ⁻[g|m] := by
    refine
      ae_le_of_forall_setLIntegral_le_of_sigmaFinite
        (μ := μ.trim hm) (f := fun x => (μ⁻[f|m]) x)
        (g := fun x => (μ⁻[g|m]) x) (hf := hmeas_f) ?_
    intro s hs hμs
    have hs₀ : MeasurableSet[m₀] s := hm s hs
    have h_int_f :
        ∫⁻ x in s, (μ⁻[f|m]) x ∂μ.trim hm =
          ∫⁻ x in s, (μ⁻[f|m]) x ∂μ := by
      have h_ind_meas :
          Measurable[m] (s.indicator fun x => (μ⁻[f|m]) x) :=
        hmeas_f.indicator hs
      simpa [MeasureTheory.lintegral_indicator, hs, hs₀] using
        (lintegral_trim (μ := μ) (hm := hm)
          (f := s.indicator (fun x => (μ⁻[f|m]) x)) h_ind_meas)
    have h_int_g :
        ∫⁻ x in s, (μ⁻[g|m]) x ∂μ.trim hm =
          ∫⁻ x in s, (μ⁻[g|m]) x ∂μ := by
      have h_ind_meas :
          Measurable[m] (s.indicator fun x => (μ⁻[g|m]) x) :=
        hmeas_g.indicator hs
      simpa [MeasureTheory.lintegral_indicator, hs, hs₀] using
        (lintegral_trim (μ := μ) (hm := hm)
          (f := s.indicator (fun x => (μ⁻[g|m]) x)) h_ind_meas)
    have h_fg_set :
        ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
      setLIntegral_mono_ae' hs₀ (hfg.mono fun _ hx _ => hx)
    calc
      ∫⁻ x in s, (μ⁻[f|m]) x ∂μ.trim hm =
          ∫⁻ x in s, (μ⁻[f|m]) x ∂μ := by simp [h_int_f]
      _ = ∫⁻ x in s, f x ∂μ :=
          setLIntegral_lcondExp (μ := μ) (m := m) (m₀ := m₀)
            (f := f) (hm := hm) (hs := hs)
      _ ≤ ∫⁻ x in s, g x ∂μ := h_fg_set
      _ = ∫⁻ x in s, (μ⁻[g|m]) x ∂μ :=
          (setLIntegral_lcondExp (μ := μ) (m := m) (m₀ := m₀)
            (f := g) (hm := hm) (hs := hs)).symm
      _ = ∫⁻ x in s, (μ⁻[g|m]) x ∂μ.trim hm := by symm; simp [h_int_g]
  exact ae_le_of_ae_le_trim (hm := hm) h_trim

lemma lcondExp_sub (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hfg : g ≤ᵐ[μ] f) (hg_ne_top : ∀ᵐ x ∂μ, (μ⁻[g|m]) x ≠ ∞) :
    μ⁻[f - g|m] =ᵐ[μ] μ⁻[f|m] - μ⁻[g|m] := by
  classical
  have hf_sub : AEMeasurable (f - g) μ := hf.sub hg
  have hfg_eq :
      f =ᵐ[μ] fun x => (f - g) x + g x :=
    hfg.mono fun _ hx => by
      have := tsub_add_cancel_of_le hx
      simpa [Pi.sub_apply, Pi.add_apply, add_comm, add_left_comm, add_assoc] using this.symm
  have h_ce_sum :
      μ⁻[f|m] =ᵐ[μ] μ⁻[f - g|m] + μ⁻[g|m] :=
    (lcondExp_congr_ae (μ := μ) (m := m) (m₀ := m₀) (f := f)
      (g := fun x => (f - g) x + g x) hfg_eq).trans
        (lcondExp_add (μ := μ) (m := m) (m₀ := m₀) (f := f - g)
          (g := g) hf_sub hg)
  have h_event :
      μ⁻[f - g|m] + μ⁻[g|m] =ᵐ[μ] μ⁻[f|m] :=
    (h_ce_sum.symm)
  have h' : μ⁻[f|m] =ᵐ[μ] μ⁻[g|m] + μ⁻[f - g|m] := by
    simpa [add_comm, add_left_comm, add_assoc] using h_event.symm
  filter_upwards [hg_ne_top, h'] with x hxg hx
  have : (μ⁻[f|m]) x - (μ⁻[g|m]) x = (μ⁻[f - g|m]) x :=
    ENNReal.sub_eq_of_eq_add_rev hxg hx
  simpa [Pi.sub_apply] using this.symm

lemma lcondExp_lcondExp_of_le {m₁ m₂ m₀ : MeasurableSpace α} {μ : Measure α} [SigmaFinite μ]
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀) [SigmaFinite (μ.trim hm₂)] :
    μ⁻[μ⁻[f|m₂]|m₁] =ᵐ[μ] μ⁻[f|m₁] := by
  by_cases hμm₁ : SigmaFinite (μ.trim (hm₁₂.trans hm₂))
  swap; · simp_rw [lcondExp_of_not_sigmaFinite (hm₁₂.trans hm₂) hμm₁]; rfl
  haveI : SigmaFinite (μ.trim (hm₁₂.trans hm₂)) := hμm₁
  classical
  have hm₁ : m₁ ≤ m₀ := hm₁₂.trans hm₂
  have hgm :
      AEStronglyMeasurable[m₁] (fun x => (μ⁻[μ⁻[f|m₂]|m₁]) x) μ :=
    (measurable_lcondExp (μ := μ) (m := m₁) (m₀ := m₀)
      (f := fun x => (μ⁻[f|m₂]) x)).aestronglyMeasurable
  refine
    (ae_eq_lcondExp_of_forall_setLIntegral_eq (μ := μ) (m := m₁) (m₀ := m₀)
        (f := f) (g := fun x => (μ⁻[μ⁻[f|m₂]|m₁]) x) hm₁ ?_ hgm)
  intro s hs hμs
  have hs₂ : MeasurableSet[m₂] s := hm₁₂ s hs
  have hs₀ : MeasurableSet[m₀] s := hm₁ s hs
  calc
    ∫⁻ x in s, (μ⁻[μ⁻[f|m₂]|m₁]) x ∂μ =
        ∫⁻ x in s, (μ⁻[f|m₂]) x ∂μ :=
        setLIntegral_lcondExp (μ := μ) (m := m₁) (m₀ := m₀)
          (f := fun x => (μ⁻[f|m₂]) x) (hm := hm₁) (hs := hs)
    _ = ∫⁻ x in s, f x ∂μ :=
        setLIntegral_lcondExp (μ := μ) (m := m₂) (m₀ := m₀)
          (f := f) (hm := hm₂) (hs := hs₂)
  -- refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite' (hm₁₂.trans hm₂)
  --   (fun s _ _ => integrable_lcondExp.integrableOn)
  --   (fun s _ _ => integrable_lcondExp.integrableOn) ?_
  --   (Measurable.aemeasurable' measurable_lcondExp)
  --   (Measurable.aemeasurable' measurable_lcondExp)
  -- intro s hs _
  -- rw [setLIntegral_lcondExp (hm₁₂.trans hm₂) integrable_lcondExp hs]
  -- rw [setLIntegral_lcondExp (hm₁₂.trans hm₂) hf hs, setLIntegral_lcondExp hm₂ hf (hm₁₂ s hs)]

  -- exact (lcondExp_ae_eq_lcondExpL1 hm _).trans_le
  --   ((lcondExpL1_mono hf hg hfg).trans_eq (lcondExp_ae_eq_lcondExpL1 hm _).symm)

-- TODO: We don't have L1 convergence in `ℝ≥0∞`
-- /-- If two sequences of functions have a.e. equal conditional expectations at each step,
-- converge and verify dominated convergence hypotheses, then the conditional expectations of
-- their limits are a.e. equal. -/
-- lemma tendsto_lcondExp_unique (fs gs : ℕ → α → ℝ≥0∞) (f g : α → ℝ≥0∞)
--     (hfs : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
--     (hgs : ∀ᵐ x ∂μ, Tendsto (fun n => gs n x) atTop (𝓝 (g x))) (bound_fs : α → ℝ)
--     (h_int_bound_fs : Integrable bound_fs μ) (bound_gs : α → ℝ)
--     (h_int_bound_gs : Integrable bound_gs μ) (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
--     (hgs_bound : ∀ n, ∀ᵐ x ∂μ, ‖gs n x‖ ≤ bound_gs x) (hfg : ∀ n, μ⁻[fs n|m] =ᵐ[μ] μ⁻[gs n|m]) :
--     μ⁻[f|m] =ᵐ[μ] μ⁻[g|m] := by
--   by_cases hm : m ≤ m₀; swap; · simp_rw [lcondExp_of_not_le hm]; rfl
--   by_cases hμm : SigmaFinite (μ.trim hm)
--   swap; · simp_rw [lcondExp_of_not_sigmaFinite hm hμm]; rfl
--   haveI : SigmaFinite (μ.trim hm) := hμm
--   refine (lcondExp_ae_eq_lcondExpL1 hm f).trans ((lcondExp_ae_eq_lcondExpL1 hm g).trans ?_).symm
--   rw [← Lp.ext_iff]
--   have hn_eq : ∀ n, lcondExpL1 hm μ (gs n) = lcondExpL1 hm μ (fs n) := by
--     intro n
--     ext1
--     refine (lcondExp_ae_eq_lcondExpL1 hm (gs n)).symm.trans ((hfg n).symm.trans ?_)
--     exact lcondExp_ae_eq_lcondExpL1 hm (fs n)
--   have hcond_fs : Tendsto (fun n => lcondExpL1 hm μ (fs n)) atTop (𝓝 (lcondExpL1 hm μ f)) :=
--     tendsto_lcondExpL1_of_dominated_convergence hm _ (fun n => (hfs_int n).1) h_int_bound_fs
--       hfs_bound hfs
--   have hcond_gs : Tendsto (fun n => lcondExpL1 hm μ (gs n)) atTop (𝓝 (lcondExpL1 hm μ g)) :=
--     tendsto_lcondExpL1_of_dominated_convergence hm _ (fun n => (hgs_int n).1) h_int_bound_gs
--       hgs_bound hgs
--   exact tendsto_nhds_unique_of_eventuallyEq hcond_gs hcond_fs (.of_forall hn_eq)

end MeasureTheory
