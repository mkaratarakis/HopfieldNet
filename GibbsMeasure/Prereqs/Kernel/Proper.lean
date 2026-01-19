import GibbsMeasure.Mathlib.Data.ENNReal.Basic
import GibbsMeasure.Mathlib.MeasureTheory.Function.L1Space.Integrable
import GibbsMeasure.Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import GibbsMeasure.Mathlib.MeasureTheory.Integral.Bochner.Basic
import GibbsMeasure.Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Kernel.Proper
import Riemann.MeasureTheory.ParametricDominatedConvergence
--import Mathlib

/-!
# Proper kernels

We prove that for a proper kernel `π : Kernel[𝓑, 𝓧] X X` with `𝓑 ≤ 𝓧`, the integral of a product
`f * g` where `f` is integrable w.r.t. `𝓧` and `g` is strongly measurable w.r.t. `𝓑` (and bounded)
satisfies `∫ f * g dπ x₀ = g x₀ * ∫ f dπ x₀`.

## Main results

* `IsProper.integral_indicator_mul_indicator`: Base case for indicator functions
* `IsProper.integral_indicator_mul`: Extension to integrable functions multiplied by indicators
* `IsProper.integral_bdd_mul`: The main result for bounded `𝓑`-measurable multipliers

## Strategy

The key insight is to work with **bounded** `𝓑`-measurable functions `g` rather than general
integrable functions. This avoids the issue that `Integrable.induction` works with L¹ classes
but our predicate `P(g) = (∫ f * g = g x₀ * ∫ f)` involves pointwise evaluation.

For bounded functions:
1. First prove for indicator functions (base case)
2. Extend to simple functions by linearity
3. Use dominated convergence with `approxBounded` to get all bounded strongly measurable functions
4. For the induction on `f`, use the indicator case as base and extend by linearity/closure
-/

open MeasureTheory ENNReal NNReal Set Filter
open scoped ProbabilityTheory Topology

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {A B : Set X}
  {f g : X → ℝ≥0∞} {x₀ : X}

/-! ### Indicator base cases -/

lemma IsProper.integral_indicator_mul_indicator (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) :
    ∫ x, (B.indicator 1 x * A.indicator 1 x : ℝ) ∂(π x₀) =
      B.indicator 1 x₀ * ∫ x, A.indicator 1 x ∂(π x₀) := by
  calc
        ∫ x, (B.indicator 1 x * A.indicator 1 x : ℝ) ∂(π x₀)
    _ = (∫⁻ x, .ofReal (B.indicator 1 x * A.indicator 1 x) ∂π x₀).toReal :=
      integral_eq_lintegral_of_nonneg_ae (.of_forall <| by simp [indicator_nonneg, mul_nonneg])
        (by measurability)
    _ = (∫⁻ x, B.indicator 1 x * A.indicator 1 x ∂π x₀).toReal := by
      simp [ofReal_mul, indicator_nonneg]
    _ = (B.indicator 1 x₀ * ∫⁻ x, A.indicator 1 x ∂π x₀).toReal := by
      rw [hπ.lintegral_mul h𝓑𝓧 (by measurability) (by measurability)]
    _ = B.indicator 1 x₀ * ∫ x, A.indicator 1 x ∂π x₀ := by
      rw [integral_eq_lintegral_of_nonneg_ae (.of_forall <| by simp [indicator_nonneg])
        (by measurability)]
      simp

/-! ### Extension to integrable functions via induction -/

lemma IsProper.integral_indicator_mul {f : X → ℝ} (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hf : Integrable[𝓧] f (π x₀)) (hB : MeasurableSet[𝓑] B) :
    ∫ x, B.indicator 1 x * f x ∂(π x₀) = B.indicator 1 x₀ * ∫ x, f x ∂(π x₀) := by
  refine Integrable.induction _ (fun c S hmS bpS ↦ ?_) (fun f g _ hfint hgint hf hg ↦ ?_) ?_
    (fun f g hfg hfint hf ↦ ?_) hf
  · simp [← smul_indicator_one_apply, mul_left_comm, integral_const_mul,
      integral_indicator_mul_indicator hπ h𝓑𝓧 hmS hB]
  · have : Integrable (fun x ↦ B.indicator 1 x * f x) (π x₀) := by simp [h𝓑𝓧 _ hB, *]
    have : Integrable (fun x ↦ B.indicator 1 x * g x) (π x₀) := by simp [h𝓑𝓧 _ hB, *]
    simp [mul_add, integral_add, *]
  · refine isClosed_eq ?_ <| by fun_prop
    simpa [integral_indicator (h𝓑𝓧 B hB), ← indicator_mul_left] using continuous_setIntegral _
  · simpa [integral_congr_ae <| .fun_mul .rfl hfg, integral_congr_ae hfg] using hf

/-! ### Main theorem: bounded multipliers with integrable f -/

variable [IsFiniteKernel π]

/-- For a proper kernel `π`, if `f` is integrable and `g` is bounded and `𝓑`-strongly measurable,
then `∫ g * f dπ x₀ = g x₀ * ∫ f dπ x₀`. -/
lemma IsProper.integral_bdd_mul {f g : X → ℝ} (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hπ : IsProper π)
    (hf : Integrable[𝓧] f (π x₀)) (hg : StronglyMeasurable[𝓑] g) (hgbdd : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    ∫ x, g x * f x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
  obtain ⟨C, hC⟩ := hgbdd
  -- Use `Integrable.induction` on f with explicit arguments
  refine @Integrable.induction X ℝ 𝓧 _ (π x₀)
    (fun f => ∫ x, g x * f x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀))
    ?_ ?_ ?_ ?_ _ hf
  · -- Indicator case: f = s.indicator (fun _ => c)
    intro c s hs _
    -- Pull out the scalar `c` and reduce to the case `f = s.indicator 1`.
    simp_rw [← smul_indicator_one_apply s c, smul_eq_mul]
    -- We now prove the identity for `s.indicator 1`, then multiply by `c`.
    -- Use dominated convergence to extend from simple functions to bounded measurable g
    -- The key is that g is the pointwise limit of simple function approximations
    have hconv : Tendsto (fun n => hg.approxBounded C n x₀) atTop (𝓝 (g x₀)) :=
      hg.tendsto_approxBounded_of_norm_le (hC x₀)
    have hconv_mul :
        Tendsto (fun n => hg.approxBounded C n x₀ * ∫ x, s.indicator 1 x ∂(π x₀))
          atTop (𝓝 (g x₀ * ∫ x, s.indicator 1 x ∂(π x₀))) :=
      hconv.mul_const _
    -- The integral side also converges by dominated convergence
    have hint :
        Tendsto (fun n => ∫ x, hg.approxBounded C n x * s.indicator 1 x ∂(π x₀))
          atTop (𝓝 (∫ x, g x * s.indicator 1 x ∂(π x₀))) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => C)
      · intro n
        -- Each approximation is simple (hence strongly measurable); multiply with an indicator.
        exact (((hg.approxBounded C n).stronglyMeasurable.mono h𝓑𝓧).mul
          (stronglyMeasurable_one.indicator hs)).aestronglyMeasurable
      · exact integrable_const C
      · intro n
        filter_upwards with x
        calc ‖hg.approxBounded C n x * s.indicator 1 x‖
            ≤ ‖hg.approxBounded C n x‖ * ‖s.indicator 1 x‖ := norm_mul_le _ _
          _ ≤ C * 1 := by
              apply mul_le_mul
              · exact hg.norm_approxBounded_le ((norm_nonneg _).trans (hC x₀)) n x
              · -- `‖s.indicator 1 x‖ ≤ 1`
                have : ‖s.indicator (fun _ : X => (1 : ℝ)) x‖ ≤ ‖(fun _ : X => (1 : ℝ)) x‖ :=
                  norm_indicator_le_norm_self (s := s) (f := fun _ : X => (1 : ℝ)) (a := x)
                simpa using this
              · exact norm_nonneg _
              · exact (norm_nonneg _).trans (hC x₀)
          _ = C := mul_one C
      · filter_upwards with x
        exact (hg.tendsto_approxBounded_of_norm_le (hC x)).mul_const _
    -- Now use that each approximation satisfies the equality (by indicator lemma)
    have heq : ∀ n, ∫ x, hg.approxBounded C n x * s.indicator 1 x ∂(π x₀) =
        hg.approxBounded C n x₀ * ∫ x, s.indicator 1 x ∂(π x₀) := fun n => by
      -- A simple function is a finite linear combination of indicators
      classical
      -- Use `SimpleFunc.induction` on the approximating simple function.
      refine @SimpleFunc.induction X ℝ 𝓑 _ (motive := fun gsf : @SimpleFunc X 𝓑 ℝ =>
          ∫ x, gsf x * s.indicator 1 x ∂(π x₀) = gsf x₀ * ∫ x, s.indicator 1 x ∂(π x₀))
        ?_ ?_ (hg.approxBounded C n)
      · -- Base case: indicator function
        intro c' t ht
        -- Here `g = t.indicator (fun _ ↦ c')`; expand and use the indicator lemma.
        simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const, Set.piecewise_eq_indicator,
          Function.const_zero]
        have htB : MeasurableSet[𝓑] t := ht
        have hsX : MeasurableSet[𝓧] s := hs
        have hmul : (fun y => t.indicator (Function.const X c') y * s.indicator 1 y) =
            fun y => c' * (t.indicator 1 y * s.indicator 1 y) := by
          funext y; by_cases hy : y ∈ t <;> simp [hy]
        simp_rw [hmul, integral_const_mul]
        have hx0 : t.indicator (Function.const X c') x₀ = c' * t.indicator 1 x₀ := by
          by_cases hx : x₀ ∈ t <;> simp [hx]
        rw [hx0, mul_assoc]
        congr 1
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (integral_indicator_mul_indicator (π := π) (x₀ := x₀) (hπ := hπ) (h𝓑𝓧 := h𝓑𝓧)
            (A := s) (B := t) hsX htB)
      · -- Addition case for simple functions
        intro f' g' _ hf' hg'
        simp only [SimpleFunc.coe_add, Pi.add_apply, add_mul]
        have hind : Integrable (s.indicator (1 : X → ℝ)) (π x₀) :=
          (integrable_const (μ := π x₀) (1 : ℝ)).indicator hs
        have hint_f' : Integrable (fun x => f' x * s.indicator 1 x) (π x₀) := by
          -- simple functions are bounded, hence we can use `bdd_mul` with the integrable indicator
          classical
          by_cases hX : Nonempty X
          · classical
            let x0 : X := Classical.choice hX
            let Cf : ℝ := ((@SimpleFunc.range (α := X) (β := ℝ) 𝓑 f').image fun y => ‖y‖).max'
              (Finset.image_nonempty.2 ⟨f' x0, (@SimpleFunc.mem_range_self (α := X) (β := ℝ) 𝓑 f') x0⟩)
            have hbdd : ∀ x, ‖f' x‖ ≤ Cf := fun x => by
              have hx : ‖f' x‖ ∈ (@SimpleFunc.range (α := X) (β := ℝ) 𝓑 f').image (fun y => ‖y‖) := by
                refine Finset.mem_image.2 ?_
                exact ⟨f' x, (@SimpleFunc.mem_range_self (α := X) (β := ℝ) 𝓑 f') x, rfl⟩
              exact Finset.le_max' _ _ hx
            have := hind.bdd_mul
              (((f'.stronglyMeasurable.mono h𝓑𝓧).aestronglyMeasurable :
                AEStronglyMeasurable f' (π x₀)))
              (Eventually.of_forall hbdd)
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
          · have hbdd : ∀ x, ‖f' x‖ ≤ (0 : ℝ) := by
              intro x; exfalso; exact hX ⟨x⟩
            have := hind.bdd_mul
              (((f'.stronglyMeasurable.mono h𝓑𝓧).aestronglyMeasurable :
                AEStronglyMeasurable f' (π x₀)))
              (Eventually.of_forall hbdd)
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
        have hint_g' : Integrable (fun x => g' x * s.indicator 1 x) (π x₀) := by
          classical
          by_cases hX : Nonempty X
          · classical
            let x0 : X := Classical.choice hX
            let Cg : ℝ := ((@SimpleFunc.range (α := X) (β := ℝ) 𝓑 g').image fun y => ‖y‖).max'
              (Finset.image_nonempty.2 ⟨g' x0, (@SimpleFunc.mem_range_self (α := X) (β := ℝ) 𝓑 g') x0⟩)
            have hbdd : ∀ x, ‖g' x‖ ≤ Cg := fun x => by
              have hx : ‖g' x‖ ∈ (@SimpleFunc.range (α := X) (β := ℝ) 𝓑 g').image (fun y => ‖y‖) := by
                refine Finset.mem_image.2 ?_
                exact ⟨g' x, (@SimpleFunc.mem_range_self (α := X) (β := ℝ) 𝓑 g') x, rfl⟩
              exact Finset.le_max' _ _ hx
            have := hind.bdd_mul
              (((g'.stronglyMeasurable.mono h𝓑𝓧).aestronglyMeasurable :
                AEStronglyMeasurable g' (π x₀)))
              (Eventually.of_forall hbdd)
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
          · have hbdd : ∀ x, ‖g' x‖ ≤ (0 : ℝ) := by
              intro x; exfalso; exact hX ⟨x⟩
            have := hind.bdd_mul
              (((g'.stronglyMeasurable.mono h𝓑𝓧).aestronglyMeasurable :
                AEStronglyMeasurable g' (π x₀)))
              (Eventually.of_forall hbdd)
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
        simp [integral_add hint_f' hint_g', hf', hg']
    -- Take limits on both sides (for the `s.indicator 1` case), then reinsert the scalar `c`.
    simp_rw [heq] at hint
    have h_ind :
        ∫ x, g x * s.indicator 1 x ∂(π x₀) = g x₀ * ∫ x, s.indicator 1 x ∂(π x₀) :=
      tendsto_nhds_unique hint hconv_mul
    calc
      ∫ x, g x * (c * s.indicator 1 x) ∂(π x₀)
          = ∫ x, c * (g x * s.indicator 1 x) ∂(π x₀) := by
              congr 1; ext x; ring
      _ = c * ∫ x, g x * s.indicator 1 x ∂(π x₀) := by
              simpa using (integral_const_mul (μ := π x₀) c (fun x => g x * s.indicator 1 x))
      _ = c * (g x₀ * ∫ x, s.indicator 1 x ∂(π x₀)) := by rw [h_ind]
      _ = g x₀ * (c * ∫ x, s.indicator 1 x ∂(π x₀)) := by ring
      _ = g x₀ * ∫ x, c * s.indicator 1 x ∂(π x₀) := by
              simp [integral_const_mul]
  · -- Additivity case
    intro f₁ f₂ _ hf₁ hf₂ hind₁ hind₂
    have hfg₁ : Integrable (fun x => g x * f₁ x) (π x₀) :=
      hf₁.bdd_mul (hg.mono h𝓑𝓧).aestronglyMeasurable (Eventually.of_forall hC)
    have hfg₂ : Integrable (fun x => g x * f₂ x) (π x₀) :=
      hf₂.bdd_mul (hg.mono h𝓑𝓧).aestronglyMeasurable (Eventually.of_forall hC)
    simp [mul_add, integral_add, hfg₁, hfg₂, hf₁, hf₂, hind₁, hind₂, mul_add]
  · -- Closedness case
    refine isClosed_eq ?_ (by fun_prop)
    -- The map f ↦ ∫ g * f is Lipschitz continuous on L¹
    have hLip : LipschitzWith ⟨C, (norm_nonneg _).trans (hC x₀)⟩
        (fun (f : X →₁[π x₀] ℝ) => (∫ x, g x * f x ∂(π x₀))) := by
      intro f₁ f₂
      simp only [edist_dist, dist_eq_norm]
      have hf₁int : Integrable (↑f₁) (π x₀) := (Lp.memLp f₁).integrable (Std.IsPreorder.le_refl 1)
      have hf₂int : Integrable (↑f₂) (π x₀) := (Lp.memLp f₂).integrable (Std.IsPreorder.le_refl 1)
      have hfg₁ : Integrable (fun x => g x * f₁ x) (π x₀) :=
        hf₁int.bdd_mul (hg.mono h𝓑𝓧).aestronglyMeasurable (Eventually.of_forall hC)
      have hfg₂ : Integrable (fun x => g x * f₂ x) (π x₀) :=
        hf₂int.bdd_mul (hg.mono h𝓑𝓧).aestronglyMeasurable (Eventually.of_forall hC)
      calc ENNReal.ofReal ‖∫ x, g x * f₁ x ∂π x₀ - ∫ x, g x * f₂ x ∂π x₀‖
          = ENNReal.ofReal ‖∫ x, g x * (f₁ x - f₂ x) ∂π x₀‖ := by
              rw [← integral_sub hfg₁ hfg₂]
              have h :
                  (fun x => g x * f₁ x - g x * f₂ x) =ᵐ[π x₀] fun x => g x * (f₁ x - f₂ x) := by
                filter_upwards with x
                ring
              simp [integral_congr_ae h]
        _ ≤ ENNReal.ofReal (∫ x, ‖g x * (f₁ x - f₂ x)‖ ∂π x₀) :=
              ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)
        _ ≤ ENNReal.ofReal (∫ x, C * ‖f₁ x - f₂ x‖ ∂π x₀) := by
              apply ENNReal.ofReal_le_ofReal
              apply integral_mono_of_nonneg
              · exact .of_forall fun x => norm_nonneg _
              · exact (hf₁int.sub hf₂int).norm.const_mul C
              · exact .of_forall fun x => by
                  -- Beta-reduce the lambdas so we can use `norm_mul`.
                  change ‖g x * (f₁ x - f₂ x)‖ ≤ C * ‖f₁ x - f₂ x‖
                  -- Now apply the uniform bound `‖g x‖ ≤ C`.
                  simpa [norm_mul, mul_assoc, mul_left_comm, mul_comm] using
                    (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg (f₁ x - f₂ x)))
        _ = ENNReal.ofReal (C * ∫ x, ‖f₁ x - f₂ x‖ ∂π x₀) := by
              -- keep the whole `calc` chain in `ℝ≥0∞`
              simpa using congrArg ENNReal.ofReal
                (integral_const_mul (μ := π x₀) C (fun x => ‖f₁ x - f₂ x‖))
        _ = ENNReal.ofReal (C * ‖f₁ - f₂‖) := by
              -- show `∫ ‖f₁-f₂‖ = ‖f₁-f₂‖₁`, then apply `ENNReal.ofReal`
              refine congrArg (fun t : ℝ => ENNReal.ofReal (C * t)) ?_
              -- `Lp.norm_def` with `p = 1` is `‖f‖ = ∫ ‖f‖`
              -- (after rewriting `eLpNorm_one_eq_lintegral_enorm` and `integral_toReal_eq_lintegral_of_nonneg`)
              rw [Lp.norm_def, ← ENNReal.toReal_ofReal (integral_nonneg (fun _ => norm_nonneg _))]
              congr 1
              rw [eLpNorm_one_eq_lintegral_enorm]
              -- Convert the Bochner integral to a lintegral, then use the `Lp`-subtraction lemma.
              have h_nonneg : 0 ≤ᵐ[π x₀] fun x => ‖f₁ x - f₂ x‖ :=
                ae_of_all _ fun _ => norm_nonneg _
              have h_ofReal :
                  ENNReal.ofReal (∫ x, ‖f₁ x - f₂ x‖ ∂π x₀)
                    = ∫⁻ x, ENNReal.ofReal ‖f₁ x - f₂ x‖ ∂π x₀ := by
                simpa using
                  (ofReal_integral_eq_lintegral_ofReal (μ := π x₀)
                    (f := fun x => ‖f₁ x - f₂ x‖) (hf₁int.sub hf₂int).norm h_nonneg)
              have h_sub :
                  (fun x => ‖f₁ x - f₂ x‖ₑ) =ᵐ[π x₀] fun x => ‖(f₁ - f₂) x‖ₑ := by
                have h' : (fun x => f₁ x - f₂ x) =ᵐ[π x₀] fun x => (f₁ - f₂) x := by
                  simpa [Pi.sub_apply] using (Lp.coeFn_sub f₁ f₂).symm
                simpa using h'.fun_comp (fun y : ℝ => ‖y‖ₑ)
              calc
                ENNReal.ofReal (∫ x, ‖f₁ x - f₂ x‖ ∂π x₀)
                    = ∫⁻ x, ENNReal.ofReal ‖f₁ x - f₂ x‖ ∂π x₀ := h_ofReal
                _ = ∫⁻ x, ‖f₁ x - f₂ x‖ₑ ∂π x₀ := by
                      refine lintegral_congr fun x => ?_
                      exact ofReal_norm_eq_enorm (f₁ x - f₂ x)
                _ = ∫⁻ x, ‖(f₁ - f₂) x‖ₑ ∂π x₀ := lintegral_congr_ae h_sub
        _ ≤ ENNReal.ofReal C * ENNReal.ofReal ‖f₁ - f₂‖ := by
              have hC_nonneg : 0 ≤ C := (norm_nonneg _).trans (hC x₀)
              rw [← ENNReal.ofReal_mul hC_nonneg]
        _ = (↑(show NNReal from ⟨C, (norm_nonneg _).trans (hC x₀)⟩) : ℝ≥0∞)
              * ENNReal.ofReal ‖f₁ - f₂‖ := by
              have hC_nonneg : 0 ≤ C := (norm_nonneg _).trans (hC x₀)
              -- `ENNReal.ofReal` agrees with coercion from `NNReal` when the argument is nonnegative.
              -- We use `show` to avoid the `WithTop`/`Option` constructor ambiguity for `↑⟨C,hC_nonneg⟩`.
              have :
                  ENNReal.ofReal C = (↑(show NNReal from ⟨C, hC_nonneg⟩) : ℝ≥0∞) := by
                simpa using (ENNReal.ofReal_eq_coe_nnreal (x := C) hC_nonneg)
              simp [this]
    exact LipschitzWith.continuous hLip
  · -- AE congruence case
    intro f₁ f₂ hfg hf₁ hind₁
    have hfg' : (fun x => g x * f₁ x) =ᵐ[π x₀] (fun x => g x * f₂ x) :=
      hfg.mono fun x hx => by simp only [hx]
    rw [integral_congr_ae hfg'.symm, integral_congr_ae hfg.symm, hind₁]

end ProbabilityTheory.Kernel
