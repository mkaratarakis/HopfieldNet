import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Topology.MetricSpace.Lipschitz
import Riemann.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert

/-!
# Complex integration-by-parts tools (Arguin–Tai Lemma `lem: by parts`)

This file provides a rigorous, mathlib-idiomatic formalization of the *approximate* complex
integration-by-parts estimate used in Arguin–Tai (2018), Lemma `lem: by parts`.

**Important note (paper alignment):**
The published lemma only bounds `∂_z^2 F` and `∂_{\bar z}^2 F`, but this is not sufficient in
general (e.g. `F(z)=|z|^2` has those second derivatives zero while the Taylor remainder is quadratic).
In Lean we state a *correct* hypothesis: a Lipschitz bound on the real Fréchet derivative `fderiv`,
which controls *all* second-order directions (including the mixed `z/\bar z` terms).

We keep Wirtinger notation (`deriv_z`, `deriv_zbar`) since it matches the spin-glass literature.
-/

open scoped ProbabilityTheory Topology ComplexConjugate NNReal ENNReal
open MeasureTheory Filter Set Real Complex

namespace SpinGlass

noncomputable section

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

-- Expectation notation
local notation3 (prettyPrint := false) "𝔼[" e "]" => ∫ ω, e ∂(ℙ : Measure Ω)

/-! ## Wirtinger derivatives (defined via real Fréchet derivative) -/

/-- The Wirtinger derivative `∂_z = 1/2 (∂_x - i ∂_y)`, defined from the real Fréchet derivative. -/
noncomputable def deriv_z (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  let dF := fderiv ℝ F z
  (1 / 2 : ℂ) * (dF 1 - I * dF I)

/-- The Wirtinger derivative `∂_{\bar z} = 1/2 (∂_x + i ∂_y)`, defined from the real Fréchet derivative. -/
noncomputable def deriv_zbar (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  let dF := fderiv ℝ F z
  (1 / 2 : ℂ) * (dF 1 + I * dF I)

lemma deriv_z_add_deriv_zbar (F : ℂ → ℂ) (z : ℂ) :
    deriv_z F z + deriv_zbar F z = (fderiv ℝ F z) 1 := by
  -- `1/2*(A-B) + 1/2*(A+B) = A`
  simp [deriv_z, deriv_zbar, add_comm, add_left_comm, add_assoc, mul_add, sub_eq_add_neg]
  ring

lemma deriv_z_sub_deriv_zbar (F : ℂ → ℂ) (z : ℂ) :
    deriv_z F z - deriv_zbar F z = -I * (fderiv ℝ F z) I := by
  -- `1/2*(A-B) - 1/2*(A+B) = -B`
  simp [deriv_z, deriv_zbar, sub_eq_add_neg, add_comm, add_left_comm, mul_add]
  ring

/-- Reconstruct the real Fréchet derivative from Wirtinger derivatives:
`Df(z)·h = ∂_z f(z) * h + ∂_{\bar z} f(z) * conj h`. -/
lemma fderiv_apply_eq_deriv_z_mul_add_deriv_zbar_mul_conj
    (F : ℂ → ℂ) (z h : ℂ) :
    (fderiv ℝ F z) h = deriv_z F z * h + deriv_zbar F z * (conj h) := by
  -- Write `h = x + y*I` and use ℝ-linearity of `fderiv`.
  have h_decomp : h = (h.re : ℂ) + (h.im : ℂ) * I := by
    refine Complex.ext ?_ ?_ <;> simp
  -- Reduce to the `1` and `I` components.
  -- `fderiv` is ℝ-linear, so it respects real scalar combinations.
  have h_lin :
      (fderiv ℝ F z) h
        = (h.re : ℝ) • (fderiv ℝ F z) 1 + (h.im : ℝ) • (fderiv ℝ F z) I := by
    have hre : (h.re : ℂ) = (h.re : ℝ) • (1 : ℂ) := by simp
    have him : (h.im : ℂ) * I = (h.im : ℝ) • (I : ℂ) := by simp
    calc
      (fderiv ℝ F z) h
          = (fderiv ℝ F z) ((h.re : ℂ) + (h.im : ℂ) * I) := by
              exact congrArg (fun t => (fderiv ℝ F z) t) h_decomp
      _ = (fderiv ℝ F z) (h.re : ℂ) + (fderiv ℝ F z) ((h.im : ℂ) * I) := by
              exact map_add (fderiv ℝ F z) (h.re : ℂ) ((h.im : ℂ) * I)
      _ = (h.re : ℝ) • (fderiv ℝ F z) 1 + (h.im : ℝ) • (fderiv ℝ F z) I := by
              have h1 : (fderiv ℝ F z) (h.re : ℂ) = (h.re : ℝ) • (fderiv ℝ F z) 1 := by
                rw [hre]
                simpa using (map_smul (fderiv ℝ F z) (h.re : ℝ) (1 : ℂ))
              have h2 :
                  (fderiv ℝ F z) ((h.im : ℂ) * I) = (h.im : ℝ) • (fderiv ℝ F z) I := by
                rw [him]
                simpa using (map_smul (fderiv ℝ F z) (h.im : ℝ) (I : ℂ))
              simp [h1, h2]
  -- Now rewrite the RHS in the same `(re, im)` basis using the identities above.
  have h_rhs :
      deriv_z F z * h + deriv_zbar F z * (conj h)
        = (h.re : ℝ) • (fderiv ℝ F z) 1 + (h.im : ℝ) • (fderiv ℝ F z) I := by
    -- Express everything in terms of `h.re` and `h.im`.
    have h_conj : conj h = (h.re : ℂ) - (h.im : ℂ) * I := by
      refine Complex.ext ?_ ?_ <;> simp
    -- Use the decomp identities `∂z±∂zbar`.
    -- The computation is purely algebraic in `ℂ`.
    have hsum : deriv_z F z + deriv_zbar F z = (fderiv ℝ F z) 1 :=
      deriv_z_add_deriv_zbar F z
    have hdiff : deriv_z F z - deriv_zbar F z = -I * (fderiv ℝ F z) I :=
      deriv_z_sub_deriv_zbar F z
    -- Expand `h` and `conj h` and collect coefficients.
    -- (This mirrors the standard Wirtinger algebra.)
    calc
      deriv_z F z * h + deriv_zbar F z * (conj h)
          = deriv_z F z * ((h.re : ℂ) + (h.im : ℂ) * I)
              + deriv_zbar F z * ((h.re : ℂ) - (h.im : ℂ) * I) := by
                -- rewrite `h` and `conj h` without `simp` (which loops here)
                calc
                  deriv_z F z * h + deriv_zbar F z * (conj h)
                      =
                    deriv_z F z * ((h.re : ℂ) + (h.im : ℂ) * I) + deriv_zbar F z * (conj h) := by
                      exact
                        congrArg (fun t => deriv_z F z * t + deriv_zbar F z * (conj h)) h_decomp
                  _ =
                    deriv_z F z * ((h.re : ℂ) + (h.im : ℂ) * I)
                      + deriv_zbar F z * ((h.re : ℂ) - (h.im : ℂ) * I) := by
                      exact
                        congrArg (fun t =>
                          deriv_z F z * ((h.re : ℂ) + (h.im : ℂ) * I) + deriv_zbar F z * t) h_conj
      _ = (h.re : ℂ) * (deriv_z F z + deriv_zbar F z)
            + (h.im : ℂ) * I * (deriv_z F z - deriv_zbar F z) := by
            ring
      _ = (h.re : ℂ) * (fderiv ℝ F z) 1
            + (h.im : ℂ) * I * (-I * (fderiv ℝ F z) I) := by
            simp [hsum, hdiff]
      _ = (h.re : ℂ) * (fderiv ℝ F z) 1 + (h.im : ℂ) * (fderiv ℝ F z) I := by
            ring_nf
            simp
      _ = (h.re : ℝ) • (fderiv ℝ F z) 1 + (h.im : ℝ) • (fderiv ℝ F z) I := by
            simp
  simp [h_lin, h_rhs]

/-!
Small real inequalities used to bootstrap integrability of lower moments from a third-moment
assumption on a probability space.

We keep them `private` to avoid exporting ad-hoc API.
-/

private lemma le_one_add_self_pow_three (t : ℝ) (ht : 0 ≤ t) : t ≤ 1 + t ^ (3 : ℕ) := by
  by_cases h : t ≤ 1
  · nlinarith [h, pow_nonneg ht 3]
  · have ht1 : 1 ≤ t := le_of_not_ge h
    have ht2 : 1 ≤ t ^ (2 : ℕ) := by
      have : (1 : ℝ) ≤ t * t := by nlinarith
      simpa [pow_two] using this
    have ht3 : t ≤ t ^ (3 : ℕ) := by
      calc
        t = t * 1 := by ring
        _ ≤ t * (t ^ (2 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left ht2 ht
        _ = t ^ (3 : ℕ) := by ring
    linarith [ht3]

private lemma sq_le_one_add_self_pow_three (t : ℝ) (ht : 0 ≤ t) :
    t ^ (2 : ℕ) ≤ 1 + t ^ (3 : ℕ) := by
  by_cases h : t ≤ 1
  · have ht2 : t ^ (2 : ℕ) ≤ 1 := by nlinarith [h]
    nlinarith [ht2, pow_nonneg ht 3]
  · have ht1 : 1 ≤ t := le_of_not_ge h
    have ht23 : t ^ (2 : ℕ) ≤ t ^ (3 : ℕ) := by
      have : (t ^ (2 : ℕ)) * 1 ≤ (t ^ (2 : ℕ)) * t :=
        mul_le_mul_of_nonneg_left ht1 (by positivity : 0 ≤ t ^ (2 : ℕ))
      simpa [pow_succ, pow_two, mul_assoc] using this
    linarith

/-! ## Approximate complex IBP (Arguin–Tai Lemma 9, rigorous version) -/

/-- A convenient bundled hypothesis: the real Fréchet derivative is globally Lipschitz with constant `M`. -/
def FDerivLipschitz (F : ℂ → ℂ) (M : ℝ≥0) : Prop :=
  (∀ z, DifferentiableAt ℝ F z) ∧
    LipschitzWith M (fderiv ℝ F)

set_option maxHeartbeats 0 in
/--
**Approximate complex integration by parts** (Arguin–Tai `lem: by parts`, corrected).

Let `ξ : Ω → ℂ` satisfy `𝔼[ξ]=0`, `𝔼[ξ^2]=0`, and `𝔼[‖ξ‖^3] < ∞`. Let `F : ℂ → ℂ` be `C¹` with a
globally Lipschitz real Fréchet derivative of constant `M`.

Then
`𝔼[ξ * F(ξ)]` is close to `𝔼[‖ξ‖^2] * 𝔼[∂_{z̄}F(ξ)]`, with an explicit `O(M * 𝔼[‖ξ‖^3])` bound.
-/
theorem approx_integral_by_parts_complex
    {ξ : Ω → ℂ} (hξ_meas : Measurable ξ)
    (hξ3 : Integrable (fun ω => ‖ξ ω‖ ^ (3 : ℕ)) (ℙ : Measure Ω))
    (hEξ  : 𝔼[ξ] = 0)
    (hEξ2 : 𝔼[(fun ω => (ξ ω) ^ 2)] = 0)
    {F : ℂ → ℂ} {M : ℝ≥0} (hLip : FDerivLipschitz F M) :
    ‖𝔼[(fun ω => ξ ω * F (ξ ω))]
        - (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => deriv_zbar F (ξ ω))]‖
      ≤ (4 * M) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] := by
  classical
  have hF_diff : ∀ z, DifferentiableAt ℝ F z := hLip.1
  have hLip' : LipschitzWith M (fderiv ℝ F) := hLip.2

  -- Abbreviate constants at `0`.
  set F0 : ℂ := F 0
  set dF0 : ℂ →L[ℝ] ℂ := fderiv ℝ F 0
  set dz0 : ℂ := deriv_z F 0
  set dzb0 : ℂ := deriv_zbar F 0

  -- Key identity: `dF0 z = dz0*z + dzb0*conj z`.
  have hLin0 : ∀ z : ℂ, dF0 z = dz0 * z + dzb0 * conj z := by
    intro z
    simpa [dF0, dz0, dzb0] using
      (fderiv_apply_eq_deriv_z_mul_add_deriv_zbar_mul_conj (F := F) (z := (0:ℂ)) (h := z))

  -- Define the Taylor remainder and the `∂_{z̄}` increment.
  let R : ℂ → ℂ := fun z => F z - F0 - dF0 z
  let D : ℂ → ℂ := fun z => deriv_zbar F z - dzb0

  -- A crude quadratic bound on the remainder from Lipschitz control of `fderiv`.
  have hR_bound : ∀ z : ℂ, ‖R z‖ ≤ M * ‖z‖^2 := by
    intro z
    -- Apply the mean value theorem to `G = F - dF0`, on the segment `[0,z]`.
    let G : ℂ → ℂ := fun w => F w - dF0 w
    have hG_deriv : ∀ w, HasFDerivAt G ((fderiv ℝ F w) - dF0) w := fun w =>
      (hLip.1 w).hasFDerivAt.sub (dF0.hasFDerivAt)
    have hG_deriv_bound :
        ∀ w ∈ segment ℝ (0 : ℂ) z, ‖fderiv ℝ G w‖ ≤ M * ‖z‖ := by
      intro w hw
      have hw_le : ‖w‖ ≤ ‖z‖ := by
        -- `w` lies on the segment from `0` to `z`.
        simpa using (norm_sub_le_of_mem_segment (by simpa using hw : w ∈ segment ℝ (0 : ℂ) z))
      have hnorm :
          ‖fderiv ℝ G w‖ = ‖(fderiv ℝ F w) - (fderiv ℝ F 0)‖ := by
        -- `fderiv G w = fderiv F w - dF0`, and `dF0 = fderiv F 0`.
        simpa [dF0] using congrArg (fun T => ‖T‖) ((hG_deriv w).fderiv)
      have hLip0 : ‖(fderiv ℝ F w) - (fderiv ℝ F 0)‖ ≤ M * ‖w - 0‖ := by
        simpa using hLip'.norm_sub_le w 0
      have : ‖fderiv ℝ G w‖ ≤ M * ‖z‖ := by
        -- `‖w‖ ≤ ‖z‖` on the segment.
        have hw0 : ‖w - 0‖ = ‖w‖ := by simp
        have h1 : ‖(fderiv ℝ F w) - (fderiv ℝ F 0)‖ ≤ M * ‖w‖ := by
          simpa [hw0] using hLip0
        have h2 : (M : ℝ) * ‖w‖ ≤ M * ‖z‖ :=
          mul_le_mul_of_nonneg_left hw_le (by positivity)
        exact le_trans (by simpa [hnorm] using h1) h2
      simpa [hnorm] using this
    have hseg : Convex ℝ (segment ℝ (0 : ℂ) z) := convex_segment _ _
    have hMv :=
      Convex.norm_image_sub_le_of_norm_fderiv_le
        (𝕜 := ℝ) (E := ℂ) (G := ℂ) (f := G) (s := segment ℝ (0 : ℂ) z)
        (hf := fun w _ => (hG_deriv w).differentiableAt)
        (bound := hG_deriv_bound)
        (hs := hseg)
        (xs := left_mem_segment _ _ _)
        (ys := right_mem_segment _ _ _)
    -- Unfold and simplify.
    -- `G z - G 0 = F z - F 0 - dF0 z`.
    -- So `‖R z‖ = ‖G z - G 0‖`.
    have hG0 : G 0 = F0 := by simp [G, F0, dF0]
    have hGz : G z - G 0 = R z := by
      simp [G, R, F0, dF0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hz0 : ‖z - 0‖ = ‖z‖ := by simp
    have : ‖R z‖ ≤ M * ‖z‖ * ‖z‖ := by
      -- from mean value theorem: ‖G z - G 0‖ ≤ (M * ‖z‖) * ‖z‖
      -- since `x=0`, `y=z`.
      simpa [hGz, hz0, mul_assoc] using hMv
    simpa [pow_two, mul_assoc] using this

  have hD_bound : ∀ z : ℂ, ‖D z‖ ≤ M * ‖z‖ := by
    intro z
    -- Use Lipschitz control of `fderiv` to control the Wirtinger combination.
    -- `∂_{z̄} F(z) - ∂_{z̄} F(0)` is a linear combination of `(fderiv F z - fderiv F 0) 1`
    -- and `(fderiv F z - fderiv F 0) I`.
    have h1 :
        ‖(fderiv ℝ F z - fderiv ℝ F 0) 1‖ ≤ M * ‖z‖ := by
      have h := hLip'.norm_sub_le z 0
      have : ‖(fderiv ℝ F z - fderiv ℝ F 0) 1‖ ≤ ‖fderiv ℝ F z - fderiv ℝ F 0‖ * ‖(1:ℂ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have hz : ‖z - (0:ℂ)‖ = ‖z‖ := by simp
      have hM' : ‖fderiv ℝ F z - fderiv ℝ F 0‖ ≤ M * ‖z‖ := by
        simpa [hz] using h
      have : ‖(fderiv ℝ F z - fderiv ℝ F 0) 1‖ ≤ (M : ℝ) * ‖z‖ * ‖(1:ℂ)‖ :=
        (this.trans (mul_le_mul_of_nonneg_right hM' (norm_nonneg _)))
      simpa using (this.trans_eq (by simp))
    have hI :
        ‖(fderiv ℝ F z - fderiv ℝ F 0) I‖ ≤ M * ‖z‖ := by
      have h := hLip'.norm_sub_le z 0
      have : ‖(fderiv ℝ F z - fderiv ℝ F 0) I‖ ≤ ‖fderiv ℝ F z - fderiv ℝ F 0‖ * ‖(I:ℂ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have hz : ‖z - (0:ℂ)‖ = ‖z‖ := by simp
      have hM' : ‖fderiv ℝ F z - fderiv ℝ F 0‖ ≤ M * ‖z‖ := by
        simpa [hz] using h
      have : ‖(fderiv ℝ F z - fderiv ℝ F 0) I‖ ≤ (M : ℝ) * ‖z‖ * ‖(I:ℂ)‖ :=
        (this.trans (mul_le_mul_of_nonneg_right hM' (norm_nonneg _)))
      simpa using (this.trans_eq (by simp))
    -- Now bound the Wirtinger linear combination.
    have :
        ‖D z‖
          ≤ (1 / 2 : ℝ) * (‖(fderiv ℝ F z - fderiv ℝ F 0) 1‖
                            + ‖(fderiv ℝ F z - fderiv ℝ F 0) I‖) := by
      -- Expand `D` as a `1/2`-scaled difference, then bound by triangle inequality.
      have hD :
          D z
            = (1 / 2 : ℂ) *
                ((fderiv ℝ F z - fderiv ℝ F 0) 1 + I * ((fderiv ℝ F z - fderiv ℝ F 0) I)) := by
        -- purely algebraic; `simp` knows how `fderiv` behaves on `1`/`I` and how subtraction applies.
        simp [D, deriv_zbar, dzb0, sub_eq_add_neg, mul_add, add_assoc, add_comm, add_left_comm]
      -- Now take norms.
      calc
        ‖D z‖
            = ‖(1 / 2 : ℂ)‖ *
                ‖(fderiv ℝ F z - fderiv ℝ F 0) 1 + I * ((fderiv ℝ F z - fderiv ℝ F 0) I)‖ := by
              simp [hD]
        _ ≤ ‖(1 / 2 : ℂ)‖ *
              (‖(fderiv ℝ F z - fderiv ℝ F 0) 1‖ + ‖I * ((fderiv ℝ F z - fderiv ℝ F 0) I)‖) := by
              gcongr
              exact norm_add_le _ _
        _ = (1 / 2 : ℝ) *
              (‖(fderiv ℝ F z - fderiv ℝ F 0) 1‖ + ‖(fderiv ℝ F z - fderiv ℝ F 0) I‖) := by
              -- `‖1/2‖ = 1/2` and `‖I * x‖ = ‖x‖`.
              simp
    have hsum :
        (1 / 2 : ℝ) * (‖(fderiv ℝ F z - fderiv ℝ F 0) 1‖ + ‖(fderiv ℝ F z - fderiv ℝ F 0) I‖)
          ≤ M * ‖z‖ := by
      have : ‖(fderiv ℝ F z - fderiv ℝ F 0) 1‖ + ‖(fderiv ℝ F z - fderiv ℝ F 0) I‖
            ≤ 2 * (M * ‖z‖) := by
        nlinarith [h1, hI]
      -- divide by 2
      nlinarith
    exact this.trans hsum

  -- Use the same algebraic rewrite as in the paper.
  have hEξ_norm : 𝔼[ξ] = 0 := hEξ
  have hEξ_sq : 𝔼[(fun ω => (ξ ω) ^ 2)] = 0 := hEξ2

  -- Rewrite the target difference in terms of `R` and `D`.
  have hRewrite :
      𝔼[(fun ω => ξ ω * F (ξ ω))]
          - (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => deriv_zbar F (ξ ω))]
        =
      𝔼[(fun ω => ξ ω * R (ξ ω))]
          - (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => D (ξ ω))] := by
    -- Expand `R` and `D`, cancel constants using `𝔼[ξ]=0`, `𝔼[ξ^2]=0`.
    -- Also use `dF0 z = dz0*z + dzb0*conj z`, so `ξ * dF0 ξ = ξ^2*dz0 + ‖ξ‖^2*dzb0`.
    have hξ_dF0 :
        ∀ ω, ξ ω * dF0 (ξ ω) = (ξ ω)^2 * dz0 + (‖ξ ω‖^2) * dzb0 := by
      intro ω
      have h := hLin0 (ξ ω)
      -- multiply by `ξ ω` and split the sum
      calc
        ξ ω * dF0 (ξ ω) = ξ ω * (dz0 * ξ ω + dzb0 * conj (ξ ω)) := by simp [h]
        _ = ξ ω * (dz0 * ξ ω) + ξ ω * (dzb0 * conj (ξ ω)) := by simp [mul_add]
        _ = (ξ ω) ^ (2 : ℕ) * dz0 + (‖ξ ω‖ ^ (2 : ℕ)) * dzb0 := by
          have h1 : ξ ω * (dz0 * ξ ω) = (ξ ω) ^ (2 : ℕ) * dz0 := by
            simp [pow_two, mul_assoc, mul_comm]
          have h2 : ξ ω * (dzb0 * conj (ξ ω)) = (‖ξ ω‖ ^ (2 : ℕ)) * dzb0 := by
            calc
              ξ ω * (dzb0 * conj (ξ ω)) = dzb0 * (ξ ω * conj (ξ ω)) := by
                simp [mul_left_comm]
              _ = dzb0 * ((‖ξ ω‖ ^ (2 : ℕ)) : ℂ) := by
                have : ξ ω * conj (ξ ω) = ((‖ξ ω‖ ^ (2 : ℕ)) : ℂ) := by
                  simpa [Complex.normSq_eq_norm_sq] using (Complex.mul_conj (ξ ω))
                simp [this]
              _ = (‖ξ ω‖ ^ (2 : ℕ)) * dzb0 := by
                simp [mul_comm]
          simp [h1, h2]
    -- Now do the expectation algebra.
    -- Bootstrap `‖ξ‖` and `‖ξ‖^2` integrability from `‖ξ‖^3`.
    have hξ1 : Integrable (fun ω => ‖ξ ω‖) (ℙ : Measure Ω) := by
      let g : Ω → ℝ := fun ω => 1 + ‖ξ ω‖ ^ (3 : ℕ)
      have hg : Integrable g (ℙ : Measure Ω) :=
        (integrable_const (μ := (ℙ : Measure Ω)) (c := (1 : ℝ))).add hξ3
      have hf_m : AEStronglyMeasurable (fun ω => ‖ξ ω‖) (ℙ : Measure Ω) :=
        ((continuous_norm).measurable.comp hξ_meas).aestronglyMeasurable
      refine Integrable.mono' hg hf_m ?_
      refine ae_of_all _ (fun ω => ?_)
      have ht : 0 ≤ ‖ξ ω‖ := norm_nonneg _
      have hle := le_one_add_self_pow_three (t := ‖ξ ω‖) ht
      simpa [g, Real.norm_eq_abs, abs_of_nonneg ht] using hle

    have hξ2 : Integrable (fun ω => ‖ξ ω‖ ^ (2 : ℕ)) (ℙ : Measure Ω) := by
      let g : Ω → ℝ := fun ω => 1 + ‖ξ ω‖ ^ (3 : ℕ)
      have hg : Integrable g (ℙ : Measure Ω) :=
        (integrable_const (μ := (ℙ : Measure Ω)) (c := (1 : ℝ))).add hξ3
      have hf_m : AEStronglyMeasurable (fun ω => ‖ξ ω‖ ^ (2 : ℕ)) (ℙ : Measure Ω) :=
        (((continuous_norm).measurable.comp hξ_meas).pow_const 2).aestronglyMeasurable
      refine Integrable.mono' hg hf_m ?_
      refine ae_of_all _ (fun ω => ?_)
      have ht : 0 ≤ ‖ξ ω‖ := norm_nonneg _
      have hle := sq_le_one_add_self_pow_three (t := ‖ξ ω‖) ht
      have ht2 : 0 ≤ ‖ξ ω‖ ^ (2 : ℕ) := by positivity
      simpa [g, Real.norm_eq_abs, abs_of_nonneg ht2] using hle

    have hξ_int : Integrable ξ (ℙ : Measure Ω) :=
      (integrable_norm_iff (f := ξ) (hξ_meas.aestronglyMeasurable)).1 hξ1

    -- Integrability of the terms we need to split integrals.
    have hInt_xiF0 : Integrable (fun ω => ξ ω * F0) (ℙ : Measure Ω) :=
      hξ_int.mul_const F0

    have hInt_xiR : Integrable (fun ω => ξ ω * R (ξ ω)) (ℙ : Measure Ω) := by
      have hAE :
          ∀ᵐ ω ∂(ℙ : Measure Ω), ‖ξ ω * R (ξ ω)‖ ≤ (M : ℝ) * ‖ξ ω‖ ^ (3 : ℕ) := by
        refine ae_of_all _ (fun ω => ?_)
        have hR := hR_bound (ξ ω)
        calc
          ‖ξ ω * R (ξ ω)‖ = ‖ξ ω‖ * ‖R (ξ ω)‖ := by simp
          _ ≤ ‖ξ ω‖ * ((M : ℝ) * ‖ξ ω‖ ^ (2 : ℕ)) := by gcongr
          _ = (M : ℝ) * ‖ξ ω‖ ^ (3 : ℕ) := by
                simp [pow_succ,  mul_left_comm, mul_comm]
      have hIntDom :
          Integrable (fun ω => (M : ℝ) * ‖ξ ω‖ ^ (3 : ℕ)) (ℙ : Measure Ω) :=
        hξ3.const_mul _
      -- measurability: `R` is continuous (since `F` is differentiable everywhere), hence measurable.
      have hF_diff' : Differentiable ℝ F := fun z => hF_diff z
      have hF_cont : Continuous F := hF_diff'.continuous
      have hR_cont : Continuous R := by
        -- `R z = F z - F0 - dF0 z`
        dsimp [R]
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (hF_cont.sub continuous_const).sub dF0.continuous
      have hR_meas : Measurable R := hR_cont.measurable
      have hmeas : Measurable (fun ω => ξ ω * R (ξ ω)) :=
        hξ_meas.mul (hR_meas.comp hξ_meas)
      exact hIntDom.mono' hmeas.aestronglyMeasurable (hAE.mono fun _ hx => hx)

    have hInt_xi_dF0 : Integrable (fun ω => ξ ω * dF0 (ξ ω)) (ℙ : Measure Ω) := by
      have hAE :
          ∀ᵐ ω ∂(ℙ : Measure Ω),
            ‖ξ ω * dF0 (ξ ω)‖ ≤ ‖dF0‖ * ‖ξ ω‖ ^ (2 : ℕ) := by
        refine ae_of_all _ (fun ω => ?_)
        -- `‖dF0 (ξ ω)‖ ≤ ‖dF0‖ * ‖ξ ω‖`
        have hOp : ‖dF0 (ξ ω)‖ ≤ ‖dF0‖ * ‖ξ ω‖ :=
          ContinuousLinearMap.le_opNorm dF0 (ξ ω)
        calc
          ‖ξ ω * dF0 (ξ ω)‖ = ‖ξ ω‖ * ‖dF0 (ξ ω)‖ := by simp
          _ ≤ ‖ξ ω‖ * (‖dF0‖ * ‖ξ ω‖) := by gcongr
          _ = ‖dF0‖ * ‖ξ ω‖ ^ (2 : ℕ) := by
                simp [pow_two, mul_assoc, mul_comm]
      have hDom : Integrable (fun ω => ‖dF0‖ * ‖ξ ω‖ ^ (2 : ℕ)) (ℙ : Measure Ω) :=
        hξ2.const_mul ‖dF0‖
      have hmeas : Measurable (fun ω => ξ ω * dF0 (ξ ω)) :=
        hξ_meas.mul (dF0.continuous.measurable.comp hξ_meas)
      exact hDom.mono' hmeas.aestronglyMeasurable hAE

    have hInt_D : Integrable (fun ω => D (ξ ω)) (ℙ : Measure Ω) := by
      have hAE :
          ∀ᵐ ω ∂(ℙ : Measure Ω), ‖D (ξ ω)‖ ≤ (M : ℝ) * ‖ξ ω‖ := by
        refine ae_of_all _ (fun ω => ?_)
        simpa using hD_bound (ξ ω)
      have hDom : Integrable (fun ω => (M : ℝ) * ‖ξ ω‖) (ℙ : Measure Ω) :=
        by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hξ1.const_mul (M : ℝ)
      -- `D` is continuous since `fderiv` is Lipschitz, hence measurable.
      have hfderiv_cont : Continuous (fun z => fderiv ℝ F z) := hLip'.continuous
      have h1_cont : Continuous (fun z => (fderiv ℝ F z) 1) :=
        ((ContinuousLinearMap.apply ℝ ℂ) 1).continuous.comp hfderiv_cont
      have hI_cont : Continuous (fun z => (fderiv ℝ F z) I) :=
        ((ContinuousLinearMap.apply ℝ ℂ) I).continuous.comp hfderiv_cont
      have hderivzbar_cont : Continuous (deriv_zbar F) := by
        -- Prove continuity of the explicit formula, then rewrite it to `deriv_zbar`.
        let g : ℂ → ℂ :=
          fun z => (1 / 2 : ℂ) * ((fderiv ℝ F z) 1 + I * (fderiv ℝ F z) I)
        have hg : Continuous g :=
          continuous_const.mul (h1_cont.add (continuous_const.mul hI_cont))
        have hg_eq : g = deriv_zbar F := by
          funext z
          simp [g, deriv_zbar, one_div]
        simpa [hg_eq] using hg
      have hD_cont : Continuous D := by
        dsimp [D]
        simpa [sub_eq_add_neg] using hderivzbar_cont.sub continuous_const
      have hmeas : Measurable (fun ω => D (ξ ω)) := hD_cont.measurable.comp hξ_meas
      exact hDom.mono' hmeas.aestronglyMeasurable hAE

    -- Compute `𝔼[ξ·F0] = 0` and `𝔼[ξ·dF0(ξ)] = 𝔼[‖ξ‖^2]·dzb0`.
    have hE_xiF0 : 𝔼[(fun ω => ξ ω * F0)] = 0 := by
      have hfac : 𝔼[(fun ω => ξ ω * F0)] = (𝔼[ξ]) * F0 := by
        simp [integral_mul_const]
      simp [hfac, hEξ_norm]

    set A : ℝ := 𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]
    have hE_xi_dF0 : 𝔼[(fun ω => ξ ω * dF0 (ξ ω))] = (A : ℂ) * dzb0 := by
      have hcongr :
          (fun ω => ξ ω * dF0 (ξ ω)) =ᵐ[ℙ] fun ω =>
            (ξ ω) ^ (2 : ℕ) * dz0 + (‖ξ ω‖ ^ (2 : ℕ)) * dzb0 := by
        exact ae_of_all _ (fun ω => hξ_dF0 ω)
      have h0 :
          𝔼[(fun ω => ξ ω * dF0 (ξ ω))]
            = 𝔼[(fun ω => (ξ ω) ^ (2 : ℕ) * dz0 + (‖ξ ω‖ ^ (2 : ℕ)) * dzb0)] := by
        simpa using (integral_congr_ae hcongr)
      -- split the sum
      have hξsq_int : Integrable (fun ω => (ξ ω) ^ (2 : ℕ)) (ℙ : Measure Ω) := by
        -- integrable since `‖ξ^2‖ = ‖ξ‖^2`
        have hnorm : Integrable (fun ω => ‖(ξ ω) ^ (2 : ℕ)‖) (ℙ : Measure Ω) := by
          simpa using hξ2
        exact (integrable_norm_iff (f := fun ω => (ξ ω) ^ (2 : ℕ))
          ((hξ_meas.pow_const 2).aestronglyMeasurable)).1 hnorm
      have hInt1 : Integrable (fun ω => (ξ ω) ^ (2 : ℕ) * dz0) (ℙ : Measure Ω) :=
        hξsq_int.mul_const dz0
      have hInt2 : Integrable (fun ω => ((‖ξ ω‖ : ℂ) ^ (2 : ℕ) * dzb0)) (ℙ : Measure Ω) := by
        -- cast the real function to ℂ and multiply by a constant
        have : Integrable (fun ω => ((‖ξ ω‖ : ℂ) ^ (2 : ℕ))) (ℙ : Measure Ω) := by
          simpa using (MeasureTheory.Integrable.ofReal (𝕜 := ℂ) hξ2)
        simpa using this.mul_const dzb0
      have hsplit :
          𝔼[(fun ω => (ξ ω) ^ (2 : ℕ) * dz0 + ((‖ξ ω‖ : ℂ) ^ (2 : ℕ) * dzb0))]
            =
          𝔼[(fun ω => (ξ ω) ^ (2 : ℕ) * dz0)]
            + 𝔼[(fun ω => ((‖ξ ω‖ : ℂ) ^ (2 : ℕ) * dzb0))] := by
        simpa using (integral_add (μ := (ℙ : Measure Ω)) hInt1 hInt2)
      -- evaluate the two terms
      have hterm1 :
          𝔼[(fun ω => (ξ ω) ^ (2 : ℕ) * dz0)] = 0 := by
        have : 𝔼[(fun ω => (ξ ω) ^ (2 : ℕ) * dz0)] = (𝔼[(fun ω => (ξ ω) ^ (2 : ℕ))]) * dz0 := by
          simp [integral_mul_const]
        simp [this, hEξ_sq]
      have hterm2 :
          𝔼[(fun ω => ((‖ξ ω‖ : ℂ) ^ (2 : ℕ) * dzb0))] = (A : ℂ) * dzb0 := by
        -- factor the constant on the right and move the coercion out of the integral
        have : 𝔼[(fun ω => ((‖ξ ω‖ : ℂ) ^ (2 : ℕ) * dzb0))]
              = (∫ ω, ((‖ξ ω‖ : ℂ) ^ (2 : ℕ)) ∂(ℙ : Measure Ω)) * dzb0 := by
          simp [integral_mul_const]
        -- rewrite the integral of a coerced real function
        have h_ofReal :
            (∫ ω, ((‖ξ ω‖ : ℂ) ^ (2 : ℕ)) ∂(ℙ : Measure Ω))
              = (A : ℂ) := by
          -- `integral_ofReal` moves the coercion outside the integral
          -- first rewrite `(‖ξ ω‖ : ℂ)^2` as `((‖ξ ω‖^2) : ℂ)`
          have : (fun ω => ((‖ξ ω‖ : ℂ) ^ (2 : ℕ))) = fun ω => ((‖ξ ω‖ ^ (2 : ℕ)) : ℂ) := by
            funext ω; simp
          -- then apply `integral_ofReal`
          simpa [A, this] using
            (integral_ofReal (μ := (ℙ : Measure Ω)) (f := fun ω => ‖ξ ω‖ ^ (2 : ℕ)) (𝕜 := ℂ))
        simp [this, h_ofReal]
      -- assemble
      calc
        𝔼[(fun ω => ξ ω * dF0 (ξ ω))]
            = 𝔼[(fun ω => (ξ ω) ^ (2 : ℕ) * dz0 + ((‖ξ ω‖ : ℂ) ^ (2 : ℕ) * dzb0))] := by
                simpa using h0
        _ = 𝔼[(fun ω => (ξ ω) ^ (2 : ℕ) * dz0)] + 𝔼[(fun ω => ((‖ξ ω‖ : ℂ) ^ (2 : ℕ) * dzb0))] := hsplit
        _ = (A : ℂ) * dzb0 := by simp [hterm1, hterm2]

    have hE_deriv :
        𝔼[(fun ω => deriv_zbar F (ξ ω))]
          = 𝔼[(fun ω => D (ξ ω))] + dzb0 := by
      have hpoint : (fun ω => deriv_zbar F (ξ ω)) = fun ω => D (ξ ω) + dzb0 := by
        funext ω
        simp [D, sub_eq_add_neg, add_comm, add_left_comm]
      -- split and use `∫ const = const` for a probability measure
      calc
        𝔼[(fun ω => deriv_zbar F (ξ ω))] = 𝔼[(fun ω => D (ξ ω) + dzb0)] := by simp [hpoint]
        _ = 𝔼[(fun ω => D (ξ ω))] + 𝔼[(fun _ : Ω => dzb0)] := by
              simpa using (integral_add (μ := (ℙ : Measure Ω)) hInt_D (integrable_const (c := dzb0)))
        _ = 𝔼[(fun ω => D (ξ ω))] + dzb0 := by
              simp

    have hE_xiF :
        𝔼[(fun ω => ξ ω * F (ξ ω))]
          =
        𝔼[(fun ω => ξ ω * R (ξ ω))] + 𝔼[(fun ω => ξ ω * F0)] + 𝔼[(fun ω => ξ ω * dF0 (ξ ω))] := by
      have hcongr :
          (fun ω => ξ ω * F (ξ ω)) =ᵐ[ℙ] fun ω =>
            ξ ω * R (ξ ω) + (ξ ω * F0 + ξ ω * dF0 (ξ ω)) := by
        refine ae_of_all _ (fun ω => ?_)
        -- expand `R` and regroup
        simp [R, mul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      have h0 :
          𝔼[(fun ω => ξ ω * F (ξ ω))]
            =
          𝔼[(fun ω => ξ ω * R (ξ ω) + (ξ ω * F0 + ξ ω * dF0 (ξ ω)))] := by
        simpa using (integral_congr_ae hcongr)
      have hsum :
          𝔼[(fun ω => ξ ω * R (ξ ω) + (ξ ω * F0 + ξ ω * dF0 (ξ ω)))]
            =
          𝔼[(fun ω => ξ ω * R (ξ ω))]
            + 𝔼[(fun ω => ξ ω * F0 + ξ ω * dF0 (ξ ω))] := by
        simpa using
          (integral_add (μ := (ℙ : Measure Ω)) hInt_xiR (hInt_xiF0.add hInt_xi_dF0))
      have hsum2 :
          𝔼[(fun ω => ξ ω * F0 + ξ ω * dF0 (ξ ω))]
            =
          𝔼[(fun ω => ξ ω * F0)] + 𝔼[(fun ω => ξ ω * dF0 (ξ ω))] := by
        simpa using (integral_add (μ := (ℙ : Measure Ω)) hInt_xiF0 hInt_xi_dF0)
      -- assemble
      have : 𝔼[(fun ω => ξ ω * F (ξ ω))]
            = 𝔼[(fun ω => ξ ω * R (ξ ω))]
                + (𝔼[(fun ω => ξ ω * F0)] + 𝔼[(fun ω => ξ ω * dF0 (ξ ω))]) := by
        simp [h0, hsum, hsum2]
      simpa [add_assoc] using this

    -- Finish the rewrite: expand `𝔼[ξ·F(ξ)]` and `𝔼[∂_{z̄}F(ξ)]`, then cancel constants.
    have hfinal :
      𝔼[(fun ω => ξ ω * F (ξ ω))]
          - (A : ℂ) * 𝔼[(fun ω => deriv_zbar F (ξ ω))]
          =
        𝔼[(fun ω => ξ ω * R (ξ ω))]
            - (A : ℂ) * 𝔼[(fun ω => D (ξ ω))] := by
      -- Substitute the computed identities and let `ring` do the algebra.
      simp [hE_xiF, hE_deriv, hE_xiF0, hE_xi_dF0, sub_eq_add_neg, mul_add]
      ring

    -- Re-express the statement with `𝔼[‖ξ‖^2]` instead of `A`.
    simpa [A] using hfinal

  -- Now bound by the triangle inequality and the domination bounds.
  have hTerm1 :
      ‖𝔼[(fun ω => ξ ω * R (ξ ω))]‖ ≤ (M : ℝ) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] := by
    -- `‖ξ*R(ξ)‖ ≤ ‖ξ‖ * ‖R(ξ)‖ ≤ M * ‖ξ‖^3`
    have hAE :
        ∀ᵐ ω ∂(ℙ : Measure Ω),
          ‖ξ ω * R (ξ ω)‖ ≤ (M : ℝ) * ‖ξ ω‖ ^ (3 : ℕ) := by
      refine ae_of_all _ (fun ω => ?_)
      have hR := hR_bound (ξ ω)
      calc
        ‖ξ ω * R (ξ ω)‖ = ‖ξ ω‖ * ‖R (ξ ω)‖ := by simp
        _ ≤ ‖ξ ω‖ * ((M : ℝ) * ‖ξ ω‖ ^ (2 : ℕ)) := by gcongr
        _ = (M : ℝ) * ‖ξ ω‖ ^ (3 : ℕ) := by
              simp [pow_succ, mul_left_comm, mul_comm]
    have hIntDom : Integrable (fun ω => (M : ℝ) * ‖ξ ω‖ ^ (3 : ℕ)) (ℙ : Measure Ω) :=
      hξ3.const_mul _
    have h :=
      norm_integral_le_of_norm_le (μ := (ℙ : Measure Ω))
        (f := fun ω => ξ ω * R (ξ ω))
        (g := fun ω => (M : ℝ) * ‖ξ ω‖ ^ (3 : ℕ)) hIntDom hAE
    simpa [integral_const_mul] using h

  have hTerm2 :
      ‖(𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => D (ξ ω))]‖
        ≤ (3 * M) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] := by
    -- `‖E[‖ξ‖^2]‖ ≤ E[‖ξ‖^2] ≤ E[‖ξ‖^3]`
    -- and `‖E[D(ξ)]‖ ≤ E[‖D(ξ)‖] ≤ M * E[‖ξ‖] ≤ M * E[‖ξ‖^3]`.
    have hξ2 : Integrable (fun ω => ‖ξ ω‖ ^ (2 : ℕ)) (ℙ : Measure Ω) := by
      -- `‖ξ‖^2 ≤ 1 + ‖ξ‖^3`
      let g : Ω → ℝ := fun ω => 1 + ‖ξ ω‖ ^ (3 : ℕ)
      have hg : Integrable g (ℙ : Measure Ω) :=
        (integrable_const (μ := (ℙ : Measure Ω)) (c := (1 : ℝ))).add hξ3
      have hf_m : AEStronglyMeasurable (fun ω => ‖ξ ω‖ ^ (2 : ℕ)) (ℙ : Measure Ω) :=
        (((continuous_norm).measurable.comp hξ_meas).pow_const 2).aestronglyMeasurable
      refine Integrable.mono' hg hf_m ?_
      refine ae_of_all _ (fun ω => ?_)
      have ht : 0 ≤ ‖ξ ω‖ := norm_nonneg _
      have hle : ‖ξ ω‖ ^ (2 : ℕ) ≤ 1 + ‖ξ ω‖ ^ (3 : ℕ) :=
        sq_le_one_add_self_pow_three (t := ‖ξ ω‖) ht
      have ht2 : 0 ≤ ‖ξ ω‖ ^ (2 : ℕ) := by positivity
      simpa [g, Real.norm_eq_abs, abs_of_nonneg ht2] using hle
    have hξ1 : Integrable (fun ω => ‖ξ ω‖) (ℙ : Measure Ω) := by
      -- `‖ξ‖ ≤ 1 + ‖ξ‖^3`
      let g : Ω → ℝ := fun ω => 1 + ‖ξ ω‖ ^ (3 : ℕ)
      have hg : Integrable g (ℙ : Measure Ω) :=
        (integrable_const (μ := (ℙ : Measure Ω)) (c := (1 : ℝ))).add hξ3
      have hf_m : AEStronglyMeasurable (fun ω => ‖ξ ω‖) (ℙ : Measure Ω) :=
        ((continuous_norm).measurable.comp hξ_meas).aestronglyMeasurable
      refine Integrable.mono' hg hf_m ?_
      refine ae_of_all _ (fun ω => ?_)
      have ht : 0 ≤ ‖ξ ω‖ := norm_nonneg _
      have hle : ‖ξ ω‖ ≤ 1 + ‖ξ ω‖ ^ (3 : ℕ) := le_one_add_self_pow_three (t := ‖ξ ω‖) ht
      simp only [Real.norm_eq_abs, abs_of_nonneg ht]
      exact hle
    have hED :
        ‖𝔼[(fun ω => D (ξ ω))]‖ ≤ (M : ℝ) * 𝔼[(fun ω => ‖ξ ω‖)] := by
      -- Name the integrand and dominating function to keep elaboration light.
      let f : Ω → ℂ := fun ω => D (ξ ω)
      let g : Ω → ℝ := fun ω => (M : ℝ) * ‖ξ ω‖
      have hDae :
          ∀ᵐ ω ∂(ℙ : Measure Ω), ‖f ω‖ ≤ g ω := by
        refine ae_of_all _ (fun ω => ?_)
        dsimp [f, g]
        exact hD_bound (ξ ω)
      have hDom : Integrable g (ℙ : Measure Ω) := by
        -- Avoid `simp` (which can be expensive here); `g` is definitional.
        dsimp [g]
        exact hξ1.const_mul (M : ℝ)
      have h :
          ‖∫ ω, f ω ∂(ℙ : Measure Ω)‖ ≤ ∫ ω, g ω ∂(ℙ : Measure Ω) :=
        norm_integral_le_of_norm_le (μ := (ℙ : Measure Ω))
          (f := f) (g := g) hDom hDae
      -- Rewrite the RHS integral of a constant multiple without `simp` (which can be costly here).
      dsimp [g] at h
      -- `∫ (M * ‖ξ‖) = M * ∫ ‖ξ‖`
      simpa [f, integral_const_mul] using
        (h.trans_eq
          (integral_const_mul (μ := (ℙ : Measure Ω)) (r := (M : ℝ)) (f := fun ω => ‖ξ ω‖)))
    have hEξ2_le :
        (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) ≤ 𝔼[(fun ω => 1 + ‖ξ ω‖ ^ (3 : ℕ))] := by
      have hmaj : ∀ ω, ‖ξ ω‖ ^ (2 : ℕ) ≤ (1 : ℝ) + ‖ξ ω‖ ^ (3 : ℕ) := by
        intro ω
        have ht : 0 ≤ ‖ξ ω‖ := norm_nonneg _
        simpa using (sq_le_one_add_self_pow_three (t := ‖ξ ω‖) ht)
      refine integral_mono_of_nonneg (μ := (ℙ : Measure Ω))
        (hf := by
          refine Eventually.of_forall (fun _ => ?_)
          positivity)
        (hgi := (integrable_const (μ := (ℙ : Measure Ω)) (c := (1 : ℝ))).add hξ3)
        (h := by
          refine ae_of_all _ (fun ω => ?_)
          simpa using hmaj ω)
    have hE1 : 𝔼[(1:ℝ)] = 1 := by simp
    have hEξ3_le :
        𝔼[(fun ω => ‖ξ ω‖)] ≤ 𝔼[(fun ω => 1 + ‖ξ ω‖ ^ (3 : ℕ))] := by
      have hmaj : ∀ ω, ‖ξ ω‖ ≤ (1 : ℝ) + ‖ξ ω‖ ^ (3 : ℕ) := by
        intro ω
        have ht : 0 ≤ ‖ξ ω‖ := norm_nonneg _
        simpa using (le_one_add_self_pow_three (t := ‖ξ ω‖) ht)
      refine integral_mono_of_nonneg (μ := (ℙ : Measure Ω))
        (hf := by
          refine Eventually.of_forall (fun _ => ?_)
          positivity)
        (hgi := (integrable_const (μ := (ℙ : Measure Ω)) (c := (1 : ℝ))).add hξ3)
        (h := by
          refine ae_of_all _ (fun ω => ?_)
          simpa using hmaj ω)
    -- Keep the smallness of moments: use Lp monotonicity on a probability measure.
    have hMoment :
        𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))] * 𝔼[(fun ω => ‖ξ ω‖)]
          ≤ 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] := by
      -- Work in `ℝ≥0∞` via `eLpNorm`, then convert back using `toReal`.
      let X : Ω → ℝ := fun ω => ‖ξ ω‖
      have hX_meas : Measurable X := (continuous_norm).measurable.comp hξ_meas
      have hX_aesm : AEStronglyMeasurable X (ℙ : Measure Ω) := hX_meas.aestronglyMeasurable

      -- Lp norms of `X` (as `ENNReal = ℝ≥0∞`).
      let N1 : ENNReal := eLpNorm X (1 : ENNReal) (ℙ : Measure Ω)
      let N2 : ENNReal := eLpNorm X (2 : ENNReal) (ℙ : Measure Ω)
      let N3 : ENNReal := eLpNorm X (3 : ENNReal) (ℙ : Measure Ω)

      have hN1 : N1 ≤ N3 := by
        have : eLpNorm X (1 : ENNReal) (ℙ : Measure Ω) ≤ eLpNorm X (3 : ENNReal) (ℙ : Measure Ω) :=
          eLpNorm_le_eLpNorm_of_exponent_le (μ := (ℙ : Measure Ω)) (f := X) (by norm_num) hX_aesm
        simpa [N1, N3] using this
      have hN2 : N2 ≤ N3 := by
        have : eLpNorm X (2 : ENNReal) (ℙ : Measure Ω) ≤ eLpNorm X (3 : ENNReal) (ℙ : Measure Ω) :=
          eLpNorm_le_eLpNorm_of_exponent_le (μ := (ℙ : Measure Ω)) (f := X) (by norm_num) hX_aesm
        simpa [N2, N3] using this

      -- Convert `N1`, `N2^2`, `N3^3` to the corresponding `lintegral`s.
      have hN1_eq : N1 = ∫⁻ ω, ‖X ω‖ₑ ∂(ℙ : Measure Ω) := by
        -- p = 1
        simpa [N1] using
          (eLpNorm_eq_lintegral_rpow_enorm (μ := (ℙ : Measure Ω)) (f := X)
            (by simp : (1 : ENNReal) ≠ 0) (by simp : (1 : ENNReal) ≠ (⊤ : ENNReal)))

      have hN2_sq :
          N2 ^ (2 : ℕ) = ∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℕ) ∂(ℙ : Measure Ω) := by
        -- Use the defining formula for `eLpNorm` and raise to `2`.
        have hdef :=
          (eLpNorm_eq_lintegral_rpow_enorm (μ := (ℙ : Measure Ω)) (f := X)
            (by simp : (2 : ENNReal) ≠ 0) (by simp : (2 : ENNReal) ≠ (⊤ : ENNReal)))
        -- First in `ℝ`-powers, then convert to nat powers.
        have :
            N2 ^ (2 : ℝ) = ∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℝ) ∂(ℙ : Measure Ω) := by
          calc
            N2 ^ (2 : ℝ)
                = ((∫⁻ ω, ‖X ω‖ₑ ^ (2 : ENNReal).toReal ∂(ℙ : Measure Ω)) ^ (1 / (2 : ENNReal).toReal)) ^
                      (2 : ℝ) := by
                    simp [N2, hdef]
            _ =
                (∫⁻ ω, ‖X ω‖ₑ ^ (2 : ENNReal).toReal ∂(ℙ : Measure Ω)) ^
                  ((1 / (2 : ENNReal).toReal) * (2 : ℝ)) := by
                    simpa using
                      (ENNReal.rpow_mul
                        (∫⁻ ω, ‖X ω‖ₑ ^ (2 : ENNReal).toReal ∂(ℙ : Measure Ω))
                        (1 / (2 : ENNReal).toReal) (2 : ℝ)).symm
            _ = ∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(ℙ : Measure Ω) := by
                  have : (1 / (2 : ENNReal).toReal) * (2 : ℝ) = 1 := by norm_num
                  simp
            _ = ∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℝ) ∂(ℙ : Measure Ω) := by
                  norm_num
        -- Convert `ℝ`-power `2` to nat-power `2`.
        have hNat : N2 ^ (2 : ℕ) = N2 ^ (2 : ℝ) := by
          simp
        -- And similarly on the integrand, but avoid `simp` (it can loop here).
        -- First rewrite the RHS exponent as `↑(2 : ℕ)`.
        have this' :
            N2 ^ ((2 : ℕ) : ℝ) = ∫⁻ ω, ‖X ω‖ₑ ^ ((2 : ℕ) : ℝ) ∂(ℙ : Measure Ω) := by
          -- `((2 : ℕ) : ℝ) = (2 : ℝ)`
          simpa [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num] using this
        -- Convert `rpow` with nat-cast exponent to nat powers on both sides.
        have hleft : N2 ^ (2 : ℕ) = N2 ^ ((2 : ℕ) : ℝ) :=
          (ENNReal.rpow_natCast N2 2).symm
        have hright :
            (∫⁻ ω, ‖X ω‖ₑ ^ ((2 : ℕ) : ℝ) ∂(ℙ : Measure Ω)) =
              ∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℕ) ∂(ℙ : Measure Ω) := by
          refine lintegral_congr (fun ω => ?_)
          simp
        exact (hleft.trans (this'.trans hright))

      have hN3_cube :
          N3 ^ (3 : ℕ) = ∫⁻ ω, ‖X ω‖ₑ ^ (3 : ℕ) ∂(ℙ : Measure Ω) := by
        have hdef :=
          (eLpNorm_eq_lintegral_rpow_enorm (μ := (ℙ : Measure Ω)) (f := X)
            (by simp : (3 : ℝ≥0∞) ≠ 0) (by simp : (3 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)))
        have :
            N3 ^ (3 : ℝ) = ∫⁻ ω, ‖X ω‖ₑ ^ (3 : ℝ) ∂(ℙ : Measure Ω) := by
          calc
            N3 ^ (3 : ℝ)
                = ((∫⁻ ω, ‖X ω‖ₑ ^ (3 : ℝ≥0∞).toReal ∂(ℙ : Measure Ω)) ^ (1 / (3 : ℝ≥0∞).toReal)) ^
                      (3 : ℝ) := by
                    simp [N3, hdef]
            _ =
                (∫⁻ ω, ‖X ω‖ₑ ^ (3 : ℝ≥0∞).toReal ∂(ℙ : Measure Ω)) ^
                  ((1 / (3 : ℝ≥0∞).toReal) * (3 : ℝ)) := by
                    simpa using
                      (ENNReal.rpow_mul
                        (∫⁻ ω, ‖X ω‖ₑ ^ (3 : ℝ≥0∞).toReal ∂(ℙ : Measure Ω))
                        (1 / (3 : ℝ≥0∞).toReal) (3 : ℝ)).symm
            _ = ∫⁻ ω, ‖X ω‖ₑ ^ (3 : ℝ≥0∞).toReal ∂(ℙ : Measure Ω) := by
                  have : (1 / (3 : ℝ≥0∞).toReal) * (3 : ℝ) = 1 := by norm_num
                  simp
            _ = ∫⁻ ω, ‖X ω‖ₑ ^ (3 : ℝ) ∂(ℙ : Measure Ω) := by
                  norm_num
        have hNat : N3 ^ (3 : ℕ) = N3 ^ (3 : ℝ) := by
          simp [N3]
        -- Avoid `simp` (it can loop); convert via `ENNReal.rpow_natCast`.
        have this' :
            N3 ^ ((3 : ℕ) : ℝ) = ∫⁻ ω, ‖X ω‖ₑ ^ ((3 : ℕ) : ℝ) ∂(ℙ : Measure Ω) := by
          simpa [show ((3 : ℕ) : ℝ) = (3 : ℝ) by norm_num] using this
        have hleft : N3 ^ (3 : ℕ) = N3 ^ ((3 : ℕ) : ℝ) :=
          (ENNReal.rpow_natCast N3 3).symm
        have hright :
            (∫⁻ ω, ‖X ω‖ₑ ^ ((3 : ℕ) : ℝ) ∂(ℙ : Measure Ω)) =
              ∫⁻ ω, ‖X ω‖ₑ ^ (3 : ℕ) ∂(ℙ : Measure Ω) := by
          refine lintegral_congr (fun ω => ?_)
          simp
        exact (hleft.trans (this'.trans hright))

      -- Lp monotonicity implies `N2^2 * N1 ≤ N3^3`.
      have hN2pow : N2 ^ (2 : ℕ) ≤ N3 ^ (2 : ℕ) := by
        -- monotone in the base (avoid `pow_le_pow_of_le_left`, not in scope here)
        simpa [pow_two] using
          (mul_le_mul hN2 hN2 (by positivity : (0 : ENNReal) ≤ N2) (by positivity : (0 : ENNReal) ≤ N3))
      have hProd : (N2 ^ (2 : ℕ)) * N1 ≤ (N3 ^ (3 : ℕ)) := by
        -- Multiply `N2^2 ≤ N3^2` by `N1 ≤ N3`, then rewrite `N3^2 * N3 = N3^3`.
        have hN1' : N1 ≤ N3 := hN1
        have hmul :
            (N2 ^ (2 : ℕ)) * N1 ≤ (N3 ^ (2 : ℕ)) * N3 :=
          mul_le_mul hN2pow hN1' (by positivity) (by positivity)
        simpa [pow_succ, pow_two, mul_assoc] using hmul

      -- Convert the ENNReal inequality to a real inequality on `𝔼[...]` using `toReal`.
      have hI3_fin : (∫⁻ ω, ‖X ω‖ₑ ^ (3 : ℕ) ∂(ℙ : Measure Ω)) ≠ ⊤ := by
        -- This is the `HasFiniteIntegral` field of `hξ3`.
        have : (∫⁻ ω, ‖ξ ω‖ₑ ^ (3 : ℕ) ∂(ℙ : Measure Ω)) < ⊤ := by
          simpa [MeasureTheory.HasFiniteIntegral] using hξ3.2
        -- Rewrite `‖ξ ω‖ₑ` as `‖X ω‖ₑ` pointwise.
        have hrewrite :
            (∫⁻ ω, ‖ξ ω‖ₑ ^ (3 : ℕ) ∂(ℙ : Measure Ω))
              = ∫⁻ ω, ‖X ω‖ₑ ^ (3 : ℕ) ∂(ℙ : Measure Ω) := by
          refine lintegral_congr (fun ω => ?_)
          simp [X]
        exact ne_of_lt (by simpa [hrewrite] using this)

      -- Now finish in ℝ via `toReal_le_toReal` and the identification of `𝔼[...]`.
      have hReal :
          ((N2 ^ (2 : ℕ)) * N1).toReal ≤ (N3 ^ (3 : ℕ)).toReal := by
        -- Both sides are finite since RHS is finite.
        have hRhs_ne : (N3 ^ (3 : ℕ)) ≠ ⊤ := by
          -- use `hN3_cube`
          simpa [hN3_cube] using hI3_fin
        have hLhs_ne : ((N2 ^ (2 : ℕ)) * N1) ≠ ⊤ := by
          -- product of finite terms
          have hN2_ne : (N2 ^ (2 : ℕ)) ≠ ⊤ := by
            -- from `hN2_sq` and finiteness of `X^2` (via `hξ2`)
            -- `Integrable` gives finiteness for the ENNReal integral of the norm.
            -- After simp, this is naturally stated using `‖ξ ω‖ₑ ^ 2`.
            have : (∫⁻ ω, ‖ξ ω‖ₑ ^ (2 : ℕ) ∂(ℙ : Measure Ω)) < ⊤ := by
              simpa [MeasureTheory.HasFiniteIntegral] using hξ2.2
            -- Rewrite `‖ξ ω‖ₑ` as `‖X ω‖ₑ` pointwise.
            have hrewrite :
                (∫⁻ ω, ‖ξ ω‖ₑ ^ (2 : ℕ) ∂(ℙ : Measure Ω))
                  = ∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℕ) ∂(ℙ : Measure Ω) := by
              refine lintegral_congr (fun ω => ?_)
              simp [X]
            have hfinite : (∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℕ) ∂(ℙ : Measure Ω)) ≠ ⊤ :=
              ne_of_lt (by simpa [hrewrite] using this)
            simpa [hN2_sq] using hfinite
          have hN1_ne : N1 ≠ ⊤ := by
            -- from `hN1_eq` and finiteness of `X` (via `hξ1`)
            have : (∫⁻ ω, ‖ξ ω‖ₑ ∂(ℙ : Measure Ω)) < ⊤ := by
              simpa [MeasureTheory.HasFiniteIntegral] using hξ1.2
            have hrewrite :
                (∫⁻ ω, ‖ξ ω‖ₑ ∂(ℙ : Measure Ω))
                  = ∫⁻ ω, ‖X ω‖ₑ ∂(ℙ : Measure Ω) := by
              refine lintegral_congr (fun ω => ?_)
              simp [X]
            have hfinite : (∫⁻ ω, ‖X ω‖ₑ ∂(ℙ : Measure Ω)) ≠ ⊤ :=
              ne_of_lt (by simpa [hrewrite] using this)
            simpa [hN1_eq] using hfinite
          exact ENNReal.mul_ne_top hN2_ne hN1_ne
        -- Convert inequality in ENNReal to inequality in ℝ.
        exact (ENNReal.toReal_le_toReal hLhs_ne hRhs_ne).2 hProd

      -- Finally identify these `toReal`s with the expectations `𝔼[...]`.
      -- `X` is nonnegative and measurable, so we can use `integral_eq_lintegral_of_nonneg_ae`.
      have hE1 :
          𝔼[(fun ω => ‖ξ ω‖)] = (∫⁻ ω, ‖X ω‖ₑ ∂(ℙ : Measure Ω)).toReal := by
        -- `‖X ω‖ₑ = ofReal (X ω)` since `X ω ≥ 0`.
        have hX0 : 0 ≤ᶠ[ae (ℙ : Measure Ω)] X := by
          refine Filter.Eventually.of_forall (fun ω => ?_)
          exact norm_nonneg _
        -- rewrite integrand
        have : (∫⁻ ω, ENNReal.ofReal (X ω) ∂(ℙ : Measure Ω))
              = ∫⁻ ω, ‖X ω‖ₑ ∂(ℙ : Measure Ω) := by
          refine lintegral_congr (fun ω => ?_)
          have hx : 0 ≤ X ω := norm_nonneg _
          simp [Real.enorm_of_nonneg hx]
        -- Bochner integral to lintegral
        have := integral_eq_lintegral_of_nonneg_ae (μ := (ℙ : Measure Ω)) hX0 hX_aesm
        -- Use the local notation `𝔼[...]`.
        simp [X, this]

      have hE2 :
          𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))] = (∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℕ) ∂(ℙ : Measure Ω)).toReal := by
        have hX2_0 : 0 ≤ᶠ[ae (ℙ : Measure Ω)] fun ω => X ω ^ (2 : ℕ) := by
          refine Filter.Eventually.of_forall (fun ω => ?_)
          positivity
        have hX2_aesm : AEStronglyMeasurable (fun ω => X ω ^ (2 : ℕ)) (ℙ : Measure Ω) :=
          ((hX_meas.pow_const 2)).aestronglyMeasurable
        have : (∫⁻ ω, ENNReal.ofReal (X ω ^ (2 : ℕ)) ∂(ℙ : Measure Ω))
              = ∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℕ) ∂(ℙ : Measure Ω) := by
          refine lintegral_congr (fun ω => ?_)
          have hx : 0 ≤ X ω := norm_nonneg _
          simp [Real.enorm_of_nonneg hx, ENNReal.ofReal_pow hx]
        have := integral_eq_lintegral_of_nonneg_ae (μ := (ℙ : Measure Ω)) hX2_0 hX2_aesm
        simp [X, this]

      have hE3 :
          𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] = (∫⁻ ω, ‖X ω‖ₑ ^ (3 : ℕ) ∂(ℙ : Measure Ω)).toReal := by
        have hX3_0 : 0 ≤ᶠ[ae (ℙ : Measure Ω)] fun ω => X ω ^ (3 : ℕ) := by
          refine Filter.Eventually.of_forall (fun ω => ?_)
          positivity
        have hX3_aesm : AEStronglyMeasurable (fun ω => X ω ^ (3 : ℕ)) (ℙ : Measure Ω) :=
          ((hX_meas.pow_const 3)).aestronglyMeasurable
        have : (∫⁻ ω, ENNReal.ofReal (X ω ^ (3 : ℕ)) ∂(ℙ : Measure Ω))
              = ∫⁻ ω, ‖X ω‖ₑ ^ (3 : ℕ) ∂(ℙ : Measure Ω) := by
          refine lintegral_congr (fun ω => ?_)
          have hx : 0 ≤ X ω := norm_nonneg _
          simp [Real.enorm_of_nonneg hx, ENNReal.ofReal_pow hx]
        have := integral_eq_lintegral_of_nonneg_ae (μ := (ℙ : Measure Ω)) hX3_0 hX3_aesm
        simp [X, this]

      -- Put everything together.
      -- `hReal` is the inequality on `toReal` of the ENNReal quantities.
      -- Rewrite those `toReal`s as the expectations.
      -- Note: `N1 = ∫⁻ ‖X‖ₑ` and `N2^2 = ∫⁻ ‖X‖ₑ^2` and `N3^3 = ∫⁻ ‖X‖ₑ^3`.
      have hN2_sq_toReal :
          (N2 ^ (2 : ℕ)).toReal = (∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℕ) ∂(ℙ : Measure Ω)).toReal := by
        simp [hN2_sq]
      have hN3_cube_toReal :
          (N3 ^ (3 : ℕ)).toReal = (∫⁻ ω, ‖X ω‖ₑ ^ (3 : ℕ) ∂(ℙ : Measure Ω)).toReal := by
        simp [hN3_cube]
      -- rewrite `N1.toReal`
      have hN1_toReal :
          N1.toReal = (∫⁻ ω, ‖X ω‖ₑ ∂(ℙ : Measure Ω)).toReal := by
        simp [hN1_eq]

      -- `toReal` of a product is the product of `toReal`s (since both finite, already ensured above).
      -- So `hReal` gives the desired inequality.
      have :
          (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => ‖ξ ω‖)]
            ≤ 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] := by
        -- Rewrite each expectation using `hE1/hE2/hE3`, and use `hReal`.
        -- `hReal` is:
        --   ((N2^2) * N1).toReal ≤ (N3^3).toReal
        -- rewrite the LHS `toReal` of product as product of `toReal`s.
        -- then substitute `hE*`.
        have hLHS :
            ((N2 ^ (2 : ℕ)) * N1).toReal =
              (∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℕ) ∂(ℙ : Measure Ω)).toReal *
                (∫⁻ ω, ‖X ω‖ₑ ∂(ℙ : Measure Ω)).toReal := by
          -- finiteness already shown above, so `toReal_mul` applies.
          -- we can just use the lemma and rewrite.
          simp [ENNReal.toReal_mul, hN2_sq_toReal, hN1_toReal]
        -- now use hReal and rewrite all pieces
        have hReal' :
            (∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℕ) ∂(ℙ : Measure Ω)).toReal *
                (∫⁻ ω, ‖X ω‖ₑ ∂(ℙ : Measure Ω)).toReal
              ≤ (∫⁻ ω, ‖X ω‖ₑ ^ (3 : ℕ) ∂(ℙ : Measure Ω)).toReal := by
          -- rewrite hReal using `hLHS` and `hN3_cube_toReal`
          simpa [hLHS, hN3_cube_toReal] using hReal
        -- convert back to expectations
        simpa [hE1, hE2, hE3] using hReal'

      exact this

    -- Main bound: keep `𝔼[‖ξ‖]` (no coarse `≤ 1 + 𝔼[‖ξ‖^3]`).
    have hmain :
        ‖(𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => D (ξ ω))]‖
          ≤ (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * (M * 𝔼[(fun ω => ‖ξ ω‖)]) := by
      have hE2_nonneg : 0 ≤ 𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))] := by positivity
      have :
          ‖(𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => D (ξ ω))]‖
                = (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * ‖𝔼[(fun ω => D (ξ ω))]‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg hE2_nonneg]
      rw [this]
      gcongr

    have :
        (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * ((M : ℝ) * 𝔼[(fun ω => ‖ξ ω‖)])
              ≤ (3 * M) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] := by
      have hM0 : 0 ≤ (M : ℝ) := by positivity
      have hE3 : 0 ≤ 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] := by positivity
      -- First use the sharp moment bound, then relax `M` to `3*M`.
      calc
        (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * ((M : ℝ) * 𝔼[(fun ω => ‖ξ ω‖)])
            = (M : ℝ) * (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))] * 𝔼[(fun ω => ‖ξ ω‖)]) := by ring
        _ ≤ (M : ℝ) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] := by
              gcongr
        _ ≤ (3 * M) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] := by nlinarith

    exact le_trans hmain this
  -- Final assembly (avoid a trailing `calc` to keep parsing unambiguous).
  have h0 :
    ‖𝔼[(fun ω => ξ ω * F (ξ ω))]
        - (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => deriv_zbar F (ξ ω))]‖
        =
      ‖𝔼[(fun ω => ξ ω * R (ξ ω))]
              - (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => D (ξ ω))]‖ := by
            simp [hRewrite]

  have h1 :
      ‖𝔼[(fun ω => ξ ω * R (ξ ω))]
            - (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => D (ξ ω))]‖
        ≤ ‖𝔼[(fun ω => ξ ω * R (ξ ω))]‖
          + ‖(𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => D (ξ ω))]‖ := by
            -- Pin the type by providing explicit terms to `norm_sub_le`.
            simpa using
              (norm_sub_le
                (𝔼[(fun ω => ξ ω * R (ξ ω))])
                (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))] * 𝔼[(fun ω => D (ξ ω))]))

  have h2 :
      ‖𝔼[(fun ω => ξ ω * R (ξ ω))]‖
            + ‖(𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => D (ξ ω))]‖
        ≤ (M : ℝ) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))]
          + (3 * M) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] := by
            exact add_le_add hTerm1 hTerm2

  have h3 :
      ‖𝔼[(fun ω => ξ ω * R (ξ ω))]
            - (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => D (ξ ω))]‖
        ≤ (M : ℝ) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))]
            + (3 * M) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] :=
    le_trans h1 h2

  have h4 :
      ‖𝔼[(fun ω => ξ ω * F (ξ ω))]
            - (𝔼[(fun ω => ‖ξ ω‖ ^ (2 : ℕ))]) * 𝔼[(fun ω => deriv_zbar F (ξ ω))]‖
        ≤ (M : ℝ) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))]
            + (3 * M) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] := by
    simpa [h0] using h3

  have hsum :
      (M : ℝ) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))]
            + (3 * M) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))]
        = (4 * M) * 𝔼[(fun ω => ‖ξ ω‖ ^ (3 : ℕ))] := by
    ring

  refine le_trans h4 ?_
  simp [hsum]

end
end SpinGlass
