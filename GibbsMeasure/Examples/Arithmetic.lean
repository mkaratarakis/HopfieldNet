import GibbsMeasure.Potential
import GibbsMeasure.Specification
import GibbsMeasure.Prereqs.Filtration.Consistent
import Mathlib

open ENNReal MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GibbsMeasure.Examples.Arithmetic

variable {P : Type*} [DecidableEq P] [Fintype P] [MeasurableSpace P] -- Primes in the window

-- Ensure Bool has a measurable space for the Specification
instance : MeasurableSpace Bool := ⊤

/-- The single-site Hamiltonian term for a prime p.
    Y_p(σ) = 1_{σ_p} - 1/p.
    Here represented as a function on spins σ_p ∈ {0, 1}. -/
def Y (p_inv : P → ℝ) (p : P) (σ : P → Bool) : ℝ :=
  (if σ p then 1 else 0) - p_inv p

/-- The potential for the Arithmetic Spin Glass.
    Φ_{p}(σ) = Y_p(σ).
    All other interaction terms are 0. -/
noncomputable def arithmeticPotential (p_inv : P → ℝ) : Potential P Bool :=
  fun Δ σ ↦
    if h : ∃ p, Δ = {p} then
      Y p_inv h.choose σ
    else
      0

instance (p_inv : P → ℝ) : Potential.IsFinitary (arithmeticPotential p_inv) where
  finite_support := by
    let s : Finset (Finset P) := Finset.univ.map ⟨fun p ↦ {p}, by simp⟩
    apply Set.Finite.subset (s := (s : Set (Finset P)))
    · exact Finset.finite_toSet s
    · intro Δ hΔ
      simp only [arithmeticPotential, ne_eq, Set.mem_setOf_eq] at hΔ
      split at hΔ
      · obtain ⟨p, rfl⟩ := ‹∃ p, Δ = {p}›
        simp [s]
      · contradiction

instance (p_inv : P → ℝ) : Potential.IsPotential (arithmeticPotential p_inv) where
  measurable Δ := by
    simp only [arithmeticPotential]
    split_ifs with h
    · obtain ⟨p, rfl⟩ := h
      apply Measurable.sub
      · apply Measurable.ite
        · change MeasurableSet[MeasureTheory.cylinderEvents {p}] {σ | σ p}
          exact measurable_cylinderEvent_apply (i := p) (X := fun _ : P ↦ Bool) (by simp) {true} trivial
        · exact measurable_const
        · exact measurable_const
      · exact measurable_const
    · exact measurable_const

/-- The Gibbs specification for the arithmetic model. -/
noncomputable def arithmeticSpecification (p_inv : P → ℝ) (β : ℝ) (ν : Measure Bool)
    [IsProbabilityMeasure ν]
    (hZ : ∀ (Λ : Finset P) (η : P → Bool),
      Specification.premodifierZ ν (Potential.boltzmannWeight (arithmeticPotential p_inv) β) Λ η ≠ ⊤) :
    Specification P Bool :=
  Potential.gibbsSpecification (arithmeticPotential p_inv) β ν hZ

/-- The finite-volume free energy density. -/
noncomputable def freeEnergyDensity (p_inv : P → ℝ) (β : ℝ) (ν : Measure Bool)
    [IsProbabilityMeasure ν] (Λ : Finset P) (η : P → Bool) : ℝ :=
  let Z := Specification.premodifierZ ν (Potential.boltzmannWeight (arithmeticPotential p_inv) β) Λ η
  (1 / (Λ.card : ℝ)) * Real.log (ENNReal.toReal Z)

/-- The prime overlap q_{12}.
    Relates to the covariance of the Gaussian field G(σ) = ∑_p g_p Y_p(σ) by:
    Cov(G(σ₁), G(σ₂)) = L * primeOverlap σ₁ σ₂. -/
def primeOverlap (p_inv : P → ℝ) (L : ℝ) (σ₁ σ₂ : P → Bool) : ℝ :=
  (1 / L) * ∑ p : Finset.univ, Y p_inv p σ₁ * Y p_inv p σ₂

/-- The self-overlap q_{11}. -/
def selfOverlap (p_inv : P → ℝ) (L : ℝ) (σ : P → Bool) : ℝ :=
  primeOverlap p_inv L σ σ

/-- The finite-volume free energy density for the interpolated potential. -/
noncomputable def interpolatedFreeEnergyDensity (p_inv : P → ℝ) (g : P → ℝ) (t : ℝ) (β : ℝ) (ν : Measure Bool)
    [IsProbabilityMeasure ν] (Λ : Finset P) (η : P → Bool) : ℝ :=
  let Z := Specification.premodifierZ ν (Potential.boltzmannWeight (interpolatedPotential p_inv g t) β) Λ η
  (1 / (Λ.card : ℝ)) * Real.log (ENNReal.toReal Z)

/-- The derivative of the free energy density with respect to t.
    ∂_t F_N(t) = - (β / (2 * N * √t)) * ⟨ ∑_p g_p Y_p ⟩_t
    where the expectation is taken with respect to the Gibbs measure at time t. -/
noncomputable def interpolatedFreeEnergyDerivative (p_inv : P → ℝ) (g : P → ℝ) (t : ℝ) (β : ℝ) (ν : Measure Bool)
    [IsProbabilityMeasure ν] (Λ : Finset P) (η : P → Bool) : ℝ :=
  let μ := Specification.isssd ν Λ η
  let ρ := Potential.boltzmannWeight (interpolatedPotential p_inv g t) β Λ
  let Z := ∫⁻ σ, ρ σ ∂μ
  let H_deriv := fun σ ↦ ∑ p ∈ Λ, g p * Y p_inv p σ
  let num := ∫ σ, H_deriv σ * (ρ σ).toReal ∂μ
  let expectation := num / Z.toReal;
  -(β / (2 * Real.sqrt t * Λ.card)) * expectation

/-- The standard Gaussian measure on the space of coefficients P → ℝ. -/
noncomputable def standardGaussianMeasure : Measure (P → ℝ) :=
  Measure.pi (fun _ ↦ gaussianReal 0 1)

/-- The Guerra interpolation identity.
    ∂_t E[F_N(t)] = - (β^2 L / (2 N)) * E[ ⟨ q_{11} - q_{12} ⟩_t ].
    This relates the change in free energy to the variance of the overlap. -/
theorem guerra_interpolation_identity
    (p_inv : P → ℝ) (β : ℝ) (ν : Measure Bool) [IsProbabilityMeasure ν]
    (Λ : Finset P) (η : P → Bool)
    :
    ∀ t > 0,
    deriv (fun t ↦ ∫ g, interpolatedFreeEnergyDensity p_inv g t β ν Λ η ∂standardGaussianMeasure) t =
    - (β^2 * Λ.card / (2 * Λ.card)) * -- Assuming L ≈ Λ.card for normalization
      ∫ g, (
        let μ := Specification.isssd ν Λ η
        let H := interpolatedPotential p_inv g t
        let ρ := Potential.boltzmannWeight H β Λ
        let Z := ∫⁻ σ, ρ σ ∂μ
        -- The Gibbs expectation of (q11 - q12)
        (∫ σ, (selfOverlap p_inv Λ.card σ) * (ρ σ).toReal ∂μ) / Z.toReal -
        (∫ σ, (∫ σ', (primeOverlap p_inv Λ.card σ σ') * (ρ σ').toReal ∂μ) * (ρ σ).toReal ∂μ) / (Z.toReal ^ 2)
      ) ∂standardGaussianMeasure := sorry

end GibbsMeasure.Examples.Arithmetic
