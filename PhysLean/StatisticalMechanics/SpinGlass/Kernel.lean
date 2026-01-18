/-
import Mathlib
import Riemann.PhysLean.SpinGlass.Replicas

open MeasureTheory ProbabilityTheory SpinGlass

-- To define overlaps, we assume the spin values can be embedded into the reals.
variable {Spin : Type*} [Fintype Spin] [MeasurableSpace Spin] [MeasurableSingletonClass Spin]
variable [CommSemiring Spin] [CoeTC Spin ℝ]

namespace PhysLean.SpinGlass

/-- The Spin Glass Kernel:
    A Georgii-style kernel from the Disorder (H) to the Configuration (σ). -/
noncomputable def skKernel (N : ℕ) (β : ℝ) (energy_map : @Config N Spin → EnergySpace N)
    [Fintype (Config N)] [MeasurableSpace (Config N)] [MeasurableSingletonClass (Config N)]
    [MeasurableSpace (EnergySpace N)] :
    Kernel (EnergySpace N) (Config N) :=
  Kernel.mk (fun h ↦
    (gibbs_pmf N β energy_map h).toMeasure
  ) (by
    refine Measure.measurable_of_measurable_coe _ (fun s _ ↦ ?_)
    simp only [PMF.toMeasure_apply]
    apply Measurable.ennreal_tsum
    intro x
    exact measurable_gibbs_pmf N β energy_map x)

/-- The Replica Expectation ⟨f⟩:
    In Vol 2, this is a monadic composition of Kernels. -/
noncomputable def replicaExpectation (n : ℕ) (N : ℕ) (β : ℝ) (energy_map : @Config N Spin → EnergySpace N)
    [Fintype (Config N)] [MeasurableSpace (Config N)] [MeasurableSingletonClass (Config N)]
    [MeasurableSpace (EnergySpace N)] :
    Kernel (EnergySpace N) (Fin n → Config N) :=
  Kernel.pi (fun _ ↦ skKernel N β energy_map)

section GhirlandaGuerra

/-- The overlap between two spin configurations. `q₁₂ = (1/N) Σᵢ σ₁ᵢ σ₂ᵢ` -/
--noncomputable def overlap (N : ℕ) (σ₁ σ₂ : @Config N Spin) : ℝ :=
--  (1 / (N : ℝ)) * ∑ i, ((σ₁ i : ℝ) * (σ₂ i : ℝ))

/-- The overlap between two replicas `a` and `b`. -/
--noncomputable def replica_overlap {n : ℕ} (N : ℕ) (σs : Fin n → @Config N Spin) (a b : Fin n) : ℝ :=
--  overlap N (σs a) (σs b)

/--
The Ghirlanda-Guerra identities.

This property of a spin glass model states that the law of the overlaps is subject to
a specific stochastic stability. A common consequence, which we formalize here, is that
for `n ≥ 2`, the expected product of overlaps with a new replica `n+1`
is equal to the expected overlap of the original two replicas.
`E[q_{0,n} q_{1,n}] = E[q₀₁]`
(See, e.g., Talagrand, "Spin Glasses: A Challenge for Mathematicians", Vol 1, Eq. 2.5.2, using 0-based indexing)

This property holds for the Sherrington-Kirkpatrick model and is a cornerstone of the
proof of the Parisi formula. It is a property of the full quenched measure, averaged over
the disorder.
-/
def HasGhirlandaGuerraIdentities (N : ℕ) (β : ℝ) (energy_map : @Config N Spin → EnergySpace N)
    [Fintype (Config N)] [MeasurableSpace (Config N)] [MeasurableSingletonClass (Config N)]
    [MeasurableSpace (EnergySpace N)]
    (P_H : Measure (EnergySpace N)) [IsProbabilityMeasure P_H] : Prop :=
  ∀ n ≥ 2,
    let κ := skKernel N β energy_map
    let μ_quenched (k : ℕ) := P_H ∘ₖ (Kernel.pi (fun _ : Fin k => κ))
    let lhs_integrand (σs : Fin (n + 1) → Config N) := replica_overlap N σs 0 n * replica_overlap N σs 1 n
    let rhs_integrand (σs : Fin 2 → Config N) := replica_overlap N σs 0 1
    ∫ σs, lhs_integrand σs ∂(μ_quenched (n + 1)) = ∫ σs, rhs_integrand σs ∂(μ_quenched 2)

end GhirlandaGuerra

end PhysLean.SpinGlass
#min_imports-/
