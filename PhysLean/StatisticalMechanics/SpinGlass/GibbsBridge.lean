/-import GibbsMeasure.Mathlib.MeasureTheory.Measure.GiryMonad
import GibbsMeasure.KolmogorovExtension4.ProductMeasure
import GibbsMeasure.Prereqs.Filtration.Consistent
import GibbsMeasure.Prereqs.Juxt
import GibbsMeasure.Prereqs.Kernel.CondExp
import Riemann.PhysLean.SpinGlass.SKModel

/-!
  BRIDGE:
  Wrapping our 'gibbs_pmf' (Vol 1 Calculus)
  into a Georgii 'ProperKernel' (Vol 2 Structure).
-/

/-- The Spin Glass Kernel:
    A Georgii-style kernel from the Disorder (H) to the Configuration (σ). -/
noncomputable def skKernel (N : ℕ) (β : ℝ) (energy_map : Config N → EnergySpace N) :
    Kernel (EnergySpace N) (Config N) :=
  Kernel.mk (fun h ↦
    -- Use our 'gibbs_pmf' logic here to define the measure
    Measure.from_gibbs_pmf (SpinGlass.gibbs_pmf N h)
  ) (sorry)

/-- The Replica Expectation ⟨f⟩:
    In Vol 2, this is a monadic composition of Kernels. -/
noncomputable def replicaExpectation (n : ℕ) : Kernel (EnergySpace N) (Fin n → Config N) :=
  (skKernel N β energy_map).prod_n n

-/
