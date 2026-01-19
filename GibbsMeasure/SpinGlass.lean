import GibbsMeasure.Potential
import GibbsMeasure.Specification
import GibbsMeasure.Prereqs.Filtration.Consistent
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
--import Riemann.PhysLean.SpinGlass.Kernel

open ENNReal MeasureTheory

namespace GibbsMeasure.Examples.SpinGlass

variable {V : Type*} [DecidableEq V] [Fintype V] -- Vertices/Spins

-- Ensure Int has a measurable space
instance : MeasurableSpace Int := ⊤


/-- The Sherrington-Kirkpatrick (or Edwards-Anderson) potential.
    Φ_{ij}(σ) = - J_{ij} * σ_i * σ_j.
    (Using -J for ferromagnetic convention, or just J). -/
def skPotential (J : V → V → ℝ) : Potential V Int :=
  fun Δ σ ↦
    if h : ∃ i j, i ≠ j ∧ Δ = {i, j} then
      let ⟨i, j, _⟩ := h
      -- We need to be careful with double counting if {i,j} = {j,i}.
      -- The potential is defined on the set Δ.
      -- J should be symmetric.
      - J i j * (σ i : ℝ) * (σ j : ℝ)
    else
      0

instance (J : V → V → ℝ) : Potential.IsFinitary (skPotential J) where
  finite_support := by
    let s : Finset (Finset V) := Finset.univ.biUnion fun i ↦ Finset.univ.map ⟨fun j ↦ {i, j}, by simp⟩
    apply Set.Finite.subset (s := (s : Set (Finset V)))
    · exact Finset.finite_toSet s
    · intro Δ hΔ
      simp only [skPotential, ne_eq, Set.mem_setOf_eq] at hΔ
      split at hΔ
      · obtain ⟨i, j, _, rfl⟩ := ‹∃ i j, i ≠ j ∧ Δ = {i, j}›
        simp [s]
      · contradiction

instance (J : V → V → ℝ) : Potential.IsPotential (skPotential J) where
  measurable Δ := by
    simp only [skPotential]
    split_ifs with h
    · obtain ⟨i, j, _, rfl⟩ := h
      apply Measurable.mul
      · apply Measurable.mul
        · exact measurable_const
        · exact (measurable_from_top.comp (measurable_cylinderEvent_apply (i := i) (X := fun _ : V ↦ Int) (by simp)))
      · exact (measurable_from_top.comp (measurable_cylinderEvent_apply (i := j) (X := fun _ : V ↦ Int) (by simp)))
    · exact measurable_const

/-- The Gibbs specification for the SK model. -/
noncomputable def skSpecification (J : V → V → ℝ) (β : ℝ) (ν : Measure Int)
    [IsProbabilityMeasure ν]
    (hZ : ∀ (Λ : Finset V) (η : V → Int),
      Specification.premodifierZ ν (Potential.boltzmannWeight (skPotential J) β) Λ η ≠ ⊤) :
    Specification V Int :=
  Potential.gibbsSpecification (skPotential J) β ν hZ


end GibbsMeasure.Examples.SpinGlass
