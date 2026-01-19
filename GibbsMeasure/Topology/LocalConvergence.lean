import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Topology of local convergence on probability measures

This file introduces the **topology of local convergence** on `ProbabilityMeasure (S → E)`.

Informally, local convergence is the coarsest topology for which the maps

`μ ↦ μ A`

are continuous for all *cylinder events* `A`, i.e. events depending only on finitely many
coordinates. For probability measures it is enough (by a π-λ argument) to use **square cylinders**
as a generating π-system.

We define the topology as the induced topology from the evaluation map on the collection of square
cylinders. We then prove that this topology is Hausdorff (T2), and we record the usual
characterization of convergence: `μₙ → μ` iff `μₙ(A) → μ(A)` for every square cylinder `A`.
-/

open Set Filter
open scoped ENNReal

namespace MeasureTheory

namespace ProbabilityMeasure

variable {S E : Type*} [MeasurableSpace E]

/-! ### Square cylinders (measurable rectangles) -/

/-- The π-system of **square cylinders** in `(S → E)` built from measurable sets. -/
def squareCylindersMeas (S E : Type*) [MeasurableSpace E] : Set (Set (S → E)) :=
  MeasureTheory.squareCylinders (fun _ : S ↦ {s : Set E | MeasurableSet s})

/-- Evaluation of a probability measure on a square cylinder. -/
def evalSquareCylinder (S E : Type*) [MeasurableSpace E] :
    ProbabilityMeasure (S → E) → (squareCylindersMeas S E) → ℝ≥0∞ :=
  fun μ A ↦ (μ : Measure (S → E)) A.1

/-! ### Local convergence topology -/

/-- The **topology of local convergence** on `ProbabilityMeasure (S → E)`.

It is the induced topology from the evaluation map on square cylinders. -/
def localConvergence (S E : Type*) [MeasurableSpace E] : TopologicalSpace (ProbabilityMeasure (S → E)) :=
  TopologicalSpace.induced (evalSquareCylinder S E) inferInstance

lemma nhds_eq_comap_evalSquareCylinder (μ : ProbabilityMeasure (S → E)) :
    @nhds (ProbabilityMeasure (S → E)) (localConvergence S E) μ =
      Filter.comap (evalSquareCylinder S E) (nhds (evalSquareCylinder S E μ)) :=
  nhds_induced _ _

lemma tendsto_localConvergence_iff {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure (S → E)} {μ : ProbabilityMeasure (S → E)} :
    @Tendsto ι (ProbabilityMeasure (S → E)) μs l
        (@nhds (ProbabilityMeasure (S → E)) (localConvergence S E) μ) ↔
      Tendsto (fun i ↦ evalSquareCylinder S E (μs i)) l (nhds (evalSquareCylinder S E μ)) := by
  -- This is the standard `Tendsto` characterization for induced topologies.
  -- `nhds` in the induced topology is the comap of `nhds` in the codomain.
  -- First rewrite `nhds` using the induced-topology formula, then apply `tendsto_comap_iff`.
  rw [nhds_eq_comap_evalSquareCylinder (S := S) (E := E) (μ := μ)]
  rw [Filter.tendsto_comap_iff]
  rfl

/-- In the topology of local convergence, `μs → μ` iff `μs(A) → μ(A)` for every square cylinder `A`.
-/
lemma tendsto_localConvergence_iff_forall {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure (S → E)} {μ : ProbabilityMeasure (S → E)} :
    @Tendsto ι (ProbabilityMeasure (S → E)) μs l
        (@nhds (ProbabilityMeasure (S → E)) (localConvergence S E) μ) ↔
      ∀ A : squareCylindersMeas S E,
        Tendsto (fun i ↦ (μs i : Measure (S → E)) A.1) l (nhds ((μ : Measure (S → E)) A.1)) := by
  -- Convert to `Tendsto` in the Pi topology and use `tendsto_pi_nhds`.
  have := (tendsto_localConvergence_iff (S := S) (E := E) (l := l) (μs := μs) (μ := μ))
  -- Rewrite the statement of `tendsto_pi_nhds` in our notation.
  simpa [evalSquareCylinder, Function.comp] using (this.trans tendsto_pi_nhds)

/-! ### Hausdorffness -/

lemma evalSquareCylinder_injective :
    Function.Injective (evalSquareCylinder S E) := by
  classical
  intro μ₁ μ₂ h
  -- We show the underlying measures are equal by π-λ on square cylinders.
  apply Subtype.ext
  -- Use `Measure.ext_of_generateFrom_of_iUnion` on the π-system of square cylinders.
  let C : Set (Set (S → E)) := squareCylindersMeas S E
  have hC_pi : IsPiSystem C := by
    refine isPiSystem_squareCylinders (fun _ ↦ MeasurableSpace.isPiSystem_measurableSet) ?_
    intro _; exact MeasurableSet.univ
  have hgen : (inferInstance : MeasurableSpace (S → E)) = MeasurableSpace.generateFrom C := by
    simpa [C, squareCylindersMeas] using (generateFrom_squareCylinders (ι := S) (α := fun _ : S ↦ E)).symm
  -- A trivial spanning family in `C`: constant `univ`.
  let B : ℕ → Set (S → E) := fun _ ↦ Set.univ
  have h1B : (⋃ i, B i) = (Set.univ : Set (S → E)) := by
    simp [B]; aesop
  have huniv : (Set.univ : Set (S → E)) ∈ C := by
    refine ⟨∅, (fun _ : S ↦ (Set.univ : Set E)), ?_, ?_⟩
    · simp [Set.mem_pi, MeasurableSet.univ]
    · ext x; simp
  have h2B : ∀ i : ℕ, B i ∈ C := by intro _; simpa [B] using huniv
  have hμ1B : ∀ i : ℕ, (μ₁ : Measure (S → E)) (B i) ≠ ⊤ := by
    intro i
    simp [B]
  -- Apply the π-λ lemma extensionality.
  refine MeasureTheory.Measure.ext_of_generateFrom_of_iUnion (μ := (μ₁ : Measure (S → E)))
      (ν := (μ₂ : Measure (S → E))) (C := C) (B := B) (hA := hgen) (hC := hC_pi)
      (h1B := h1B) (h2B := h2B) (hμB := hμ1B) ?_
  intro s hs
  -- `h` gives equality on all square cylinders.
  have hs' : (⟨s, hs⟩ : C) = ⟨s, hs⟩ := rfl
  -- Unfold `evalSquareCylinder`.
  simpa [evalSquareCylinder] using congrArg (fun f ↦ f ⟨s, hs⟩) h

/-- The topology of local convergence is Hausdorff (T2). -/
theorem t2Space_localConvergence :
    @T2Space (ProbabilityMeasure (S → E)) (localConvergence S E) := by
  classical
  -- Work with the induced topology as an instance.
  letI : TopologicalSpace (ProbabilityMeasure (S → E)) := localConvergence S E
  -- We use the induced topology and the injective evaluation map into a Hausdorff space.
  let f := evalSquareCylinder S E
  have hf_inj : Function.Injective f := evalSquareCylinder_injective (S := S) (E := E)
  -- Build the `T2Space` structure directly from the `T2Space` of the codomain.
  refine T2Space.mk ?_
  intro μ₁ μ₂ hne
  have hne' : f μ₁ ≠ f μ₂ := by
    intro hEq
    exact hne (hf_inj hEq)
  -- Separate `f μ₁` and `f μ₂` in the codomain (a Pi of a Hausdorff space).
  rcases t2_separation hne' with ⟨U, V, hUo, hVo, hUμ, hVμ, hdisj⟩
  refine ⟨f ⁻¹' U, f ⁻¹' V, ?_, ?_, hUμ, hVμ, ?_⟩
  · -- Openness in induced topology.
    exact isOpen_induced hUo
  · exact isOpen_induced hVo
  · -- Disjointness is preserved under preimages.
    exact hdisj.preimage (f := f)

end ProbabilityMeasure

end MeasureTheory
