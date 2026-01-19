import GibbsMeasure.Specification.Structure
import GibbsMeasure.Specification.QuasilocalSpecification
import GibbsMeasure.Topology.LocalConvergence
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Thermodynamic limits (Georgii, Ch. 4 — setup)

This file introduces the basic objects used to state *existence* results for Gibbs measures:

- the directed system of finite volumes `Λ : Finset S` with the filter `atTop`;
- the net of finite-volume Gibbs distributions `Λ ↦ γ Λ η`;
- the predicate `IsThermodynamicLimit` (cluster point along `atTop`), using the topology of
  **local convergence** from `GibbsMeasure/Topology/LocalConvergence.lean`.
We prove Existence of a Gibbs measure on a **compact** single-spin space.

-/

open Filter

namespace MeasureTheory

namespace GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

variable (γ : Specification S E)

/-- The filter corresponding to the limit `Λ → S` along the directed set of finite subsets. -/
def volumeLimit (S : Type*) : Filter (Finset S) :=
  Filter.atTop

/-- The net of finite-volume Gibbs distributions with boundary condition `η`. -/
noncomputable def finiteVolumeDistributions [γ.IsMarkov] (η : S → E) :
    (Finset S) → ProbabilityMeasure (S → E) :=
  fun Λ => ⟨γ Λ η, inferInstance⟩

/-- A probability measure `μ` is a thermodynamic limit (for boundary condition `η`) if it is a
cluster point of the net `Λ ↦ γ Λ η` in the topology of local convergence. -/
def IsThermodynamicLimit [γ.IsMarkov] (η : S → E) (μ : ProbabilityMeasure (S → E)) : Prop :=
  letI : TopologicalSpace (ProbabilityMeasure (S → E)) :=
    ProbabilityMeasure.localConvergence S E
  ClusterPt μ (Filter.map (finiteVolumeDistributions (γ := γ) η) (volumeLimit S))

/-! ### Existence on compact spaces via Prokhorov + Feller continuity (weak topology) -/

section WeakCompact

open scoped Topology BoundedContinuousFunction
open BoundedContinuousFunction

variable {S E : Type*} [MeasurableSpace E] [TopologicalSpace E]

-- Weak topology on probability measures requires measurability of open sets in the configuration space.
variable [OpensMeasurableSpace (S → E)]

variable (γ : Specification S E)

 /-- Thermodynamic limit defined using the **weak topology** on `ProbabilityMeasure (S → E)`
(`MeasureTheory.ProbabilityMeasure`'s default topology instance). -/
def IsThermodynamicLimitWeak [γ.IsMarkov] (η : S → E) (μ : ProbabilityMeasure (S → E)) : Prop :=
  ClusterPt μ (Filter.map (finiteVolumeDistributions (γ := γ) η) (volumeLimit S))

namespace Specification

open ProbabilityTheory

variable {γ}
variable [γ.IsMarkov]

omit [TopologicalSpace E] [OpensMeasurableSpace (S → E)] [γ.IsMarkov] in
-- A helper: kernels of a specification are measurable as functions into measures for the *full*
-- product σ-algebra (even though they are defined with `cylinderEvents (Λᶜ)` as source σ-algebra).
lemma measurable_kernel_toMeasure (Λ : Finset S) :
    @Measurable (S → E) (Measure (S → E)) MeasurableSpace.pi Measure.instMeasurableSpace (γ Λ) := by
  -- Start from kernel-measurability on `cylinderEvents (Λᶜ)` and widen the source measurable space.
  exact (Kernel.measurable (γ Λ)).mono
    (MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ))) le_rfl

/-- Bind a probability measure by a specification kernel (as a probability measure). -/
noncomputable def bindPM (Λ : Finset S) (μ : ProbabilityMeasure (S → E)) :
    ProbabilityMeasure (S → E) :=
  ⟨(μ : Measure (S → E)).bind (γ Λ), by
    -- `μ.bind (γ Λ)` is a probability measure because `γ Λ` is Markov.
    have hAEM : AEMeasurable (γ Λ) (μ : Measure (S → E)) :=
      (measurable_kernel_toMeasure (γ := γ) Λ).aemeasurable
    haveI : IsProbabilityMeasure (μ : Measure (S → E)) := by infer_instance
    constructor
    -- compute mass on `univ`
    rw [Measure.bind_apply MeasurableSet.univ hAEM]
    -- integrand is constantly `1`
    simp⟩

omit [TopologicalSpace E] [OpensMeasurableSpace (S → E)] in
@[simp] lemma coe_bindPM (Λ : Finset S) (μ : ProbabilityMeasure (S → E)) :
    ((bindPM (γ := γ) Λ μ : ProbabilityMeasure (S → E)) : Measure (S → E)) =
      (μ : Measure (S → E)).bind (γ Λ) :=
  rfl

variable [γ.IsFeller]
--variable [T2Space E] [OpensMeasurableSpace (S → E)]


/-- Feller continuity: `μ ↦ μ.bind (γ Λ)` is continuous for the weak topology on probability measures. -/
theorem continuous_bindPM (Λ : Finset S) :
    Continuous (bindPM (γ := γ) Λ :
      ProbabilityMeasure (S → E) → ProbabilityMeasure (S → E)) := by
  -- Use the characterization of continuity in the weak topology by testing against bounded continuous functions.
  refine (MeasureTheory.ProbabilityMeasure.continuous_iff_forall_continuous_integral
    (μs := (bindPM (γ := γ) Λ))).2 ?_
  intro f
  -- Let `g x := ∫ y, f y ∂(γ Λ x)`; this is bounded continuous by the Feller property.
  let g : BoundedContinuousFunction (S → E) ℝ :=
    ProbabilityTheory.Kernel.continuousAction (κ := γ Λ) f
  have hg : Continuous fun μ : ProbabilityMeasure (S → E) => ∫ x, g x ∂(μ : Measure (S → E)) := by
    -- This is exactly `continuous_integral_boundedContinuousFunction`, just with a minor coercion.
    simpa using
      (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction (f := g)
        (X := (S → E)))
  -- Rewrite the integral against the bound measure as an integral of `g` against `μ`.
  have hEq :
      (fun μ : ProbabilityMeasure (S → E) =>
          ∫ x, f x ∂((μ : Measure (S → E)).bind (γ Λ)))
        =
      (fun μ : ProbabilityMeasure (S → E) =>
          ∫ x, g x ∂(μ : Measure (S → E))) := by
    funext μ
    -- Apply `integral_comp` to the composition of kernels `γ Λ ∘ₖ const μ`. We first coarsen the
    -- domain σ-algebra of `γ Λ` to the full product σ-algebra using `Kernel.comap id …`.
    let ηpi : Kernel (S → E) (S → E) :=
      (γ Λ).comap id (MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ)))
    let κ0 : Kernel Unit (S → E) := Kernel.const Unit (μ : Measure (S → E))
    have hcomp : (ηpi ∘ₖ κ0) () = (μ : Measure (S → E)).bind (γ Λ) := by
      -- `comp_apply` reduces to `Measure.bind`; `ηpi` has the same underlying function as `γ Λ`.
      simp [ηpi, κ0]
    -- `f` is integrable against any probability measure.
    haveI : IsFiniteMeasure ((μ : Measure (S → E)).bind (γ Λ)) := by
      -- `bind` is a probability measure.
      haveI :
          IsProbabilityMeasure
            ((bindPM (γ := γ) Λ μ : ProbabilityMeasure (S → E)) : Measure (S → E)) := by
        infer_instance
      simpa [coe_bindPM] using
        (inferInstance :
          IsFiniteMeasure
            ((bindPM (γ := γ) Λ μ : ProbabilityMeasure (S → E)) : Measure (S → E)))
    have hf_int : Integrable (fun x : S → E => f x) ((μ : Measure (S → E)).bind (γ Λ)) := by
      simpa using (BoundedContinuousFunction.integrable (μ := (μ : Measure (S → E)).bind (γ Λ)) f)
    -- Main computation.
    have hf_int' : Integrable (fun x : S → E => f x) ((ηpi ∘ₖ κ0) ()) := by
      simpa [hcomp] using hf_int
    have := ProbabilityTheory.Kernel.integral_comp (κ := κ0) (η := ηpi) (a := ())
      (f := fun x : S → E => f x) hf_int'
    -- Unpack `g` and simplify.
    -- RHS: outer integral is w.r.t. `κ0 () = μ`.
    -- LHS: the composed kernel at `()` is `μ.bind (γ Λ)`.
    simpa [hcomp, κ0, ηpi, g, Kernel.const_apply,
      ProbabilityTheory.Kernel.continuousAction_apply] using this
  -- Finish by rewriting to the continuous expression.
  simpa [Specification.bindPM, Specification.coe_bindPM, hEq] using hg

end Specification

open Specification

variable [γ.IsMarkov] [γ.IsFeller]
--variable [T2Space E] [OpensMeasurableSpace (S → E)]
variable [T2Space (ProbabilityMeasure (S → E))]
--set_option linter.unusedSectionVars false
/-- Any **weak** thermodynamic limit of finite-volume distributions is a Gibbs measure (compact case
uses this with existence of a cluster point). -/
theorem isGibbsMeasure_of_isThermodynamicLimitWeak
    (hγ : γ.IsProper) (η : S → E) {μ : ProbabilityMeasure (S → E)}
    (hμ : IsThermodynamicLimitWeak (γ := γ) η μ) :
    μ ∈ GP (S := S) (E := E) γ := by
  -- Use the fixed-point characterization `μ.bind (γ Λ) = μ`.
  have hfix : ∀ Λ : Finset S, (μ : Measure (S → E)).bind (γ Λ) = (μ : Measure (S → E)) := by
    intro Λ
    -- Work with the cluster-point filter `𝓝 μ ⊓ F`.
    let μs : Finset S → ProbabilityMeasure (S → E) := finiteVolumeDistributions (γ := γ) η
    let F : Filter (ProbabilityMeasure (S → E)) := Filter.map μs (volumeLimit S)
    have h_ne : NeBot (𝓝 μ ⊓ F) := hμ
    -- The map `ν ↦ ν.bind (γ Λ)` is continuous.
    have hcont :
        Continuous (Specification.bindPM (γ := γ) Λ :
          ProbabilityMeasure (S → E) → ProbabilityMeasure (S → E)) :=
      Specification.continuous_bindPM (γ := γ) Λ
    -- Eventually along `F`, `μs` is fixed by binding with `γ Λ` (by specification consistency).
    have h_event_F :
        ∀ᶠ ν in F, Specification.bindPM (γ := γ) Λ ν = ν := by
      -- unfold `F` and use that `Λ ≤ Λ'` eventually along `atTop`.
      -- (`atTop` on `Finset` is eventual containment.)
      have h_event_atTop :
          ∀ᶠ Λ' in (volumeLimit S : Filter (Finset S)),
            Specification.bindPM (γ := γ) Λ (μs Λ') = μs Λ' := by
        -- take `Λ` as the threshold
        refine Filter.eventually_atTop.2 ?_
        refine ⟨Λ, ?_⟩
        intro Λ' hΛ
        -- `hΛ : Λ ≤ Λ'` is `Λ ⊆ Λ'`.
        apply Subtype.ext
        -- equality of underlying measures by specification consistency
        simpa [μs, finiteVolumeDistributions, Specification.coe_bindPM] using
          (_root_.Specification.bind (γ := γ) (hΛ := hΛ) (η := η))
      -- push forward along `μs`
      simpa [F, μs] using h_event_atTop
    -- Transport eventual fixed-point to `𝓝 μ ⊓ F`.
    have h_event :
        ∀ᶠ ν in (𝓝 μ ⊓ F), Specification.bindPM (γ := γ) Λ ν = ν :=
      (inf_le_right : (𝓝 μ ⊓ F) ≤ F) h_event_F
    -- `id` tends to `μ` along `𝓝 μ ⊓ F`.
    have hid : Tendsto id (𝓝 μ ⊓ F) (𝓝 μ) :=
      (tendsto_id'.2 (inf_le_left : (𝓝 μ ⊓ F) ≤ 𝓝 μ))
    -- Replace `id` by the eventually equal map `ν ↦ ν.bind (γ Λ)`.
    have hbind_to_μ : Tendsto (Specification.bindPM (γ := γ) Λ) (𝓝 μ ⊓ F) (𝓝 μ) :=
      hid.congr' (h_event.mono fun ν hν => by simpa [id, Function.id_def] using hν.symm)
    have hbind_to_bindμ : Tendsto (Specification.bindPM (γ := γ) Λ) (𝓝 μ ⊓ F)
        (𝓝 (Specification.bindPM (γ := γ) Λ μ)) :=
      (hcont.tendsto μ).mono_left inf_le_left
    -- Uniqueness of limits in `ProbabilityMeasure (S → E)` (weak topology) uses the `T2Space`
    -- instance assumed in this section.
    have : Specification.bindPM (γ := γ) Λ μ = μ := tendsto_nhds_unique hbind_to_bindμ hbind_to_μ
    -- Convert to an equality of underlying measures.
    simpa [Specification.bindPM, Specification.coe_bindPM] using
      congrArg (fun ν : ProbabilityMeasure (S → E) => (ν : Measure (S → E))) this
  -- Conclude Gibbs property from the fixed-point equation.
  simpa [GP, Specification.isGibbsMeasure_iff_forall_bind_eq (γ := γ) hγ] using hfix

section Compact

variable [CompactSpace E]
variable [BorelSpace E] [SecondCountableTopology E] [Countable S]
variable [T2Space E]
/-- Existence of a Gibbs measure on a **compact** single-spin space, via compactness of
`ProbabilityMeasure (S → E)` (Prokhorov) and the previous limit-closure lemma. -/
theorem existence_of_gibbsMeasure_compact (hγ : γ.IsProper) (η : S → E) :
    (GP (S := S) (E := E) γ).Nonempty := by
  classical
  -- Use compactness of `ProbabilityMeasure (S → E)` (weak topology) to extract a cluster point.
  haveI : CompactSpace (ProbabilityMeasure (S → E)) := by infer_instance
  let μs : Finset S → ProbabilityMeasure (S → E) := finiteVolumeDistributions (γ := γ) η
  let F : Filter (ProbabilityMeasure (S → E)) := Filter.map μs (volumeLimit S)
  -- `atTop` on `Finset S` is nontrivial, hence so is its pushforward along `μs`.
  haveI : NeBot (volumeLimit S : Filter (Finset S)) := by
    simpa [volumeLimit] using (Filter.atTop_neBot (α := Finset S))
  haveI : NeBot F := by infer_instance
  obtain ⟨μ, hμ⟩ : ∃ μ : ProbabilityMeasure (S → E), ClusterPt μ F :=
    exists_clusterPt_of_compactSpace F
  refine ⟨μ, ?_⟩
  exact isGibbsMeasure_of_isThermodynamicLimitWeak (γ := γ) (hγ := hγ) (η := η) hμ

end Compact

/-! ### Existence from tightness (Prokhorov) -/

section Tight

variable [T2Space (S → E)] [BorelSpace (S → E)]

/-- Existence of a Gibbs measure from **tightness** of the finite-volume distributions, using
Prokhorov compactness of the closure of a tight set. -/
theorem existence_of_gibbsMeasure_of_isTight
    (hγ : γ.IsProper) (η : S → E)
    (hT :
      IsTightMeasureSet
        {x : Measure (S → E) |
          ∃ μ ∈ Set.range (finiteVolumeDistributions (γ := γ) η),
            (μ : Measure (S → E)) = x}) :
    (GP (S := S) (E := E) γ).Nonempty := by
  classical
  -- Apply Prokhorov: closure of a tight set of probability measures is compact.
  let μs : Finset S → ProbabilityMeasure (S → E) := finiteVolumeDistributions (γ := γ) η
  let Sset : Set (ProbabilityMeasure (S → E)) := Set.range μs
  have hcompact : IsCompact (closure Sset) := by
    -- `hT` is exactly the tightness assumption in the statement of Prokhorov's theorem.
    simpa [Sset] using
      (isCompact_closure_of_isTightMeasureSet (E := (S → E)) (S := Sset) (hS := hT))
  -- Extract a cluster point of the net `Λ ↦ μs Λ` in the compact set `closure Sset`.
  let F : Filter (ProbabilityMeasure (S → E)) := Filter.map μs (volumeLimit S)
  haveI : NeBot (volumeLimit S : Filter (Finset S)) := by
    simpa [volumeLimit] using (Filter.atTop_neBot (α := Finset S))
  haveI : NeBot F := by infer_instance
  have hF_le : F ≤ 𝓟 (closure Sset) := by
    -- First, `map μs (volumeLimit S)` is supported on the range of `μs`.
    have hF_range : F ≤ 𝓟 (Set.range μs) := by
      intro s hs
      have hsub : Set.range μs ⊆ s := hs
      have : μs ⁻¹' s = (Set.univ : Set (Finset S)) := by
        ext Λ
        constructor
        · intro _; trivial
        · intro _; exact hsub ⟨Λ, rfl⟩
      -- Membership in `map` is membership of the preimage.
      simp [F, Filter.map, this]
    -- Then enlarge to the closure.
    exact hF_range.trans (Filter.principal_mono.2 subset_closure)
  obtain ⟨μ, _hμ_mem, hμ⟩ : ∃ μ ∈ closure Sset, ClusterPt μ F :=
    hcompact.exists_clusterPt (f := F) hF_le
  refine ⟨μ, ?_⟩
  -- Any cluster point is a Gibbs measure.
  exact isGibbsMeasure_of_isThermodynamicLimitWeak (γ := γ) (hγ := hγ) (η := η) hμ

end Tight

/-! ### Topological properties of `GP(γ)` (weak topology) -/

section GPTopology

open scoped Topology

variable {S E : Type*} [MeasurableSpace E] [TopologicalSpace E]
variable [OpensMeasurableSpace (S → E)]

variable (γ : Specification S E)
variable [γ.IsMarkov] [γ.IsFeller]
variable [T2Space (ProbabilityMeasure (S → E))]

omit [TopologicalSpace
  E] [OpensMeasurableSpace (S → E)] [γ.IsFeller] [T2Space (ProbabilityMeasure (S → E))] in
/-- Fixed-point characterization of Gibbs probability measures, expressed using `bindPM`. -/
lemma mem_GP_iff_forall_bindPM_eq (hγ : γ.IsProper) (μ : ProbabilityMeasure (S → E)) :
    μ ∈ GP (S := S) (E := E) γ ↔ ∀ Λ : Finset S, Specification.bindPM (γ := γ) Λ μ = μ := by
  constructor
  · intro hμ
    -- Convert `μ ∈ GP γ` to the `bind` fixed-point property at the level of measures.
    have hμ' :
        ∀ Λ : Finset S, (μ : Measure (S → E)).bind (γ Λ) = (μ : Measure (S → E)) := by
      have hGibbs : γ.IsGibbsMeasure (μ : Measure (S → E)) := hμ
      haveI : IsFiniteMeasure (μ : Measure (S → E)) := by infer_instance
      simpa [_root_.Specification.isGibbsMeasure_iff_forall_bind_eq (γ := γ) hγ] using hGibbs
    intro Λ
    -- Upgrade the measure equality to an equality of probability measures.
    apply Subtype.ext
    simpa [Specification.coe_bindPM] using hμ' Λ
  · intro hfix
    -- Convert the `bindPM` fixed-point property to the `bind` fixed-point property for measures.
    have hfix' :
        ∀ Λ : Finset S, (μ : Measure (S → E)).bind (γ Λ) = (μ : Measure (S → E)) := by
      intro Λ
      have := congrArg (fun ν : ProbabilityMeasure (S → E) => (ν : Measure (S → E))) (hfix Λ)
      simpa [Specification.coe_bindPM] using this
    -- Turn the fixed-point property into the Gibbs property.
    haveI : IsFiniteMeasure (μ : Measure (S → E)) := by infer_instance
    have : γ.IsGibbsMeasure (μ : Measure (S → E)) := by
      simpa [_root_.Specification.isGibbsMeasure_iff_forall_bind_eq (γ := γ) hγ] using hfix'
    exact this

/-- `GP(γ)` is closed in the weak topology, provided `γ` is Feller and proper. -/
theorem isClosed_GP (hγ : γ.IsProper) :
    IsClosed (GP (S := S) (E := E) γ) := by
  classical
  -- Express `GP(γ)` as an intersection of fixed-point sets of continuous maps.
  have hGP :
      GP (S := S) (E := E) γ =
        ⋂ Λ : Finset S, {μ : ProbabilityMeasure (S → E) | Specification.bindPM (γ := γ) Λ μ = μ} := by
    ext μ
    simp [mem_GP_iff_forall_bindPM_eq (γ := γ) hγ μ]
  -- Each fixed-point set is closed, hence the intersection is closed.
  have hclosed :
      ∀ Λ : Finset S,
        IsClosed {μ : ProbabilityMeasure (S → E) | Specification.bindPM (γ := γ) Λ μ = μ} := by
    intro Λ
    -- Closedness of an equalizer of continuous maps in a T2 space.
    have hcont : Continuous (Specification.bindPM (γ := γ) Λ :
        ProbabilityMeasure (S → E) → ProbabilityMeasure (S → E)) :=
      Specification.continuous_bindPM (γ := γ) Λ
    simpa using isClosed_eq hcont continuous_id
  simpa [hGP] using isClosed_iInter hclosed

/-- If the ambient space of probability measures is compact, then `GP(γ)` is compact
(`GP(γ)` is closed by `isClosed_GP`). -/
theorem isCompact_GP [CompactSpace (ProbabilityMeasure (S → E))] (hγ : γ.IsProper) :
    IsCompact (GP (S := S) (E := E) γ) :=
  (isClosed_GP (γ := γ) hγ).isCompact

end GPTopology

end WeakCompact

end GibbsMeasure

end MeasureTheory
