import GibbsMeasure.Prereqs.Kernel.Feller
import GibbsMeasure.Specification
import GibbsMeasure.Specification.Quasilocal
import Mathlib.Topology.Continuous

/-!
# Quasilocal specifications (Georgii, Def. 2.23)

This file links the *functional-analytic* notion of quasilocal observables to specifications.

Assuming a specification `γ` is **Markov** and its kernels are **Feller** (in the sense of
`ProbabilityTheory.Kernel.IsFeller`), we can define the induced action on bounded continuous
observables:

`f ↦ (η ↦ ∫ x, f x ∂(γ Λ η))`.

A specification is **quasilocal** (Georgii, Def. 2.23) if this action preserves the submodule of
quasilocal observables (uniform closure of cylinder observables).

We also record the convenient “dense-check” formulation: it suffices to verify quasilocality on
cylinder observables, since the action is continuous in the sup-norm.
-/

open Set
open scoped Topology

namespace Specification

open ProbabilityTheory

variable {S E : Type*} [MeasurableSpace E] [TopologicalSpace E]
variable [OpensMeasurableSpace (S → E)]

-- We work with bounded continuous observables on the configuration space.
open BoundedContinuousFunction
local notation3 (prettyPrint := false) "Obs" => ((S → E) →ᵇ ℝ)

/-- A specification is **Feller** if all of its finite-volume kernels are Feller kernels. -/
class IsFeller (γ : Specification S E) : Prop where
  isFellerKernel : ∀ Λ, ProbabilityTheory.Kernel.IsFeller (γ Λ)

attribute [instance] IsFeller.isFellerKernel

namespace IsFeller

instance (γ : Specification S E) [γ.IsFeller] (Λ : Finset S) : ProbabilityTheory.Kernel.IsFeller (γ Λ) :=
  IsFeller.isFellerKernel (γ := γ) Λ

end IsFeller

section Action

variable (γ : Specification S E)
variable [γ.IsMarkov] [γ.IsFeller]

/-- The (Feller) action of `γ(Λ)` on bounded continuous observables. -/
noncomputable def continuousAction (Λ : Finset S) : Obs → Obs :=
  fun f => ProbabilityTheory.Kernel.continuousAction (κ := γ Λ) f

omit [OpensMeasurableSpace (S → E)] in
@[simp] lemma continuousAction_apply (Λ : Finset S) (f : Obs) (η : S → E) :
    continuousAction (γ := γ) Λ f η = ∫ x, f x ∂(γ Λ η) := by
  simp [continuousAction]

/-- The action operator as a continuous linear map on observables. -/
noncomputable def continuousActionCLM (Λ : Finset S) : Obs →L[ℝ] Obs :=
  ProbabilityTheory.Kernel.continuousActionCLM (κ := γ Λ)

@[simp] lemma continuousActionCLM_apply (Λ : Finset S) (f : Obs) :
    continuousActionCLM (γ := γ) Λ f = continuousAction (γ := γ) Λ f :=
  rfl

lemma continuous_continuousAction (Λ : Finset S) :
    Continuous (continuousAction (γ := γ) Λ : Obs → Obs) :=
  (continuousActionCLM (γ := γ) Λ).continuous

end Action

/-! ### Quasilocality (Georgii Def. 2.23) -/

section Quasilocal

variable (γ : Specification S E)
variable [γ.IsMarkov] [γ.IsFeller]

open BoundedContinuousFunction

/-- A specification is **quasilocal** if its Feller action preserves quasilocal observables. -/
def IsQuasilocal : Prop :=
  ∀ (Λ : Finset S) (f : Obs),
    f ∈ quasilocalFunctions (S := S) (E := E) (F := ℝ) →
      continuousAction (γ := γ) Λ f ∈ quasilocalFunctions (S := S) (E := E) (F := ℝ)

/-- Dense-check version: it suffices to verify quasilocality on cylinder observables. -/
def IsQuasilocal' : Prop :=
  ∀ (Λ : Finset S) (f : Obs),
    f ∈ cylinderFunctions (S := S) (E := E) (F := ℝ) →
      continuousAction (γ := γ) Λ f ∈ quasilocalFunctions (S := S) (E := E) (F := ℝ)

lemma IsQuasilocal.of_IsQuasilocal' (h : IsQuasilocal' (γ := γ)) : IsQuasilocal (γ := γ) := by
  intro Λ f hf
  -- `f` is in the closure of the cylinder observables.
  have hf' : f ∈ closure (cylinderFunctions (S := S) (E := E) (F := ℝ) : Set Obs) := by
    simpa [quasilocalFunctions, Submodule.topologicalClosure_coe] using hf
  -- Apply continuity of the action map to move from `closure` to `closure`.
  have h_cont : Continuous (continuousAction (γ := γ) Λ : Obs → Obs) :=
    continuous_continuousAction (γ := γ) Λ
  have himage :
      continuousAction (γ := γ) Λ f ∈
        closure ((continuousAction (γ := γ) Λ) '' (cylinderFunctions (S := S) (E := E) (F := ℝ) : Set Obs)) :=
    by
      let s : Set Obs := (cylinderFunctions (S := S) (E := E) (F := ℝ) : Set Obs)
      have hx : continuousAction (γ := γ) Λ f ∈ (continuousAction (γ := γ) Λ) '' closure s :=
        ⟨f, hf', rfl⟩
      exact (image_closure_subset_closure_image h_cont (s := s)) hx
  -- The image of cylinder observables is contained in quasilocal observables by `h`.
  have hsubset :
      (continuousAction (γ := γ) Λ) '' (cylinderFunctions (S := S) (E := E) (F := ℝ) : Set Obs) ⊆
        (quasilocalFunctions (S := S) (E := E) (F := ℝ) : Set Obs) := by
    intro g hg
    rcases hg with ⟨f0, hf0, rfl⟩
    exact h Λ f0 hf0
  -- `quasilocalFunctions` is closed (it's a topological closure).
  have hclosed :
      IsClosed (quasilocalFunctions (S := S) (E := E) (F := ℝ) : Set Obs) :=
    Submodule.isClosed_topologicalClosure _
  -- Conclude using `closure_mono` and `hclosed.closure_eq`.
  have :
      continuousAction (γ := γ) Λ f ∈
        closure (quasilocalFunctions (S := S) (E := E) (F := ℝ) : Set Obs) :=
    closure_mono hsubset himage
  simpa [hclosed.closure_eq, quasilocalFunctions] using this

lemma IsQuasilocal_iff_IsQuasilocal' :
    IsQuasilocal (γ := γ) ↔ IsQuasilocal' (γ := γ) := by
  constructor
  · intro h Λ f hf
    -- Cylinder observables are quasilocal by definition.
    have hf' : f ∈ quasilocalFunctions (S := S) (E := E) (F := ℝ) :=
      cylinderFunctions_le_quasilocalFunctions (S := S) (E := E) (F := ℝ) hf
    exact h Λ f hf'
  · intro h
    exact IsQuasilocal.of_IsQuasilocal' (γ := γ) h

end Quasilocal

end Specification
