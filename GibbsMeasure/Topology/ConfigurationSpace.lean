import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Basic

/-!
# Topology and measurability of configuration spaces

This file provides lightweight, Mathlib-aligned infrastructure for configuration spaces of the form
`S → E`.

The main points are:
- The product topology on `S → E` is available via the standard `Pi` instances.
- If `S` is countable and `E` is second-countable Borel, then `S → E` is a `BorelSpace` as well
  (Mathlib instance `Pi.borelSpace`). In particular, the *existing* measurable space on `S → E`
  (the product `MeasurableSpace.pi`) coincides with `borel (S → E)`.

We also record the standard notion of a **cylinder (local) observable**: a function depending only
on finitely many coordinates.
-/

namespace GibbsMeasure

namespace ConfigurationSpace

open scoped BigOperators

variable {S E : Type*}

/-! ### Cylinder (local) observables -/

/-- A function `f : (S → E) → F` is a **cylinder function** if it depends only on finitely many
coordinates. -/
def IsCylinderFunction {F : Type*} (f : (S → E) → F) : Prop :=
  ∃ Λ : Finset S, ∀ σ₁ σ₂ : S → E, (∀ x ∈ Λ, σ₁ x = σ₂ x) → f σ₁ = f σ₂

namespace IsCylinderFunction

variable {F : Type*}

lemma congr {f g : (S → E) → F} (hf : IsCylinderFunction (S := S) (E := E) f) (hfg : f = g) :
    IsCylinderFunction (S := S) (E := E) g := by
  simpa [hfg] using hf

lemma const (c : F) : IsCylinderFunction (S := S) (E := E) (fun _ : S → E ↦ c) := by
  refine ⟨∅, ?_⟩
  intro _ _ _; rfl

lemma add {F : Type*} [Add F] {f g : (S → E) → F}
    (hf : IsCylinderFunction (S := S) (E := E) f)
    (hg : IsCylinderFunction (S := S) (E := E) g) :
    IsCylinderFunction (S := S) (E := E) (fun σ ↦ f σ + g σ) := by
  classical
  rcases hf with ⟨Λf, hf⟩
  rcases hg with ⟨Λg, hg⟩
  refine ⟨Λf ∪ Λg, ?_⟩
  intro σ₁ σ₂ hσ
  have hf' : f σ₁ = f σ₂ := hf σ₁ σ₂ (fun x hx ↦ hσ x (Finset.mem_union_left _ hx))
  have hg' : g σ₁ = g σ₂ := hg σ₁ σ₂ (fun x hx ↦ hσ x (Finset.mem_union_right _ hx))
  simp [hf', hg']

lemma smul {𝕜 F : Type*} [SMul 𝕜 F] {c : 𝕜} {f : (S → E) → F}
    (hf : IsCylinderFunction (S := S) (E := E) f) :
    IsCylinderFunction (S := S) (E := E) (fun σ ↦ c • f σ) := by
  rcases hf with ⟨Λ, hf⟩
  refine ⟨Λ, ?_⟩
  intro σ₁ σ₂ hσ
  simp [hf σ₁ σ₂ hσ]

lemma neg {F : Type*} [Neg F] {f : (S → E) → F}
    (hf : IsCylinderFunction (S := S) (E := E) f) :
    IsCylinderFunction (S := S) (E := E) (fun σ ↦ - f σ) := by
  rcases hf with ⟨Λ, hf⟩
  refine ⟨Λ, ?_⟩
  intro σ₁ σ₂ hσ
  simp [hf σ₁ σ₂ hσ]

lemma sub {F : Type*} [AddGroup F] {f g : (S → E) → F}
    (hf : IsCylinderFunction (S := S) (E := E) f)
    (hg : IsCylinderFunction (S := S) (E := E) g) :
    IsCylinderFunction (S := S) (E := E) (fun σ ↦ f σ - g σ) := by
  -- `sub` is just `add` + `neg`, but we keep a dedicated lemma for convenience.
  simpa [sub_eq_add_neg] using (add (S := S) (E := E) hf (neg (S := S) (E := E) hg))

end IsCylinderFunction

/-! ### Borel measurability alignment for countable products -/

variable (S E)

/-- If `S` is countable and `E` is second-countable Borel, then the product measurable space on
`S → E` is the Borel σ-algebra of the product topology. -/
lemma measurableSpace_pi_eq_borel
    [Countable S] [TopologicalSpace E] [MeasurableSpace E] [SecondCountableTopology E] [BorelSpace E] :
    (inferInstance : MeasurableSpace (S → E)) = borel (S → E) := by
  -- This is exactly `BorelSpace.measurable_eq` for the Mathlib instance `Pi.borelSpace`.
  simpa using (BorelSpace.measurable_eq (α := S → E))

end ConfigurationSpace

end GibbsMeasure
