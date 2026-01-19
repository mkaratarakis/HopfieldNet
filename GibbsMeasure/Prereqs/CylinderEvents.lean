import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Cylinder σ-algebras on configuration spaces

This file provides a small, reusable API around `MeasureTheory.cylinderEvents` for configuration
spaces `(S → E)`.  In particular, we record the convenient characterization

`cylinderEvents Δ = MeasurableSpace.comap (Set.restrict Δ) _`,

so that measurability with respect to a cylinder σ-algebra can be phrased as “depending only on the
coordinates in `Δ`”.
-/

open Set

namespace MeasureTheory

variable {S E : Type*} [MeasurableSpace E]

/-! ### `cylinderEvents` as a pullback σ-algebra -/

lemma cylinderEvents_eq_comap_restrict (Δ : Set S) :
    cylinderEvents (X := fun _ : S ↦ E) Δ =
      MeasurableSpace.comap (Set.restrict (π := fun _ : S ↦ E) Δ)
        (inferInstance : MeasurableSpace (Δ → E)) := by
  -- `≤`: every coordinate projection `σ ↦ σ i` for `i ∈ Δ` factors through `Set.restrict Δ`.
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun i hi => ?_
    simpa [MeasureTheory.cylinderEvents, MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, Function.comp_def] using
      (le_iSup (fun j : Δ => MeasurableSpace.comap (fun σ : S → E => σ j) (inferInstance : MeasurableSpace E))
        ⟨i, hi⟩)
  · -- `≥`: `Set.restrict Δ` is measurable from `cylinderEvents Δ` (Mathlib lemma).
    exact (MeasureTheory.measurable_restrict_cylinderEvents (X := fun _ : S ↦ E) Δ).comap_le

/-! ### Cylinder-measurable sets depend only on the relevant coordinates -/

lemma measurableSet_cylinderEvents_iff_determined_by_coords (Δ : Set S) (B : Set (S → E)) :
    MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) Δ] B →
      (∀ (σ₁ σ₂ : S → E), (∀ x ∈ Δ, σ₁ x = σ₂ x) → (σ₁ ∈ B ↔ σ₂ ∈ B)) := by
  intro hB
  -- Rewrite `cylinderEvents Δ` as a pullback along the restriction map.
  have hB' :
      MeasurableSet[
          MeasurableSpace.comap (Set.restrict (π := fun _ : S ↦ E) Δ)
            (inferInstance : MeasurableSpace (Δ → E))]
        B := by
    simpa [cylinderEvents_eq_comap_restrict (S := S) (E := E) (Δ := Δ)] using hB
  -- Unpack comap-measurability: `B = restrict ⁻¹' C` for some measurable `C`.
  rcases hB' with ⟨C, _hC, hpreim⟩
  intro σ₁ σ₂ hEq
  have hrestrict :
      Set.restrict (π := fun _ : S ↦ E) Δ σ₁ =
        Set.restrict (π := fun _ : S ↦ E) Δ σ₂ := by
    funext x
    exact hEq x x.2
  -- Membership is decided by the restricted configuration.
  simp only [← hpreim, Set.mem_preimage, hrestrict]

end MeasureTheory
