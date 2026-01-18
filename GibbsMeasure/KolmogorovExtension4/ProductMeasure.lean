/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion

This file used to contain a local (incomplete) construction of infinite product measures.
Mathlib now provides a complete and well-maintained development in
`Mathlib.Probability.ProductMeasure`.

For the Gibbs measure development (Georgii-style specifications), we keep the name
`MeasureTheory.productMeasure` as a thin wrapper around Mathlib’s `Measure.infinitePi`.
-/

import Mathlib.Probability.ProductMeasure

open scoped ENNReal

namespace MeasureTheory

universe u
variable {ι : Type*} {X : ι → Type u} [∀ i, MeasurableSpace (X i)]

variable (μ : (i : ι) → Measure (X i))

/-- The product measure of an arbitrary family of probability measures.

This is `Measure.infinitePi` from Mathlib, re-exported under the name `productMeasure` to serve as
the canonical reference measure for the independent specification in the Gibbs measure API. -/
noncomputable abbrev productMeasure : Measure ((i : ι) → X i) :=
  Measure.infinitePi μ

@[simp] lemma productMeasure_def : productMeasure μ = Measure.infinitePi μ := rfl

instance [∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (productMeasure μ) := by
  dsimp [productMeasure]
  infer_instance

theorem isProjectiveLimit_productMeasure [∀ i, IsProbabilityMeasure (μ i)] :
    IsProjectiveLimit (productMeasure μ) (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  simpa [productMeasure] using (Measure.isProjectiveLimit_infinitePi (μ := μ))

theorem productMeasure_boxes [∀ i, IsProbabilityMeasure (μ i)]
    {s : Finset ι} {t : (i : ι) → Set (X i)} (mt : ∀ i ∈ s, MeasurableSet (t i)) :
    productMeasure μ (Set.pi s t) = ∏ i ∈ s, (μ i) (t i) := by
  simpa [productMeasure] using (Measure.infinitePi_pi (μ := μ) mt)

theorem productMeasure_cylinder [∀ i, IsProbabilityMeasure (μ i)]
    {s : Finset ι} {S : Set ((i : s) → X i)} (mS : MeasurableSet S) :
    productMeasure μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S := by
  simpa [productMeasure] using (Measure.infinitePi_cylinder (μ := μ) mS)

end MeasureTheory
