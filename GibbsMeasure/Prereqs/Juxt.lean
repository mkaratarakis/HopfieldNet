import GibbsMeasure.Prereqs.CylinderEvents

open MeasureTheory

section juxt
variable {S E : Type*} {𝓔 : MeasurableSpace E} {Λ : Set S} {η : S → E} {x : S}

noncomputable def juxt (Λ : Set S) (η : S → E) (ζ : Λ → E) (x : S) : E := by
  classical exact dite (x ∈ Λ) (fun h ↦ ζ ⟨x, h⟩) (fun _ ↦ η x)

lemma juxt_apply_of_mem (hx : x ∈ Λ) (ζ : Λ → E) : juxt Λ η ζ x = ζ ⟨x, hx⟩ := by simp [juxt, hx]
lemma juxt_apply_of_not_mem (h : x ∉ Λ) (ζ : Λ → E) : juxt Λ η ζ x = η x := by simp [juxt, h]


lemma Measurable.juxt : Measurable (juxt Λ η) := by
  classical
  letI : MeasurableSpace E := 𝓔
  refine (measurable_pi_iff).2 (fun x => ?_)
  by_cases hx : x ∈ Λ
  · have hix : Measurable (fun ζ : Λ → E => ζ ⟨x, hx⟩) :=
      measurable_pi_apply (⟨x, hx⟩ : Λ)
    convert hix using 1
    ext ζ
    exact juxt_apply_of_mem hx ζ
  · have : Measurable (fun _ : Λ → E => η x) := measurable_const
    convert this using 1
    ext ζ
    exact juxt_apply_of_not_mem hx ζ

/-- The juxtaposition function is jointly measurable in (η, ζ). -/
lemma measurable_juxt_joint (Λ : Set S) :
    Measurable (fun (p : (S → E) × (Λ → E)) => juxt Λ p.1 p.2) := by
  classical
  letI : MeasurableSpace E := 𝓔
  rw [measurable_pi_iff]
  intro x
  simp only [juxt]
  by_cases hx : x ∈ Λ
  · simp only [dif_pos hx]
    exact (measurable_pi_apply (⟨x, hx⟩ : Λ)).comp measurable_snd
  · simp only [dif_neg hx]
    exact (measurable_pi_apply x).comp measurable_fst

/--
The juxtaposition function is jointly measurable when the space of boundary conditions η
is equipped with the restricted σ-algebra cylinderEvents Λᶜ.
-/
lemma measurable_juxt_joint_restricted {Λ : Finset S} :
    Measurable[
      (cylinderEvents ((Λ : Set S)ᶜ)).prod inferInstance
    ]
      (fun (p : (S → E) × (↥(Λ : Set S) → E)) => juxt (Λ : Set S) p.1 p.2) := by
  classical
  letI : MeasurableSpace E := 𝓔
  simp_rw [measurable_pi_iff]
  intro x
  simp only [juxt]
  by_cases hx : x ∈ (Λ : Set S)
  · simp only [dif_pos hx]
    exact (measurable_pi_apply (⟨x, hx⟩ : ↥(Λ : Set S))).comp measurable_snd
  · simp only [dif_neg hx]
    have hx' : x ∈ ((Λ : Set S)ᶜ) := by
      simpa using hx
    have h_meas_proj :
        Measurable[cylinderEvents ((Λ : Set S)ᶜ)] (fun η : S → E => η x) :=
      measurable_cylinderEvent_apply (i := x) (Δ := ((Λ : Set S)ᶜ)) hx'
    exact h_meas_proj.comp measurable_fst

lemma juxt_agree_on_compl (Λ : Finset S) (η : S → E) (ζ : Λ → E) :
    ∀ x ∉ Λ, juxt Λ η ζ x = η x := by
  intro x hx
  exact juxt_apply_of_not_mem (Finset.mem_coe.not.mpr hx) ζ

end juxt
