import Riemann.PhysLean.SpinGlass.SKModel
import Riemann.PhysLean.SpinGlass.GuerraBound
import Riemann.PhysLean.SpinGlass.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory ProbabilityTheory Real BigOperators SpinGlass SpinGlass.Algebra
open PhysLean.Probability.GaussianIBP

namespace SpinGlass

/-!
# Section 1.4: General Replica Calculus and Latala's Argument

To prove concentration, we must manage functions of `n` replicas.
Differentiation increases the number of replicas by 2.

**Terminology:** this file implements the **interpolation / smart path** machinery
(Talagrand Vol. I, §§1.3–1.4). It is *not* the cavity method (Talagrand Vol. I, §1.6),
which is an induction on `N`.
-/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (N : ℕ) (β h q : ℝ)
variable (sk : SKDisorder (Ω := Ω) N β h) (sim : SimpleDisorder (Ω := Ω) N β q)

section ReplicaCalculus

variable (n : ℕ)

/-- The space of `n` replicas: (Fin n → Config N). -/
abbrev ReplicaSpace := Fin n → Config N

/-- A function of `n` replicas. -/
abbrev ReplicaFun := ReplicaSpace N n → ℝ

/-- A generic two-replica interaction kernel `U(σ,τ)` (Talagrand’s `U_{ℓ,ℓ'}`). -/
abbrev InteractionKernel := Config N → Config N → ℝ

/--
Interpolated Hamiltonian (Guerra):
\[
H_t = \sqrt{t}\,U + \sqrt{1-t}\,V + H_{\text{field}}.
\]

The external field term uses the **magnetization-dependent** energy
`magnetic_field_vector` (not a constant shift).
-/
noncomputable def H_gauss (t : ℝ) : Ω → EnergySpace N :=
  fun w =>
    (Real.sqrt t) • sk.U w
      + (Real.sqrt (1 - t)) • sim.V w

noncomputable def H_field : EnergySpace N :=
  magnetic_field_vector (N := N) h

noncomputable def H_t (t : ℝ) : Ω → EnergySpace N :=
  fun w =>
    H_gauss (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w
      + H_field (N := N) (h := h)

/-!
### Joint Gaussian packaging for `(U,V)`

To apply Hilbert-space Gaussian IBP to functions depending on **both** processes `U` and `V`,
we package the pair `(sk.U, sim.V)` as a single `IsGaussianHilbert` random variable valued in
the `L²`-product space `WithLp 2 (EnergySpace N × EnergySpace N)`.

This construction uses the independence assumption `sk.U ⟂ᵢ sim.V` and the existing coordinate
models `sk.hU` and `sim.hV`.
-/

/-- The joint Gaussian vector `(U,V)` in the `L²`-product space. -/
noncomputable def UV : Ω → WithLp 2 (EnergySpace N × EnergySpace N) :=
  fun ω => WithLp.toLp 2 (sk.U ω, sim.V ω)

/-- `UV` is a centered Gaussian Hilbert random variable when `U` and `V` are independent. -/
noncomputable def isGaussianHilbert_UV
    (hIndep : ProbabilityTheory.IndepFun sk.U sim.V (ℙ : Measure Ω)) :
    IsGaussianHilbert (UV (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
  classical
  -- abbreviate the two coordinate models
  let hU := sk.hU
  let hV := sim.hV
  -- Build the combined coordinate family on a sigma index (Bool chooses which process).
  let κ : Bool → Type* := fun
    | true => hU.ι
    | false => hV.ι
  let X : (b : Bool) → (j : κ b) → Ω → ℝ :=
    fun b =>
      match b with
      | true => fun j => hU.c j
      | false => fun j => hV.c j
  have mX : ∀ b j, Measurable (X b j) := by
    intro b j
    cases b <;> simpa [X] using (by
      first | exact hV.c_meas j | exact hU.c_meas j)
  have h2 : ∀ b, ProbabilityTheory.iIndepFun (X b) (ℙ : Measure Ω) := by
    intro b
    cases b <;> simpa [X] using (by
      first | exact hV.c_indep | exact hU.c_indep)
  -- Independence across `b : Bool` of the *tuples* `(X b ·)`.
  have h1 : ProbabilityTheory.iIndepFun (fun b ω => (X b · ω)) (ℙ : Measure Ω) := by
    -- For `Bool`, mutual independence reduces to the 2-variable case.
    -- We derive independence of the coordinate-tuples from independence of `(U,V)` by composition.
    have hφ : Measurable (fun u : EnergySpace N => fun i : hU.ι => inner ℝ u (hU.w i)) := by
      refine measurable_pi_lambda _ ?_
      intro i
      -- `u ↦ ⟪u, w i⟫` is continuous, hence measurable.
      have hcont : Continuous (fun u : EnergySpace N => inner ℝ u (hU.w i)) := by
        have hpair : Continuous (fun u : EnergySpace N => (u, hU.w i)) :=
          (continuous_id.prodMk continuous_const)
        simpa using (continuous_inner.comp hpair)
      exact hcont.measurable
    have hψ : Measurable (fun v : EnergySpace N => fun j : hV.ι => inner ℝ v (hV.w j)) := by
      refine measurable_pi_lambda _ ?_
      intro j
      have hcont : Continuous (fun v : EnergySpace N => inner ℝ v (hV.w j)) := by
        have hpair : Continuous (fun v : EnergySpace N => (v, hV.w j)) :=
          (continuous_id.prodMk continuous_const)
        simpa using (continuous_inner.comp hpair)
      exact hcont.measurable
    have hInd_tuples :
        ProbabilityTheory.IndepFun
          (fun ω : Ω => fun i : hU.ι => hU.c i ω)
          (fun ω : Ω => fun j : hV.ι => hV.c j ω)
          (ℙ : Measure Ω) := by
      -- Start from `IndepFun (φ ∘ U) (ψ ∘ V)` and rewrite with `coord_eq_c`.
      have hcomp :
          ProbabilityTheory.IndepFun (fun ω => (fun u => fun i : hU.ι => inner ℝ u (hU.w i)) (sk.U ω))
            (fun ω => (fun v => fun j : hV.ι => inner ℝ v (hV.w j)) (sim.V ω))
            (ℙ : Measure Ω) :=
        (ProbabilityTheory.IndepFun.comp hIndep hφ hψ)
      -- Replace the composed maps by the coordinate-tuples `hU.c` and `hV.c`.
      refine ProbabilityTheory.IndepFun.congr hcomp ?_ ?_
      · -- left tuple
        refine Filter.Eventually.of_forall (fun ω => ?_)
        funext i
        have hcoord : PhysLean.Probability.GaussianIBP.coord hU.w sk.U i = hU.c i := by
          funext ω'
          simpa using
            congrArg (fun f => f i ω')
              (PhysLean.Probability.GaussianIBP.coord_eq_c (g := sk.U) hU)
        -- evaluate at `ω`
        simpa [PhysLean.Probability.GaussianIBP.coord] using congrArg (fun f => f ω) hcoord
      · -- right tuple
        refine Filter.Eventually.of_forall (fun ω => ?_)
        funext j
        have hcoord : PhysLean.Probability.GaussianIBP.coord hV.w sim.V j = hV.c j := by
          funext ω'
          simpa using
            congrArg (fun f => f j ω')
              (PhysLean.Probability.GaussianIBP.coord_eq_c (g := sim.V) hV)
        simpa [PhysLean.Probability.GaussianIBP.coord] using congrArg (fun f => f ω) hcoord
    -- Now prove `iIndepFun` on `Bool` by cases on the finset.
    refine
      (ProbabilityTheory.iIndepFun_iff (m := fun b => inferInstance)
        (f := fun b ω => (X b · ω)) (μ := (ℙ : Measure Ω))).2 ?_
    intro s f' hs
    classical
    -- `Bool` finsets are: `∅`, `{false}`, `{true}`, `{false,true}`.
    by_cases hfalse : false ∈ s
    · by_cases htrue : true ∈ s
      · -- both are present
        have hs' :
            (ℙ : Measure Ω) (f' false ∩ f' true) =
              (ℙ : Measure Ω) (f' false) * (ℙ : Measure Ω) (f' true) := by
          -- Use independence of the two tuples.
          have hInd_bool :
              ProbabilityTheory.IndepFun (fun ω => (X false · ω)) (fun ω => (X true · ω))
                (ℙ : Measure Ω) := by
            simpa [X] using hInd_tuples.symm
          -- Convert to independence of the corresponding measurable sets.
          have hInd_ms :
              ProbabilityTheory.Indep
                (MeasurableSpace.comap (fun ω => (X false · ω)) (inferInstance))
                (MeasurableSpace.comap (fun ω => (X true · ω)) (inferInstance))
                (ℙ : Measure Ω) := by
            simpa [ProbabilityTheory.IndepFun] using
              (ProbabilityTheory.IndepFun_iff_Indep (f := fun ω => (X false · ω))
                (g := fun ω => (X true · ω)) (μ := (ℙ : Measure Ω))).1 hInd_bool
          have hA :
              MeasurableSet[
                MeasurableSpace.comap (fun ω => (X false · ω)) (inferInstance)] (f' false) := by
            simpa using hs false hfalse
          have hB :
              MeasurableSet[
                MeasurableSpace.comap (fun ω => (X true · ω)) (inferInstance)] (f' true) := by
            simpa using hs true htrue
          have hIndSet :
              ProbabilityTheory.IndepSet (f' false) (f' true) (ℙ : Measure Ω) :=
            hInd_ms.indepSet_of_measurableSet hA hB
          simpa [Set.inter_comm] using hIndSet.measure_inter_eq_mul
        -- reduce the general `Finset` intersection/product to the `{false,true}` case
        have hs_eq : s = ({false, true} : Finset Bool) := by
          ext b
          cases b <;> simp [hfalse, htrue]
        subst hs_eq
        -- Rewrite `⋂ i, f' i` as `f' false ∩ f' true` and use `hs'`.
        have hInter : (⋂ i : Bool, f' i) = f' false ∩ f' true := by
          ext ω; simp
        simpa [hInter] using hs'
      · -- only `false` present
        have hs_eq : s = ({false} : Finset Bool) := by
          ext b
          cases b <;> simp [hfalse, htrue]
        subst hs_eq
        simp
    · -- `false` not in `s`
      by_cases htrue : true ∈ s
      · have hs_eq : s = ({true} : Finset Bool) := by
          ext b
          cases b <;> simp [hfalse, htrue]
        subst hs_eq
        simp
      · -- neither present
        have hs_eq : s = (∅ : Finset Bool) := by
          ext b
          cases b <;> simp [hfalse, htrue]
        subst hs_eq
        simp
  -- Combine the families using `iIndepFun_uncurry` and transport to a sum-indexed family.
  have h_uncurry :
      ProbabilityTheory.iIndepFun (fun (p : (b : Bool) × κ b) ω => X p.1 p.2 ω) (ℙ : Measure Ω) :=
    ProbabilityTheory.iIndepFun_uncurry (P := (ℙ : Measure Ω)) (X := X) mX h1 h2
  -- Surjective map from the sigma index `(b, j)` to the sum index.
  let g : (b : Bool) × κ b → hU.ι ⊕ hV.ι :=
    fun
      | ⟨true, i⟩ => Sum.inl i
      | ⟨false, j⟩ => Sum.inr j
  have hg : Function.Surjective g := by
    intro s
    cases s with
    | inl i => exact ⟨⟨true, i⟩, rfl⟩
    | inr j => exact ⟨⟨false, j⟩, rfl⟩
  have h_sum :
      ProbabilityTheory.iIndepFun (fun i ω => (Sum.elim hU.c hV.c i) ω) (ℙ : Measure Ω) := by
    -- `h_uncurry` is an independence statement on a surjective precomposition of the sum-family.
    have hpre :
        ProbabilityTheory.iIndepFun (fun p ω => (Sum.elim hU.c hV.c (g p)) ω) (ℙ : Measure Ω) := by
      -- `h_uncurry` is expressed using `X`; transport it to the `Sum.elim` presentation.
      refine
        (ProbabilityTheory.iIndepFun.congr (μ := (ℙ : Measure Ω))
            (f := fun p ω => X p.1 p.2 ω)
            (g := fun p ω => (Sum.elim hU.c hV.c (g p)) ω) ?_) h_uncurry
      intro p
      refine Filter.Eventually.of_forall (fun ω => ?_)
      cases p with
      | mk b j =>
        cases b <;> rfl
    refine ProbabilityTheory.iIndepFun.of_precomp (μ := (ℙ : Measure Ω)) (g := g) hg ?_
    exact hpre
  -- Assemble the `IsGaussianHilbert` structure.
  refine
    { ι := hU.ι ⊕ hV.ι
      fintype_ι := inferInstance
      w := hU.w.prod hV.w
      τ := Sum.elim hU.τ hV.τ
      c := Sum.elim hU.c hV.c
      c_meas := by
        intro i
        cases i <;> simpa using (by
          first | exact hU.c_meas _ | exact hV.c_meas _)
      c_gauss := by
        intro i
        cases i <;> simpa using (by
          first | exact hU.c_gauss _ | exact hV.c_gauss _)
      c_indep := by
        simpa using h_sum
      repr := by
        -- The ONB sum splits into the two component ONB sums.
        funext ω
        apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
        simp [UV, hU.repr, hV.repr, OrthonormalBasis.prod_apply]
        -- Reduce to an equality in the underlying product `EnergySpace × EnergySpace`.
        ext i
        · -- fst component
          -- push `Prod.fst` through both sums and simplify the zero-component
          have hfstU :
              (∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))).1
                = ∑ x : hU.ι, hU.c x ω • hU.w x := by
            -- push `fst` through the sum; each term projects to `c • w`
            simpa using
              (Prod.fst_sum (s := (Finset.univ : Finset hU.ι))
                (f := fun x : hU.ι => hU.c x ω • (hU.w x, (0 : EnergySpace N))))
          have hfstV :
              (∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).1 = 0 := by
            -- push `Prod.fst` through the sum; each term is `0`
            calc
              (∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).1
                  = ∑ x : hV.ι, (hV.c x ω • ((0 : EnergySpace N), hV.w x)).1 := by
                      simpa using
                        (Prod.fst_sum (s := (Finset.univ : Finset hV.ι))
                          (f := fun x : hV.ι => hV.c x ω • ((0 : EnergySpace N), hV.w x)))
              _ = ∑ x : hV.ι, (0 : EnergySpace N) := by simp
              _ = 0 := by simp
          -- evaluate at configuration `i`
          have hfstU' :
              (∑ i' : hU.ι, hU.c i' ω • hU.w i') i
                = (∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))).1 i := by
            simpa using (congrArg (fun H : EnergySpace N => H i) hfstU.symm)
          -- reduce the RHS to the `U`-term using `hfstV`
          have hfstV' : ((∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).1) i = 0 := by
            -- evaluate `hfstV` at the configuration `i`
            simpa using congrArg (fun H : EnergySpace N => H i) hfstV
          -- close the goal by rewriting the `U`-part via `hfstU'`
          -- and killing the `V`-part via `hfstV'`
          calc
            (WithLp.toLp 2
                (∑ j : hU.ι, hU.c j ω • hU.w j, ∑ j : hV.ι, hV.c j ω • hV.w j)).fst i
                = (∑ j : hU.ι, hU.c j ω • hU.w j) i := by
                    simp
            _ = (∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))).1 i := by
                    exact hfstU'
            _ =
                (∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))
                  + ∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).1 i := by
                    simp only [Prod.fst_add, hfstV, add_zero]
          aesop
        · -- snd component
          have hsndU :
              (∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))).2 = 0 := by
            calc
              (∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))).2
                  = ∑ x : hU.ι, (hU.c x ω • (hU.w x, (0 : EnergySpace N))).2 := by
                      simpa using
                        (Prod.snd_sum (s := (Finset.univ : Finset hU.ι))
                          (f := fun x : hU.ι => hU.c x ω • (hU.w x, (0 : EnergySpace N))))
              _ = ∑ x : hU.ι, (0 : EnergySpace N) := by simp
              _ = 0 := by simp
          have hsndV :
              (∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).2
                = ∑ x : hV.ι, hV.c x ω • hV.w x := by
            simpa using
              (Prod.snd_sum (s := (Finset.univ : Finset hV.ι))
                (f := fun x : hV.ι => hV.c x ω • ((0 : EnergySpace N), hV.w x)))
          have hsndV' :
              (∑ i' : hV.ι, hV.c i' ω • hV.w i') i
                = (∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).2 i := by
            exact congrArg (fun H : EnergySpace N => H i) hsndV.symm
          have hsndU' : ((∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))).2) i = 0 := by
            simpa using congrArg (fun H : EnergySpace N => H i) hsndU
          -- close the goal by rewriting the `V`-part via `hsndV'`
          -- and killing the `U`-part via `hsndU'`
          calc
            (WithLp.toLp 2
                (∑ j : hU.ι, hU.c j ω • hU.w j, ∑ j : hV.ι, hV.c j ω • hV.w j)).snd i
                = (∑ j : hV.ι, hV.c j ω • hV.w j) i := by
                    simp
            _ = (∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).2 i := by
                  exact hsndV'
            _ =
                (∑ x : hU.ι, hU.c x ω • (hU.w x, (0 : EnergySpace N))
                  + ∑ x : hV.ι, hV.c x ω • ((0 : EnergySpace N), hV.w x)).2 i := by
                    simp only [Prod.snd_add, hsndU, zero_add]
          classical
          simp only [Prod.smul_mk]
          aesop
    }

/--
**Equation (1.17)**: The Gibbs average of a function of `n` replicas.
⟨f⟩ = (1/Z^n) ∑_{σ^1...σ^n} f(σ) exp(-∑ H(σ^l))
-/
noncomputable def gibbs_average_n_det (H : EnergySpace N) (f : ReplicaFun N n) : ℝ :=
  ∑ σs : ReplicaSpace N n, f σs * ∏ l, gibbs_pmf N H (σs l)

noncomputable def gibbs_average_n (t : ℝ) (f : ReplicaFun N n) : Ω → ℝ :=
  fun w =>
    let H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w
    gibbs_average_n_det (N := N) (n := n) H f

/-!
### Basic bounds for `gibbs_average_n_det`

These are used both for integrability and for “moderate growth” hypotheses in Gaussian IBP.
-/

lemma abs_gibbs_average_n_det_le (H : EnergySpace N) (f : ReplicaFun N n) :
    |gibbs_average_n_det (N := N) (n := n) H f| ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
  classical
  -- Triangle inequality, using `0 ≤ gibbs_pmf ≤ 1`.
  have hnonneg :
      ∀ σs : ReplicaSpace N n, 0 ≤ ∏ l, gibbs_pmf N H (σs l) :=
    fun σs => by
      classical
      refine Finset.prod_nonneg ?_
      intro l _hl
      exact SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l)
  have hprod_le_one :
      ∀ σs : ReplicaSpace N n, (∏ l, gibbs_pmf N H (σs l)) ≤ (1 : ℝ) :=
    fun σs => by
      classical
      -- `∏ l, p_l ≤ 1` since each `0 ≤ p_l ≤ 1`.
      have hfac : ∀ l : Fin n, gibbs_pmf N H (σs l) ≤ 1 := by
        intro l
        have hZpos : 0 < Z N H := SpinGlass.Z_pos (N := N) (H := H)
        have hterm_le : Real.exp (-H (σs l)) ≤ Z N H := by
          -- a single term is bounded by the sum `Z`
          have :=
            Finset.single_le_sum
              (s := (Finset.univ : Finset (Config N)))
              (f := fun τ => Real.exp (-H τ))
              (hf := fun τ _hτ => (Real.exp_pos _).le)
              (a := σs l) (h := Finset.mem_univ (σs l))
          simpa [Z] using this
        have := (div_le_one hZpos).2 hterm_le
        simpa [SpinGlass.gibbs_pmf] using this
      simpa using
        (Finset.prod_le_one (s := (Finset.univ : Finset (Fin n)))
          (f := fun l => gibbs_pmf N H (σs l))
          (fun l _hl => SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l))
          (fun l _hl => hfac l))
  calc
    |gibbs_average_n_det (N := N) (n := n) H f|
        = |∑ σs : ReplicaSpace N n, f σs * ∏ l, gibbs_pmf N H (σs l)| := by
            rfl
    _ ≤ ∑ σs : ReplicaSpace N n, |f σs * ∏ l, gibbs_pmf N H (σs l)| := by
          -- finset triangle inequality
          simpa using
            (Finset.abs_sum_le_sum_abs
              (f := fun σs : ReplicaSpace N n => f σs * ∏ l, gibbs_pmf N H (σs l))
              (s := (Finset.univ : Finset (ReplicaSpace N n))))
    _ = ∑ σs : ReplicaSpace N n, (|f σs| * |∏ l, gibbs_pmf N H (σs l)|) := by
          refine Finset.sum_congr rfl (fun σs _hσs => ?_)
          simp [abs_mul]
    _ ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
          refine Finset.sum_le_sum ?_
          intro σs _hσs
          have habs :
              |∏ l, gibbs_pmf N H (σs l)| = ∏ l, gibbs_pmf N H (σs l) := by
            have h0 : 0 ≤ ∏ l, gibbs_pmf N H (σs l) := hnonneg σs
            simp [abs_of_nonneg h0]
          have hle1 : |∏ l, gibbs_pmf N H (σs l)| ≤ 1 := by
            simpa [habs] using hprod_le_one σs
          simpa using (mul_le_mul_of_nonneg_left hle1 (abs_nonneg (f σs)))

/-- Expected Gibbs average: ν_t(f) = E[ ⟨f⟩_t ]. -/
noncomputable def nu (t : ℝ) (f : ReplicaFun N n) : ℝ :=
  ∫ w, gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w ∂ℙ

/-- Lift a function of `n` replicas to `n + k` replicas by ignoring the last `k`. -/
def liftReplicaFun (k : ℕ) (f : ReplicaFun N n) : ReplicaFun N (n + k) :=
  fun σs => f (fun i => σs (Fin.castAdd k i))

/--
The product Gibbs weights on `n` replicas sum to `1`.

This is the finite-dimensional fact that the `n`-replica Gibbs measure is the product of `n`
copies of the one-replica Gibbs measure.
-/
lemma sum_prod_gibbs_pmf_eq_one (H : EnergySpace N) :
    (∑ σs : ReplicaSpace N n, ∏ l, gibbs_pmf N H (σs l)) = 1 := by
  classical
  -- Induction on `n`, splitting `Fin (n+1) → Config N` into head/tail via `Fin.consEquiv`.
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let p : Config N → ℝ := gibbs_pmf N H
      have hs1 : (∑ σ : Config N, p σ) = 1 := by
        simpa [p] using (SpinGlass.sum_gibbs_pmf (N := N) (H := H))
      let e : (Config N × (Fin n → Config N)) ≃ (Fin (n + 1) → Config N) :=
        Fin.consEquiv (fun _ : Fin (n + 1) => Config N)
      have hrew :
          (∑ σs : (Fin (n + 1) → Config N), ∏ l : Fin (n + 1), p (σs l))
            = ∑ x : (Config N × (Fin n → Config N)), ∏ l : Fin (n + 1), p (e x l) := by
        -- `Fintype.sum_equiv` lets us change variables along the equivalence `e`.
        simpa using
          (Fintype.sum_equiv e
              (f := fun x => ∏ l : Fin (n + 1), p (e x l))
              (g := fun σs => ∏ l : Fin (n + 1), p (σs l))
              (h := fun x => rfl)).symm
      -- Compute the RHS by iterating sums over `(σ₀, σtail)` and factoring.
      calc
        (∑ σs : (Fin (n + 1) → Config N), ∏ l : Fin (n + 1), p (σs l))
            = ∑ x : (Config N × (Fin n → Config N)), ∏ l : Fin (n + 1), p (e x l) := hrew
        _ = ∑ σ₀ : Config N, ∑ σtail : (Fin n → Config N),
              p σ₀ * (∏ i : Fin n, p (σtail i)) := by
              -- Expand the sum over the product type, then split the `Fin (n+1)` product.
              classical
              -- First rewrite the sum over pairs as an iterated sum.
              simp [Fintype.sum_prod_type, e, p, Fin.prod_univ_succ]
        _ = ∑ σ₀ : Config N, p σ₀ * (∑ σtail : (Fin n → Config N), ∏ i : Fin n, p (σtail i)) := by
              classical
              -- Pull out the constant scalar `p σ₀` from the inner sum.
              simp [Finset.mul_sum]
        _ = ∑ σ₀ : Config N, p σ₀ * 1 := by
              -- Use the induction hypothesis for the tail sum.
              simpa [p] using congrArg (fun r => ∑ σ₀ : Config N, p σ₀ * r) ih
        _ = ∑ σ₀ : Config N, p σ₀ := by simp
        _ = 1 := hs1

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/--
Uniform bound on the n-replica Gibbs average:
\[
|\langle f\rangle_{t,n}| \le \max_{\sigma^1,\dots,\sigma^n} |f(\sigma^1,\dots,\sigma^n)|.
\]
-/
lemma abs_gibbs_average_n_le (t : ℝ) (f : ReplicaFun N n) (w : Ω) :
    |gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w|
      ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
  classical
  -- crude but sufficient: triangle inequality and `0 ≤ ∏ l, gibbs_pmf ...`.
  have hnonneg :
      ∀ σs : ReplicaSpace N n,
        0 ≤ ∏ l, gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) :=
    fun σs => by
      classical
      -- product of nonnegative terms
      have : ∀ l : Fin n,
          0 ≤ gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) :=
        fun l => SpinGlass.gibbs_pmf_nonneg (N := N) (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σ := σs l)
      -- move to finset product
      simpa using Finset.prod_nonneg (fun l _hl => this l)
  -- triangle inequality
  calc
    |gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w|
        = |∑ σs : ReplicaSpace N n,
            f σs * ∏ l,
              gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)| := by
            rfl
    _ ≤ ∑ σs : ReplicaSpace N n,
          |f σs * ∏ l,
              gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)| := by
          classical
          -- Apply the finset triangle inequality on `univ`.
          simpa using
            (Finset.abs_sum_le_sum_abs
              (f := fun σs : ReplicaSpace N n =>
                f σs * ∏ l, gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
              (s := (Finset.univ : Finset (ReplicaSpace N n))))
    _ = ∑ σs : ReplicaSpace N n,
          (|f σs| * |∏ l,
              gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)|) := by
          refine Finset.sum_congr rfl ?_
          intro σs _hσs
          simp [abs_mul]
    _ ≤ ∑ σs : ReplicaSpace N n, |f σs| := by
          -- use `|∏ ...| = ∏ ... ≤ 1`, but we only need a crude bound by `1`.
          -- Since each factor is a probability, it is ≤ 1.
          classical
          -- compare termwise on the finset `univ` and `simp` back to the `Fintype` sum.
          simpa using
            (Finset.sum_le_sum (s := (Finset.univ : Finset (ReplicaSpace N n))) (fun σs _hσs => by
              have hle1 : |∏ l,
                  gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)| ≤ 1 := by
                -- crude: each factor `gibbs_pmf` is ≤ 1, hence product ≤ 1
                have hfac : ∀ l : Fin n,
                    gibbs_pmf N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) ≤ 1 := by
                  intro l
                  have hZpos :
                      0 < Z N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) :=
                    SpinGlass.Z_pos (N := N)
                      (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
                  have hterm_le :
                      Real.exp (-(H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
                        ≤ Z N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
                    -- a single term is bounded by the sum `Z`
                    classical
                    -- use `Finset.single_le_sum` on `s = univ`, `f = exp(-H)`
                    have :=
                      Finset.single_le_sum
                        (s := (Finset.univ : Finset (Config N)))
                        (f := fun τ =>
                          Real.exp (-(H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ))
                        (hf := fun τ _hτ => (Real.exp_pos _).le)
                        (a := (σs l)) (h := Finset.mem_univ (σs l))
                    simpa [Z] using this
                  have := (div_le_one hZpos).2 hterm_le
                  simpa [SpinGlass.gibbs_pmf] using this
                -- absolute value is redundant since factors are nonnegative
                have habs :
                    |∏ l,
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)|
                      =
                    ∏ l,
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) := by
                  have hnonneg' : 0 ≤ ∏ l,
                      gibbs_pmf N
                        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) :=
                    hnonneg σs
                  simp [abs_of_nonneg hnonneg']
                have hprod :
                    ∏ l,
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)
                      ≤ (1 : ℝ) := by
                  -- `∏ l, a_l ≤ 1` if each `0 ≤ a_l` and `a_l ≤ 1`.
                  classical
                  simpa using
                    (Finset.prod_le_one (s := (Finset.univ : Finset (Fin n)))
                      (f := fun l =>
                        gibbs_pmf N
                          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
                      (fun l _hl => SpinGlass.gibbs_pmf_nonneg (N := N)
                        (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
                        (σ := σs l))
                      (fun l _hl => hfac l))
                simpa [habs] using hprod
              -- finish the termwise inequality: `|f| * |w| ≤ |f|`
              have : |f σs| * |∏ l,
                  gibbs_pmf N
                    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)|
                    ≤ |f σs| := by
                -- multiply the bound `|w| ≤ 1` by the nonnegative factor `|f|`
                simpa using (mul_le_mul_of_nonneg_left hle1 (abs_nonneg (f σs)))
              -- close
              simpa [mul_assoc] using this))

-- From the above crude bound, integrability under the probability measure is immediate.
lemma integrable_gibbs_average_n (t : ℝ) (f : ReplicaFun N n) :
    Integrable (fun w => gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w) := by
  classical
  -- A uniform (in `w`) bound, hence an a.e. bound.
  have hbound :
      ∀ w, ‖gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w‖
        ≤ ∑ σs : ReplicaSpace N n, ‖f σs‖ := by
    intro w
    simpa [Real.norm_eq_abs] using
      (abs_gibbs_average_n_le (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) (n := n) (t := t) (f := f) w)
  -- Measurability of the Gibbs average is by finite sums/products of measurable functions.
  have hU_meas : Measurable (sk.U) := sk.hU.repr_measurable
  have hV_meas : Measurable (sim.V) := sim.hV.repr_measurable
  have hHt_meas :
      Measurable (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
    -- linear combination of measurable maps + constant
    have h1 : Measurable (fun w => (Real.sqrt t) • sk.U w) := hU_meas.const_smul (Real.sqrt t)
    have h2 : Measurable (fun w => (Real.sqrt (1 - t)) • sim.V w) := hV_meas.const_smul (Real.sqrt (1 - t))
    have h3 : Measurable (fun _w : Ω => H_field (N := N) (h := h)) := measurable_const
    -- Keep the addition parenthesization aligned with the definition of `H_t`:
    -- `H_t = (√t • U + √(1-t) • V) + H_field`.
    simpa [H_t, H_gauss] using ((h1.add h2).add h3)
  have h_gibbs_pmf_meas :
      ∀ (σ : Config N),
        Measurable fun w =>
          gibbs_pmf N
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ := by
    intro σ
    -- unfold `gibbs_pmf` and use measurability of evaluation, exp, the finite sum `Z`, and division.
    have hEval : Measurable fun w =>
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ :=
      (evalCLM (N := N) σ).measurable.comp hHt_meas
    have hNum : Measurable fun w =>
        Real.exp (-
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ) :=
      (Real.continuous_exp.measurable.comp (measurable_neg.comp hEval))
    have hZ : Measurable fun w =>
        Z N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
      classical
      -- `Z` is a finite sum of exponentials of measurable evaluations.
      have hterm : ∀ τ : Config N,
          Measurable fun w =>
            Real.exp (-
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) := by
        intro τ
        have hEvalτ : Measurable fun w =>
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ :=
          (evalCLM (N := N) τ).measurable.comp hHt_meas
        exact (Real.continuous_exp.measurable.comp (measurable_neg.comp hEvalτ))
      -- now apply `Finset.measurable_sum` on `Finset.univ`.
      simpa [Z] using
        (Finset.measurable_sum (s := (Finset.univ : Finset (Config N)))
          (f := fun τ w =>
            Real.exp (-
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ))
          (hf := by intro τ _hτ; simpa using hterm τ))
    -- division is measurable
    simpa [SpinGlass.gibbs_pmf] using hNum.div hZ
  have hMeas :
      Measurable (fun w =>
        gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w) := by
    classical
    -- Expand the finite sum over replica configurations.
    -- We work with the `Finset.univ` presentation to use `Finset.measurable_sum/prod`.
    have hterm :
        ∀ σs : ReplicaSpace N n,
          Measurable fun w =>
            f σs * ∏ l : Fin n,
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) := by
      intro σs
      -- measurability of the product over replicas
      have hprod :
          Measurable fun w =>
            ∏ l : Fin n,
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) := by
        -- rewrite as a finset product and use `Finset.measurable_prod`
        classical
        simpa using
          (Finset.measurable_prod (s := (Finset.univ : Finset (Fin n)))
            (f := fun l w =>
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
            (hf := by
              intro l _hl
              simpa using h_gibbs_pmf_meas (σs l)))
      simpa [mul_assoc] using (measurable_const.mul hprod)
    -- sum over `σs`
    simpa [gibbs_average_n] using
      (Finset.measurable_sum (s := (Finset.univ : Finset (ReplicaSpace N n)))
        (f := fun σs w =>
          f σs * ∏ l : Fin n,
            gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
        (hf := by intro σs _hσs; simpa using hterm σs))
  have hAESM :
      AEStronglyMeasurable
        (fun w =>
          gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w) ℙ :=
    hMeas.aestronglyMeasurable
  -- Finish by boundedness on a finite measure space.
  have hBoundAE :
      ∀ᵐ w ∂ℙ, ‖gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w‖
        ≤ ∑ σs : ReplicaSpace N n, ‖f σs‖ :=
    Filter.Eventually.of_forall hbound
  exact Integrable.of_bound (μ := (ℙ : Measure Ω)) hAESM _ hBoundAE

/--
The Covariance function U(σ^l, σ^l') appearing in the derivative.
U_{l,l'} = E[u(σ^l)u(σ^l')] - E[v(σ^l)v(σ^l')].
For SK: U_{l,l'} = (β²/2)(R_{l,l'}^2 - q).
-/
def U_interaction (U : InteractionKernel (N := N)) (l l' : Fin n) (σs : ReplicaSpace N n) : ℝ :=
  U (σs l) (σs l')

noncomputable def U_kernel_SK : InteractionKernel (N := N) :=
  fun σ τ =>
    let R := overlap N σ τ
    (β^2 / 2) * (R^2 - q)

noncomputable def U_interaction_SK (l l' : Fin n) (σs : ReplicaSpace N n) : ℝ :=
  U_interaction (N := N) (n := n) (U := U_kernel_SK (N := N) (β := β) (q := q)) l l' σs

/-!
### The Derivative of the Gibbs Average with respect to the Hamiltonian

This is an essential building block for deriving the replica‑derivative formula (Talagrand Lemma
1.4.2). Given a function `f : ReplicaFun N n` and a test direction `v : EnergySpace N`, the
directional derivative of the Gibbs average with respect to the Hamiltonian `H` in direction `v` is:

  `∑_{σs} f(σs) * ∑_l p_l * (⟨v⟩ - v(σ^l))`

where `p_l` is the product Gibbs weight over replicas **except** replica `l`.
-/

/--
The derivative of the Gibbs weight `∏ l, gibbs_pmf N H (σs l)` with respect to `H` in direction `v`.
Mathematically:
\[
  \frac{d}{dε}\bigg|_{ε=0} ∏_l p_{H + ε v}(σ^l)
    = ∏_l p_H(σ^l) \cdot \sum_l \bigl(\langle v \rangle_H - v(σ^l)\bigr),
\]
where \(\langle v \rangle_H = \sum_\sigma p_H(\sigma) v(\sigma)\).
-/
lemma fderiv_prod_gibbs_pmf_apply (H v : EnergySpace N) (σs : ReplicaSpace N n) :
    fderiv ℝ (fun H' => ∏ l : Fin n, gibbs_pmf N H' (σs l)) H v =
      (∏ l : Fin n, gibbs_pmf N H (σs l)) *
        ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)) := by
  classical
  -- `gibbs_pmf N (·) σ` is smooth in `H` and its derivative was computed in `fderiv_gibbs_pmf_apply`.
  -- We differentiate the product using `fderiv_finset_prod`.
  have hdiff : ∀ l : Fin n,
      DifferentiableAt ℝ (fun H' => gibbs_pmf N H' (σs l)) H := by
    intro l
    exact SpinGlass.differentiableAt_gibbs_pmf (N := N) (H := H) (σ := σs l)
  have h_fderiv_prod :=
    fderiv_finset_prod
      (𝕜 := ℝ) (E := EnergySpace N) (𝔸' := ℝ) (u := (Finset.univ : Finset (Fin n)))
      (g := fun l H' => gibbs_pmf N H' (σs l))
      (fun l _hl => hdiff l)
  rw [h_fderiv_prod]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  -- Substitute the explicit derivative `fderiv_gibbs_pmf_apply` for each term.
  have hterm : ∀ l : Fin n,
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
        fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H v
      = (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
          (gibbs_pmf N H (σs l) *
            ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))) := by
    intro l
    simp [SpinGlass.fderiv_gibbs_pmf_apply]
  -- Simplify the sum over `l`.
  calc
    ∑ l ∈ (Finset.univ : Finset (Fin n)),
        (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
          fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H v
      = ∑ l ∈ (Finset.univ : Finset (Fin n)),
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
            (gibbs_pmf N H (σs l) *
              ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))) := by
          refine Finset.sum_congr rfl (fun l _hl => ?_)
          simpa using hterm l
    _ = ∑ l ∈ (Finset.univ : Finset (Fin n)),
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
            (gibbs_pmf N H (σs l) *
              ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))) := by
          rfl
    _ = ∑ l ∈ (Finset.univ : Finset (Fin n)),
          (∏ j : Fin n, gibbs_pmf N H (σs j)) *
            ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)) := by
            refine Finset.sum_congr rfl (fun l _hl => ?_)
            -- `(∏_{j ≠ l} p_j) * p_l = ∏_j p_j`
            have herase : (∏ j ∈ (Finset.univ : Finset (Fin n)).erase l, gibbs_pmf N H (σs j)) *
                gibbs_pmf N H (σs l)
                = ∏ j : Fin n, gibbs_pmf N H (σs j) := by
              classical
              simpa using
                (Finset.prod_erase_mul
                  (s := (Finset.univ : Finset (Fin n)))
                  (f := fun j => gibbs_pmf N H (σs j))
                  (a := l) (Finset.mem_univ l))
            -- pull `((∑ τ, ...) - v (σs l))` out to the far right, then rewrite the left factor via `herase`
            have := congrArg (fun a => a * (((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)))) herase
            -- the remaining goal is purely associativity/commutativity
            -- (we keep it explicit to avoid fragile `simp` behaviour)
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
    _ = (∏ j : Fin n, gibbs_pmf N H (σs j)) *
          ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)) := by
            -- factor the constant `∏_j p_j` out of the sum
            -- (`∑ l : Fin n, …` is definitional equal to `∑ l ∈ Finset.univ, …`.)
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
                (f := fun l => (∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))
                (a := (∏ j : Fin n, gibbs_pmf N H (σs j)))).symm

/-- Differentiability of the product Gibbs weight as a function of the Hamiltonian. -/
lemma differentiableAt_prod_gibbs_pmf (H : EnergySpace N) (σs : ReplicaSpace N n) :
    DifferentiableAt ℝ (fun H' => ∏ l : Fin n, gibbs_pmf N H' (σs l)) H := by
  classical
  -- Use `HasFDerivAt.finset_prod` and the differentiability of `gibbs_pmf`.
  have hg :
      ∀ l ∈ (Finset.univ : Finset (Fin n)),
        HasFDerivAt (fun H' => gibbs_pmf N H' (σs l))
          (fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H) H := by
    intro l _hl
    exact (SpinGlass.differentiableAt_gibbs_pmf (N := N) (H := H) (σ := σs l)).hasFDerivAt
  have hHas :=
    (HasFDerivAt.finset_prod (u := (Finset.univ : Finset (Fin n)))
      (g := fun l H' => gibbs_pmf N H' (σs l))
      (g' := fun l => fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H)
      (x := H) hg).differentiableAt
  -- The `Fintype` product is definitional equal to the `Finset.univ` product.
  simpa using hHas

/-- Directional derivative of `gibbs_average_n_det` with respect to the Hamiltonian. -/
lemma fderiv_gibbs_average_n_det_apply (H v : EnergySpace N) (f : ReplicaFun N n) :
    fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f) H v =
      ∑ σs : ReplicaSpace N n,
        f σs * (∏ l : Fin n, gibbs_pmf N H (σs l)) *
          ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)) := by
  classical
  let u : Finset (ReplicaSpace N n) := Finset.univ
  let A : ReplicaSpace N n → EnergySpace N → ℝ :=
    fun σs H' => f σs * ∏ l : Fin n, gibbs_pmf N H' (σs l)
  have hA_diff : ∀ σs ∈ u, DifferentiableAt ℝ (A σs) H := by
    intro σs _hσs
    have hprod :
        DifferentiableAt ℝ (fun H' => ∏ l : Fin n, gibbs_pmf N H' (σs l)) H :=
      differentiableAt_prod_gibbs_pmf (N := N) (n := n) (H := H) σs
    simpa [A] using (DifferentiableAt.const_mul hprod (f σs))
  have hfderiv_sum :
      fderiv ℝ (fun H' : EnergySpace N => ∑ σs ∈ u, A σs H') H
        = ∑ σs ∈ u, fderiv ℝ (A σs) H := by
    simpa [u] using (fderiv_fun_sum (u := u) (A := A) (x := H) hA_diff)
  -- Rewrite `gibbs_average_n_det` in terms of the finset sum `∑ σs ∈ u, A σs`.
  -- (This is definitional because `u = Finset.univ`.)
  have hrewrite :
      (fun H' : EnergySpace N => gibbs_average_n_det (N := N) (n := n) H' f)
        = fun H' : EnergySpace N => ∑ σs ∈ u, A σs H' := by
    funext H'
    simp [gibbs_average_n_det, u, A]
  -- Apply the `fderiv_fun_sum` formula and compute termwise using `fderiv_const_mul`
  -- and `fderiv_prod_gibbs_pmf_apply`.
  -- We keep the algebra explicit to avoid `simp` producing the alternative form
  -- `n * E[v] - ∑ v(σ^l)`.
  rw [hrewrite]
  -- replace the `Fintype` sum with the `Finset.univ` sum
  have : fderiv ℝ (fun H' : EnergySpace N => ∑ σs ∈ u, A σs H') H v =
      (∑ σs ∈ u, fderiv ℝ (A σs) H) v := by
    -- rewrite via `hfderiv_sum`
    simp [hfderiv_sum]
  -- now expand the RHS at direction `v`
  -- and simplify each term
  simp [this, u, A, fderiv_const_mul, differentiableAt_prod_gibbs_pmf,
    fderiv_prod_gibbs_pmf_apply, mul_assoc, mul_left_comm, mul_comm, mul_add, sub_eq_add_neg,
    Finset.mul_sum]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/--
Differentiability of the `gibbs_average_n` in the Hamiltonian `H`.
-/
lemma differentiableAt_gibbs_average_n (t : ℝ) (f : ReplicaFun N n) (w : Ω) :
    DifferentiableAt ℝ
      (fun H' => ∑ σs : ReplicaSpace N n, f σs * ∏ l, gibbs_pmf N H' (σs l))
      (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
  classical
  let H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w
  -- Each term in the finite sum is differentiable (product of differentiable factors).
  have hterm : ∀ σs : ReplicaSpace N n,
      DifferentiableAt ℝ (fun H' => f σs * ∏ l, gibbs_pmf N H' (σs l)) H := by
    intro σs
    -- First, differentiate the product Gibbs weight in `H'`.
    have hprod :
        DifferentiableAt ℝ (fun H' => ∏ l : Fin n, gibbs_pmf N H' (σs l)) H := by
      -- Prove `HasFDerivAt` for the finset product and take `differentiableAt`.
      have hg :
          ∀ l ∈ (Finset.univ : Finset (Fin n)),
            HasFDerivAt (fun H' => gibbs_pmf N H' (σs l))
              (fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H) H := by
        intro l _hl
        exact
          (SpinGlass.differentiableAt_gibbs_pmf (N := N) (H := H) (σ := σs l)).hasFDerivAt
      have hHas :=
        (HasFDerivAt.finset_prod (u := (Finset.univ : Finset (Fin n)))
          (g := fun l H' => gibbs_pmf N H' (σs l))
          (g' := fun l => fderiv ℝ (fun H' => gibbs_pmf N H' (σs l)) H)
          (x := H) hg).differentiableAt
      -- The `Fintype` product is definitional equal to the `Finset.univ` product.
      simpa using hHas
    -- Multiply by the constant factor `f σs`.
    exact DifferentiableAt.const_mul hprod (f σs)
  -- Now differentiate the finite sum over replica configurations.
  -- The `Fintype` sum is definitional equal to the `Finset.univ` sum.
  have hsum :
      DifferentiableAt ℝ
        (fun H' => ∑ σs ∈ (Finset.univ : Finset (ReplicaSpace N n)),
          f σs * ∏ l, gibbs_pmf N H' (σs l)) H := by
    refine
      (DifferentiableAt.fun_sum (𝕜 := ℝ) (E := EnergySpace N) (F := ℝ)
        (u := (Finset.univ : Finset (ReplicaSpace N n)))
        (A := fun σs : ReplicaSpace N n => fun H' : EnergySpace N =>
          f σs * ∏ l, gibbs_pmf N H' (σs l))
        (x := H) ?_)
    intro σs _hσs
    simpa using hterm σs

  simpa using hsum

/-!
### Differentiation of `ν_t(f)` with respect to `t`

This is the analytic “outer layer” of Talagrand’s Lemma 1.4.2:
we differentiate the expected Gibbs average along the smart path `H_t`.

At this stage we only push the derivative through the outer expectation;
the subsequent Gaussian IBP step (turning the derivative into replica–interaction terms)
is developed later.
-/

open scoped Topology

open Set

/-- Derivative of the interpolated Hamiltonian `H_t` with respect to `t` (pointwise in `ω`). -/
noncomputable def dH_t (t : ℝ) (w : Ω) : EnergySpace N :=
  (1 / (2 * Real.sqrt t)) • sk.U w - (1 / (2 * Real.sqrt (1 - t))) • sim.V w

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma hasDerivAt_H_gauss (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (w : Ω) :
    HasDerivAt
        (fun s =>
          H_gauss (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) t := by
  -- Differentiate `√t • U + √(1-t) • V`.
  have ht_ne0 : t ≠ 0 := ne_of_gt ht.1
  have h1t_ne0 : (1 - t) ≠ 0 := by
    have : t < 1 := ht.2
    linarith
  -- `t ↦ √t`
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt s) (1 / (2 * Real.sqrt t)) t :=
    (Real.hasDerivAt_sqrt ht_ne0)
  -- `t ↦ √(1 - t)`
  have hsub : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1 : ℝ) t := by
    simpa using (HasDerivAt.const_sub (c := (1 : ℝ)) (hasDerivAt_id t))
  have hsqrt_sub :
      HasDerivAt (fun s : ℝ => Real.sqrt ((1 : ℝ) - s))
        ((1 / (2 * Real.sqrt (1 - t))) * (-1 : ℝ)) t := by
    -- chain rule: `sqrt ∘ (1 - ·)`
    exact (Real.hasDerivAt_sqrt h1t_ne0).comp t hsub
  -- Now scale by constant vectors `U w` and `V w`, and add.
  have hU :
      HasDerivAt (fun s : ℝ => (Real.sqrt s) • sk.U w)
        ((1 / (2 * Real.sqrt t)) • sk.U w) t :=
    hsqrt.smul_const (sk.U w)
  have hV :
      HasDerivAt (fun s : ℝ => (Real.sqrt ((1 : ℝ) - s)) • sim.V w)
        (((1 / (2 * Real.sqrt (1 - t))) * (-1 : ℝ)) • sim.V w) t :=
    hsqrt_sub.smul_const (sim.V w)
  -- Put the pieces together and normalize to the chosen `dH_t` expression.
  have hadd := hU.add hV
  -- `((1/(2√(1-t))) * (-1)) • V = -(1/(2√(1-t))) • V`.
  simpa [H_gauss, dH_t, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    mul_assoc, mul_left_comm, mul_comm] using hadd

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma hasDerivAt_H_t (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (w : Ω) :
    HasDerivAt
        (fun s =>
          H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) t := by
  -- `H_t = H_gauss + H_field`, and `H_field` is constant in `t`.
  simpa [H_t, dH_t, H_field]
    using (hasDerivAt_H_gauss (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ht w).add_const
      (H_field (N := N) (h := h))

/-- Pointwise derivative of the `n`-replica Gibbs average along the path `H_t`. -/
noncomputable def dgibbs_average_n (t : ℝ) (f : ReplicaFun N n) (w : Ω) : ℝ :=
  fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma hasDerivAt_gibbs_average_n (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (f : ReplicaFun N n) (w : Ω) :
    HasDerivAt
        (fun s =>
          gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n s f w)
        (dgibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w) t := by
  classical
  -- Chain rule: `t ↦ H_t(t,w)` then `H ↦ gibbs_average_n_det H f`.
  let G : EnergySpace N → ℝ := fun H' => gibbs_average_n_det (N := N) (n := n) H' f
  have hG_diff :
      DifferentiableAt ℝ G
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
    -- `gibbs_average_n_det` is a finite sum of products of `gibbs_pmf`, hence differentiable.
    -- This is exactly `differentiableAt_gibbs_average_n` after unfolding `gibbs_average_n_det`.
    simpa [G, gibbs_average_n_det] using
      differentiableAt_gibbs_average_n (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) (n := n) (t := t) (f := f) w
  have hG : HasFDerivAt G (fderiv ℝ G (H_t (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t w))
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) :=
    hG_diff.hasFDerivAt
  have hHt :
      HasDerivAt
          (fun s => H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) t :=
    hasDerivAt_H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ht w
  -- Apply the chain rule in the form `HasFDerivAt.comp_hasDerivAt`.
  -- Then rewrite the derivative as `dgibbs_average_n`.
  have hcomp :=
    (HasFDerivAt.comp_hasDerivAt (x := t) (f := fun s =>
        H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
      (l := G) (l' := fderiv ℝ G (H_t (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t w)) hG hHt)
  -- Unfold `gibbs_average_n` and `dgibbs_average_n`.
  simpa [gibbs_average_n, G, dgibbs_average_n] using hcomp

/-!
To differentiate `ν_t(f) = 𝔼[⟨f⟩_t]`, we use the dominated differentiation lemma
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

The only nontrivial analytic inputs are:
- pointwise differentiability of `t ↦ ⟨f⟩_t(ω)`,
- an integrable uniform (in `t` near `t₀`) bound on the derivative.
-/

lemma norm_fderiv_gibbs_average_n_det_le (H : EnergySpace N) (f : ReplicaFun N n) :
    ‖fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f) H‖
      ≤ (2 * (n : ℝ)) * (∑ σs : ReplicaSpace N n, ‖f σs‖) := by
  classical
  -- Use `opNorm_le_bound` with the explicit `fderiv` formula.
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ (fun v => ?_)
  · -- nonnegativity of the constant
    have : 0 ≤ (2 : ℝ) * (n : ℝ) := by positivity
    exact mul_nonneg this (by
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  · -- bound on `‖fderiv ... v‖`
    -- Start from the explicit directional derivative formula.
    have hv_formula :
        fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f) H v =
          ∑ σs : ReplicaSpace N n,
            f σs * (∏ l : Fin n, gibbs_pmf N H (σs l)) *
              ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)) := by
      simpa using
        fderiv_gibbs_average_n_det_apply (N := N) (n := n) (H := H) (v := v) f
    -- Crude bounds: `∏ p ≤ 1` and each `|(E[v]) - v(σ)| ≤ 2‖v‖`.
    have hprod_le_one :
        ∀ σs : ReplicaSpace N n, (∏ l : Fin n, gibbs_pmf N H (σs l)) ≤ (1 : ℝ) := by
      intro σs
      classical
      have hfac : ∀ l : Fin n, gibbs_pmf N H (σs l) ≤ 1 := by
        intro l
        exact SpinGlass.gibbs_pmf_le_one (N := N) (H := H) (σ := σs l)
      have hnonneg : ∀ l : Fin n, 0 ≤ gibbs_pmf N H (σs l) := by
        intro l
        exact SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l)
      simpa using
        (Finset.prod_le_one (s := (Finset.univ : Finset (Fin n)))
          (f := fun l => gibbs_pmf N H (σs l))
          (fun l _hl => hnonneg l) (fun l _hl => hfac l))
    have hEval_le : ∀ τ : Config N, |v τ| ≤ ‖v‖ := by
      intro τ
      -- evaluation is 1-Lipschitz in `PiLp 2`
      simpa [Real.norm_eq_abs] using
        (SpinGlass.abs_apply_le_norm (N := N) v τ)
    have hE_le : |∑ τ : Config N, gibbs_pmf N H τ * v τ| ≤ ‖v‖ := by
      classical
      -- `|∑ pτ * vτ| ≤ ∑ pτ * |vτ| ≤ ‖v‖ * ∑ pτ = ‖v‖`.
      have hsum1 : (∑ τ : Config N, gibbs_pmf N H τ) = 1 := by
        simpa using SpinGlass.sum_gibbs_pmf (N := N) (H := H)
      calc
        |∑ τ : Config N, gibbs_pmf N H τ * v τ|
            ≤ ∑ τ : Config N, |gibbs_pmf N H τ * v τ| := by
                -- triangle inequality
                simpa using
                  (Finset.abs_sum_le_sum_abs
                    (f := fun τ : Config N => gibbs_pmf N H τ * v τ)
                    (s := (Finset.univ : Finset (Config N))))
        _ = ∑ τ : Config N, (gibbs_pmf N H τ) * |v τ| := by
              refine Finset.sum_congr rfl (fun τ _ => ?_)
              rw [abs_mul]
              congr 1
              exact abs_of_nonneg (SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σ := τ))
        _ ≤ ∑ τ : Config N, (gibbs_pmf N H τ) * ‖v‖ := by
              refine Finset.sum_le_sum (fun τ _ => ?_)
              gcongr; exact gibbs_pmf_nonneg N H τ; exact hEval_le τ
        _ = ‖v‖ * ∑ τ : Config N, gibbs_pmf N H τ := by
              rw [← Finset.sum_mul]
              exact CommMonoid.mul_comm (∑ i, gibbs_pmf N H i) ‖v‖ --refine Finset.sum_congr rfl (fun τ _ => ?_)
        _ = ‖v‖ := by simp [hsum1]
    have hdiff_le : ∀ σs : ReplicaSpace N n, ∀ l : Fin n,
        |(∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)| ≤ 2 * ‖v‖ := by
      intro σs l
      -- `|a - b| ≤ |a| + |b|`.
      have : |(∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)|
          ≤ |∑ τ : Config N, gibbs_pmf N H τ * v τ| + |v (σs l)| := by
        simpa [sub_eq_add_neg, abs_add_le] using (abs_sub _ _)
      -- then bound each absolute value by `‖v‖`.
      have hvσ : |v (σs l)| ≤ ‖v‖ := by
        simpa using hEval_le (σs l)
      calc
        |(∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)|
            ≤ |∑ τ : Config N, gibbs_pmf N H τ * v τ| + |v (σs l)| := this
        _ ≤ ‖v‖ + ‖v‖ := by gcongr
        _ = 2 * ‖v‖ := by ring
    -- Now bound the whole sum using `∏ p ≤ 1`.
    rw [hv_formula]
    -- turn the goal into an `abs` inequality
    simp only [Real.norm_eq_abs]
    calc
      |∑ σs : ReplicaSpace N n,
          (f σs * (∏ l : Fin n, gibbs_pmf N H (σs l)) *
            ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)))|
          ≤ ∑ σs : ReplicaSpace N n,
              |f σs * (∏ l : Fin n, gibbs_pmf N H (σs l)) *
                ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))| := by
                simpa using
                  (Finset.abs_sum_le_sum_abs
                    (f := fun σs : ReplicaSpace N n =>
                      f σs * (∏ l : Fin n, gibbs_pmf N H (σs l)) *
                        ∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)))
                    (s := (Finset.univ : Finset (ReplicaSpace N n))))
      _ = ∑ σs : ReplicaSpace N n,
            (‖f σs‖ * |∏ l : Fin n, gibbs_pmf N H (σs l)| *
              |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))|) := by
            refine Finset.sum_congr rfl (fun σs _ => ?_)
            simp [abs_mul, Real.norm_eq_abs, mul_assoc]
      _ ≤ ∑ σs : ReplicaSpace N n,
            (‖f σs‖ * (1 : ℝ) * ((2 * (n : ℝ)) * ‖v‖)) := by
            refine Finset.sum_le_sum (fun σs _ => ?_)
            have hprod_abs : |∏ l : Fin n, gibbs_pmf N H (σs l)|
                ≤ (1 : ℝ) := by
              have hnonneg : 0 ≤ ∏ l : Fin n, gibbs_pmf N H (σs l) := by
                classical
                refine Finset.prod_nonneg ?_
                intro l _hl
                exact SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l)
              have hle1 : (∏ l : Fin n, gibbs_pmf N H (σs l)) ≤ (1 : ℝ) := hprod_le_one σs
              simpa [abs_of_nonneg hnonneg] using hle1
            have hsum_abs :
                |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))|
                  ≤ (2 * (n : ℝ)) * ‖v‖ := by
              classical
              -- triangle inequality then termwise bound by `2‖v‖`
              calc
                |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))|
                    ≤ ∑ l : Fin n,
                        |(∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l)| := by
                          simpa using
                            (Finset.abs_sum_le_sum_abs
                              (f := fun l : Fin n =>
                                (∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))
                              (s := (Finset.univ : Finset (Fin n))))
                _ ≤ ∑ l : Fin n, (2 * ‖v‖) := by
                      refine Finset.sum_le_sum (fun l _ => ?_)
                      exact hdiff_le σs l
                _ = (2 * ‖v‖) * (n : ℝ) := by
                      -- `∑_{Fin n} c = c * n`
                      simp [Finset.card_univ, mul_comm]
              -- put the RHS in the same form as the statement
              simp [mul_assoc, mul_comm]
            -- combine the bounds
            have : ‖f σs‖ * |∏ l : Fin n, gibbs_pmf N H (σs l)| *
                |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))|
                ≤ ‖f σs‖ * (1 : ℝ) * ((2 * (n : ℝ)) * ‖v‖) := by
              have h1 : |∏ l : Fin n, gibbs_pmf N H (σs l)| ≤ 1 := hprod_abs
              have h2 : |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))| ≤ (2 * (n : ℝ)) * ‖v‖ := hsum_abs
              have h3 : 0 ≤ ‖f σs‖ := norm_nonneg (f σs)
              have h4 : 0 ≤ |∏ l : Fin n, gibbs_pmf N H (σs l)| := abs_nonneg _
              have h5 : 0 ≤ |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))| := abs_nonneg _
              calc ‖f σs‖ * |∏ l : Fin n, gibbs_pmf N H (σs l)| *
                      |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))|
                  ≤ ‖f σs‖ * 1 * |∑ l : Fin n, ((∑ τ : Config N, gibbs_pmf N H τ * v τ) - v (σs l))| := by
                    apply mul_le_mul_of_nonneg_right
                    · apply mul_le_mul_of_nonneg_left h1 h3
                    · exact h5
                _ ≤ ‖f σs‖ * 1 * ((2 * (n : ℝ)) * ‖v‖) := by
                    apply mul_le_mul_of_nonneg_left h2
                    apply mul_nonneg h3
                    norm_num
            simpa [mul_assoc] using this
      _ = ((2 * (n : ℝ)) * ‖v‖) * (∑ σs : ReplicaSpace N n, ‖f σs‖) := by
            classical
            -- factor out the constant `(2*n*‖v‖)` from the finset sum
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun σs _ => ?_)
            ring
      _ = (2 * (n : ℝ)) * (∑ σs : ReplicaSpace N n, ‖f σs‖) * ‖v‖ := by
            ring

set_option maxHeartbeats 600000 in
theorem hasDerivAt_nu (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (f : ReplicaFun N n) :
    HasDerivAt
        (fun s => nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n s f)
        (∫ w, dgibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n t f w ∂ℙ) t := by
  classical
  -- Apply the general “differentiate under the integral” lemma on a small ball inside `(0,1)`.
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have h1t0 : 0 < 1 - t := by linarith
  let ε : ℝ := (min t (1 - t)) / 2
  have hε_pos : 0 < ε := by
    have hmin : 0 < min t (1 - t) := lt_min ht0 h1t0
    have : 0 < (min t (1 - t)) / 2 := by linarith
    simpa [ε] using this
  have hball_Ioo : ∀ x ∈ Metric.ball t ε, x ∈ Ioo (0 : ℝ) 1 := by
    intro x hx
    have hx' : |x - t| < ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm, ε] using hx
    have hx1 : x - t < ε := (abs_sub_lt_iff.1 hx').1
    have hx2 : t - x < ε := (abs_sub_lt_iff.1 hx').2
    have hε_le_t : ε ≤ t / 2 := by
      have : min t (1 - t) ≤ t := min_le_left _ _
      have : (min t (1 - t)) / 2 ≤ t / 2 := by nlinarith
      simpa [ε] using this
    have hε_le_1t : ε ≤ (1 - t) / 2 := by
      have : min t (1 - t) ≤ (1 - t) := min_le_right _ _
      have : (min t (1 - t)) / 2 ≤ (1 - t) / 2 := by nlinarith
      simpa [ε] using this
    have hx_lower : t / 2 < x := by
      have ht_eps : t / 2 ≤ t - ε := by nlinarith [hε_le_t]
      have hx_gt : t - ε < x := by linarith
      exact lt_of_le_of_lt ht_eps hx_gt
    -- We'll just use `linarith` on the simple inequalities to get `0 < x` and `x < 1`.
    have hx_gt0 : 0 < x := by
      have ht_eps : t - ε ≥ t / 2 := by nlinarith [hε_le_t]
      have hx_gt : t - ε < x := by linarith
      have : t / 2 < x := lt_of_le_of_lt ht_eps hx_gt
      have : 0 < t / 2 := by nlinarith [ht0]
      exact Std.lt_trans this hx_lower-- lt_trans this this_1
    have hx_lt1 : x < 1 := by
      have hx_lt : x < t + ε := by linarith
      have ht_eps : t + ε ≤ (1 + t) / 2 := by nlinarith [hε_le_1t]
      have : x < (1 + t) / 2 := lt_of_lt_of_le hx_lt ht_eps
      have : (1 + t) / 2 < 1 := by nlinarith [ht1]
      simp; grind-- lt_trans this this_1
    exact ⟨hx_gt0, hx_lt1⟩
  -- Set up the parametric integral data.
  let F : ℝ → Ω → ℝ :=
    fun s w =>
      gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n s f w
  let F' : ℝ → Ω → ℝ :=
    fun s w =>
      dgibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) n s f w
  -- measurability of `F s` near `t`: integrability implies a.e. strong measurability
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) (ℙ : Measure Ω) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    exact (integrable_gibbs_average_n (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) (n := n) (t := s) (f := f)).aestronglyMeasurable
  have hF_int : Integrable (F t) (ℙ : Measure Ω) :=
    integrable_gibbs_average_n (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) (n := n) (t := t) (f := f)
  -- A measurable and integrable domination bound for `F'` on the ball.
  -- Bound the `fderiv` operator norm uniformly in `H`.
  let Cf : ℝ := (2 * (n : ℝ)) * (∑ σs : ReplicaSpace N n, ‖f σs‖)
  have hCf_nonneg : 0 ≤ Cf := by
    have : 0 ≤ (2 : ℝ) * (n : ℝ) := by positivity
    exact mul_nonneg this (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  -- Coefficient bounds on the ball: `|1/(2√x)|` and `|1/(2√(1-x))|` are bounded by constants.
  let cU : ℝ := 1 / (2 * Real.sqrt (t / 2))
  let cV : ℝ := 1 / (2 * Real.sqrt ((1 - t) / 2))
  have hcU_nonneg : 0 ≤ cU := by
    have : 0 ≤ 2 * Real.sqrt (t / 2) := by positivity
    exact one_div_nonneg.2 this
  have hcV_nonneg : 0 ≤ cV := by
    have : 0 ≤ 2 * Real.sqrt ((1 - t) / 2) := by positivity
    exact one_div_nonneg.2 this
  let bound : Ω → ℝ := fun w => Cf * (cU * ‖sk.U w‖ + cV * ‖sim.V w‖)
  have hbound_int : Integrable bound (ℙ : Measure Ω) := by
    -- `‖U‖` and `‖V‖` are integrable since both are finite-dimensional Gaussians.
    have hU_int : Integrable (fun w => ‖sk.U w‖) (ℙ : Measure Ω) :=
      (integrable_norm_of_gaussian (g := sk.U) sk.hU)
    have hV_int : Integrable (fun w => ‖sim.V w‖) (ℙ : Measure Ω) :=
      (integrable_norm_of_gaussian (g := sim.V) sim.hV)
    -- close by linearity
    have h1 : Integrable (fun w => cU * ‖sk.U w‖) (ℙ : Measure Ω) := (hU_int.const_mul cU)
    have h2 : Integrable (fun w => cV * ‖sim.V w‖) (ℙ : Measure Ω) := (hV_int.const_mul cV)
    have hsum : Integrable (fun w => cU * ‖sk.U w‖ + cV * ‖sim.V w‖) (ℙ : Measure Ω) := h1.add h2
    simpa [bound, Cf, mul_add, mul_assoc] using hsum.const_mul Cf
  have hF'_meas : AEStronglyMeasurable (F' t) (ℙ : Measure Ω) := by
    -- We get this from integrability of the domination bound plus a crude inequality;
    -- in particular, `F' t` is a.e. dominated by an integrable function, hence integrable,
    -- hence a.e. strongly measurable. We prove integrability below and reuse it here.
    -- For the dominated differentiation lemma we only need a.e. strong measurability;
    -- we obtain it from measurability of all components directly.
    -- (Since everything is a finite sum/product of measurable functions.)
    -- We give an explicit measurability proof to avoid circularity.
    -- First, show measurability of `H_t t` and `dH_t t`.
    have hU_meas : Measurable (sk.U) := sk.hU.repr_measurable
    have hV_meas : Measurable (sim.V) := sim.hV.repr_measurable
    have hHt_meas :
        Measurable (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
      have h1 : Measurable (fun w => (Real.sqrt t) • sk.U w) := hU_meas.const_smul (Real.sqrt t)
      have h2 : Measurable (fun w => (Real.sqrt (1 - t)) • sim.V w) := hV_meas.const_smul (Real.sqrt (1 - t))
      have h3 : Measurable (fun _w : Ω => H_field (N := N) (h := h)) := measurable_const
      simpa [H_t, H_gauss] using ((h1.add h2).add h3)
    have hdHt_meas :
        Measurable (fun w =>
          dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
      have h1 : Measurable (fun w => (1 / (2 * Real.sqrt t)) • sk.U w) :=
        hU_meas.const_smul (1 / (2 * Real.sqrt t))
      have h2 : Measurable (fun w => (1 / (2 * Real.sqrt (1 - t))) • sim.V w) :=
        hV_meas.const_smul (1 / (2 * Real.sqrt (1 - t)))
      simpa [dH_t, sub_eq_add_neg] using h1.add h2.neg
    -- Measurability of each coordinate weight `gibbs_pmf N (H_t t w) σ`.
    have h_gibbs_pmf_meas :
        ∀ (σ : Config N),
          Measurable fun w =>
            gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) σ := by
      intro σ
      -- use smoothness/continuity in `H` + measurability of `H_t`
      have hcont : Continuous fun H : EnergySpace N => gibbs_pmf N H σ :=
        (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σ)).continuous
      exact hcont.measurable.comp hHt_meas
    -- Measurability of the derivative integrand via the explicit `fderiv` formula.
    have hterm :
        ∀ σs : ReplicaSpace N n,
          Measurable fun w =>
            f σs *
              (∏ l : Fin n,
                gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)) *
                ∑ l : Fin n,
                  ((∑ τ : Config N,
                      gibbs_pmf N
                        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) -
                    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)) := by
      intro σs
      classical
      -- `w ↦ ∏ l, gibbs_pmf ...` is measurable.
      have hprod :
          Measurable fun w =>
            ∏ l : Fin n,
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l) := by
        -- rewrite as `Finset.univ` product
        simpa using
          (Finset.measurable_prod (s := (Finset.univ : Finset (Fin n)))
            (f := fun l w =>
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
            (hf := by
              intro l _hl
              simpa using h_gibbs_pmf_meas (σs l)))
      -- `w ↦ (dH_t t w) τ` is measurable for each `τ`.
      have h_dHt_eval : ∀ τ : Config N, Measurable fun w =>
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ := by
        intro τ
        exact (evalCLM (N := N) τ).measurable.comp hdHt_meas
      -- `w ↦ ∑ τ, gibbs_pmf ... τ * dH_t(t,w) τ` is measurable.
      have hEv :
          Measurable fun w =>
            ∑ τ : Config N,
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ := by
        classical
        simpa using
          (Finset.measurable_sum (s := (Finset.univ : Finset (Config N)))
            (f := fun τ w =>
              gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ)
            (hf := by
              intro τ _hτ
              exact (h_gibbs_pmf_meas τ).mul (h_dHt_eval τ)))
      -- `w ↦ ∑ l, (Ev(w) - dH_t(w)(σs l))` is measurable.
      have hsumL :
          Measurable fun w =>
            ∑ l : Fin n,
              ((∑ τ : Config N,
                  gibbs_pmf N
                    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) -
                (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)) := by
        classical
        simpa using
          (Finset.measurable_sum (s := (Finset.univ : Finset (Fin n)))
            (f := fun l w => (∑ τ : Config N,
                  gibbs_pmf N
                    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) -
                (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))
            (hf := by
              intro l _hl
              exact hEv.sub (h_dHt_eval (σs l))))
      -- finish: constant times measurable product times measurable sum
      simpa [mul_assoc] using (measurable_const.mul (hprod.mul hsumL))
    have hderiv_meas :
        Measurable fun w =>
          (∑ σs : ReplicaSpace N n,
            f σs *
              (∏ l : Fin n,
                gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)) *
                ∑ l : Fin n,
                  ((∑ τ : Config N,
                      gibbs_pmf N
                        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) -
                    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))) := by
      classical
      simpa using
        (Finset.measurable_sum (s := (Finset.univ : Finset (ReplicaSpace N n)))
          (f := fun σs w =>
            f σs *
              (∏ l : Fin n,
                gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)) *
                ∑ l : Fin n,
                  ((∑ τ : Config N,
                      gibbs_pmf N
                        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) -
                    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)))
          (hf := by intro σs _; simpa using hterm σs))
    -- Now `dgibbs_average_n` is `fderiv` applied to `dH_t`; rewrite via the formula.
    have :
        (fun w => dgibbs_average_n (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) n t f w)
          =
        (fun w =>
          ∑ σs : ReplicaSpace N n,
            f σs *
              (∏ l : Fin n,
                gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l)) *
                ∑ l : Fin n,
                  ((∑ τ : Config N,
                      gibbs_pmf N
                        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ *
                        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) τ) -
                    (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (σs l))) := by
      funext w
      -- unfold `dgibbs_average_n` and rewrite the `fderiv` using `fderiv_gibbs_average_n_det_apply`
      simp [dgibbs_average_n, fderiv_gibbs_average_n_det_apply]
    -- Conclude a.e. strong measurability.
    simpa [F', this] using hderiv_meas.aestronglyMeasurable
  have h_bound :
      ∀ᵐ w ∂(ℙ : Measure Ω), ∀ x ∈ Metric.ball t ε, ‖F' x w‖ ≤ bound w := by
    -- the bound is pointwise, so we can use `ae_of_all`.
    refine ae_of_all _ (fun w => ?_)
    intro x hx
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 := hball_Ioo x hx
    -- Use `‖fderiv‖ ≤ Cf` and `‖dH_t x w‖ ≤ cU‖U‖ + cV‖V‖`.
    have hL :
        ‖fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖ ≤ Cf := by
      -- `norm_fderiv_gibbs_average_n_det_le` is uniform in `H`.
      simpa [Cf] using
        (norm_fderiv_gibbs_average_n_det_le (N := N) (n := n)
          (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) (f := f))
    have hCoeffU :
        |1 / (2 * Real.sqrt x)| ≤ cU := by
      -- On the ball, `x ≥ t/2`, hence `1/(2√x) ≤ 1/(2√(t/2))`.
      have hx_gt0 : 0 < x := hxIoo.1
      have hx_lower : t / 2 ≤ x := by
        -- from `|x - t| < ε` and `ε ≤ t/2`
        have hx' : |x - t| < ε := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
        have hx2 : t - x < ε := (abs_sub_lt_iff.1 hx').2
        have hε_le_t : ε ≤ t / 2 := by
          have : min t (1 - t) ≤ t := min_le_left _ _
          have : (min t (1 - t)) / 2 ≤ t / 2 := by nlinarith
          simpa [ε] using this
        have hx_gt : t - ε < x := by linarith
        have ht_eps : t / 2 ≤ t - ε := by nlinarith [hε_le_t]
        exact le_trans ht_eps (le_of_lt hx_gt)
      -- finish with monotonicity; since everything is nonnegative, abs is redundant
      have hx_ge : t / 2 ≤ x := hx_lower
      have hsqrt_le : Real.sqrt (t / 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx_ge
      have hpos : 0 < 2 * Real.sqrt (t / 2) := by
        have : 0 < Real.sqrt (t / 2) := by
          have : 0 < t / 2 := by nlinarith [ht0]
          exact Real.sqrt_pos.2 this
        nlinarith
      have hle :
          2 * Real.sqrt (t / 2) ≤ 2 * Real.sqrt x := by nlinarith [hsqrt_le]
      have : 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt (t / 2)) := by
        -- invert the inequality `2*sqrt(t/2) ≤ 2*sqrt x`
        simpa [one_div] using (one_div_le_one_div_of_le hpos hle)
      -- rewrite as abs bounds
      have hnonneg : 0 ≤ 1 / (2 * Real.sqrt x) := by positivity
      have hnonneg' : 0 ≤ 1 / (2 * Real.sqrt (t / 2)) := by positivity
      -- `simp` may rewrite `|1/(2*√x)|` into an expression involving `|√x|⁻¹`;
      -- make sure those abs's simplify using `0 ≤ √x`.
      simpa [cU, abs_of_nonneg hnonneg, abs_of_nonneg hnonneg', abs_of_nonneg (Real.sqrt_nonneg x), one_div]
        using this
    have hCoeffV :
        |1 / (2 * Real.sqrt (1 - x))| ≤ cV := by
      -- Similar bound for `1 - x ≥ (1 - t)/2` on the ball.
      have hx_lt1 : x < 1 := hxIoo.2
      have h1x_pos : 0 < 1 - x := by linarith
      have h1x_lower : (1 - t) / 2 ≤ 1 - x := by
        have hx' : |x - t| < ε := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
        have hx1 : x - t < ε := (abs_sub_lt_iff.1 hx').1
        have hε_le_1t : ε ≤ (1 - t) / 2 := by
          have : min t (1 - t) ≤ (1 - t) := min_le_right _ _
          have : (min t (1 - t)) / 2 ≤ (1 - t) / 2 := by nlinarith
          simpa [ε] using this
        have hx_le : x ≤ t + (1 - t) / 2 := by
          have hx_le' : x ≤ t + ε := by linarith
          exact le_trans hx_le' (by nlinarith [hε_le_1t])
        -- `x ≤ t + (1 - t)/2 = (1+t)/2` is equivalent to `(1 - t)/2 ≤ 1 - x`.
        nlinarith [hx_le]
      have hsqrt_le : Real.sqrt ((1 - t) / 2) ≤ Real.sqrt (1 - x) := Real.sqrt_le_sqrt h1x_lower
      have hpos : 0 < 2 * Real.sqrt ((1 - t) / 2) := by
        have : 0 < (1 - t) / 2 := by nlinarith [h1t0]
        have : 0 < Real.sqrt ((1 - t) / 2) := Real.sqrt_pos.2 this
        nlinarith
      have hle :
          2 * Real.sqrt ((1 - t) / 2) ≤ 2 * Real.sqrt (1 - x) := by nlinarith [hsqrt_le]
      have : 1 / (2 * Real.sqrt (1 - x)) ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by
        simpa [one_div] using (one_div_le_one_div_of_le hpos hle)
      have hnonneg : 0 ≤ 1 / (2 * Real.sqrt (1 - x)) := by positivity
      have hnonneg' : 0 ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by positivity
      simpa [cV, abs_of_nonneg hnonneg, abs_of_nonneg hnonneg',
        abs_of_nonneg (Real.sqrt_nonneg (1 - x)), one_div] using this
    -- Bound `‖dH_t x w‖`.
    have hdH_norm :
        ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖
          ≤ cU * ‖sk.U w‖ + cV * ‖sim.V w‖ := by
      -- expand `dH_t` and use triangle inequality + coefficient bounds
      have htri :
          ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖
            ≤ |1 / (2 * Real.sqrt x)| * ‖sk.U w‖ +
              |1 / (2 * Real.sqrt (1 - x))| * ‖sim.V w‖ := by
        -- `‖a • U - b • V‖ ≤ ‖a • U‖ + ‖b • V‖`
        simpa [dH_t, sub_eq_add_neg, norm_add_le, norm_smul, abs_mul] using
          (norm_add_le ((1 / (2 * Real.sqrt x)) • sk.U w) (-(1 / (2 * Real.sqrt (1 - x))) • sim.V w))
      have : |1 / (2 * Real.sqrt x)| * ‖sk.U w‖ +
            |1 / (2 * Real.sqrt (1 - x))| * ‖sim.V w‖
          ≤ cU * ‖sk.U w‖ + cV * ‖sim.V w‖ := by
        gcongr
      exact le_trans htri this
    -- Finally, combine everything.
    have hF'_bound :
        ‖F' x w‖ ≤ Cf * ‖dH_t (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) x w‖ := by
      -- `‖L v‖ ≤ ‖L‖ * ‖v‖` with `‖L‖ ≤ Cf`
      -- rewrite `F'` and use `‖L v‖ ≤ ‖L‖ * ‖v‖` plus monotonicity of `(*)` on `ℝ≥0`.
      -- (Avoid `nlinarith`: we need the fact `0 ≤ ‖dH_t …‖`.)
      have hop :
          ‖(fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w))
              (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖
            ≤ ‖fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖ *
              ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖ := by
        simpa using
          (ContinuousLinearMap.le_opNorm
            (fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w))
            (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w))
      have hmul :
          ‖fderiv ℝ (fun H' => gibbs_average_n_det (N := N) (n := n) H' f)
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖ *
              ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖
            ≤ Cf * ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖ := by
        exact mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      -- now put everything together and unfold `F'`.
      simpa [F', dgibbs_average_n, mul_assoc] using le_trans hop hmul
    have : ‖F' x w‖ ≤ bound w := by
      -- combine the previous bound with `hdH_norm`.
      have : ‖F' x w‖ ≤ Cf * (cU * ‖sk.U w‖ + cV * ‖sim.V w‖) := by
        exact le_trans hF'_bound (mul_le_mul_of_nonneg_left hdH_norm (hCf_nonneg))
      simpa [bound, mul_add, mul_assoc, mul_left_comm, mul_comm] using this
    exact this
  -- Pointwise differentiability on the ball.
  have h_diff :
      ∀ᵐ w ∂(ℙ : Measure Ω), ∀ x ∈ Metric.ball t ε,
        HasDerivAt (fun s => F s w) (F' x w) x := by
    refine ae_of_all _ (fun w => ?_)
    intro x hx
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 := hball_Ioo x hx
    simpa [F, F'] using
      hasDerivAt_gibbs_average_n (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) (n := n) (t := x) (ht := hxIoo) (f := f) w
  -- Now apply the dominated differentiation lemma.
  have hMain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (ℙ : Measure Ω)) (F := F) (F' := F') (x₀ := t) (bound := bound) (ε := ε)
      hε_pos hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  -- Unfold `nu`, `F`, `F'`.
  simpa [nu, F, F'] using hMain

end ReplicaCalculus

end SpinGlass
