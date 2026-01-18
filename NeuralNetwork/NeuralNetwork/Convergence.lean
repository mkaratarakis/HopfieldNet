/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/

import NeuralNetwork.BoltzmannMachine
import NeuralNetwork.aux

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

/-!
# Convergence of Strictly Hamiltonian Neural Networks
This file defines the `IsStrictlyHamiltonian` typeclass abstraction for a physical system whose dynamics are guaranteed to converge to a
fixed point. It formalizes the concept of a Lyapunov function with a tie-breaking
auxiliary potential, generalizing the proof given in the file Core.lean and executable in test.lean.
-/
variable {R U σ : Type*} [Field R] [LinearOrder R] [DecidableEq U] --[Fintype U] [DecidableEq U]

--variable {R U σ : Type*} [Field R] [LinearOrder R] --[IsStrictOrderedRing R] [Fintype U] --
variable (NN : NeuralNetwork R U σ)

open scoped Order Set Topology Filter Mathlib

/--
A typeclass asserting that a `NeuralNetwork`'s dynamics are governed by a pair of
potentials that guarantee convergence to a fixed point.

This is the formal requirement for a system to have convergent asynchronous dynamics.
-/
class IsStrictlyHamiltonian' where
  /-- The primary potential (energy), a real-valued function on the state space. -/
  energy (p : Params NN) (s : NN.State) : R
  /-- The auxiliary potential, mapping states to a well-founded set (e.g., ℕ) for tie-breaking. -/
  auxPotential (p : Params NN) (s : NN.State) : ℕ
  /-- Axiom 1: The energy is a Lyapunov function for the dynamics. -/
  energy_is_lyapunov (p : Params NN) (s : NN.State) (u : U) :
    energy p (s.Up p u) ≤ energy p s
  /-- Axiom 2: If the energy is constant and the state changes, the auxiliary potential
  strictly decreases. This is the crucial tie-breaking condition that prevents cycles. -/
  aux_strictly_decreases_on_tie (p : Params NN) (s : NN.State) (u : U)
    (h_state_change : s.Up p u ≠ s)
    (h_energy_tie : energy p (s.Up p u) = energy p s) :
    auxPotential p (s.Up p u) < auxPotential p s

class IsStrictlyHamiltonian where
  /-- The primary potential (energy), a real-valued function on the state space. -/
  energy (p : Params NN) (s : NN.State) : R
  /-- The auxiliary potential, mapping states to a well-founded set (e.g., ℕ) for tie-breaking. -/
  auxPotential (p : Params NN) (s : NN.State) : ℕ
  /-- Axiom 1: The energy is a Lyapunov function for the dynamics. -/
  energy_is_lyapunov (p : Params NN) (s : NN.State) (u : U) :
    energy p (s.Up p u) ≤ energy p s
  /-- Axiom 2: If an update changes the state and the energy stays constant, then
      the auxiliary potential strictly decreases (tie-breaking to ensure termination). -/
  aux_strictly_decreases_on_tie
      (p : Params NN) (s : NN.State) (u : U) :
      s.Up p u ≠ s →
      energy p (s.Up p u) = energy p s →
      auxPotential p (s.Up p u) < auxPotential p s

/--
The state of a `StrictlyHamiltonian` system can be mapped to a pair `(Energy, AuxPotential)`
which allows for a well-founded lexicographical ordering.
-/
def stateToLex [IsStrictlyHamiltonian NN] (p : Params NN) (s : NN.State) : R × ℕ :=
  (IsStrictlyHamiltonian.energy p s, IsStrictlyHamiltonian.auxPotential p s)

/--
The lexicographical order on `(Energy, AuxPotential)` is well-founded because the
state space is finite.

We avoid needing global well-foundedness of `<` on `R` by working on the finite
domain `NN.State`. On any finite type, any irreflexive relation is well-founded;
here we also supply transitivity (both required by `Finite.wellFounded_of_trans_of_irrefl`).
-/
instance wellFoundedRelation [Fintype NN.State] [IsStrictlyHamiltonian NN] (p : Params NN) :
    WellFounded (InvImage (Prod.Lex LT.lt LT.lt) (stateToLex NN p)) := by
  set r :=
      (InvImage (Prod.Lex LT.lt LT.lt) (stateToLex NN p))
    with hr
  let E := IsStrictlyHamiltonian.energy p
  let A := IsStrictlyHamiltonian.auxPotential p
  have instIrrefl : IsIrrefl NN.State r :=
    ⟨by
      intro s
      intro hs
      dsimp [r, InvImage] at hs
      have h := (Prod.lex_def).1 hs
      rcases h with hE | ⟨hEq, hA⟩
      · exact lt_irrefl _ hE
      · exact lt_irrefl _ hA⟩
  have instTrans : IsTrans NN.State r :=
    ⟨by
      intro a b c hab hbc
      have hab' :
          E a < E b ∨ (E a = E b ∧ A a < A b) := by
        have := (Prod.lex_def).1 (by simpa [r, InvImage] using hab)
        simpa [stateToLex, E, A]
      have hbc' :
          E b < E c ∨ (E b = E c ∧ A b < A c) := by
        have := (Prod.lex_def).1 (by simpa [r, InvImage] using hbc)
        simpa [stateToLex, E, A]
      have hResult :
          E a < E c ∨ (E a = E c ∧ A a < A c) := by
        rcases hab' with hEab | ⟨hEab, hAab⟩
        · rcases hbc' with hEbc | ⟨hEbc, hAbc⟩
          · exact Or.inl (lt_trans hEab hEbc)
          · have : E a < E c := by simpa [hEbc] using hEab
            exact Or.inl this
        · rcases hbc' with hEbc | ⟨hEbc, hAbc⟩
          · have : E a < E c := by simpa [hEab] using hEbc
            exact Or.inl this
          · have hEac : E a = E c := hEab.trans hEbc
            have hAac : A a < A c := lt_trans hAab hAbc
            exact Or.inr ⟨hEac, hAac⟩
      have : Prod.Lex LT.lt LT.lt (stateToLex NN p a) (stateToLex NN p c) := by
        refine (Prod.lex_def).2 ?_
        simpa [stateToLex, E, A] using hResult
      simpa [r, InvImage]⟩
  have : WellFounded r :=
    Finite.wellFounded_of_trans_of_irrefl (r:=r)
  simpa [hr]

variable {R U σ : Type*} [Field R] [LinearOrder R] [DecidableEq U]

/-- An update at index n is effective if the (n+1)-th state in the trajectory differs
    from the n-th state. Parameterized by the network, parameters, update sequence,
    and initial state so it can be used globally (the local symbol `S` is not available here). -/
def effective {NN : NeuralNetwork R U σ}
    (p : Params NN) (useq : ℕ → U) (s₀ : NN.State) (n : ℕ) : Prop :=
  s₀.seqStates p useq (n+1) ≠ s₀.seqStates p useq n

/-
We prove convergence by (1) by defining a strict well-founded measure (energy, aux),
(2) showing it strictly decreases on effective steps,
(3) showing effective indices inject into the finite state space,
(4) deducing finiteness of effective indices,
(5) extracting a maximal effective index (or 0 if none),
(6) showing the tail is constant hence stable by fairness.
-/
section
variable {R U σ : Type*} [Field R] [DecidableEq U]

--variable {R U σ : Type*} [Field R]
variable (NN : NeuralNetwork R U σ)
/-- Unfold one asynchronous step of the trajectory. -/
@[simp] lemma seqStates_succ (s₀ : NN.State) (p : Params NN)
    (useq : ℕ → U) (n : ℕ) :
    s₀.seqStates p useq (n+1) =
      (s₀.seqStates p useq n).Up p (useq n) := rfl

variable {R U σ : Type*} [Field R] [LinearOrder R] [DecidableEq U]
variable (NN : NeuralNetwork R U σ)
variable [IsStrictlyHamiltonian NN]

lemma lex_decreases_on_effective
    (p : Params NN) (useq : ℕ → U) (s₀ : NN.State) :
    ∀ n, effective (NN:=NN) p useq s₀ n →
      Prod.Lex (· < ·) (· < ·)
        (stateToLex NN p (s₀.seqStates p useq (n+1)))
        (stateToLex NN p (s₀.seqStates p useq n)) := by
  intro n heff
  set s := s₀.seqStates p useq n
  set u := useq n
  have hChange : s.Up p u ≠ s := by
    intro hEq
    apply heff
    simp [ seqStates_succ, s, u, hEq]
  -- We apply Lyapunov + tie-break
  have hE_le := IsStrictlyHamiltonian.energy_is_lyapunov p s u
  unfold stateToLex
  rcases lt_or_eq_of_le hE_le with hlt | heq
  · exact (Prod.lex_def).2 (Or.inl hlt)
  · have hA_lt :=
      IsStrictlyHamiltonian.aux_strictly_decreases_on_tie p s u hChange heq
    exact (Prod.lex_def).2 (Or.inr ⟨heq, hA_lt⟩)

--variable [Fintype NN.State] [IsStrictlyHamiltonian NN]

local notation "S" => NeuralNetwork.State.seqStates

/-- Relation induced by lex on states (strict). -/
private def rel (p : Params NN) : NN.State → NN.State → Prop :=
  InvImage (Prod.Lex (· < ·) (· < ·)) (stateToLex NN p)

/-- Either a strict step (if effective) or equality (if ineffective). -/
lemma step_rel_or_eq
    (p : Params NN) (useq : ℕ → U) (s₀ : NN.State) (n : ℕ) :
    rel (NN:=NN) p (s₀.seqStates p useq (n+1)) (s₀.seqStates p useq n) ∨
      s₀.seqStates p useq (n+1) = s₀.seqStates p useq n := by
  by_cases hEff : effective (NN:=NN) p useq s₀ n
  · -- effective ⇒ strict lex descent
    left
    dsimp [rel, InvImage]
    exact lex_decreases_on_effective (NN:=NN) p useq s₀ n hEff
  · -- ineffective ⇒ states coincide
    right
    -- `¬ effective` means successive states are equal.
    have : s₀.seqStates p useq (n + 1) = s₀.seqStates p useq n := by
      by_contra hNe
      have : effective (NN:=NN) p useq s₀ n := by
        simpa [effective] using hNe
      exact (hEff this).elim
    exact this

/-- Refl-transitive closure over a block of k steps going backwards:
`(m,k) ↦ S (m+k+1) →* S (m+1)`. -/
lemma segment_reflTrans
    (p : Params NN) (useq : ℕ → U) (s₀ : NN.State) :
    ∀ (m k : ℕ),
      Relation.ReflTransGen (rel (NN:=NN) p)
        (s₀.seqStates p useq (m+k+1)) (s₀.seqStates p useq (m+1)) := by
  intro m k
  induction k with
  | zero =>
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      have hstep := step_rel_or_eq (NN:=NN) p useq s₀ (m+k+1)
      rcases hstep with hrel | heq
      · exact Relation.ReflTransGen.head hrel ih
      · have h' :
          s₀.seqStates p useq (m + (k+1) + 1) = s₀.seqStates p useq (m + (k+1)) := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using heq
        have ih' :
          Relation.ReflTransGen (rel (NN:=NN) p)
            (s₀.seqStates p useq (m + (k+1))) (s₀.seqStates p useq (m+1)) := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ih
        aesop

--variable {R U σ : Type*}

lemma head_tail_trans
    {α} {r : α → α → Prop} {a b c : α}
    (hab : r a b) (hbc : Relation.ReflTransGen r b c) :
    Relation.TransGen r a c := by
  -- We build a TransGen chain starting with the initial edge r a b
  -- and extend it along the ReflTransGen from b to the target.
  have aux : ∀ {x}, Relation.ReflTransGen r b x → Relation.TransGen r a x := by
    intro x hx
    induction hx with
    | refl =>
        exact Relation.TransGen.single hab
    | tail hx' hstep ih =>
        exact Relation.TransGen.tail ih (hstep)
  exact aux hbc

/-- If `n₂` is effective and `n₁ < n₂` then there is a strict multi-step descent (TransGen)
from `S (n₂+1)` to `S (n₁+1)`. -/
lemma transgen_from_indices
    (p : Params NN) (useq : ℕ → U) (s₀ : NN.State)
    {n₁ n₂ : ℕ} (hEff₂ : effective (NN:=NN) p useq s₀ n₂) (hlt : n₁ < n₂) :
    Relation.TransGen (rel (NN:=NN) p)
      (s₀.seqStates p useq (n₂+1)) (s₀.seqStates p useq (n₁+1)) := by
  have hstep :
      rel (NN:=NN) p (s₀.seqStates p useq (n₂+1)) (s₀.seqStates p useq n₂) :=
    (step_rel_or_eq (NN:=NN) (p:=p) (useq:=useq) s₀ n₂).resolve_right (by
      intro hEq; exact hEff₂ (by simpa [effective] using hEq))
  have hChain :
      Relation.ReflTransGen (rel (NN:=NN) p)
        (s₀.seqStates p useq n₂) (s₀.seqStates p useq (n₁+1)) := by
    -- Decompose n₂ = n₁ + (n₂ - n₁ - 1) + 1
    have hpos : 1 ≤ n₂ - n₁ := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hlt)
    have hpred : (n₂ - n₁ - 1) + 1 = n₂ - n₁ := Nat.sub_add_cancel hpos
    have hAdd' : n₁ + (n₂ - n₁) = n₂ := Nat.add_sub_of_le (Nat.le_of_lt hlt)
    have hk : n₁ + (n₂ - n₁ - 1) + 1 = n₂ := by
      calc
        n₁ + (n₂ - n₁ - 1) + 1
            = n₁ + ((n₂ - n₁ - 1) + 1) := by simp [Nat.add_assoc]
        _   = n₁ + (n₂ - n₁) := by simp [hpred]
        _   = n₂ := hAdd'
    have hSeg :=
      segment_reflTrans (NN:=NN) (p:=p) (useq:=useq) s₀ n₁ (n₂ - n₁ - 1)
    simpa [hk, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hSeg
  exact head_tail_trans (hab:=hstep) (hbc:=hChain)

variable {R U σ : Type*}

/-- A TransGen descent induces a strict lex descent on the `stateToLex` images. -/
lemma transgen_lex_strict
    (p : Params NN) {x y : NN.State}
    (t : Relation.TransGen (rel (NN:=NN) p) x y) :
    Prod.Lex (· < ·) (· < ·) (stateToLex NN p x) (stateToLex NN p y) := by
  induction t with
  | single h =>
      dsimp [rel, InvImage] at h
      exact h
  | tail hxy t ih =>
      dsimp [rel, InvImage] at hxy
      exact Prod.Lex.trans ih t

variable {R U σ : Type*} [Field R] [LinearOrder R] [DecidableEq U]
variable (NN : NeuralNetwork R U σ)
variable [IsStrictlyHamiltonian NN]
/-- Effective indices inject via the strict lex descent. -/
lemma effective_injective_lex
    (p : Params NN) (useq : ℕ → U) (s₀ : NN.State)
    {n₁ n₂ : ℕ}
    (_ : effective (NN:=NN) p useq s₀ n₁)
    (h₂ : effective (NN:=NN) p useq s₀ n₂)
    (hlt : n₁ < n₂) :
    stateToLex NN p (s₀.seqStates p useq (n₂+1)) ≠
      stateToLex NN p (s₀.seqStates p useq (n₁+1)) := by
  have t := transgen_from_indices (NN:=NN) (p:=p) (useq:=useq) s₀ h₂ hlt
  have hlex := transgen_lex_strict (NN:=NN) (p:=p) t
  intro hEq
  -- We convert the lexicographic ordering to the disjunctive form to avoid dependent elimination
  have hlex_disj :
    (stateToLex NN p (s₀.seqStates p useq (n₂+1))).1 <
    (stateToLex NN p (s₀.seqStates p useq (n₁+1))).1 ∨
    ((stateToLex NN p (s₀.seqStates p useq (n₂+1))).1 =
     (stateToLex NN p (s₀.seqStates p useq (n₁+1))).1 ∧
     (stateToLex NN p (s₀.seqStates p useq (n₂+1))).2 <
     (stateToLex NN p (s₀.seqStates p useq (n₁+1))).2) := by
    exact (Prod.lex_def).1 hlex
  cases hlex_disj with
  | inl hE_lt =>
    have h_fst_eq : (stateToLex NN p (s₀.seqStates p useq (n₂+1))).1 =
                    (stateToLex NN p (s₀.seqStates p useq (n₁+1))).1 :=
      congrArg Prod.fst hEq
    dsimp [stateToLex] at h_fst_eq
    exact (ne_of_lt hE_lt) h_fst_eq
  | inr h_tie_aux =>
    obtain ⟨_, hA_lt⟩ := h_tie_aux
    have h_snd_eq : (stateToLex NN p (s₀.seqStates p useq (n₂+1))).2 =
                    (stateToLex NN p (s₀.seqStates p useq (n₁+1))).2 :=
      congrArg Prod.snd hEq
    dsimp [stateToLex] at h_snd_eq
    exact (ne_of_lt hA_lt) h_snd_eq

/-- Mapping effective indices to states is injective. -/
lemma effective_injective_to_state
    (p : Params NN) (useq : ℕ → U) (s₀ : NN.State) :
    ∀ {n₁ n₂}, effective (NN:=NN) p useq s₀ n₁ →
      effective (NN:=NN) p useq s₀ n₂ →
      (s₀.seqStates p useq (n₁+1)) = (s₀.seqStates p useq (n₂+1)) → n₁ = n₂ := by
  intro n₁ n₂ h₁ h₂ hEq
  by_cases h : n₁ = n₂
  · exact h
  · cases lt_or_gt_of_ne h with
    | inl hlt =>
        have hlex :=
          effective_injective_lex (NN:=NN) (p:=p) (useq:=useq) s₀ h₁ h₂ hlt
        have := congrArg (stateToLex NN p) hEq
        exact False.elim (hlex (id (Eq.symm this)))
    | inr hgt =>
        have hlt : n₂ < n₁ := hgt
        have hlex :=
          effective_injective_lex (NN:=NN) (p:=p) (useq:=useq) s₀ h₂ h₁ hlt
        have := congrArg (stateToLex NN p) hEq.symm
        exact False.elim (hlex (id (Eq.symm this)))

/-- The set of effective indices is finite. -/
lemma effective_set_finite [Fintype NN.State]
    (p : Params NN) (useq : ℕ → U) (s₀ : NN.State) :
    ( {n | effective (NN:=NN) p useq s₀ n} : Set ℕ ).Finite := by
  set Seff : Set ℕ := {n | effective (NN:=NN) p useq s₀ n} with hSeff
  -- Injectivity of the successor-state map on effective indices
  have hinj :
      ∀ {n₁ n₂},
        n₁ ∈ Seff →
        n₂ ∈ Seff →
        s₀.seqStates p useq (n₁+1) = s₀.seqStates p useq (n₂+1) →
        n₁ = n₂ := by
    intro n₁ n₂ hn₁ hn₂ hEq
    simp [Seff] at hn₁ hn₂
    exact effective_injective_to_state (NN:=NN) (p:=p) (useq:=useq) s₀ hn₁ hn₂ hEq
  -- Function from the subtype of effective indices to states
  let f : {n // n ∈ Seff} → NN.State :=
    fun n => s₀.seqStates p useq (n.val + 1)
  have f_inj : Function.Injective f := by
    intro a b hEq
    rcases a with ⟨n₁, hn₁⟩
    rcases b with ⟨n₂, hn₂⟩
    change _ = _ at hEq
    have : n₁ = n₂ := hinj (by simpa) (by simpa) hEq
    subst this
    rfl
  -- Build a Fintype instance on the subtype using injectivity into finite `NN.State`
  haveI : Fintype {n // n ∈ Seff} := Fintype.ofInjective f f_inj
  have hImg :
      Seff = (fun (x : {n // n ∈ Seff}) => (x : ℕ)) '' (Set.univ : Set {n // n ∈ Seff}) := by
    ext n; constructor
    · intro hn; exact ⟨⟨n, hn⟩, trivial, rfl⟩
    · intro hn; rcases hn with ⟨⟨m, hm⟩, -, rfl⟩; exact hm
  have : (Set.univ : Set {n // n ∈ Seff}).Finite := Set.finite_univ
  have : Seff.Finite := by
    simp_rw [hImg]; simp only [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq]
    exact Set.toFinite Seff
  simpa [hSeff] using this

variable {R U σ : Type*} [Field R] [DecidableEq U]
variable (NN : NeuralNetwork R U σ)

/-- Tail constancy if there are no effective indices beyond `N`. -/
lemma tail_constant_of_no_effective_after
    (p : Params NN) (useq : ℕ → U) (s₀ : NN.State)
    {N : ℕ}
    (h : ∀ n ≥ N, ¬ effective (NN:=NN) p useq s₀ n) :
    ∀ m ≥ N, s₀.seqStates p useq m = s₀.seqStates p useq N := by
  intro m hm
  induction' m with m ih
  · exact (le_antisymm hm (Nat.zero_le _)) ▸ rfl
  · cases lt_or_eq_of_le hm with
    | inl hlt =>
        have hge : N ≤ m :=
          le_trans (Nat.le_of_lt_succ hlt) (Nat.le_of_lt_succ (Nat.lt_succ_self _))
        specialize ih hge
        have hIneff : ¬ effective (NN:=NN) p useq s₀ m :=
          h _ (le_trans (Nat.le_of_lt_succ hlt) (Nat.le_of_lt_succ (Nat.lt_succ_self _)))
        dsimp [effective] at hIneff
        have : s₀.seqStates p useq (m+1) = s₀.seqStates p useq m := by
          by_contra hneq
          exact hIneff hneq
        simpa [this, ih]
    | inr heq => subst heq; rfl

/-- If the tail from `N` onward has no effective indices then `S N` is stable. -/
theorem stable_of_no_effective_after
    (p : Params NN) (useq : ℕ → U) (s₀ : NN.State)
    {N : ℕ}
    (h : ∀ n ≥ N, ¬ effective (NN:=NN) p useq s₀ n)
    (hfair : fair useq) :
    (s₀.seqStates p useq N).isStable p := by
  intro u
  have hfair' : ∀ u N, ∃ n ≥ N, useq n = u := hfair
  obtain ⟨n, hn_ge, hn_site⟩ := hfair' u N
  have tail_const :=
    tail_constant_of_no_effective_after (NN:=NN) (p:=p) (useq:=useq) s₀ (N:=N) h
  have hSn : s₀.seqStates p useq n = s₀.seqStates p useq N := tail_const _ hn_ge
  have hSn1 : s₀.seqStates p useq (n+1) = s₀.seqStates p useq N :=
    tail_const _ (le_trans hn_ge (Nat.le_succ _))
  have hIneff : ¬ effective (NN:=NN) p useq s₀ n :=
    h _ (le_trans hn_ge (Nat.le_refl n))
  dsimp [effective] at hIneff
  have hUpdEq : s₀.seqStates p useq (n+1) = s₀.seqStates p useq n := by simpa using hIneff
  have : (s₀.seqStates p useq N).Up p u = s₀.seqStates p useq N := by
    have h1 := hSn
    subst hn_site
    simp_all only [ge_iff_le, le_refl, seqStates_succ, not_true_eq_false, not_false_eq_true]
  simpa [NeuralNetwork.State.isStable] using congrArg (fun s => s.act u) this

end
variable {R U σ : Type*} [Field R] [LinearOrder R] [DecidableEq U]
variable (NN : NeuralNetwork R U σ)

/--
# Theorem: Convergence of Hamiltonian Dynamics

Any `NeuralNetwork` that is an instance of `IsStrictlyHamiltonian` is guaranteed to
converge to a stable fixed point under any fair asynchronous update sequence.
-/
theorem convergence_of_hamiltonian [Fintype NN.State] [IsStrictlyHamiltonian NN]
    (s₀ : NN.State) (p : Params NN) (useq : ℕ → U) (hfair : fair useq) :
    ∃ N, (s₀.seqStates p useq N).isStable p := by
  -- Finite set of effective indices
  let Eff : Set ℕ := { n | effective (NN:=NN) p useq s₀ n }
  have hEffFinite : Eff.Finite := effective_set_finite (NN:=NN) (p:=p) (useq:=useq) s₀
  by_cases hEmpty : Eff = ∅
  · -- No effective updates: sequence constant → stable at 0
    have hNo : ∀ k ≥ 0, ¬ effective (NN:=NN) p useq s₀ k := by
      intro k _
      have hk : k ∉ Eff := by simp [hEmpty]
      -- translate membership
      simpa [Eff] using hk
    -- tail is constant from 0
    have hZero :
      ∀ n, s₀.seqStates p useq n = s₀.seqStates p useq 0 := by
        intro n
        exact tail_constant_of_no_effective_after (NN:=NN) (p:=p) (useq:=useq) s₀
          (N:=0) hNo n (Nat.zero_le _)
    refine ⟨0, ?_⟩
    -- Stability at time 0
    exact stable_of_no_effective_after (NN:=NN) (p:=p) (useq:=useq) s₀ (N:=0) hNo hfair
  · -- Nonempty: pick maximal effective index via finset max'
    have hNonempty : Eff.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    -- obtain a nonempty finset of effective indices
    have hFinsetNE : (hEffFinite.toFinset).Nonempty := by
      rcases hNonempty with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      simpa [Set.Finite.mem_toFinset] using hx
    -- choose maximum effective index
    let N := (hEffFinite.toFinset).max' hFinsetNE
    have hNmem : N ∈ Eff := by
      have : N ∈ hEffFinite.toFinset := Finset.max'_mem _ _
      simpa [Set.Finite.mem_toFinset] using this
    -- maximality property: any effective index ≤ N
    have hMax : ∀ n ∈ Eff, n ≤ N := by
      intro n hn
      have : n ∈ hEffFinite.toFinset := by simpa [Set.Finite.mem_toFinset] using hn
      exact Finset.le_max' _ _ this
    -- No effective beyond N
    have hTail :
      ∀ n ≥ N+1, ¬ effective (NN:=NN) p useq s₀ n := by
        intro n hn
        by_contra hEff
        have hnEff : n ∈ Eff := by simpa [Eff, effective] using hEff
        have hle : n ≤ N := hMax _ hnEff
        have hNlt : N < n := by
          -- N+1 ≤ n ↔ N < n
          simpa [Nat.succ_le_iff] using hn
        have : N < N := Nat.lt_of_lt_of_le hNlt hle
        exact (Nat.lt_irrefl _ this)
    refine ⟨N+1, ?_⟩
    -- Stable at time N+1 (index shift)
    have hTail' :
      ∀ k ≥ N+1, ¬ effective (NN:=NN) p useq s₀ k := hTail
    exact stable_of_no_effective_after (NN:=NN) (p:=p) (useq:=useq) s₀
        (N:=N+1) hTail' hfair
/-
### Instantiating the Framework for `TwoStateNeuralNetwork`

Now, we need to prove that our concrete models satisfy this general contract. -/

open TwoState
/--
An auxiliary potential for `TwoStateNeuralNetwork`s, defined as the negated sum
of the embedded `m` values. For `SymmetricBinary`, this is the negative of the
total magnetization, which acts as a tie-breaker.

We realize this as the (finite) rank of the current state's magnetization among
all state magnetizations, counted from the top (larger magnetization ⇒ smaller rank),
so that increasing magnetization strictly decreases this ℕ-valued potential.
-/
noncomputable def twoStateAuxPotential
    (NN : NeuralNetwork ℝ U σ) [TwoStateNeuralNetwork NN]
    [Fintype U] [DecidableEq U] [Fintype NN.State]
    (s : NN.State) : ℕ :=
  -- Magnetization of a state
  let mag : NN.State → ℝ := fun t => ∑ u : U, NN.m (t.act u)
  -- Finite set of all magnetizations
  let mags : Finset ℝ := (Finset.univ.image fun t : NN.State => mag t)
  let mcur := mag s
  -- Rank from the top: number of strictly larger magnetizations
  (mags.filter (fun x => mcur < x)).card

/--
Flip–direction under an energy tie for exclusive two–state networks:

If an asynchronous update at site `u` changes the state and the energy (from `spec.E`)
stays constant, then necessarily the activation at `u` flips from `σ_neg` to `σ_pos`
(not the other way).  This is the key lemma needed to justify the
`h_s'_pos` step in `aux_strictly_decreases_on_tie`, avoiding ad‑hoc reasoning.

Intuition:
  If we started at `σ_pos` and flipped to `σ_neg` with a change, then
  (threshold condition ⇒ local field < 0) and the flip–energy relation
  gives a strict energy decrease, contradicting the assumed tie.
-/
lemma twoState_flip_neg_to_pos_of_energy_tie
    {U σ} (NN : NeuralNetwork ℝ U σ)
    [Fintype U] [DecidableEq U] [Fintype NN.State]
    [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
    (spec : EnergySpec' (NN:=NN))
    (p : Params NN) (s : NN.State) (u : U)
    (h_change : s.Up p u ≠ s)
    (h_energy_tie : spec.E p (s.Up p u) = spec.E p s) :
    s.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN) ∧
      (s.Up p u).act u = TwoStateNeuralNetwork.σ_pos (NN:=NN) := by
  set s' := s.Up p u
  -- Change implies the activation at u flipped
  have h_flip_act : s.act u ≠ s'.act u := by
    have hOnly : (∀ v ≠ u, s'.act v = s.act v) := by
      intro v hv; simp [s', NeuralNetwork.State.Up, hv]
    intro hEq; apply h_change
    ext v; by_cases hv : v = u
    · subst hv; simp_all only [ne_eq, s']
    · simp [hOnly v hv]
  -- Exclusivity: only two possibilities
  have h_excl_s  := (TwoStateExclusive.pact_iff (NN:=NN) (a:=s.act u)).1 (s.hp u)
  have h_excl_s' := (TwoStateExclusive.pact_iff (NN:=NN) (a:=s'.act u)).1 (s'.hp u)
  have h_orient :
      (s.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN) ∧ s'.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN)) ∨
      (s.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN) ∧ s'.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN)) := by
    rcases h_excl_s with hpos | hneg
    · rcases h_excl_s' with hpos' | hneg'
      · cases h_flip_act (by simp [hpos, hpos'])
      · exact Or.inl ⟨hpos, hneg'⟩
    · rcases h_excl_s' with hpos' | hneg'
      · exact Or.inr ⟨hneg, hpos'⟩
      · cases h_flip_act (by simp [hneg, hneg'])
  -- Exclude pos→neg orientation
  have h_not_pos_neg :
      ¬ (s.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN) ∧ s'.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN)) := by
    intro hpair
    rcases hpair with ⟨hpos, hneg⟩
    -- Local field symbols
    set net := s.net p u
    set θ   := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
    set L : ℝ := net - θ
    -- Show net < θ (else the update would keep σ_pos)
    have h_net_lt : net < θ := by
      by_contra hNot
      have hθle : θ ≤ net := le_of_not_gt hNot
      -- Classification of Up
      have h_class := TwoState.Up_eq_updPos_or_updNeg (NN:=NN) p s u
      -- If θ ≤ net then Up = updPos; activation at u would be σ_pos, contradiction
      have : s' = updPos (NN:=NN) s u := by
        -- rewrite the classification; the lemma produces a definitional equality,
        -- so we normalize the auxiliary `net`/`θ` names by rewriting.
        simpa [s', net, θ, hθle] using h_class
      have : s'.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN) := by
        -- activation of updPos at u
        simp [this, TwoState.updPos_act_at_u]
      exact (TwoStateNeuralNetwork.h_pos_ne_neg (NN:=NN)) (by simp_all only [ne_eq,
        ↓reduceIte, updPos_act_at_u, not_true_eq_false, s', net, θ])
    have hLneg : L < 0 := sub_lt_zero.mpr h_net_lt
    -- Flip–energy relation
    let fid : ℝ →+* ℝ := RingHom.id _
    have h_flip_energy :
      spec.E p (updPos (NN:=NN) s u) - spec.E p (updNeg (NN:=NN) s u)
        = - (TwoState.scale (NN:=NN) (f:=fid)) * L := by
      have h0 := spec.flip_energy_relation fid p s u
      simp [spec.localField_spec] at h0
      simpa using h0
    -- κ > 0
    set κ := TwoState.scale (NN:=NN) (f:=fid)
    have hκ_pos : 0 < κ := by
      have hmo := TwoStateNeuralNetwork.m_order (NN:=NN)
      have : 0 < NN.m (TwoStateNeuralNetwork.σ_pos (NN:=NN)) -
                 NN.m (TwoStateNeuralNetwork.σ_neg (NN:=NN)) := sub_pos.mpr hmo
      simpa [κ, TwoState.scale, fid, RingHom.id_apply]
    -- Energy difference positive
    have hΔpos : 0 < -κ * L := by
      have : 0 < κ * (-L) := mul_pos hκ_pos (neg_pos.mpr hLneg)
      simpa [mul_comm, mul_left_comm, mul_assoc, neg_mul, neg_mul_neg] using this
    have hStrict :
        spec.E p (updNeg (NN:=NN) s u) < spec.E p (updPos (NN:=NN) s u) := by
      -- From 0 < (E updPos - E updNeg) derive E updNeg < E updPos
      have hpos :
          0 < spec.E p (updPos (NN:=NN) s u) - spec.E p (updNeg (NN:=NN) s u) := by
        simpa [h_flip_energy, sub_eq_add_neg] using hΔpos
      exact (sub_pos).1 hpos
    -- Identify s, s'
    have hs_eq_updPos : s = updPos (NN:=NN) s u := by
      ext v; by_cases hv : v = u
      · subst hv; simp [TwoState.updPos_act_at_u, hpos]
      · simp [TwoState.updPos_act_noteq (NN:=NN) s u v hv]
    have hs'_eq_updNeg : s' = updNeg (NN:=NN) s u := by
      -- Using h_net_lt, classification chooses updNeg
      have h_not_le : ¬ θ ≤ net := not_le_of_gt h_net_lt
      have h_class := TwoState.Up_eq_updPos_or_updNeg (NN:=NN) p s u
      have hUp : s' = updNeg (NN:=NN) s u := by
        simpa [s', net, θ, h_not_le] using h_class
      exact hUp
    -- Energy strict decrease contradicting tie
    -- Use symmetric rewrites so that simp reduces (updPos s u) and (updNeg s u) instead of expanding s.
    have : spec.E p s' < spec.E p s := by
      simpa [hs'_eq_updNeg.symm, hs_eq_updPos.symm] using hStrict
    exact (lt_of_lt_of_eq this h_energy_tie.symm).false
  -- Only neg→pos remains
  rcases h_orient with hposneg | hnegpos
  · exact False.elim (h_not_pos_neg hposneg)
  · exact hnegpos

variable {R U σ : Type*} [Field R] [LinearOrder R] [DecidableEq U]
variable (NN : NeuralNetwork R U σ)

/--
This instance proves that any `TwoStateNeuralNetwork` with an `EnergySpec` is
strictly Hamiltonian. This is a powerful theorem that makes our abstract
convergence proof applicable to all our concrete models.
-/
noncomputable instance IsStrictlyHamiltonian_of_TwoState_EnergySpec
    {U σ} (NN : NeuralNetwork ℝ U σ)
    [DecidableEq U] [Fintype U]
    [Fintype NN.State] [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
    (spec : EnergySpec' (NN:=NN)) :
    IsStrictlyHamiltonian NN where
  energy := spec.E
  auxPotential := fun _ s => twoStateAuxPotential NN s
  energy_is_lyapunov p s u := by
    have hcur := (TwoStateExclusive.pact_iff (NN:=NN) (a:=s.act u)).1 (s.hp u)
    exact TwoState.EnergySpec'.energy_is_lyapunov_at_site'' (NN:=NN)
      (spec:=spec) p s u hcur
  aux_strictly_decreases_on_tie := by
    intro p s u h_change h_energy_tie
    set s' := s.Up p u
    obtain ⟨h_s_neg, h_s'_pos⟩ :=
      twoState_flip_neg_to_pos_of_energy_tie (NN:=NN) (spec:=spec) p s u h_change h_energy_tie
    let mag : NN.State → ℝ := fun t => ∑ v : U, NN.m (t.act v)
    have h_split_s :
        mag s = NN.m (s.act u) +
          ∑ v ∈ (Finset.univ.erase u), NN.m (s.act v) := by
      unfold mag
      simp_all only [ne_eq, Finset.mem_univ, Finset.sum_erase_eq_sub, add_sub_cancel, s']
    have h_split_s' :
        mag s' = NN.m (s'.act u) +
          ∑ v ∈ (Finset.univ.erase u), NN.m (s.act v) := by
      unfold mag
      have hActs : ∀ v, v ≠ u → s'.act v = s.act v := by
        intro v hv; simp [s', NeuralNetwork.State.Up, hv]
      have hOff :
          (∑ v ∈ (Finset.univ.erase u), NN.m (s'.act v))
            = ∑ v ∈ (Finset.univ.erase u), NN.m (s.act v) := by
        refine Finset.sum_congr rfl ?_
        intro v hv
        rcases Finset.mem_erase.mp hv with ⟨hv_ne, _⟩
        simp [hActs _ hv_ne]
      have h_split_raw :
          (∑ v : U, NN.m (s'.act v)) =
            NN.m (s'.act u) +
              ∑ v ∈ (Finset.univ.erase u), NN.m (s'.act v) := by
        rw [Matrix.sum_split_at (R:=ℝ) (ι:=U) (f:=fun v => NN.m (s'.act v)) u]
      simp [h_split_raw, hOff]
    -- Strict magnetization increase
    have h_mag_lt :
        mag s < mag s' := by
      have h_m_lt : NN.m (s.act u) < NN.m (s'.act u) := by
          -- Rewrite constants σ_neg/σ_pos to the actual activations
          have hmo := TwoStateNeuralNetwork.m_order (NN:=NN)
          simpa [←h_s_neg, ←h_s'_pos] using hmo
      have hL := h_split_s
      have hR := h_split_s'
      set A := ∑ v ∈ (Finset.univ.erase u), NN.m (s.act v)
      have : (NN.m (s.act u) + A) < (NN.m (s'.act u) + A) :=
        add_lt_add_right h_m_lt _
      simp at this
      simpa [hL, hR]
    -- Rank argument
    let mags : Finset ℝ := (Finset.univ.image fun t : NN.State => mag t)
    set m_old := mag s
    set m_new := mag s'
    have hm_old_mem : m_old ∈ mags := by
      refine Finset.mem_image.mpr ?_; exact ⟨s, Finset.mem_univ _, rfl⟩
    have hm_new_mem : m_new ∈ mags := by
      refine Finset.mem_image.mpr ?_; exact ⟨s', Finset.mem_univ _, rfl⟩
    set A_old := mags.filter (fun x => m_old < x)
    set A_new := mags.filter (fun x => m_new < x)
    have h_subset : A_new ⊆ A_old := by
      intro x hx
      simp [A_new] at hx
      rcases hx with ⟨hx_mem, hx_gt_new⟩
      have hx_gt_old : m_old < x := lt_trans h_mag_lt hx_gt_new
      simp [A_old, hx_mem, hx_gt_old]
    have h_not_in_new : m_new ∉ A_new := by
      simp [A_new]
    have h_in_old : m_new ∈ A_old := by
      have : m_old < m_new := h_mag_lt
      simp [A_old, hm_new_mem, this]
    have h_ss : A_new ⊂ A_old := ⟨h_subset, by
      intro hAO
      have : m_new ∈ A_new := hAO h_in_old
      exact h_not_in_new this⟩
    have h_card : A_new.card < A_old.card := Finset.card_lt_card h_ss
    unfold twoStateAuxPotential
    simp [mags, m_old, m_new, A_old, A_new, s', mag, h_card]
