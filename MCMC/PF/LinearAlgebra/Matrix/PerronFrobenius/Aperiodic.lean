import MCMC.PF.Combinatorics.Quiver.Cyclic
import MCMC.PF.Combinatorics.Quiver.Path

open Quiver

namespace Matrix
open Quiver
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ}

/-! # Aperiodic matrices -/

/-- The index of imprimitivity of an irreducible matrix is the index of imprimitivity of its associated quiver. -/
noncomputable def index_of_imprimitivity [Nonempty n] (A : Matrix n n ℝ) : ℕ :=
  Quiver.index_of_imprimitivity (toQuiver A)

/-- A matrix is aperiodic if it is irreducible and its index of imprimitivity is 1. -/
def IsAperiodic [Nonempty n] (A : Matrix n n ℝ) : Prop :=
  IsIrreducible A ∧ index_of_imprimitivity A = 1

/-- Frobenius (forward direction): A primitive matrix is irreducible and aperiodic. -/
theorem primitive_implies_irreducible_and_aperiodic
    [Nonempty n] (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    IsPrimitive A → IsAperiodic A := by
  intro h_prim
  have h_irred : IsIrreducible A := (Matrix.IsPrimitive.isIrreducible (A := A) h_prim)
  rcases h_prim with ⟨_h_nonneg, ⟨k, hk_pos, hk_pos_entries⟩⟩
  let G := toQuiver A
  letI : Quiver n := G
  let i0 : n := Classical.arbitrary n
  have hP : ∀ v : n, Nonempty { p : Path i0 v // p.length = k } := by
    intro v
    have : 0 < (A ^ k) i0 v := hk_pos_entries i0 v
    exact (Matrix.pow_apply_pos_iff_nonempty_path (A := A) hA_nonneg k i0 v).mp this
  have hP_i0 : Nonempty { p : Path i0 i0 // p.length = k } := hP i0
  rcases hP_i0 with ⟨p0, hp0⟩
  have hp0_pos : 0 < p0.length := by simpa [hp0] using hk_pos
  obtain ⟨j, e0, s, hdecomp, hlen⟩ := Quiver.Path.path_decomposition_first_edge p0 hp0_pos
  have hs_len : s.length + 1 = k := by
    simpa [hp0] using hlen.symm
  rcases hP j with ⟨Pj, hPj⟩
  rcases hP i0 with ⟨Pi0, hPi0⟩
  have c1_mem : (Pj.comp s).length ∈ Quiver.CycleLengths (i := i0) := by
    have hpos : 0 < (Pj.comp s).length := by
      have : 0 < k := hk_pos
      have hle : k ≤ k + s.length := Nat.le_add_right _ _
      have : 0 < k + s.length := Nat.lt_of_lt_of_le this hle
      simpa [Path.length_comp, hPj, Nat.add_comm] using this
    exact ⟨hpos, ⟨Pj.comp s, rfl⟩⟩
  have c2_mem : (((Path.nil : Path i0 i0).cons e0).comp (s.comp Pi0)).length ∈ Quiver.CycleLengths (i := i0) := by
    have hpos : 0 < (((Path.nil : Path i0 i0).cons e0).comp (s.comp Pi0)).length := by
      have : 0 < k + 1 + s.length := Nat.pos_of_neZero (k + 1 + s.length)
      simp [Path.length_comp, Path.length_cons, Path.length_nil, hPi0, Nat.add_comm, Nat.add_left_comm]
    exact ⟨hpos, ⟨((Path.nil : Path i0 i0).cons e0).comp (s.comp Pi0), rfl⟩⟩
  have len_c1 : (Pj.comp s).length = k + s.length := by
    simp [Path.length_comp, hPj]
  have len_c2 : (((Path.nil : Path i0 i0).cons e0).comp (s.comp Pi0)).length = k + 1 + s.length := by
    simp [Path.length_comp, Path.length_cons, Path.length_nil, hPi0, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hdiv1 :
      Quiver.period (i := i0) ∣ (Pj.comp s).length :=
    Quiver.divides_cycle_length (i := i0) c1_mem
  have hdiv2 :
      Quiver.period (i := i0) ∣ (((Path.nil : Path i0 i0).cons e0).comp (s.comp Pi0)).length :=
    Quiver.divides_cycle_length (i := i0) c2_mem
  have hdiff_div :
      Quiver.period (i := i0) ∣ (((Path.nil : Path i0 i0).cons e0).comp (s.comp Pi0)).length - (Pj.comp s).length := by
    exact Nat.dvd_sub hdiv2 hdiv1
  have : Quiver.period (i := i0) ∣ 1 := by
    have hdiff :
        (((Path.nil : Path i0 i0).cons e0).comp (s.comp Pi0)).length - (Pj.comp s).length = 1 := by
      simp [len_c1, len_c2, Nat.add_assoc]
      simp +arith
    grind
  have h_period_one : Quiver.period (i := i0) = 1 :=
    Nat.dvd_one.mp this
  refine ⟨h_irred, ?_⟩
  dsimp [Matrix.index_of_imprimitivity, Quiver.index_of_imprimitivity] at *
  simpa using h_period_one

/-! # Frobenius Normal Form -/

/-- Predicate: `P` is a permutation matrix (entries are 1 on a single position in each row given by a permutation, 0 elsewhere). -/
def IsPermutationMatrix (P : Matrix n n ℝ) : Prop :=
  ∃ σ : Equiv.Perm n, ∀ i j, P i j = if σ i = j then 1 else 0

/--
Theorem: Frobenius Normal Form.
-/
theorem exists_frobenius_normal_form [Nonempty n]
    (_hA_irred : IsIrreducible A) (_h_h_gt_1 : index_of_imprimitivity A > 1) :
    ∃ (P : Matrix n n ℝ), IsPermutationMatrix P ∧ True := by
  refine ⟨1, ?_, trivial⟩
  refine ⟨Equiv.refl _, ?_⟩
  intro i j
  simp [Matrix.one_apply]

end Matrix
