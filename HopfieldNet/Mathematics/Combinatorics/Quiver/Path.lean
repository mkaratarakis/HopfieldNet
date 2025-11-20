import Mathlib.Combinatorics.Quiver.Path
import HopfieldNet.Mathematics.Data.List
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

open List

/-!
# Quiver.Path

This module provides definitions, theorems, and lemmas for manipulating and
reasoning about paths in a `Quiver` (directed graph). The key concepts and results include:

## 1. Weights on Paths
  - **Definitions:** `weight`, `weightFromVertices` assign values in a monoid/semiring to edges
  and extend multiplicatively to paths.
  - **Lemmas:** `weight_comp`, `weightFromVertices_comp` (multiplicativity under composition);
    `weight_pos`, `weightFromVertices_pos`, `weightFromVertices_nonneg` (positivity/non-negativity results).

## 2. Path Decomposition and Splitting
  - **Theorems/Lemmas:**
    - `path_decomposition_first_edge`, `path_decomposition_last_edge`: decompose a path at the first or last edge.
    - `exists_decomp_at_length`: split a path so the first component has a specified length.
    - `exists_decomp_of_mem_vertices`, `exists_decomp_of_mem_vertices_prop`: split at an arbitrary visited vertex, with a proposition version.
    - `split_at_vertex`: decompose a path precisely at the position of a chosen vertex.

## 3. Boundary and Crossing Edges
  - **Theorems:**
    - `exists_boundary_edge`, `exists_crossing_edge`: existence of boundary/crossing arrows for paths entering a set.

## 4. Vertices of a Path
  - **Definitions:** `«end»`, `activeVertices`, `vertices`, `activeFinset`.
  - **Lemmas:**
    - `vertices_length`, `vertices_head?`, `vertices_nonempty`, `vertices_comp`, `start_mem_vertices`.
    - Extraction lemmas for head/last and vertex membership.

## 5. Path Properties and Simplicity
  - **Definitions:**
    - `isStrictlySimple`: predicate for strictly simple (no repeated vertices except possibly endpoints) paths.
  - **Theorems/Lemmas:**
    - `isStrictlySimple_of_shortest`: shortest path between two vertices is strictly simple.
    - Related characterizations and implications for path minimality and structure.

## 6. Induced Subquivers and Embeddings
  - **Definitions:** `Quiver.inducedQuiver`, `Subquiver.embedding`.
  - **Lemma:** `mapPath_embedding_vertices_in_set` (embedded paths remain in the subset).

## 7. Prefunctor Interaction
  - **Lemma:** `Prefunctor.end_map` (compatibility of path endpoint with functorial mapping).

## 8. Path Replication
  - **Definitions:** `replicate`.
  - **Lemma:** `length_replicate` (length scales with replication).
-/

namespace Quiver.Path

variable {V : Type*} [Quiver V] {R : Type*}

section Weight

variable [Monoid R]

@[simp]
def weight (w : ∀ {i j : V}, (i ⟶ j) → R) : ∀ {i j : V}, Path i j → R
  | _, _, Path.nil => 1
  | _, _, Path.cons p e => weight w p * w e

def weightFromVertices (w : V → V → R) : ∀ {i j : V}, Path i j → R :=
  weight (fun {i j} (_ : i ⟶ j) => w i j)

@[simp]
lemma weight_comp (w : ∀ {i j : V}, (i ⟶ j) → R) {a b c : V} (p : Path a b) (q : Path b c) :
    weight w (p.comp q) = weight w p * weight w q := by
  induction q with | nil => simp only [comp_nil, weight, mul_one] | cons q' e ih => simp only [comp_cons,
    weight, ih, mul_assoc]

@[simp]
lemma weightFromVertices_comp (w : V → V → R) {a b c : V} (p : Path a b) (q : Path b c) :
    weightFromVertices w (p.comp q) = weightFromVertices w p * weightFromVertices w q := by
  simp only [weightFromVertices, weight_comp]

end Weight

section PositiveWeight

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R]

lemma weight_pos {w : ∀ {i j : V}, (i ⟶ j) → R}
    (hw : ∀ {i j : V} (e : i ⟶ j), 0 < w e) {i j : V} (p : Path i j) :
    0 < weight w p := by
  induction p with
  | nil => simp only [weight, zero_lt_one];
  | cons p e ih => simp only [weight, mul_pos ih (hw e)]

end PositiveWeight

section RealWeight

lemma weightFromVertices_pos {w : V → V → ℝ}
    (hw : ∀ i j : V, 0 < w i j) {i j : V} (p : Path i j) :
    0 < weightFromVertices w p := by
  apply weight_pos; intro i j _; exact hw i j

lemma weightFromVertices_nonneg {w : V → V → ℝ}
    (hw : ∀ i j : V, 0 ≤ w i j) {i j : V} (p : Path i j) :
    0 ≤ weightFromVertices w p := by
  induction p using Path.rec with
  | nil => simp only [weightFromVertices, weight, zero_le_one]
  | cons p' e ih => simp only [weightFromVertices, weight]; exact mul_nonneg ih (hw _ _)

end RealWeight

section PathDecomposition

variable {V : Type*} [Quiver V]

/-- Every non-empty path can be decomposed as an initial path plus a final edge. -/
lemma path_decomposition_last_edge {a b : V} (p : Path a b) (h : p.length > 0) :
    ∃ (c : V) (p' : Path a c) (e : c ⟶ b), p = p'.cons e := by
  cases p with | nil => simp at h | cons p' e => exact ⟨_, p', e, rfl⟩

/-- Every non-empty path can be decomposed as a first edge plus a remaining path. -/
lemma path_decomposition_first_edge {a b : V} (p : Path a b) (h : p.length > 0) :
    ∃ (c : V) (e : a ⟶ c) (p' : Path c b), p = e.toPath.comp p' ∧ p.length = p'.length + 1 := by
  have h_len : p.length = (p.length - 1) + 1 := by omega
  obtain ⟨c, e, p', hp', rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p h_len
  use c, e, p'; exact ⟨rfl, by omega⟩

end PathDecomposition

section BoundaryEdges

variable {V : Type*} [Quiver V]

@[simp]
lemma cons_eq_comp_toPath {a b c : V} (p : Path a b) (e : b ⟶ c) :
    p.cons e = p.comp e.toPath := by
  rfl

/-- A path from a vertex not in `S` to a vertex in `S` must cross the boundary. -/
theorem exists_boundary_edge {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b ∈ S) :
    ∃ (u v : V) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      u ∉ S ∧ v ∈ S ∧ p = p₁.comp (e.toPath.comp p₂) := by
  induction' h_len : p.length with n ih generalizing a b S ha_not_in_S hb_in_S
  · -- Base case n = 0: Path must be nil, so a = b. Contradiction.
    have hab : a = b := eq_of_length_zero p h_len
    subst hab
    exact (ha_not_in_S hb_in_S).elim
  · -- Inductive step: Assume true for all paths of length < n+1.
    have h_pos : 0 < p.length := by rw[h_len]; simp only [lt_add_iff_pos_left, add_pos_iff,
      Nat.lt_one_iff, pos_of_gt, or_true]
    obtain ⟨c, p', e, rfl⟩ := path_decomposition_last_edge p h_pos
    by_cases hc_in_S : c ∈ S
    · -- Case 1: The endpoint of `p'` is already in `S`.
      have p'_len : p'.length = n := by exact Nat.succ_inj.mp h_len
      obtain ⟨u, v, e_uv, p₁, p₂, hu_not_S, hv_S, hp'⟩ :=
        ih p' S ha_not_in_S hc_in_S p'_len
      refine ⟨u, v, e_uv, p₁, p₂.comp e.toPath, hu_not_S, hv_S, ?_⟩
      rw [cons_eq_comp_toPath, hp', Path.comp_assoc, Path.comp_assoc]
    · -- Case 2: The endpoint of `p'` is not in `S`.
      refine ⟨c, b, e, p', Path.nil, hc_in_S, hb_in_S, ?_⟩
      simp only [comp_nil]
      simp_all only [exists_and_left, length_cons, Nat.add_right_cancel_iff, lt_add_iff_pos_left, add_pos_iff,
        Nat.lt_one_iff, pos_of_gt, or_true]
      subst h_len
      rfl

/-- A path from a vertex in `S` to a vertex not in `S` must cross the boundary. -/
theorem exists_boundary_edge_from_set {a b : V} (p : Path a b) (S : Set V)
    (ha_in_S : a ∈ S) (hb_not_in_S : b ∉ S) :
    ∃ (u v : V) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      u ∈ S ∧ v ∉ S ∧ p = p₁.comp (e.toPath.comp p₂) := by
  classical
  have ha_not_in_compl : a ∉ Sᶜ := by simpa
  have hb_in_compl : b ∈ Sᶜ := by simpa
  obtain ⟨u, v, e, p₁, p₂, hu_not_in_compl, hv_in_compl, hp⟩ :=
    exists_boundary_edge p Sᶜ ha_not_in_compl hb_in_compl
  refine ⟨u, v, e, p₁, p₂, ?_, ?_, hp⟩
  · simpa using hu_not_in_compl
  · simpa using hv_in_compl

/-- Alternative formulation: there exists an edge crossing the boundary. -/
theorem exists_crossing_edge {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b ∈ S) :
    ∃ (u v : V) (_ : u ⟶ v), u ∉ S ∧ v ∈ S := by
  obtain ⟨u, v, e, _, _, hu_not_S, hv_S, _⟩ := exists_boundary_edge p S ha_not_in_S hb_in_S
  exact ⟨u, v, e, hu_not_S, hv_S⟩

end BoundaryEdges

end Quiver.Path

namespace Quiver.Path

variable {V : Type*} [Quiver V]

/-- The end vertex of a path. A path `p : Path a b` has `p.end = b`. -/
def «end» {a : V} : ∀ {b : V}, Path a b → V
  | b, _ => b

/-- The set of vertices in a path. -/
def activeVertices {a : V} : ∀ {b : V}, Path a b → Set V
  | _, nil => {a}
  | _, cons p e => activeVertices p ∪ {«end» (cons p e)}

@[simp] lemma end_cons {a b c : V} (p : Path a b) (e : b ⟶ c) : «end» (p.cons e) = c := rfl
@[simp] lemma activeVertices_nil {a : V} : activeVertices (nil : Path a a) = {a} := rfl
@[simp] lemma activeVertices_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  activeVertices (p.cons e) = activeVertices p ∪ {c} := by simp [activeVertices]; rfl

/-- The list of vertices in a path, including the start and end vertices. -/
def vertices {a : V} : ∀ {b : V}, Path a b → List V
  | _, nil => [a]
  | _, cons p e => (p.vertices).concat («end» (p.cons e))

@[simp]
lemma vertices_nil (a : V) : (nil : Path a a).vertices = [a] := rfl

@[simp]
lemma vertices_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  (p.cons e).vertices = p.vertices.concat c := rfl

-- Vertices of a path are always non-empty
lemma vertices_nonempty' {V : Type*} [Quiver V] {a b : V} (p : Path a b) : p.vertices.length > 0 := by
  induction p with
  | nil => simp only [vertices_nil, List.length_cons, List.length_nil, le_refl, Nat.eq_of_le_zero,
    zero_add, gt_iff_lt, Nat.lt_one_iff, pos_of_gt]
  | cons p' e ih =>
    rw [vertices_cons]
    simp only [List.concat_eq_append, List.length_append, List.length_cons, List.length_nil,
      zero_add, gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, ih, Nat.lt_one_iff, pos_of_gt, or_self]

/-- The set of vertices in a path, excluding the final vertex. -/
def activeFinset [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.dropLast.toFinset

def activeVertices' {a : V} {b : V} (p : Path a b) : Set V :=
  {v | v ∈ p.vertices}

@[simp]
lemma mem_activeVertices {a b : V} (p : Path a b) (v : V) :
    v ∈ p.activeVertices' ↔ v ∈ p.vertices := by
  rfl

/-- The finset of vertices in a path. -/
def vertexFinset [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.toFinset

/-- The vertex list of `cons` — convenient `simp` form. -/
@[simp] lemma mem_vertices_cons {a b c : V} (p : Path a b)
    (e : b ⟶ c) {x : V} :
    x ∈ (p.cons e).vertices ↔ x ∈ p.vertices ∨ x = c := by
  simp only [vertices_cons, List.mem_concat]

/--
A vertex `x` is in the `activeFinset` of a path `p` if and only if it is in the `dropLast` of the `vertices` list of `p`.
-/
@[simp]
lemma mem_activeFinset_iff [DecidableEq V] {a b : V} (p : Path a b) {x : V} :
    x ∈ activeFinset p ↔ x ∈ p.vertices.dropLast := by
  simp only [activeFinset, List.mem_toFinset]

/-- The length of vertices list equals path length plus one -/
@[simp]
lemma vertices_length {V : Type*} [Quiver V] {a b : V} (p : Path a b) :
    p.vertices.length = p.length + 1 := by
  induction p with
  | nil => simp only [vertices_nil, List.length_cons, List.length_nil, zero_add, length_nil]
  | cons p' e ih =>
    simp only [vertices_cons, length_cons, List.length_concat, ih]

lemma vertices_nonempty {a : V} {b : V} (p : Path a b) : p.vertices ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, vertices_length]; omega

/-- The head of the vertices list is the start vertex -/
@[simp]
lemma vertices_head? {a b : V} (p : Path a b) : p.vertices.head? = some a := by
  induction p with
  | nil => simp only [vertices_nil, List.head?_cons]
  | cons p' e ih =>
    simp only [vertices_cons]
    have : ¬p'.vertices.isEmpty := by
      simp_all only [List.isEmpty_iff]
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      simp_all only [List.head?_nil, reduceCtorEq]
    simp
    simp_all only [List.isEmpty_iff, Option.getD_some]

@[simp]
lemma length_toPath {a b : V} (e : a ⟶ b) : (e.toPath).length = 1 := rfl

variable {α : Type*} [DecidableEq α]

@[simp]
lemma vertices_getLast {a b : V} (p : Path a b) (h : p.vertices ≠ []) :
  p.vertices.getLast h = b := by
  induction p with
  | nil => simp only [vertices_nil, List.getLast_singleton]
  | cons p' e ih =>
    simp only [vertices_cons]
    rw [@List.getLast_concat']

/-- A path from a single arrow. -/
def List.toPath {a b : V} (e : a ⟶ b) : Path a b :=
  Path.nil.cons e

@[simp]
lemma vertices_comp {a b c : V} (p : Path a b) (q : Path b c) :
  (p.comp q).vertices = p.vertices.dropLast ++ q.vertices := by
  induction q with
  | nil =>
    simp only [comp_nil, vertices_nil]
    have h_nonempty : p.vertices.length > 0 := by exact vertices_nonempty' p
    have h_ne_nil : p.vertices ≠ [] := List.ne_nil_of_length_pos h_nonempty
    rw [← List.dropLast_append_getLast h_ne_nil, vertices_getLast p h_ne_nil]
    simp_all only [gt_iff_lt, ne_eq, List.cons_ne_self, not_false_eq_true, List.dropLast_append_of_ne_nil,
      List.dropLast_singleton, List.append_nil]
  | cons q' e ih =>
    simp only [comp_cons, vertices_cons, ih, List.concat_eq_append]
    rw [List.append_assoc]

lemma start_mem_vertices {a b : V} (p : Path a b) : a ∈ p.vertices := by
  induction p with
  | nil => simp only [vertices_nil, List.mem_cons, List.not_mem_nil, or_false]
  | cons p' e ih =>
    simp only [vertices_cons]
    simp_all only [List.concat_eq_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or]

@[simp] lemma length_eq_zero_iff {a : V} (p : Path a a) :
    p.length = 0 ↔ p = Path.nil := by
  cases p
  · simp only [length_nil]
  · constructor
    · intro h; cases h
    · intro h; cases h

/-- Given vertices lists from a path composition, the prefix path's vertices is a prefix of the full path's vertices -/
lemma isPrefix_dropLast_of_comp_eq {V : Type*} [Quiver V] {a b c : V} {p : Path a b} {p₁ : Path a c} {p₂ : Path c b}
    (h : p.vertices = p₁.vertices.dropLast ++ p₂.vertices) : p₁.vertices.dropLast.IsPrefix p.vertices := by
  rw [h]
  exact List.prefix_append p₁.vertices.dropLast p₂.vertices

/-- The head of the vertices list is the start vertex. -/
@[simp]
lemma vertices_head_eq_start {a b : V} (p : Path a b) : p.vertices.head (vertices_nonempty p) = a := by
  induction p with
  | nil => simp only [vertices_nil, List.head_cons]
  | cons p' _ ih =>
    simp only [vertices_cons, List.concat_eq_append]
    have : p'.vertices ≠ [] := vertices_nonempty p'
    simp only [List.head_append_of_ne_nil this]
    exact ih

/-- The last element of the vertices list is the end vertex. -/
@[simp]
lemma vertices_getLast_eq_end {a b : V} (p : Path a b) :
  p.vertices.getLast (vertices_nonempty p) = b := by
  exact vertices_getLast p (vertices_nonempty p)

variable {V : Type*} [Quiver V]

lemma end_prefix_eq_get_vertices {a b c : V} (p₁ : Path a c) (p₂ : Path c b) :
    c = (p₁.comp p₂).vertices.get
        ⟨p₁.length, by
  simp only [vertices_comp, List.length_append, List.length_dropLast,
    vertices_length, add_tsub_cancel_right, lt_add_iff_pos_right, add_pos_iff,
    Nat.lt_one_iff, pos_of_gt, or_true]⟩ := by
  simp only [List.get_eq_getElem, vertices_comp, List.length_dropLast, vertices_length,
    add_tsub_cancel_right, le_refl, List.getElem_append_right, tsub_self, List.getElem_zero,
    vertices_head_eq_start]

@[simp] lemma vertices_toPath {i j : V} (e : i ⟶ j) :
    (e.toPath).vertices = [i, j] := by
  change (Path.nil.cons e).vertices = [i, j]
  simp; rfl

@[simp] lemma vertices_toPath_tail {i j : V} (e : i ⟶ j) :
    (e.toPath).vertices.tail = [j] := by
  simp [vertices_toPath]

/-- If a composition is `nil`, the left component must be `nil`
    (proved via lengths, avoiding dependent pattern-matching). -/
@[simp]
lemma nil_of_comp_eq_nil_left {a b : V} {p : Path a b} {q : Path b a}
    (h : p.comp q = (Path.nil : Path a a)) : p.length = 0 := by
  have hlen : (p.comp q).length = 0 := by
    simpa using congrArg Path.length h
  have : p.length + q.length = 0 := by
    simpa [length_comp] using hlen
  exact Nat.eq_zero_of_add_eq_zero_right this-- Nat.eq_zero_of_add_eq_zero_left this

/-- If a composition is `nil`, the right component must be `nil`-/
lemma nil_of_comp_eq_nil_right {a b : V} {p : Path a b} {q : Path b a}
    (h : p.comp q = (Path.nil : Path a a)) : q.length = 0 := by
  have hlen : (p.comp q).length = 0 := by
    simpa using congrArg Path.length h
  have : p.length + q.length = 0 := by
    simpa [length_comp] using hlen
  exact Nat.eq_zero_of_add_eq_zero_left this

@[simp] lemma end_mem_vertices {a b : V} (p : Path a b) : b ∈ p.vertices := by
  have h₁ : p.vertices.getLast (vertices_nonempty p) = b :=
    vertices_getLast p (vertices_nonempty p)
  have h₂ := List.getLast_mem (l := p.vertices) (vertices_nonempty p)
  simpa [h₁] using h₂

lemma mem_vertices_to_active {V : Type*} [Quiver V]
    {a b : V} {p : Path a b} {x : V} :
    x ∈ p.vertices → x ∈ p.activeVertices := by
  intro hx
  induction p with
  | nil =>
      simpa [Quiver.Path.vertices_nil,
             Quiver.Path.activeVertices_nil] using hx
  | cons p' e ih =>
      have hxSplit : x ∈ p'.vertices.dropLast ∨ x ∈ e.toPath.vertices := by
        simpa [Quiver.Path.vertices_cons] using hx
      cases hxSplit with
      | inl h_in_drop =>
          have : x ∈ p'.vertices := List.mem_of_mem_dropLast h_in_drop
          have : x ∈ p'.activeVertices := ih this
          exact (by
            simpa [Quiver.Path.activeVertices_cons] using Or.inl this)
      | inr h_in_edge =>
          have h_edge : x = p'.end ∨ x = (p'.cons e).end := by
            simpa [Quiver.Path.vertices_toPath,
                   List.mem_cons, List.mem_singleton] using h_in_edge
          cases h_edge with
          | inl h_eq =>
              have : x ∈ p'.activeVertices := by
                subst h_eq; simp_all only [end_mem_vertices, forall_const, cons_eq_comp_toPath, vertices_comp,
                  vertices_toPath, mem_append, mem_cons, not_mem_nil, or_false, true_or, or_true]
              exact (by
                simpa [Quiver.Path.activeVertices_cons] using Or.inl this)
          | inr h_eq =>
              have : x ∈ ({ (p'.cons e).end } : Set V) := by
                simp only [cons_eq_comp_toPath, h_eq, Set.mem_singleton_iff]
              exact (by
                simpa [Quiver.Path.activeVertices_cons] using Or.inr this)

/- New Simp Lemmas for activeFinset
@[simp] lemma activeFinset_nil [DecidableEq V] {a : V} : activeFinset (nil : Path a a) = {a} := by rw?
@[simp] lemma activeFinset_cons [DecidableEq V] {a b c : V} (p : Path a b) (e : b ⟶ c) :
  activeFinset (p.cons e) = activeFinset p ∪ {«end» (cons p e)} := rfl

-- A lemma to connect the two definitions
@[simp]
lemma coe_activeFinset [DecidableEq V] {a b : V} (p : Path a b) :
  (activeFinset p : Set V) = activeVertices p := by
  induction p with
  | nil => simp
  | cons p' e ih => simp [activeFinset, activeVertices, ih]-/

end Quiver.Path

namespace Prefunctor

open Quiver

variable {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W)

@[simp]
lemma end_map {a b : V} (p : Path a b) : F.obj (p.end) = (F.mapPath p).end := by
  induction p with
  | nil => rfl
  | cons p' e ih => simp; rfl

end Prefunctor

open Quiver

namespace Quiver

/-- The quiver structure on a subtype is induced by the quiver structure on the original type.
    An arrow from `a : S` to `b : S` exists if an arrow from `a.val` to `b.val` exists. -/
def inducedQuiver {V : Type u} [Quiver.{v} V] (S : Set V) : Quiver.{v} S :=
  ⟨fun a b => a.val ⟶ b.val⟩

end Quiver
namespace Quiver.Subquiver

variable {V : Type u} [Quiver.{v} V] (S : Set V)

attribute [local instance] inducedQuiver

/-- The embedding of an induced subquiver on a set `S` into the original quiver. -/
@[simps]
def embedding : Prefunctor S V where
  obj := Subtype.val
  map := id

/-- The vertices in a path mapped by the embedding are all in the original set S. -/
@[simp]
lemma mapPath_embedding_vertices_in_set {i j : S} (p : Path i j) :
  ∀ v, v ∈ ((embedding S).mapPath p).activeVertices → v ∈ S := by
  induction p with
  | nil =>
    intro v hv
    simp only [Prefunctor.mapPath_nil, Path.activeVertices_nil, Set.mem_singleton_iff] at hv
    subst hv
    exact i.property
  | cons p' e ih =>
    intro v hv
    simp only [Prefunctor.mapPath_cons, Path.activeVertices_cons, Set.mem_union,
               Set.mem_singleton_iff] at hv
    cases hv with
    | inl h => exact ih v h
    | inr h => subst h; simp_all only [embedding_obj, Subtype.coe_prop]

open Quiver.Path

/--
If a path in the original quiver only visits vertices in a set `S`, it can be lifted
to a path in the induced subquiver on `S`.
-/
def lift_path_to_induced {S : Set n} [DecidablePred (· ∈ S)]  [Quiver V]
    {i j : n} [Quiver n] (p : Path i j) (hp : ∀ k, k ∈ p.vertices → k ∈ S) :
    letI : Quiver n := inferInstance
    letI : Quiver S := inducedQuiver S
    Path (⟨i, hp i (start_mem_vertices p)⟩ : S) (⟨j, hp j (end_mem_vertices p)⟩ : S) := by
  letI : Quiver n := inferInstance
  letI : Quiver S := inducedQuiver S
  induction p with
  | nil => exact Path.nil
  | cons p' e ih =>
    exact Path.cons (ih (fun k hk => hp k ((mem_vertices_cons p' e).mpr (Or.inl hk)))) e

end Quiver.Subquiver

namespace Quiver.Path
open Quiver
variable {V : Type*} [Quiver V]

/--
Construct a path by repeating a loop `n` times.
`replicate n p` is the path `p.comp(p.comp(...p))` where `p` is composed `n` times.
If `n=0`, it is the nil path.
-/
def replicate (n : ℕ) {a : V} (p : Path a a) : Path a a :=
  match n with
  | 0 => Path.nil
  | k + 1 => (replicate k p).comp p

@[simp]
lemma length_replicate (n : ℕ) {a : V} (p : Path a a) :
  (replicate n p).length = n * p.length := by
  induction n with
  | zero => simp only [replicate, length_nil, zero_mul]
  | succ k ih =>
    simp only [replicate, length_comp, ih, add_comm, Nat.succ_mul]

variable {V : Type*} [Quiver V]



variable {V : Type*} [Quiver V]

/-!  ### Path splitting utilities -/

open List

/-- Given a path `p : Path a b` and an index `n ≤ p.length`,
    we can split `p = p₁.comp p₂` with `p₁.length = n`. -/
theorem exists_decomp_at_length {a b : V} (p : Path a b) {n : ℕ} (hn : n ≤ p.length) :
    ∃ (c : V) (p₁ : Path a c) (p₂ : Path c b),
      p = p₁.comp p₂ ∧ p₁.length = n := by
  induction p generalizing n with
  | nil =>
      have h : n = 0 := by simp_all only [length_nil, nonpos_iff_eq_zero]
      subst h
      exact ⟨a, Path.nil, Path.nil, by simp only [comp_nil], rfl⟩
  | cons p' e ih =>
      rename_i c
      rw [length_cons] at hn
      rcases (Nat.le_succ_iff).1 hn with h | h
      · rcases ih h with ⟨d, p₁, p₂, hp, hl⟩
        refine ⟨d, p₁, p₂.cons e, ?_, hl⟩
        simp only [hp, cons_eq_comp_toPath, comp_assoc]
      · subst h
        refine ⟨c, p'.cons e, Path.nil, ?_, ?_⟩
        · simp only [cons_eq_comp_toPath, comp_nil]
        · simp only [cons_eq_comp_toPath, length_comp, length_toPath, Nat.succ_eq_add_one]

theorem exists_decomp_of_mem_vertices {a b v : V} (p : Path a b)
  (h : v ∈ p.vertices) : ∃ (p₁ : Path a v) (p₂ : Path v b), p = p₁.comp p₂ := by
  obtain ⟨l₁, l₂, hv⟩ := List.exists_mem_split h
  have h_len : l₁.length ≤ p.length := by
    have : p.vertices.length = p.length + 1 := vertices_length p
    have : l₁.length < p.vertices.length := by
      rw [hv, List.length_append, List.length_cons]
      omega
    omega
  obtain ⟨c, p₁, p₂, hp, hl⟩ := exists_decomp_at_length p h_len
  suffices hvc : v = c by
    subst hvc
    exact ⟨p₁, p₂, hp⟩
  have h_verts : p.vertices = p₁.vertices.dropLast ++ p₂.vertices := by
    rw [hp, vertices_comp]
  have h_l1_len : l₁.length = p₁.vertices.dropLast.length := by
    have : p₁.vertices.length = p₁.length + 1 := vertices_length p₁
    simp only [List.length_dropLast, this, hl, add_tsub_cancel_right]
  have h_l1_eq : l₁ = p₁.vertices.dropLast := by
    have : l₁ ++ v :: l₂ = p₁.vertices.dropLast ++ p₂.vertices := by
      rw [← hv, h_verts]
    exact List.append_inj_left this h_l1_len
  have h_v_l2 : v :: l₂ = p₂.vertices := by
    have : l₁ ++ v :: l₂ = p₁.vertices.dropLast ++ p₂.vertices := by
      rw [← hv, h_verts]
    rw [h_l1_eq] at this
    exact List.append_cancel_left this
  have : p₂.vertices.head? = some c := by
    cases p₂ with
    | nil => simp only [vertices_nil, List.head?_cons]
    | cons _ _ => exact vertices_head? _
  rw [← h_v_l2] at this
  simp only [List.head?_cons, Option.some.injEq] at this
  exact this

/-
/- Equality of paths implies equality of their start and end vertices. -/
lemma eq_of_heq {a a' b b' : V} {p : Path a b} {p' : Path a' b'} (h : HEq p p') :
  a = a' ∧ b = b' := by
  -- derive equalities of start and end vertices using heterogeneous equality
  have h₁ : start p = start p' :=
    Eq.ndrec (motive := fun x => start p = x) rfl (congrArg start h)
  have h₂ : «end» p = «end» p' :=
    Eq.ndrec (motive := fun x => «end» p = x) rfl (congrArg «end» h)
  simp [Path.start, Path.end] at h₁ h₂
  exact ⟨h₁, h₂⟩

@[simp]
lemma start_eq_of_heq {a a' b b' : V} {p : Path a b} {p' : Path a' b'} (h : HEq p p') :
  a = a' :=
  (eq_of_heq h).1

@[simp]
lemma end_eq_of_heq {a a' b b' : V} {p : Path a b} {p' : Path a' b'} (h : HEq p p') :
  b = b' :=
  (eq_of_heq h).2-/


/-- `split_at_vertex` decomposes a path `p` at the vertex sitting in
    position `i` of its `vertices` list. -/
theorem split_at_vertex {a b : V} (p : Path a b) (i : ℕ)
    (hi : i < p.vertices.length) :
    ∃ (v : V) (p₁ : Path a v) (p₂ : Path v b),
      p = p₁.comp p₂ ∧
      p₁.length = i ∧
      v = p.vertices.get ⟨i, hi⟩ := by
  have hi_le_len : i ≤ p.length := by
    rw [vertices_length] at hi
    exact Nat.le_of_lt_succ hi
  obtain ⟨v, p₁, p₂, hp, hlen⟩ := exists_decomp_at_length p hi_le_len
  subst hp
  refine ⟨v, p₁, p₂, rfl, hlen, ?_⟩
  have h_eq := end_prefix_eq_get_vertices p₁ p₂
  simpa [hlen] using h_eq

end Quiver.Path

namespace Quiver.Path
open Quiver
variable {V : Type*} [Quiver V]

/-- A path is simple if it does not visit any vertex more than once, with the possible
exception of the final vertex, which may be the same as the start vertex in a cycle. -/
def IsSimple' {a b : V} (p : Path a b) : Prop :=
  p.vertices.dropLast.Nodup ∧
  (a = b → p.vertices.dropLast.length = p.length) ∧
  (a ≠ b → p.end ∉ p.vertices.dropLast)

lemma isSimple_nil {a : V} : IsSimple' (nil : Path a a) := by
  simp only [IsSimple', vertices_nil, dropLast_singleton, nodup_nil, List.length_nil, le_refl,
    Nat.eq_of_le_zero, length_nil, imp_self, ne_eq, not_true_eq_false, not_mem_nil,
    not_false_eq_true, implies_true, and_self]

/-- A path is simple if it does not contain any vertex more than once.
This is a strict definition; a cycle `a ⟶ ... ⟶ a` of non-zero length is not simple. -/
@[simp]
def IsStrictlySimple {a b : V} (p : Path a b) : Prop := p.vertices.Nodup

lemma isStrictlySimple_nil {a : V} : IsStrictlySimple (nil : Path a a) := by
  simp only [IsStrictlySimple, vertices_nil, nodup_cons, not_mem_nil, not_false_eq_true, nodup_nil,
    and_self]

@[simp]
lemma isStrictlySimple_cons [DecidableEq V] {a b c : V} (p : Path a b) (e : b ⟶ c) :
  IsStrictlySimple (p.cons e) ↔ IsStrictlySimple p ∧ c ∉ p.vertices := by
  simp only [IsStrictlySimple, vertices_cons]
  rw [List.nodup_concat]

/-- The set of vertices of a simple path has cardinality `p.length + 1`. -/
lemma card_vertexFinset_of_isStrictlySimple [DecidableEq V] {a b : V} {p : Path a b} (hp : IsStrictlySimple p) :
    p.vertexFinset.card = p.length + 1 := by
  simp [vertexFinset, List.toFinset_card_of_nodup hp, vertices_length]

lemma length_lt_card_of_isStrictlySimple [DecidableEq V] [Fintype V]
    {a b : V} {p : Path a b} (hp : IsStrictlySimple p) :
  p.length < Fintype.card V := by
  simpa [card_vertexFinset_of_isStrictlySimple hp, Nat.succ_eq_add_one] using
    (Finset.card_le_univ p.vertexFinset)

/-- If a path is not strictly simple, then there exists a vertex that occurs at least twice. -/
lemma not_strictly_simple_iff_exists_repeated_vertex [DecidableEq V] {a b : V} {p : Path a b} :
    ¬IsStrictlySimple p ↔ ∃ v, v ∈ p.vertices ∧ p.vertices.count v ≥ 2 := by
  rw [IsStrictlySimple, List.nodup_iff_not_contains_dup]
  push_neg
  simp only [List.ContainsDup]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, List.count_pos_iff.mp (by linarith), hv⟩
  · rintro ⟨v, _, hv⟩
    exact ⟨v, hv⟩


/-- Removing a positive-length cycle from a path gives a strictly shorter path with the same endpoints. -/
lemma remove_cycle_gives_shorter_path [DecidableEq V] {a v : V}
    {p_prefix : Path a v} {p_cycle : Path v v} {p_rest : Path v b}
    (h_cycle_pos : p_cycle.length > 0) :
    (p_prefix.comp p_rest).length < (p_prefix.comp (p_cycle.comp p_rest)).length := by
  simp only [length_comp]
  simp_all only [gt_iff_lt, add_lt_add_iff_left, lt_add_iff_pos_left]

open List

/-- If a vertex c appears in path p, c must either be the end vertex or appear in the tail of vertices. -/
lemma vertex_in_path_cases {a b c : V} (p : Path a b) (h : c ∈ p.vertices) :
  c = b ∨ c ∈ p.vertices.dropLast := by
  induction p with
  | nil =>
    simp [vertices_nil] at h
    subst h
    simp
  | cons p' e ih =>
    rename_i b'
    simp only [vertices_cons, List.mem_concat] at h
    rcases h with h_in_p' | h_eq_b
    · -- c is in p'.vertices
      specialize ih h_in_p'
      rcases ih with h_eq_p'_end | h_in_p'_dropLast
      · -- c is the end of p', so it's in p.vertices.dropLast which is p'.vertices
        right
        simp only [vertices_cons]
        rw [List.dropLast_append_singleton (vertices_nonempty' p')]
        rw [h_eq_p'_end]
        subst h_eq_p'_end
        simp_all only
      · -- c is in the dropLast of p'.vertices, so it's also in p.vertices.dropLast
        right
        simp only [vertices_cons]
        rw [List.dropLast_append_singleton (vertices_nonempty' p')]
        exact h_in_p'
    · -- c is the end of p
      subst h_eq_b
      left
      rfl

/-- If we have a path p from a to b with c ∈ p.vertices,
    and c is not the end vertex b, then it appears in a proper prefix of the path. -/
lemma exists_prefix_with_vertex [DecidableEq V] {a b c : V} (p : Path a b) (h : c ∈ p.vertices) (h_ne : c ≠ b) :
  ∃ (p₁ : Path a c) (p₂ : Path c b), p = p₁.comp p₂ := by
  have h_cases := vertex_in_path_cases p h
  cases h_cases with
  | inl h_eq =>
      contradiction
  | inr h_mem_tail =>
      let i := p.vertices.idxOf c
      have hi : i < p.vertices.length := List.idxOf_lt_length_of_mem h
      obtain ⟨v, p₁, p₂, h_comp, h_len, h_c_eq⟩ := split_at_vertex p i hi
      have hvc : v = c := by
        rw [h_c_eq]
        exact List.get_idxOf_of_mem h
      subst hvc
      exact ⟨p₁, p₂, h_comp⟩

/-- Split a path at the **last** occurrence of a vertex. -/
theorem exists_decomp_of_mem_vertices_prop
    [DecidableEq V] {a b x : V} (p : Path a b) (hx : x ∈ p.vertices) :
    ∃ (p₁ : Path a x) (p₂ : Path x b),
      p = p₁.comp p₂ ∧ x ∉ p₂.vertices.tail := by
  classical
  induction p with
  | nil =>
      have hxa : x = a := by
        simpa [vertices_nil, List.mem_singleton] using hx
      subst hxa
      exact ⟨Path.nil, Path.nil, by simp only [comp_nil],
        by simp only [vertices_nil, tail_cons, not_mem_nil, not_false_eq_true]⟩
  | cons pPrev e ih =>
      have hx' : x ∈ pPrev.vertices ∨ x = (pPrev.cons e).end := by
        simpa using (mem_vertices_cons pPrev e).1 hx
      -- Case 1 : `x` is the final vertex.
      have h_case₁ :
          x = (pPrev.cons e).end →
          ∃ (p₁ : Path a x) (p₂ : Path x (pPrev.cons e).end),
            pPrev.cons e = p₁.comp p₂ ∧
            x ∉ p₂.vertices.tail := by
        intro hxe; subst hxe
        exact ⟨pPrev.cons e, Path.nil, by simp only [cons_eq_comp_toPath, comp_nil],
          by simp only [vertices_nil, tail_cons, not_mem_nil, not_false_eq_true]⟩
      -- Case 2 : `x` occurs in the prefix (and **is not** the final vertex).
      have h_case₂ :
          x ∈ pPrev.vertices → x ≠ (pPrev.cons e).end →
          ∃ (p₁ : Path a x) (p₂ : Path x (pPrev.cons e).end),
            pPrev.cons e = p₁.comp p₂ ∧
            x ∉ p₂.vertices.tail := by
        intro hxPrev hxe_ne
        rcases ih hxPrev with ⟨q₁, q₂, h_prev, h_not_tail⟩
        let q₂' : Path x (pPrev.cons e).end := q₂.comp e.toPath
        have h_eq : pPrev.cons e = q₁.comp q₂' := by
          dsimp [q₂']; simp only [h_prev, cons_eq_comp_toPath, Path.comp_assoc]
        have h_no_tail : x ∉ q₂'.vertices.tail := by
          intro hmem
          have hmem' : x ∈ (q₂.vertices.dropLast ++ (e.toPath).vertices).tail := by
            simpa [q₂', vertices_comp] using hmem
          by_cases h_nil : q₂.vertices.dropLast = []
          · have h_tail_toPath : x ∈ (e.toPath).vertices.tail := by
              simpa [h_nil] using hmem'
            have hx_end : x = (pPrev.comp e.toPath).end := by
              have : e.toPath.vertices.tail = [(pPrev.cons e).end] := by
                simp only [cons_eq_comp_toPath]
                rfl
              rw [this] at h_tail_toPath
              exact List.mem_singleton.mp h_tail_toPath
            exact hxe_ne hx_end
          · have h_split := (List.mem_tail_append).1 hmem'
            have h_mem_right :
                x ∈ (q₂.vertices.dropLast).tail ++ (e.toPath).vertices := by
              cases h_split with
              | inl h_left  => cases (h_nil h_left.1)
              | inr h_right => exact h_right.2
            have h_parts := (List.mem_append).1 h_mem_right
            cases h_parts with
            | inl h_in_dropLast_tail =>
                have : x ∈ q₂.vertices.tail :=
                  List.mem_of_mem_tail_dropLast h_in_dropLast_tail
                exact h_not_tail this
            | inr h_in_toPath =>
                have hx_end : x = (pPrev.comp e.toPath).end := by
                  have h' : x = pPrev.end ∨
                            x = (pPrev.cons e).end := by
                    have : e.toPath.vertices = [pPrev.end, (pPrev.cons e).end] := by
                      simp only [cons_eq_comp_toPath]
                      rfl
                    rw [this] at h_in_toPath
                    simpa [List.mem_cons, List.mem_singleton] using h_in_toPath
                  cases h' with
                  | inl h_eq_src =>
                      have : x ∈ q₂.vertices.tail := by
                        have h_q2_len_pos : 0 < q₂.length := by
                          have h_drop_len_pos : q₂.vertices.dropLast.length > 0 :=
                            List.length_pos_of_ne_nil h_nil
                          have h_vert_len_ge_2 : q₂.vertices.length ≥ 2 := by
                            subst h_eq_src h_prev
                            simp_all
                            exact h_drop_len_pos
                          have h_path_len_ge_1 : q₂.length ≥ 1 := by
                            subst h_eq_src h_prev
                            simp_all
                          exact h_path_len_ge_1
                        have h_q2_end : q₂.end = pPrev.end := by
                          have : (q₁.comp q₂).end = pPrev.end := by rw [h_prev]
                          simpa using this
                        subst h_eq_src
                        have h_nonempty : q₂.vertices ≠ [] := by
                          rw [List.ne_nil_iff_length_pos, vertices_length]
                          omega
                        have h_x_is_last : x = q₂.vertices.getLast h_nonempty := by
                          simp
                        have h_mem_tail : q₂.vertices.getLast h_nonempty ∈ q₂.vertices.tail := by
                          have h_len2 : q₂.vertices.length ≥ 2 := by rw [vertices_length]; omega
                          exact List.getLast_mem_tail h_len2
                        rw [← h_x_is_last] at h_mem_tail
                        exact h_mem_tail
                      contradiction
                  | inr h_eq_end => exact h_eq_end
                exact hxe_ne hx_end
        exact ⟨q₁, q₂', h_eq, h_no_tail⟩
      cases hx' with
      | inl h_in_prefix =>
          by_cases h_eq_end : x = (pPrev.cons e).end
          · rcases h_case₁ h_eq_end with ⟨p₁, p₂, h_eq, h_tail⟩
            exact ⟨p₁, p₂, h_eq, h_tail⟩
          · rcases h_case₂ h_in_prefix h_eq_end with ⟨p₁, p₂, h_eq, h_tail⟩
            exact ⟨p₁, p₂, h_eq, h_tail⟩
      | inr h_eq_end =>
          rcases h_case₁ h_eq_end with ⟨p₁, p₂, h_eq, h_tail⟩
          exact ⟨p₁, p₂, h_eq, h_tail⟩

theorem isStrictlySimple_of_shortest [DecidableEq V]
    {a b : V} (p : Path a b)
    (h_min : ∀ q : Path a b, p.length ≤ q.length) :
    IsStrictlySimple p := by
  classical
  by_contra h_dup
  obtain ⟨v, hv_in, hv_ge₂⟩ :=
    not_strictly_simple_iff_exists_repeated_vertex.mp h_dup
  obtain ⟨p₁, p₂, hp, hv_not_tail⟩ :=
    exists_decomp_of_mem_vertices_prop p hv_in
  have hv_in_p1_dropLast : v ∈ p₁.vertices.dropLast := by
    have h_count_p : p.vertices.count v =
        (p₁.vertices.dropLast ++ p₂.vertices).count v := by
      rw [← vertices_comp, ← hp]
    rw [h_count_p] at hv_ge₂
    rw [List.count_append] at hv_ge₂
    have h_count_p2 : p₂.vertices.count v = 1 := by
      have h_head : p₂.vertices.head? = some v := by
        cases p₂ with
        | nil => simp [vertices_nil]
        | cons p' e =>
          simp only [vertices_cons]
          have h := vertices_head? p'
          simp [List.concat_eq_append]
      have hne : p₂.vertices ≠ [] := by
        apply List.ne_nil_of_head?_eq_some h_head
      have h_shape : p₂.vertices = v :: p₂.vertices.tail := by
        have h_first : p₂.vertices.head? = some v := h_head
        have h_decomp : ∃ h t, p₂.vertices = h :: t := List.exists_cons_of_ne_nil hne
        rcases h_decomp with ⟨h, t, heq⟩
        rw [heq]
        have h_eq : h = v := by
          rw [heq] at h_first
          simp only [List.head?_cons] at h_first
          exact Option.some.inj h_first
        rw [h_eq]
        have t_eq : t = p₂.vertices.tail := by
          rw [heq, List.tail_cons]
        rw [t_eq]
        exact rfl
      rw [h_shape]
      have h_not_in_tail : v ∉ p₂.vertices.tail := hv_not_tail
      simp only [List.count_cons_self, List.count_eq_zero_of_not_mem h_not_in_tail]
    have : (p₁.vertices.dropLast).count v ≥ 1 := by
      have : 1 + (p₁.vertices.dropLast).count v ≥ 2 := by
        rw [add_comm]
        simpa [h_count_p2] using hv_ge₂
      linarith
    exact (List.count_pos_iff).1 (lt_of_lt_of_le Nat.zero_lt_one this)
  obtain ⟨q, c, h_p1_split⟩ :=
    exists_decomp_of_mem_vertices p₁
      (List.mem_of_mem_dropLast hv_in_p1_dropLast)
  have hc_pos : c.length > 0 := by
    by_cases h_len_zero : c.length = 0
    · have hc_nil : c = Path.nil := by
        apply (length_eq_zero_iff c).mp h_len_zero
      have : p₁ = q := by
        simpa [hc_nil, comp_nil] using h_p1_split
      have h_mem : v ∈ q.vertices.dropLast := by
        simpa [this] using hv_in_p1_dropLast
      have h_last : v = q.vertices.getLast (vertices_nonempty q) := by simp
      let i := q.vertices.idxOf v
      have hi_verts : i < q.vertices.length := by
        rw [List.idxOf_lt_length_iff]
        exact List.mem_of_mem_dropLast h_mem
      have hi : i < q.length := by
        have h_idx_lt_dropLast_len : i < q.vertices.dropLast.length := by
          have h_lt : List.idxOf v q.vertices.dropLast < q.vertices.dropLast.length :=
            List.idxOf_lt_length_of_mem h_mem
          have h_prefix : (q.vertices.dropLast).IsPrefix q.vertices := by
            have h_split := List.dropLast_append_getLast (vertices_nonempty q)
            have : (q.vertices.dropLast).IsPrefix (q.vertices.dropLast ++
                  [q.vertices.getLast (vertices_nonempty q)]) :=
              List.prefix_append _ _
            exact dropLast_prefix q.vertices
          have h_eq : List.idxOf v q.vertices = List.idxOf v q.vertices.dropLast :=
            idxOf_eq_idxOf_of_isPrefix h_prefix h_mem
          simpa [i, h_eq] using h_lt
        rw [List.length_dropLast, vertices_length] at h_idx_lt_dropLast_len
        exact h_idx_lt_dropLast_len
      obtain ⟨split_v, shorter_q, _, h_comp_q, h_len_shorter, h_v_eq⟩ := split_at_vertex q i hi_verts
      have h_split_v_eq_v : split_v = v := by
        rw [h_v_eq]
        exact List.get_idxOf_of_mem (List.mem_of_mem_dropLast h_mem)
      subst h_split_v_eq_v
      let shorter_path := shorter_q.comp p₂
      have h_shorter_total : shorter_path.length < p.length := by
        have h_p1_eq : p₁ = q := by simpa [hc_nil, comp_nil] using h_p1_split
        have h_q_len : q.length > shorter_q.length := by
          rw [h_len_shorter]
          exact hi
        have h_decomp : p = p₁.comp p₂ := hp
        rw [h_p1_eq] at h_decomp
        have h_len : p.length = q.length + p₂.length := by
          rw [h_decomp, length_comp]
        have h_shorter_len : shorter_path.length = shorter_q.length + p₂.length := by
          rw [length_comp]
        rw [h_len, h_shorter_len]
        exact Nat.add_lt_add_right h_q_len p₂.length
      exact absurd (h_min shorter_path) (not_le.mpr h_shorter_total)
    · exact Nat.pos_of_ne_zero h_len_zero
  let p' : Path a b := q.comp p₂
  have h_shorter : p'.length < p.length := by
    have h_len_p : p.length = q.length + c.length + p₂.length := by
      rw [hp, h_p1_split]
      rw [length_comp, length_comp]
    have h_len_p' : p'.length = q.length + p₂.length := by
      rw [length_comp]
    rw [h_len_p, h_len_p']
    have : 0 < c.length := hc_pos
    apply Nat.add_lt_add_of_lt_of_le
    · exact Nat.lt_add_of_pos_right this
    · exact le_refl p₂.length
  exact (not_le.mpr h_shorter) (h_min p')

/-- The length of a strictly simple path is at most one less than the number of vertices in the graph. -/
lemma length_le_card_minus_one_of_isSimple [Fintype n] [DecidableEq n] [Quiver n] {a b : n} (p : Path a b) (hp : p.IsStrictlySimple) :
    p.length ≤ Fintype.card n - 1 := by
  have h_card_verts : p.vertexFinset.card = p.length + 1 := by
    exact card_vertexFinset_of_isStrictlySimple hp
  have h_card_le_univ : p.vertexFinset.card ≤ Fintype.card n := by
    exact Finset.card_le_univ p.vertexFinset
  rw [h_card_verts] at h_card_le_univ
  exact Nat.le_sub_one_of_lt h_card_le_univ

/-! ### Cycles -/

/-- A path is simple if it does not visit any vertex more than once, with the possible
exception of the final vertex, which may be the same as the start vertex in a cycle. -/
def IsSimple {a b : V} (p : Path a b) : Prop :=
  p.vertices.dropLast.Nodup

/-- A cycle is a non-trivial path from a vertex back to itself that does not repeat vertices,
except for the start/end vertex. -/
@[nolint unusedArguments]
def IsCycle {a : V} (p : Path a a) : Prop :=
  p.length > 0 ∧ IsSimple p

lemma isSimple_of_isStrictlySimple {a b : V} {p : Path a b} (h : IsStrictlySimple p) : IsSimple p := by
  unfold IsSimple IsStrictlySimple at *
  simpa using h.sublist (List.dropLast_sublist (l := p.vertices))

/-!
# Acyclic Quivers

This module defines acyclic quivers and proves that a quiver is acyclic if and only if it
contains no simple cycles.

## Main definitions

* `Quiver.IsAcyclic`: A typeclass indicating that a quiver has no non-trivial paths from a
  vertex to itself.
* `Quiver.IsCycle`: A predicate on a path indicating it is a simple cycle.

## Main results

* `isAcyclic_iff_no_cycles`: A quiver is acyclic iff it contains no simple cycles.

-/

section Acyclic

variable {V : Type*} [Quiver V]

/-- A quiver is acyclic if there are no non-trivial paths from a vertex to itself. -/
class IsAcyclic (V : Type*) [Quiver V] : Prop where
  /-- The defining property of an acyclic quiver: any path from a vertex `a` to itself
  must have length zero. -/
  acyclic : ∀ (a : V) (p : Path a a), p.length = 0

-- Expose the lemma in a more convenient form.
lemma IsAcyclic.path_eq_nil {V : Type*} [Quiver V] [IsAcyclic V] {a : V} (p : Path a a) : p = Path.nil :=
  Path.eq_nil_of_length_zero p (IsAcyclic.acyclic a p)

lemma isAcyclic_iff_length_eq_zero :
    IsAcyclic V ↔ ∀ {a : V} (p : Path a a), p.length = 0 := by
  constructor
  · intro h; exact fun {a} p ↦ IsAcyclic.acyclic a p
  · intro h; exact { acyclic := fun a p ↦ h p }

/-- If a quiver is acyclic, then it contains no simple cycles. -/
lemma isAcyclic_of_no_cycles [DecidableEq V] :
    IsAcyclic V → ∀ {a : V} (p : Path a a), ¬IsCycle p := by
  intro h_acyclic a p h_cycle
  have h_pos : p.length > 0 := h_cycle.1
  have h_zero : p.length = 0 := IsAcyclic.acyclic a p
  exact (Nat.not_lt.mpr (le_of_eq h_zero)) h_pos

/-- There exists a positive loop shorter than p if q is such a loop. -/
lemma exists_positive_loop_shorter_than_p [DecidableEq V] {a : V} {p : Path a a} (q : Path a a)
    (h_q_pos : q.length > 0) (h_q_shorter : q.length < p.length) :
    ∃ n, ∃ (r : Path a a), r.length = n ∧ r.length > 0 ∧ r.length < p.length := by
  exact ⟨q.length, q, rfl, h_q_pos, h_q_shorter⟩

open Classical


/-- For any two positive loops shorter than p, their minimum length equals
    the minimum length among all positive loops shorter than p, or there exists
    an even shorter loop. -/
lemma min_length_among_shorter_loops {a : V} {p : Path a a} (q r : Path a a)
    (h_q_pos : q.length > 0) (h_r_pos : r.length > 0)
    (h_q_shorter : q.length < p.length) (h_r_shorter : r.length < p.length) :
    min q.length r.length = Nat.find (exists_positive_loop_shorter_than_p q h_q_pos h_q_shorter) ∨
    ∃ (s : Path a a), s.length = Nat.find (exists_positive_loop_shorter_than_p q h_q_pos h_q_shorter) ∧
                     s.length > 0 ∧ s.length < p.length ∧ s.length < min q.length r.length := by
  let min_len := Nat.find (exists_positive_loop_shorter_than_p q h_q_pos h_q_shorter)
  have h_min_spec := Nat.find_spec (exists_positive_loop_shorter_than_p q h_q_pos h_q_shorter)
  obtain ⟨s, hs_eq, hs_pos, hs_shorter⟩ := h_min_spec
  by_cases h : min_len < min q.length r.length
  · right
    exact ⟨s, hs_eq, hs_pos, hs_shorter, by rwa [hs_eq]⟩
  · left
    push_neg at h
    have h_min_le_q : min_len ≤ q.length :=
      Nat.find_min' (exists_positive_loop_shorter_than_p q h_q_pos h_q_shorter)
                    ⟨q, rfl, h_q_pos, h_q_shorter⟩
    have h_min_le_r : min_len ≤ r.length :=
      Nat.find_min' (exists_positive_loop_shorter_than_p q h_q_pos h_q_shorter)
                    ⟨r, rfl, h_r_pos, h_r_shorter⟩
    have h_min_le_min : min_len ≤ min q.length r.length := by
      apply le_min
      · exact h_min_le_q
      · exact h_min_le_r
    exact le_antisymm h h_min_le_min

/--
Among all positive-length loops shorter than `p`, `q` is minimal.
-/
lemma shortest_among_shorter_loops [DecidableEq V] {a : V} {p : Path a a} (q : Path a a)
    (_ : q.length > 0)
    (h_q_shorter : q.length < p.length)
    (h_q_minimal : ∀ r : Path a a, r.length > 0 → r.length < p.length → q.length ≤ r.length) :
    ∀ r : Path a a, r.length > 0 → q.length ≤ r.length := by
  intro r h_r_pos
  by_cases h_r_shorter : r.length < p.length
  · exact h_q_minimal r h_r_pos h_r_shorter
  · have h_p_le_r : p.length ≤ r.length := le_of_not_gt h_r_shorter
    exact le_trans (le_of_lt h_q_shorter) h_p_le_r

/-- If there exists any positive-length loop at `a`, then there exists a shortest one. -/
lemma exists_shortest_positive_loop [DecidableEq V] {a : V} (q : Path a a) (hq_pos : q.length > 0) :
    ∃ (s : Path a a), s.length > 0 ∧ ∀ (r : Path a a), r.length > 0 → s.length ≤ r.length := by
  let P := fun n => ∃ (r : Path a a), r.length = n ∧ r.length > 0
  have hP_nonempty : ∃ n, P n := ⟨q.length, q, rfl, hq_pos⟩
  let min_len := Nat.find hP_nonempty
  have h_min_len_spec : P min_len := Nat.find_spec hP_nonempty
  obtain ⟨s, hs_len, hs_pos⟩ := h_min_len_spec
  use s
  constructor
  · exact hs_pos
  · intro r hr_pos
    have hr_prop : P r.length := ⟨r, rfl, hr_pos⟩
    rw [hs_len]
    exact Nat.find_min' hP_nonempty hr_prop

/-- If n < m and m ≤ n, we have a contradiction -/
private lemma Nat.lt_le_antisymm {n m : Nat} (h1 : n < m) (h2 : m ≤ n) : False :=
  Nat.lt_irrefl n (Nat.lt_of_lt_of_le h1 h2)

/-- If n ≥ m, then it's not the case that n < m. -/
private lemma not_lt_of_ge {n m : Nat} (h : n ≥ m) : ¬(n < m) :=
  fun h' => Nat.lt_le_antisymm h' h

/-- If n > m, then it's not the case that n ≤ m -/
private lemma not_le_of_gt {n m : Nat} (h : n > m) : ¬(n ≤ m) :=
  fun h' => Nat.lt_le_antisymm h h'

/-- Given a path with a repeated vertex, we can find that vertex and show it appears
    in the dropLast portion of the prefix path. -/
lemma repeated_vertex_in_prefix_dropLast [DecidableEq V] {a : V} (s : Path a a)
    (h_not_simple : ¬IsStrictlySimple s) :
    ∃ (v : V) (p₁ : Path a v) (p₂ : Path v a),
      v ∈ p₁.vertices.dropLast ∧ s = p₁.comp p₂ ∧ v ∉ p₂.vertices.tail := by
  obtain ⟨v, hv_in, hv_ge₂⟩ := not_strictly_simple_iff_exists_repeated_vertex.mp h_not_simple
  obtain ⟨p₁, p₂, hp, hv_not_tail⟩ := exists_decomp_of_mem_vertices_prop s hv_in
  have hv_in_p1_dropLast : v ∈ p₁.vertices.dropLast := by
    have h_count_s : s.vertices.count v = (p₁.vertices.dropLast ++ p₂.vertices).count v := by
      rw [hp, vertices_comp]
    rw [h_count_s, List.count_append] at hv_ge₂
    have h_count_p2 : p₂.vertices.count v = 1 := by
      have h_head : p₂.vertices.head? = some v := by
        cases p₂ with
        | nil => simp [vertices_nil]
        | cons _ _ => exact vertices_head? _
      have hne : p₂.vertices ≠ [] := List.ne_nil_of_head?_eq_some h_head
      have h_shape : p₂.vertices = v :: p₂.vertices.tail := by
        have h_first : p₂.vertices.head? = some v := h_head
        have h_decomp : ∃ h t, p₂.vertices = h :: t := List.exists_cons_of_ne_nil hne
        rcases h_decomp with ⟨h, t, heq⟩
        rw [heq]
        have h_eq : h = v := by
          rw [heq] at h_first
          simp only [List.head?_cons] at h_first
          exact Option.some.inj h_first
        rw [h_eq]
        have t_eq : t = p₂.vertices.tail := by rw [heq, List.tail_cons]
        rw [t_eq]; exact rfl
      rw [h_shape, List.count_cons_self, List.count_eq_zero_of_not_mem hv_not_tail]
    have h_count_p1 : (p₁.vertices.dropLast).count v ≥ 1 := by
      have h_sum : (p₁.vertices.dropLast).count v + p₂.vertices.count v ≥ 2 := hv_ge₂
      rw [h_count_p2] at h_sum
      linarith
    exact (List.count_pos_iff).mp (by linarith)
  exact ⟨v, p₁, p₂, hv_in_p1_dropLast, hp, hv_not_tail⟩

lemma extract_cycle_from_prefix [DecidableEq V] {a vertex : V} {p₁ : Path a vertex}
    (hvertex_in_p1_dropLast : vertex ∈ p₁.vertices.dropLast) :
    ∃ (q : Path a vertex) (c : Path vertex vertex),
      p₁ = q.comp c ∧ vertex ∉ q.vertices.dropLast := by
  classical
  let i := p₁.vertices.idxOf vertex
  have h_mem : vertex ∈ p₁.vertices :=
    List.mem_of_mem_dropLast hvertex_in_p1_dropLast
  have hi_lt : i < p₁.vertices.length :=
    List.idxOf_lt_length_of_mem h_mem
  obtain ⟨v_split, q, c, h_comp, h_len, h_get⟩ := split_at_vertex p₁ i hi_lt
  have hv_eq : v_split = vertex := by
    have h_idx : p₁.vertices.get ⟨i, hi_lt⟩ = vertex :=
      List.get_idxOf_of_mem h_mem
    simpa [h_get] using h_idx
  have hv_not_in_q : vertex ∉ q.vertices.dropLast := by
    intro h_in
    have h_decomp_vertices :
        p₁.vertices = q.vertices.dropLast ++ c.vertices := by
      simp [h_comp]
    have h_prefix :
        q.vertices.dropLast.IsPrefix p₁.vertices := by
      simp [h_decomp_vertices]
    have h_idx_eq :
        p₁.vertices.idxOf vertex =
          (q.vertices.dropLast).idxOf vertex :=
      List.idxOf_eq_idxOf_of_isPrefix h_prefix h_in
    have h_idx_prefix_lt :
        (q.vertices.dropLast).idxOf vertex <
          (q.vertices.dropLast).length :=
      List.idxOf_lt_length_of_mem h_in
    have h_len_drop :
        (q.vertices.dropLast).length = q.length := by
      simp [List.length_dropLast, vertices_length]
    have : i < i := by
      have : (q.vertices.dropLast).idxOf vertex < i := by
        simpa [h_len_drop, h_len] using h_idx_prefix_lt
      simpa [i, h_idx_eq]
    exact (lt_irrefl _ this)
  subst hv_eq
  exact ⟨q, c, h_comp, hv_not_in_q⟩

lemma extract_cycle_from_prefix' [DecidableEq V] {a v : V} {p₁ : Path a v}
    (hv_in_p1_dropLast : v ∈ p₁.vertices.dropLast) :
    ∃ (q : Path a v) (c : Path v v),
      p₁ = q.comp c := by
  obtain ⟨q, c, h_split⟩ :=
    exists_decomp_of_mem_vertices p₁ (List.mem_of_mem_dropLast hv_in_p1_dropLast)
  exact ⟨q, c, h_split⟩

/-- A cycle extracted from a path with a repeated vertex has positive length. -/
lemma extracted_cycle_has_positive_length [DecidableEq V] {a v : V}
    {p₁ q : Path a v} {c : Path v v}
    (h_p1_split : p₁ = q.comp c)
    (hv_in_p1_dropLast : v ∈ p₁.vertices.dropLast)
    (hv_not_in_q : v ∉ q.vertices.dropLast) : c.length > 0 := by
  by_cases h_len_zero : c.length = 0
  · have hc_nil : c = Path.nil := (length_eq_zero_iff c).mp h_len_zero
    have h_p1_eq_q : p₁ = q := by
      rw [h_p1_split, hc_nil, comp_nil]
    have h_v_in_q : v ∈ q.vertices.dropLast := by
      subst h_p1_eq_q
      exact hv_in_p1_dropLast
    exact False.elim (hv_not_in_q h_v_in_q)
  · exact Nat.pos_of_ne_zero h_len_zero

/-- Removing a cycle from a path creates a strictly shorter path. -/
lemma removing_cycle_gives_shorter_path [DecidableEq V] {a : V} {s : Path a a}
    {q : Path a v} {c : Path v v} {p₂ : Path v a}
    (hp : s = (q.comp c).comp p₂) (hc_pos : c.length > 0) : (q.comp p₂).length < s.length := by
  have h_len_shorter : (q.comp p₂).length = q.length + p₂.length := by
    rw [length_comp]
  have h_len_s : s.length = q.length + c.length + p₂.length := by
    rw [hp, comp_assoc, length_comp, length_comp]
    ring
  rw [h_len_shorter, h_len_s]
  subst hp
  simp_all only [le_refl, gt_iff_lt, length_comp, comp_assoc, add_lt_add_iff_right,
    lt_add_iff_pos_right, Nat.eq_of_le_zero]

/-
/-- A shortest positive loop is strictly simple. -/
theorem shortest_positive_loop_is_strictly_simple {a : V} :
    ∀ (c : Path a a), c.length > 0 → (∀ p' : Path a a, p'.length > 0 → c.length ≤ p'.length) →
    c.IsStrictlySimple := by sorry
-/
