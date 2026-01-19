import GibbsMeasure.Topology.ConfigurationSpace
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Quasilocal functions (Georgii, Def. 2.20)

In statistical mechanics, *local observables* are functions depending only on finitely many spins.
Following Georgii, a bounded continuous observable is **quasilocal** if it is in the uniform closure
of the local observables.

This file sets up the basic API:
- `ConfigurationSpace.IsCylinderFunction` (defined in `Topology/ConfigurationSpace.lean`);
- `BoundedContinuousFunction.cylinderFunctions`: the submodule of bounded continuous cylinder
  functions;
- `BoundedContinuousFunction.quasilocalFunctions`: its topological (uniform) closure;
- `BoundedContinuousFunction.IsQuasilocal`: membership predicate.

We deliberately keep this file purely functional-analytic: it does *not* yet talk about
specifications. The latter will require a Feller-type hypothesis to act on bounded continuous
functions.
-/

open scoped Topology

namespace BoundedContinuousFunction

open GibbsMeasure.ConfigurationSpace

variable {S E F : Type*}
variable [TopologicalSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The submodule of **cylinder functions** inside `C_b(S → E, F)`. -/
def cylinderFunctions (S E F : Type*) [TopologicalSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Submodule ℝ ((S → E) →ᵇ F) where
  carrier := {f | IsCylinderFunction (S := S) (E := E) (fun σ => f σ)}
  zero_mem' := by
    simpa using (GibbsMeasure.ConfigurationSpace.IsCylinderFunction.const (S := S) (E := E) (F := F) 0)
  add_mem' := by
    intro f g hf hg
    -- Stability under addition is a property of cylinder functions on `(S → E)`.
    exact GibbsMeasure.ConfigurationSpace.IsCylinderFunction.add (S := S) (E := E) hf hg
  smul_mem' := by
    intro c f hf
    exact GibbsMeasure.ConfigurationSpace.IsCylinderFunction.smul (S := S) (E := E) (c := c) hf

/-- The submodule of **quasilocal functions**: the uniform closure of `cylinderFunctions`. -/
def quasilocalFunctions (S E F : Type*) [TopologicalSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Submodule ℝ ((S → E) →ᵇ F) :=
  (cylinderFunctions (S := S) (E := E) (F := F)).topologicalClosure

/-- A bounded continuous function is **quasilocal** if it belongs to `quasilocalFunctions`. -/
def IsQuasilocal (f : (S → E) →ᵇ F) : Prop :=
  f ∈ quasilocalFunctions (S := S) (E := E) (F := F)

@[simp] lemma mem_cylinderFunctions {f : (S → E) →ᵇ F} :
    f ∈ cylinderFunctions (S := S) (E := E) (F := F) ↔
      IsCylinderFunction (S := S) (E := E) (fun σ => f σ) := by
  rfl

@[simp] lemma mem_quasilocalFunctions {f : (S → E) →ᵇ F} :
    f ∈ quasilocalFunctions (S := S) (E := E) (F := F) ↔ IsQuasilocal f := by
  rfl

lemma cylinderFunctions_le_quasilocalFunctions :
    cylinderFunctions (S := S) (E := E) (F := F) ≤ quasilocalFunctions (S := S) (E := E) (F := F) :=
  Submodule.le_topologicalClosure _

lemma isQuasilocal_of_mem_cylinderFunctions {f : (S → E) →ᵇ F}
    (hf : f ∈ cylinderFunctions (S := S) (E := E) (F := F)) :
    IsQuasilocal f :=
  cylinderFunctions_le_quasilocalFunctions (S := S) (E := E) (F := F) hf

end BoundedContinuousFunction
