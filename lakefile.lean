import Lake
open Lake DSL

package «HopfieldNet» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «HopfieldNet» where
  -- add any library configuration options here

lean_lib MCMC where
  -- Builds the `MCMC.*` modules living under the top-level `MCMC/` directory.

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

--meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
