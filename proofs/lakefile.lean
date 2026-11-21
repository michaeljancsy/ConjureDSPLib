import Lake
open Lake DSL

package «ConjureDSPLib» where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Aeneas's Lean library, from the pinned commit of the `conjure` branch of michaeljancsy/aeneas
-- (see PINS). scripts/prove.sh links `.toolchain/aeneas` to a checkout at that commit.
require aeneas from ".toolchain/aeneas/backends/lean"

-- FloatLib links Lean's Float to rounded real arithmetic. Its last Lean 4.35 version.
require FloatLib from git
  "https://github.com/lean-dojo/FloatLib" @ "acba2057e452f32f4ed4f06bb0adbeda5342ba92"

@[default_target] lean_lib «ConjureDSPLib» where
