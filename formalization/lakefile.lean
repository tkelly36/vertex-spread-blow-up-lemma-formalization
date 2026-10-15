import Lake
open Lake DSL

package «tablet» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Tablet» where
  srcDir := "."

require egorychevFalikmanFormalization from git
  "https://github.com/tkelly36/egorychev-falikman-formalization.git" @
    "8ede09b1840d24dd40ede7d12c4473cf4723c956" / "library"

require hajnalSzemerediFormalization from git
  "https://github.com/tkelly36/hajnal-szemeredi-formalization.git" @
    "ea2da77c281e40ec7f3e714a201b8d053d4ca619" / "library"

require entropyMethodsFormalization from git
  "https://github.com/tkelly36/entropy-methods-formalization.git" @
    "898fb2596141391cf64d456dd82798489cea85ef" / "library"

-- Keep the downstream project's Mathlib pin last so it governs the shared
-- transitive dependency graph of all three release packages.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "a090f46da78e9af11fee348cd7ee47bf8dd219d2"
