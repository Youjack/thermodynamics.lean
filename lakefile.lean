import Lake
open Lake DSL

package «thermodynamics» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here
  moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.5.0"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.0.2"

@[default_target]
lean_lib «Thermodynamics» where
  -- add any library configuration options here
