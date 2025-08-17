import Lake
open Lake DSL

package "reap" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "openAI_client" from git "https://github.com/frenzymath/openai_client.git"

@[default_target]
lean_lib «Reap» where
  -- add any library configuration options here
