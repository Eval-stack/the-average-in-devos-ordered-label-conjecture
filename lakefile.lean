import Lake

open Lake DSL

package devosOrderedLabel where
  version := v!"0.1.0"

@[default_target]
lean_lib DeVos where
  roots := #[`Definitions, `devosProofStrong, `devosProofWeak, `devosNegation]
