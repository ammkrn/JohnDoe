import Lake
open Lake DSL

package JohnDoe {
  -- add configuration options here
  dependencies := #[
    {
      name := `UsCourts
      src := Source.path "/Users/ammkrn_/UsCourts"
    },
    {
      name := `mathlib
      src := Source.git "https://github.com/leanprover-community/mathlib4.git" "master"
    }
  ]
  defaultFacet := PackageFacet.staticLib
}
