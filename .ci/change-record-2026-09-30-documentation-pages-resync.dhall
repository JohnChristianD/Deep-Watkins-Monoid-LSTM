{
  date = "2026-09-30",
  scope = "Markdown documentation index, Mirth-to-Elm presentation synchronization, and GitHub Pages recovery",
  request = "Audit the Markdown/Elm/Dhall/Mirth synchronization surfaces and repair the independently red GitHub Pages deployment.",
  affected_code = [
    "README.md",
    "docs/research/agda-auto-proof-search.md",
    "site/Main.elm",
    ".ci/readme-doc-sync.dhall",
    ".ci/presentation-contract.dhall",
    ".ci/mirth/agda_to_elm.mth",
    ".ci/actions_ci.dhall",
    ".github/workflows/github-pages.yml",
    ".ci/change-record-2026-09-29-ci-pages-verification.dhall"
  ],
  knowledge_delta = [
    ".ci/change-record-2026-09-30-documentation-pages-resync.dhall"
  ],
  changes = [
    "Broadened the README documentation index to all tracked Markdown outside internal .ci paths.",
    "Updated README and the Agda proof-search research note with the current proof-search and Pages synchronization boundaries.",
    "Changed the Mirth module declaration to package-qualified actions.agda_to_elm and reduced the generated surface to compiler-stable Agda module metadata.",
    "Repaired site/Main.elm by defining the missing moduleItem helper and consuming the generated module metadata.",
    "Narrowed the Dhall presentation contract and both Pages/Nix verification lanes to the stable generated field, while independently checking both canonical Agda module declarations.",
    "Recorded the prior Mirth failures accurately; the latest Pages run is the authoritative verification receipt."
  ],
  verification = [
    "GitHub Pages run 36669916012 compiled the simplified Mirth source successfully, then failed because the emitted binary lacked the executable bit.",
    "Nix connected-composition run 36669915957 reached the Pages presentation job on the same commit; its final receipt is pending at the time of this change.",
    "GitHub Pages run 36671154344 confirmed the corrected manifest is valid JSON, then failed because the generated project requested Elm 0.19.1 while the pinned Nix environment provides Elm 0.19.2.",
    "The remediation now declares Elm 0.19.2 in both generated application manifests so the Pages build matches the pinned compiler actually supplied by Nix.",
    "No green Pages deployment is claimed until the corrected standalone Pages workflow completes successfully."
  ],
  caveat = "Generated presentation metadata is synchronization/build data, not proof evidence. Agda --safe remains the only proof authority.",
  stale_when = "Update this record when the Mirth compiler module rules, generated Elm fields, Markdown indexing policy, or Pages deployment architecture changes."
}
