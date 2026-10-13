{
  date = "2026-09-29",
  scope = "Canonical learner executable entrypoint, Mirth module synchronization, and unused Tsallis theorem-wrapper pruning",
  request = "Make the canonical learner executable, fix the Mirth module/file-name mismatch, and prune only Tsallis theorem declarations in TheoremsMonolith that have no surviving dependents.",
  affected_code = [
    "Main.agda",
    "Exotic/ERL/FullCoupled/TheoremsMonolith.agda",
    ".ci/mirth/agda_to_elm.mth",
    ".ci/actions_ci.dhall",
    ".github/workflows/nix-composition.yml"
  ],
  before = {
    executable = "CanonicalLearnerMonolith.agda was --safe proof-checked but had no standalone main entrypoint.",
    mirth = ".ci/mirth/agda_to_elm.mth declared module actions.agda-to-elm, which did not match the tracked filename.",
    tsallis = "TheoremsMonolith contained Tsallis-specific wrapper declarations with no surviving references outside that local section; generic carrier-polymorphic injectivity facts still had later dependents."
  },
  change = {
    executable = "Added Main.agda with a concrete canonical FullLearnerKernel and FullLearnerState, one canonicalFullStep evaluation, and a Main/IO entrypoint.",
    mirth = "Changed the Mirth top-level module declaration to agda_to_elm so it matches agda_to_elm.mth.",
    tsallis = "Removed only zero-reference Tsallis wrappers: TsallisCompatibleStatisticalRepresentation, tsallisCompatibleEncodeInjective, tsallisCompatibleEncodeDistinguishes, canonicalGRUTsallisCompatibleRepresentation, canonicalGRUTsallisCompatibleInjective, and canonicalGRUTsallisCompatibleDistinguishability.",
    verification = "Added a dedicated CI lane and workflow step that safe-checks, compiles, and runs Main.agda."
  },
  now = {
    proof_authority = "CanonicalLearnerMonolith.agda and TheoremsMonolith.agda remain the proof monoliths.",
    executable = "Main.agda is an execution adapter and is not part of theorem-source extraction.",
    tsallis = "No removed Tsallis wrapper remains in TheoremsMonolith; CarrierPolymorphicStatisticalRepresentation and its generic injectivity/distinguishability facts remain because later ZPF theorems depend on them."
  },
  why = "Restore the failing Mirth source-synchronization surface, expose a real executable harness for the canonical learner semantics, and remove dead Tsallis wrappers without deleting shared statistical infrastructure.",
  business_intent = "_Unknown - ask the owner and record the answer._",
  product_intent = "The repository exposes a directly compilable learner entrypoint while preserving the existing proof-source boundary.",
  alternatives = [
    "Embedding IO in CanonicalLearnerMonolith was rejected to keep theorem semantics independent of the executable adapter.",
    "Removing the generic statistical representation kernel was rejected because later ZPF representation theorems still depend on it."
  ],
  compatibility = "The change is additive except for deletion of six zero-reference Tsallis wrappers inside TheoremsMonolith.",
  operational_consequence = "CI now compiles and runs an Agda executable. Main-generated MAlonzo output and the native binary are removed after execution.",
  verification = "Final verification must use GitHub Actions exit codes for the changed Agda, executable, Mirth, and surface checks.",
  future_implications = "Any future CLI behavior must remain an adapter over canonical learner definitions and must not duplicate learner semantics.",
  stale_when = "Update this record if executable entrypoint semantics, Mirth source layout, or statistical representation dependencies change."
}