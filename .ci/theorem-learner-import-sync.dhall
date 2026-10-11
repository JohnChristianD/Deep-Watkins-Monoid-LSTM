let learnerModule : Text =
      "FullCoupled.CanonicalLearnerMonolith"
let learnerPath : Text =
      "FullCoupled/CanonicalLearnerMonolith.agda"
let learnerSpecModule : Text =
      "FullCoupled.LearnerLogicalSpec"
let learnerSpecPath : Text =
      "FullCoupled/LearnerLogicalSpec.agda"
let expectedSpecImport : Text =
      "import " ++ learnerSpecModule ++ " as LearnerLogicalSpec"
let theoremModule : Text =
      "FullCoupled.TheoremsMonolith"
let theoremPath : Text =
      "FullCoupled/TheoremsMonolith.agda"
let expectedImport : Text =
      "open import " ++ learnerModule ++ " as C"
in ''
#!/usr/bin/env bash
set -euo pipefail

learner="${learnerPath}"
learner_spec="${learnerSpecPath}"
theorem="${theoremPath}"
learner_module="module ${learnerModule} where"
learner_spec_module="module ${learnerSpecModule} where"
theorem_module="module ${theoremModule} where"
expected_import="${expectedImport}"
expected_spec_import="${expectedSpecImport}"

[ -f "$learner" ] || { echo "missing canonical learner: $learner"; exit 1; }
[ -f "$learner_spec" ] || { echo "missing learner logical spec: $learner_spec"; exit 1; }
[ -f "$theorem" ] || { echo "missing theorem monolith: $theorem"; exit 1; }

grep -Fqx "$learner_module" "$learner" || {
  echo "learner module declaration does not match Dhall contract"
  exit 1
}
grep -Fqx "$learner_spec_module" "$learner_spec" || {
  echo "learner logical spec module declaration does not match Dhall contract"
  exit 1
}
grep -Fqx "$theorem_module" "$theorem" || {
  echo "theorem module declaration does not match Dhall contract"
  exit 1
}

import_count=$(grep -Fxc "$expected_import" "$theorem")
[ "$import_count" -eq 1 ] || {
  echo "expected exactly one canonical learner import, found $import_count"
  exit 1
}
learner_spec_import_count=$(grep -Fxc "$expected_spec_import" "$theorem")
[ "$learner_spec_import_count" -eq 1 ] || {
  echo "expected exactly one learner logical spec import, found $learner_spec_import_count"
  exit 1
}

canonical_imports=$(grep -E "^(open )?import FullCoupled\\." "$theorem" || true)
unexpected_imports=$(printf '%s\\n' "$canonical_imports" | grep -Ev "^(open )?import FullCoupled\\.FormalMethods\\.|^open import FullCoupled\\.CanonicalLearnerMonolith as C$|^import FullCoupled\\.LearnerLogicalSpec as LearnerLogicalSpec$" || true)
[ -z "$unexpected_imports" ] || {
  echo "theorem monolith imports an unexpected FullCoupled semantic module:"
  printf '%s\\n' "$unexpected_imports"
  exit 1
}

echo "theorem-learner-import-sync=pass"
echo "learner_module=$learner_module"
echo "theorem_module=$theorem_module"
echo "theorem_import=$expected_import"
''
