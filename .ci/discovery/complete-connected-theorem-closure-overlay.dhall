{
  graph = "complete-connected-theorem-closure-overlay",
  status = "PARTIALLY_ESTABLISHED",
  strict_graph_invariant = "Only real Agda dependencies create graph edges; conceptual similarity never creates a dependency.",
  connected_survivors = {
    full_composition_hub = {
      name = "CanonicalFullCompositionGraphTheorem",
      status = "PROVED_ON_AGDA_SURFACE_PENDING_FRESH_CI",
      dependencies = [
        "CanonicalHaarRecurrentCompositionTheorem",
        "CanonicalGRUF4WatkinsPrefixCompositionTheorem",
        "CanonicalFullLearnerConnectedScanConjugacyTheorem",
        "CanonicalLearnerPermutationCompositionImpossibilityTheorem",
        "CanonicalPolymorphicSparsemaxCompositionTheorem"
      ],
      proof = "canonical-full-composition-graph-theorem",
      note = "One proof-relevant hub exposes the actual Haar-feature -> recurrent scan -> Watkins/F4 -> full learner composition without forcing unrelated theorem statements to depend on one another."
    },
    token_carrier = {
      name = "CanonicalToken",
      carrier = "ℤ",
      status = "PROVED_ON_AGDA_SURFACE",
      note = "The canonical token carrier is unbounded integer-valued; no fixed finite vocabulary cap is part of the canonical learner."
    },
    token_composition = {
      name = "CanonicalGlobalTokenLMCompositionTheorem",
      status = "PROVED_ON_AGDA_SURFACE_PENDING_FRESH_CI",
      parent = "CanonicalExactRNNLMTheorem",
      dependencies = [
        "CanonicalGlobalTokenEncodingConjugacyTheorem",
        "RecurrentPrefixMonoidHomomorphism",
        "canonicalTokenLogitTrace-append"
      ],
      proof = "canonical-global-token-lm-composition-theorem"
    },
    connected_endpoint = {
      name = "CanonicalPureNonOrangeBypassCompletionTheorem",
      status = "PROVED_ON_AGDA_SURFACE_PENDING_FRESH_CI",
      dependencies = [
        "RecurrentPrefixMonoidHomomorphism",
        "CanonicalFullLearnerConnectedScanConjugacyTheorem",
        "CanonicalExactCompositionTuringCompletenessContract",
        "CanonicalFiniteCycleExclusionIsomorphismTheorem",
        "CanonicalOperatorCompositionTheorem",
        "CanonicalF4GlobalOptimizerStabilityTheorem",
        "CanonicalIntegerHaarScaledOrthogonalityTheorem"
      ],
      proof = "canonical-pure-non-orange-bypass-completion-theorem"
    },
    finite_state_boundary = {
      name = "CanonicalFiniteStateRecurrentFunctionClass",
      status = "PROVED_ON_AGDA_SURFACE_PENDING_FRESH_CI",
      parameter = "n : Nat",
      carrier = "Fin n",
      note = "Generic finite-state pigeonhole remains valid for any explicit finite n; the former fixed finite-token carrier is retired."
    },
    learner_economic_welfare_bridge = {
      name = "connectedHodgeMaxwellLearnerEconomicWelfareBridge",
      status = "PROVED_ON_AGDA_SURFACE_PENDING_FRESH_CI",
      dependencies = [
        "ConnectedHodgeMaxwellGRUF4WatkinsEGraphCompositionTheorem",
        "megaEconomicSolutionStateIsomorphism",
        "megaEconomicSolutionStepConjugacy",
        "megaEconomicSolutionEquilibriumTransport",
        "megaSecondWelfareGeneralized"
      ],
      graphs = [
        ".ci/discovery/learner-economic-welfare-bridge-graph.md",
        ".ci/discovery/second-welfare-generalization-graph.md"
      ],
      note = "Exact learner/economic state isomorphism, step conjugacy, two-way equilibrium transport, and generalized welfare transport are now theorem functions rather than new certificate records."
    },
    policy_hodge_maxwell_update_seam = {
      name = "policyHodgeMaxwellCanonicalUpdateSeam",
      status = "PROVED_ON_AGDA_SURFACE_PENDING_FRESH_CI",
      dependencies = [
        "canonicalPolicy",
        "ConnectedHodgeMaxwellGRUF4WatkinsEGraphCompositionTheorem",
        "learnerToSolution",
        "learnerStepConjugacy",
        "policyHodgeMaxwellUpdateSeam"
      ],
      graph = ".ci/discovery/learner-economic-welfare-bridge-graph.md",
      note = "A supplied policy-induced learner update is required to be extensionally the canonical learner step; the existing learner-to-Hodge-Maxwell solution map and learner-step conjugacy then transport that update exactly to the Maxwell solution step."
    }
  },
  analytic_boundary = {
    convexity = "not implied by ℤ being an ordered unbounded ring",
    smoothness = "not implied by topology or discrete Z continuity",
    continuous_maxwell = "requires explicit differential-form/function-space/domain/metric/source/boundary semantics, continuity witnesses, exact encode/decode, and transition conjugacy; no finite carrier is assumed"
  },
  foundational_zero_dependency_policy = {
    rule = "Do not fabricate edges for problem specifications or foundational records.",
    examples = [
            "NonIIDMarkovWalrasianProblem",
      "Majority3ShapleyEquilibrium"
    ],
    handling = "They remain proof-surface/problem records until a real composed theorem consumes their semantics."
  },
  future_admission = {
    gates = [
      "actual Agda proposition",
      "real dependency into an existing composed consumer or explicit foundational status",
      "discoverability by theorem_graph_search",
      "e-graph synchronization",
      "strict separation only after inclusion, connected witness membership, and baseline nonrepresentability",
      "fresh --safe verification"
    ]
  },
  strict_separation_contract = {
    status = "CONTRACT_ADDED_NOT_PROVED",
    agda_records = [
      "FunctionClassInclusion",
      "StrictFunctionClassSeparation",
      "CanonicalStrictNeuralFunctionClassSeparationContract"
    ],
    gate = [
      "inclusion",
      "connected witness membership",
      "baseline nonrepresentability",
      "Agda --safe verification"
    ]
  },
  maxwell_hodge_boundary = {
    status = "CARRIER_POLYMORPHIC_CONTINUOUS_SEMANTICS",
    theorem_family = [
      "ContinuousHodgeMaxwellExactRepresentationData",
      "ConnectedContinuousHodgeMaxwellGRURepresentationTheorem",
      "ConnectedMaxwellTsallisExactConjugacyTheorem",
      "HodgeMaxwellMiddleDegreeInvolutionTransportTheorem",
      "ConnectedHodgeMaxwellTsallisDivergenceCompositionTheorem",
      "ConnectedHodgeMaxwellTsallisIdempotentProjectionTheorem",
      "ConnectedHodgeMaxwellTsallisWalrasianProjectionClosureTheorem",
      "hodgeMaxwell-globalEncode-noninjective-refutes-connected-representation",
      "ConnectedHodgeMaxwellGRUF4WatkinsGlobalEncodeInjectivityCompositionTheorem",
      "ConnectedCarrierAgnosticHodgeMaxwellGRUF4WatkinsEGraphCompositionTheorem",
      "ConnectedCarrierAgnosticHodgeMaxwellGRUF4WatkinsExactStepCompositionTheorem",
      "ConnectedCarrierAgnosticHodgeMaxwellGRUF4WatkinsExactPrefixHorizonRegretConjugacyEGraphCompositionTheorem"
    ],
    interpretation = "Maxwell and Hodge-Maxwell no longer depend on Fin n. The exact GRU carrier is arbitrary; continuity, global encode/decode, Maxwell equations, recurrent conjugacy, and Hodge involution prerequisites are explicit proof obligations.",
    universal_continuous_boundary = "The carrier-polymorphic Maxwell theorem remains conditional on explicit differential-form/function-space semantics, continuity witnesses, exact encode/decode, recurrent conjugacy, and any carrier-promotion evidence supplied by the caller.",
    global_injectivity = "The exact encode/decode laws yield a StateIsomorphism and an explicit global encode-injectivity theorem.",
    z_role = "ℤ remains the exact algebraic carrier for the canonical learner where applicable; it is not a universal carrier for arbitrary continuous Maxwell function spaces.",
    fin_dependency_pruning = "Continuous Hodge-Maxwell composition has no Fin n dependency; finite-function transport is not a prerequisite for the carrier-polymorphic representation.",
    noninjectivity_boundary = "An explicit encoder collision contradicts the connected exact representation certificate. A universal collision theorem for all continuous finite-dimensional Maxwell spaces remains unproved because no topological finite-dimensionality primitive exists on the current Agda surface.",
    unified_carrier_promotion = {
      theorem = "ConnectedCarrierAgnosticHodgeMaxwellGRUF4WatkinsEGraphCompositionTheorem",
      exact_step_theorem = "ConnectedCarrierAgnosticHodgeMaxwellGRUF4WatkinsExactStepCompositionTheorem",
      exact_endpoint = "ConnectedCarrierAgnosticHodgeMaxwellGRUF4WatkinsExactPrefixHorizonRegretConjugacyEGraphCompositionTheorem",
      status = "PROVED_ON_AGDA_SURFACE",
      physics_statement = "Composed Maxwell physics is represented by actual Agda dependencies; no new physical law is introduced or graph-hardcoded."
    }
  }
}
