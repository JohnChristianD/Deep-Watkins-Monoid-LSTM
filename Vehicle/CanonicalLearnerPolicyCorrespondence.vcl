type PolicyInput = Tensor Real [1]
type PolicyScore = Tensor Real [1]

@network
canonicalPolicyNetwork : PolicyInput -> PolicyScore

-- The Vehicle contract is intentionally phrased at the observable policy
-- boundary. The Agda bridge supplies the correspondence witness for the
-- canonical implementation.
policyAgreement : PolicyInput -> PolicyInput -> Bool
policyAgreement x y =
  x ! 0 == y ! 0 => canonicalPolicyNetwork x ! 0 == canonicalPolicyNetwork y ! 0

@property
canonicalPolicyBoundary : Bool
canonicalPolicyBoundary =
  forall x y . policyAgreement x y
