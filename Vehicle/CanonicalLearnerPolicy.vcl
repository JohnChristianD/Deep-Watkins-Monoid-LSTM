type PolicyInput = Tensor Real [1]
type PolicyOutput = Tensor Real [1]

-- Logical-specification seam for the deployable policy component of the
-- canonical learner. The concrete network is supplied by Vehicle's @network
-- resource mechanism at export/verification time.
@network
canonicalPolicyNetwork : PolicyInput -> PolicyOutput

policyMonotone : PolicyInput -> PolicyInput -> Bool
policyMonotone x y =
  x ! 0 <= y ! 0 => canonicalPolicyNetwork x ! 0 <= canonicalPolicyNetwork y ! 0

@property
canonicalPolicyMonotonicity : Bool
canonicalPolicyMonotonicity =
  forall x y . policyMonotone x y
