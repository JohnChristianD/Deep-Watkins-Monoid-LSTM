{
  canonicalAgdaModules =
    [ "FullCoupled/CanonicalLearnerMonolith.agda"
    , "FullCoupled/TheoremsMonolith.agda"
    ],
  workflowLanes = [ "Policy", "AgdaLearner", "AgdaTheorem", "RUSS", "Pages", "All" ],
  graphSearchEnabled = False,
  browserJavaScriptEnabled = False,
  classicalLogicAssumed = False,
  fullRUSSConsistencyCertified = False,
  objectCalculusRelativeConsistencyImplemented = True
}
