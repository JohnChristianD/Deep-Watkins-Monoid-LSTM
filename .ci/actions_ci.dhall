let Lane = < AgdaLearner | AgdaTheorem | Pages >

let scripts =
  { AgdaLearner =
      "nix develop .#agda-ci -c scsh -s .ci/scsh/ci-lanes.scsh AgdaLearner"
  , AgdaTheorem =
      "nix develop .#agda-ci -c scsh -s .ci/scsh/ci-lanes.scsh AgdaTheorem"
  , Pages =
      "nix develop .#presentation -c scsh -s .ci/scsh/ci-lanes.scsh Pages"
  }

in  { Lane = Lane
    , render = \(lane : Lane) -> merge scripts lane
    }
