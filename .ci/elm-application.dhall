{ type = "application"
, source_directories = [ "src" ]
, elm_version = "0.19.2"
, elm_dependencies =
    { direct =
        [ { mapKey = "elm/browser", mapValue = "1.0.2" }
        , { mapKey = "elm/core", mapValue = "1.0.5" }
        , { mapKey = "elm/html", mapValue = "1.0.0" }
        , { mapKey = "elm/svg", mapValue = "1.0.1" }
        ]
    , indirect =
        [ { mapKey = "elm/json", mapValue = "1.1.3" }
        , { mapKey = "elm/time", mapValue = "1.0.0" }
        , { mapKey = "elm/url", mapValue = "1.0.0" }
        , { mapKey = "elm/virtual-dom", mapValue = "1.0.3" }
        ]
    }
, test_dependencies =
    { direct = {=}
    , indirect = {=}
    }
}