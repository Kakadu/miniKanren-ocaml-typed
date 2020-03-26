; Use `dune build config/tests.dune` to update dune file for tests

(executables
  (names
    %{tests}
  )
  (libraries GT OCanren OCanren.tester)
  (preprocess
    (action
      (run %{workspace_root}/src/pp5+ocanren.native
        %{input-file})
    )
  )
  ;(preprocessor_deps (file %{workspace_root}/camlp5/pa_ocanren.cma))
)


