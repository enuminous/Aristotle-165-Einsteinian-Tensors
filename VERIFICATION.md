# Reproducible Lean verification

Use the committed toolchain and dependency manifest. The workflow restores
applicable caches, builds the configured library, and audits every safe
declaration defined in the project modules listed in `Audit.lean`, including
private declarations. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Audit.lean
python3 scripts/test_axiom_audit.py
```

The rejection controls inject a public axiom, private axiom and placeholder proof
and require the audit to fail for the intended reason.
Native proof evaluation is rejected. The existing finite enumeration statements now use `decide +kernel`, so no native compiler axiom is admitted. No theorem statement or hypothesis was changed.

The successful job summary records the exact commit and workflow run. Source
declarations and hypotheses determine the mathematical scope; a successful
build does not validate a broader empirical or scientific interpretation.

The finite overlap proof sums 165 small fibers instead of reducing a materialized
27,060-pair product. The project library sets Lean's thread stack to 64 MiB via
`-s65536` for the pinned 4.28 toolchain; this addresses an observed stack overflow
without changing the statements, toolchain, dependencies, or permitted axioms.

`Verified.lean` remains the public import. Its declarations are split into a
sequential chain of `Verified.*` modules to bound peak compiler memory and expose
which check is running. The audit includes every module; theorem names and
statements are unchanged.
