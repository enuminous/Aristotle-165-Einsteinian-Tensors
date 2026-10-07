# Fix Schedule

Status: audit-driven repair plan  
Repository: `enuminous/Aristotle-165-Einsteinian-Tensors`  
Prepared: 2026-10-06

## Goal

Turn this repository from a useful Aristotle export into a clean, reproducible formal-verification artifact that a fresh reviewer can clone, build, and audit without relying on Aristotle's temporary working directory or undocumented external files.

## Priority 0 — make the published Lean project build from a fresh clone

### P0.1 Restore the package layout
Create the directory structure expected by the current Lake configuration:

```
RequestProject/
  Verified.lean
  Upstream/
    Structure.lean
    Coupling.lean
    Ablations.lean
  Main.lean
```

Either move the current root files into that tree or rewrite the Lake configuration and imports consistently. Do not leave a mixed layout.

**Acceptance test:** `lake build` succeeds from a fresh clone.

### P0.2 Repair imports
`Ablations.lean` currently imports `RequestProject.Upstream.Structure`, but that path is absent in the published tree. Repair all module paths and make `Main.lean` import the verified modules so the default build exercises the actual theorem surface.

**Acceptance test:** removing or breaking any verified module causes `lake build` to fail.

### P0.3 Add CI
Add GitHub Actions for:

- Lean toolchain install
- `lake update` / dependency restore
- `lake build`
- search for `sorry`, `admit`, and `axiom` declarations added by this project
- optional `#print axioms` checks for the main exported theorems

**Acceptance test:** every push and pull request produces a visible green/red formal-build status.

---

## Priority 1 — restore reproducibility and provenance

### P1.1 Include or pin the audited source artifact
The reports refer to `EFMW_165_field_equations.txt`, but it is not present here.

Choose one:

1. include the exact source snapshot in this repository, or
2. record the exact repository, path, and commit SHA of the authoritative source.

Do not reference a moving branch such as `main` without a SHA.

### P1.2 Restore the audit script
The reports cite `scripts/audit_fieldspace.py`, but that script is absent.

Publish the exact script used to produce:

- 165 headings
- 165 populated blocks
- 585 displayed statements
- the 550 distinct coupling-symbol count
- the 56 ordered scalar-pair count

**Acceptance test:** one documented command reproduces those values.

### P1.3 Pin companion proofs
For claims delegated to `enuminous/EFMW_Post156_Zoo_Audit`, record the exact commit SHA containing:

- `fieldSpace_projected_atlas_gluing`
- `projected_atlas_gluing_unique`

Also pin the exact dependency commit(s) needed to build those theorems.

### P1.4 Correct path claims in documentation
Update `ARISTOTLE_SUMMARY.md` and `FIELDSPACE_VERIFICATION.md` so every referenced file path exists in the published repository, and clearly distinguish:

- proofs contained here,
- proofs contained in a pinned companion repository,
- script-derived observations,
- source-level claims not yet formalized.

---

## Priority 2 — tighten theorem scope

### P2.1 Separate grammar counts from source verification
FS-T05 proves the expected statement count for the formal grammar. It does not by itself prove that an external source file contains exactly those statements.

Use two explicit labels:

- **formal grammar theorem:** expected total = 585;
- **source audit result:** supplied source snapshot contains 585 statements.

Do not merge these claims.

### P2.2 Narrow FS-C02 wording
`bilinear_reciprocity` proves reciprocity for equations derived from the same bilinear term `λ φ_i φ_j`.

It does **not** prove that independently named source coefficients `λ_ij` and `λ_ji` are equal.

Document FS-C02 as:

> proved for a shared master-action bilinear term; source-level identification of directional coefficients remains an additional modeling condition unless derived from the full action.

### P2.3 Add an exported theorem index
Create a compact theorem register for this repository with, at minimum:

- theorem name
- FieldSpace ID
- file/module
- assumptions
- proof method
- status
- external dependency, if any
- physical interpretation boundary

---

## Priority 3 — formal closure targets

### P3.1 Formalize the master-action mapping
Prove, term by term, that the proposed master action generates the intended source equations for the sectors currently represented.

This is the real route from the narrow FS-C02 bilinear lemma to a general reciprocity result.

### P3.2 Define typed interaction objects
Introduce formal definitions for the currently unresolved mixed terms:

- `T^(int)`
- `Ξ`

with explicit domains/codomains and transformation behavior.

### P3.3 Conservation / Noether closure
Once the action and mixed objects are typed, state the exact assumptions required for FS-C03 and prove the resulting conservation identity.

Keep this as a mathematical theorem about the defined model, not as empirical validation.

### P3.4 Parameter economy
Turn FS-C04 into a precise equivalence-class or symmetry-reduction theorem. Explicitly distinguish:

- raw source symbols,
- independent parameters under reciprocity/symmetry,
- further reductions that require physical assumptions.

---

## Priority 4 — scientific validation boundary

Do not promote any formal result to a law of nature merely because Lean verifies the derivation.

For any physical claim, require:

1. units and dimensional consistency;
2. transformation laws;
3. named standard-model comparator;
4. quantitative prediction;
5. prespecified falsification criterion;
6. reproducible data/test harness.

The repository should continue to state explicitly that Lean establishes consequences of definitions and assumptions, not empirical truth.

---

## Recommended implementation order

1. Repair repository/package layout.
2. Make `lake build` exercise all verified modules.
3. Add CI.
4. Restore/pin source artifacts and audit script.
5. Correct documentation paths and provenance.
6. Publish theorem register.
7. Formalize full master-action reciprocity.
8. Define mixed interaction objects.
9. Attempt conservation closure.
10. Attempt parameter-economy theorem.
11. Only then open a separate empirical-validation phase.

## Completion criterion

This repair phase is complete when a reviewer can:

```bash
git clone ...
cd Aristotle-165-Einsteinian-Tensors
lake build
python scripts/audit_fieldspace.py
```

and independently recover the documented structural results, with every external theorem or source artifact pinned to an immutable commit and every physical interpretation clearly separated from the formal theorem statements.
