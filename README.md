# Aristotle 165 — Einsteinian Tensor Atlas

This repository formalizes a finite three-sector atlas built from eleven sector labels. It contains Lean proofs of combinatorial properties and a small scalar-coupling algebra model. The dashboard in [`index.html`](index.html) expands all 165 triplets and offers an interactive residual calculator for that scalar model.

> **Scope:** this is not a complete physical equation solver. The repository does not include the full field-equation source, tensor components, units, boundary conditions, or numerical data needed to solve a physical system. The dashboard's “solver” evaluates the scalar residual defined in `Coupling.lean`; it does not solve Einstein or matter field equations.

## Open the dashboard

Open `index.html` directly in a modern browser, or publish the repository root with GitHub Pages. The dashboard runs entirely in the browser and has no build step or external dependency.

The dashboard provides:

- all `C(11, 3) = 165` triplets, generated in the sector order used by `Verified.lean`;
- filters by sector, profile, and free-text query;
- the six Lean-verified profile counts;
- a statement inventory for each triplet, following the grammar in `Verified.lean`;
- an interactive scalar residual and ablation calculator following `Coupling.lean`.

The displayed statement text is an inventory label, not the missing source equation itself. No exact physical equation is invented or implied.

## Sector atlas

| Symbol | Kind |
| --- | --- |
| `E` | Gravity |
| `M`, `S` | Gauge |
| `F`, `W`, `T`, `I`, `R`, `H`, `P`, `A` | Scalar |

The six profiles partition the atlas:

| Gravity `E` present | Gauge sectors | Scalar sectors | Triplets |
| --- | ---: | ---: | ---: |
| No | 0 | 3 | 56 |
| No | 1 | 2 | 56 |
| Yes | 0 | 2 | 28 |
| Yes | 1 | 1 | 16 |
| No | 2 | 1 | 8 |
| Yes | 2 | 0 | 1 |
| **Total** |  |  | **165** |

## Formal results

`Verified.lean` defines the finite sector type and the set of every three-element subset, then proves:

| ID | Result | Lean declaration |
| --- | --- | --- |
| FS-T01 | The atlas has 165 triplets. | `triplets_card` |
| FS-T02 | Each sector occurs in 45 triplets. | `sector_incidence` |
| FS-T03 | Each distinct sector pair occurs together in 9 triplets. | `pair_incidence` |
| FS-T04 | The six profiles have counts `56 + 56 + 28 + 16 + 8 + 1 = 165` and exhaust the atlas. | `class_counts`, `classes_exhaustive` |
| FS-T05 | The formal grammar inventory totals 585 statements. | `statement_inventory` |
| FS-T06 | Removing `k` sectors leaves `C(11-k, 3)` triplets. | `ablation` |
| FS-T07 | The unordered distinct-triplet overlap counts (sharing 2, 1, or 0 sectors) are `1980`, `6930`, and `4620`. | `overlap_spectrum` |

Under the grammar encoded in `Verified.lean`, each triplet contributes one Einstein statement when `E` is present, two statements per gauge sector (dynamics and Bianchi), and one statement per scalar sector. Summed over the atlas, this gives `45 + 180 + 360 = 585`. These are proven grammar counts; they do not establish that an external source contains 585 corresponding equations. The source snapshot and audit script cited by prior reports are not included in this repository.

`Coupling.lean` defines the generic scalar expression

```text
R = base + λᵢⱼ φⱼ + λᵢₖ φₖ + λᵢⱼₖ φⱼ φₖ
```

and proves reductions when either field is set to zero, the disappearance of the trilinear term on either null slice, shared-pair overlap consistency on a null slice, and exact subtraction of the trilinear contribution. The dashboard computes this expression for user-entered real numbers; it is a model demonstrator, not a PDE/ODE integrator or a validated physical solver.

The candidate master-action reciprocity result is narrow: `Verified.lean` proves equality of cross-derivative coefficients when both equations arise from the same bilinear potential term. It does not prove equality of independently specified directional source coefficients. Other proposed consistency laws and physical interpretations remain candidates or require additional assumptions and evidence.

## Repository files

| File | Role |
| --- | --- |
| `Verified.lean` | Finite atlas, structural theorems, grammar inventory, and a bilinear reciprocity lemma. |
| `Structure.lean` | Structural arithmetic statements from the Aristotle export. |
| `Coupling.lean` | Scalar residual algebra and null-slice/ablation lemmas. |
| `Ablations.lean` | Ablation-related Lean statements. |
| `Main.lean` | Project entry point from the export. |
| `ARISTOTLE_SUMMARY.md`, `FIELDSPACE_VERIFICATION.md` | Project and verification notes. |
| `FIX_SCHEDULE.md` | Audit-driven repair plan for reproducible builds and provenance. |
| `index.html` | Standalone atlas dashboard and scalar algebra calculator. |

## Build status and reproducibility

The current published Lean project layout has known fresh-clone build issues documented in [`FIX_SCHEDULE.md`](FIX_SCHEDULE.md). In particular, the Lake configuration expects a `RequestProject/` package tree, while the Lean files are at the repository root; `Ablations.lean` also imports a module path not present in the published tree, and `Main.lean` does not import the full verified theorem surface. The schedule describes the repair and acceptance criterion. No green `lake build` result is claimed here.

The dashboard is independent of Lean and can be opened without installing anything. Reproducing the proofs requires fixing the project layout and then running `lake build` from a fresh clone as described in the schedule.

## Research boundary and collaboration

Lean verifies consequences of definitions and assumptions. It does not establish that a model describes nature. Physical validation would additionally require precise tensor definitions and transformation laws, dimensional consistency, a named comparator, quantitative predictions, a prespecified falsification test, and reproducible data or a test harness.

Contributions are welcome, especially on:

1. repairing the package/import layout and adding CI;
2. adding the pinned source snapshot and reproducible audit script;
3. connecting source equations to typed formal objects;
4. extending the formal model with explicit assumptions and proof obligations;
5. designing empirical tests that can distinguish predictions from standard models.

Please include the exact definitions, assumptions, and a reproducible check with proposed theorem or physics changes. Do not present structural counts as empirical evidence.

## License and attribution

Consult the repository license and source history for reuse terms and provenance. The initial project was edited with [Aristotle](https://aristotle.harmonic.fun); see the existing project notes for attribution guidance.
