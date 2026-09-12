# formal-gdt

A Lean 4 + Mathlib formalization of selected results from **ASME Y14.5.1-2019**
(*Mathematical Definition of Dimensioning and Tolerancing Principles*) and
**ASME Y14.5-2009** Nonmandatory Appendix B.

The development defines tolerance zones for six GD&T control types as predicates
over point sets in ℝ³, and proves the floating and fixed fastener assembly
formulas (`T = H − F` and `T = (H−F)/2`) together with matching sharpness
results, a machine-checked characterization of the fastener *tilt gap*, and two
containment chains formalizing the hierarchy of controls. Everything builds with
zero `sorry` and zero linter warnings.

## Building

```
lake exe cache get
lake build
```

Pinned versions (do not update mid-audit — the proofs are checked against these):

| | |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.35.0-rc1` |
| Mathlib revision | `09a9e06e4e5ccd5b783f25e52ad3ebecfb1e2d68` |

`lake build` completes in 2435 jobs.

## Traceability

Every definition is traceable to quoted text from the standard, collected in
[`Y14.5.1-definitions.md`](Y14.5.1-definitions.md). Where our formalization
departs from the standard's text — by generalizing, by restricting to one case,
or by supplying a model the standard does not state — the departure is recorded
in the doc comment on the definition itself. The table below is the index.

### Tolerance zone definitions

| Lean | File | Source |
|---|---|---|
| `satisfiesFlatness` | `GDT/Tolerance/Form.lean` | Y14.5.1 §5.4.2.1 |
| `satisfiesStraightness` | `GDT/Tolerance/Form.lean` | Y14.5.1 §5.4.1.1 |
| `satisfiesCircularity` | `GDT/Tolerance/Form.lean` | Y14.5.1 §5.4.3 |
| `satisfiesCylindricity` | `GDT/Tolerance/Form.lean` | Y14.5.1 §5.4.4 |
| `satisfiesPlanarOrientation` | `GDT/Tolerance/Orientation.lean` | Y14.5.1 §6.4.1 (datum-plane case) |
| `satisfiesCylindricalOrientation` | `GDT/Tolerance/Orientation.lean` | Y14.5.1 §6.4.2 (datum-axis case) |
| `satisfiesPosition` | `GDT/Tolerance/Position.lean` | Y14.5.1 §7.2.2, Table 7-3 (cylindrical zone, RFS) |
| `distToLine` | `GDT/Geometry/Line.lean` | projection residual; = `‖T̂ × (P⃗−A⃗)‖` by the bridge lemma |
| `holeClearsAt` | `GDT/Assembly.lean` | our clearance model for Y14.5-2009 App. B |
| `holeClearsTilted` | `GDT/Assembly.lean` | our tilt model for App. B §B.5 |

### Theorems

| Lean | File | Content |
|---|---|---|
| `distToLine_eq_norm_cross` | `GDT/Geometry/Line.lean` | **Bridge lemma**: projection residual = cross-product magnitude |
| `floating_fastener_sufficient` | `GDT/Assembly.lean` | App. B §B.3, `T = H − F` suffices |
| `floating_fastener_tight` | `GDT/Assembly.lean` | App. B §B.3 is sharp |
| `fixed_fastener_sufficient` | `GDT/Assembly.lean` | App. B §B.4, `T = (H−F)/2` suffices |
| `fixed_fastener_tight` | `GDT/Assembly.lean` | App. B §B.4 is sharp |
| `fixed_fastener_tilt_counterexample` | `GDT/Assembly.lean` | **The tilt gap**: §B.4 fails at its boundary under any nonzero tilt |
| `fixed_fastener_tilt_sufficient` | `GDT/Assembly.lean` | App. B §B.5 direction: the corrected bound restores the guarantee |
| `holeClearsTilted_one`, `one_lt_inv_cos` | `GDT/Assembly.lean` | tilt model grounding: `k = 1` is no tilt, `k = 1/cos α > 1` is tilt |
| `orientation_controls_flatness` | `GDT/Hierarchy.lean` | Y14.5.1 §6.2 |
| `orientation_controls_straightness` | `GDT/Hierarchy.lean` | Y14.5.1 §6.2 |
| `position_controls_cylindrical_orientation` | `GDT/Hierarchy.lean` | requires the true-position axis parallel to the datum |
| `satisfiesFlatness_iff`, `satisfiesPlanarOrientation_iff` | `GDT/Hierarchy.lean` | our scalar-offset form ≡ the standard's reference-point form |
| `cylindricity_implies_circularity_of_distToLine_eq_dist` | `GDT/Tolerance/Form.lean` | cross-sections inherit the tolerance |
| `bounded_deviation_flatness` | `GDT/Tolerance/Form.lean` | process capability δ ⟹ flatness 2δ |
| `*_monotone`, `*_subset` | throughout | each zone is monotone in `t` and inherited by subsets |

## What is *not* modelled

Read this before relying on anything here.

- **The assembly model abstracts features to points and scalars.** A hole is a
  center plus one radius; a fastener likewise. All form error is outside the
  model — an out-of-round hole, a bent fastener, and the interaction between form
  and position at MMC are not represented. Tilt is the one such effect we model,
  and we model it by inflating a scalar, not by representing geometry. The
  theorems hold over any `SeminormedAddCommGroup`, so the limitation is *not*
  dimensionality.
- **Six tolerance types only.** Profile of a line and of a surface, circular and
  total runout, concentricity, and symmetry are absent.
- **Datums are bare unit direction vectors.** No datum reference frame
  construction. Planar orientation models only the datum-plane case (`|sin θ|`)
  and cylindrical orientation only the datum-axis case (`|cos θ|`); the other
  case in each section is not formalized.
- **Position at RFS only.** No material-condition modifiers (MMC/LMC) and hence
  no bonus tolerance.
- **Straightness is stated for an arbitrary point set**, which is more general
  than §5.4.1.1's application to the derived median line; we do not formalize
  that construction, nor §5.4.1.3's cutting-plane constraints.
- **Everything is `noncomputable`.** These are specifications and metatheorems
  about specifications. No conformance-checking decision procedure is extracted,
  and evaluating conformance from measured CMM data is a separate (minimum-zone
  fitting) problem we do not address.
- **Tolerances are not constrained to be non-negative.** For `t < 0` and
  non-empty `S` the zone predicates are `False`, and for empty `S` vacuously
  `True`. The standard assumes `t ≥ 0` implicitly; the monotonicity theorems hold
  for all `t`, so we do not add the hypothesis.

## Licensing and the standards themselves

The Lean source, `paper.tex` and this README are MIT licensed (see `LICENSE`).

`Y14.5.1-definitions.md` collects the clause text each Lean definition
formalizes, quoted from ASME Y14.5.1-2019 and ASME Y14.5-2009 for reference and
commentary. Those passages are ASME's copyright, are **not** covered by the MIT
grant, and are not licensed for redistribution by this project. The standards
are sold by ASME at <https://www.asme.org/codes-standards>; the PDFs are
deliberately excluded from this repository.

## Paper

`paper.tex` — *Machine-Checked Proofs of the GD&T Fastener Formulas: A Lean 4
Formalization of ASME Y14.5.1*. Build with `pdflatex paper.tex` (twice, for
cross-references).
