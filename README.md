# Schur–Weyl duality and Haar integration in Lean

This library formalizes Schur–Weyl duality, Haar averaging, and Weingarten calculus,
with computed moments and applications to quantum learning, classical shadows,
and magic monotones. It uses the Lean toolchain and dependencies pinned in
`lean-toolchain` and `lake-manifest.json`.

## Layout

| Location | Contents |
| --- | --- |
| `LeanHaar/` and `LeanHaar/TensorPower/` | Core tensor actions, matrix coordinates, commutation, double centralizers, Schur–Weyl duality, Weingarten systems, and Haar integration. |
| [SchurWeyl.lean](LeanHaar/SchurWeyl.lean) | Assembly of the Schur–Weyl duality theorem, formerly `Main.lean`. |
| [Moments](LeanHaar/Moments) | `k1Moment`, `k2Moment`, and `k4Moment`: evaluated Haar moment formulas. |
| [SupportingDocs](LeanHaar/SupportingDocs) | Shared tensor, trace, vectorization, Haar, and algebraic channel support. |
| [ForPhyslib](LeanHaar/ForPhyslib/POVM.lean) | Local POVM extensions intended for Physlib; no LeanHaar dependencies and not yet upstream. |
| [Applications](LeanHaar/Applications) | QML, ClassicalShadows, and MagicMonotone. |
| [Examples](LeanHaar/Examples) | Standalone `UnitaryCommutant`, `PauliTwirling`, and `EulerAngleIntegral` examples. |
| [notebooks](notebooks) | The symbolic fourth-moment coefficient calculation. |
| `blueprint/` | The current mathematical blueprint. `blueprintv1/` is historical. |

The Euler-angle example is an unnormalized coordinate integral; it does not prove
an identification with Haar measure. The Bloch expression in the Pauli example
is not automatically a positive density matrix for every real coefficient vector.

## Build and imports

```sh
lake build
```

The default target checks all source modules plus the root umbrella.
The library glob includes every module under `LeanHaar`, so future files are not
silently omitted from the build. The existing CI runs this target.

Import everything with `import LeanHaar`, or select only the needed module:

```lean
import LeanHaar.SchurWeyl
import LeanHaar.Haar
import LeanHaar.Moments.k2Moment
import LeanHaar.Applications.ClassicalShadows.SnapshotEnsemble -- Observation 58
import LeanHaar.Applications.ClassicalShadows.Observation59
```

The classical-shadow application has three files. `SnapshotEnsemble` contains the
finite algebra of Observation 58. `UnitarySnapshots` defines the Haar measurement
protocol and `haarShadow`; `Observation59` applies LeanHaar's `k2_moment` to evaluate
the channel, then proves the reconstructed shadow's Born-weighted Haar expectation
is the input state. Import `Observation59` for this complete Haar result.
The independent Pauli-shadow application is retired from the current scope and
remains in Git history. No generic protocol or reconstruction structure is added.

## Import migration

The former `ForMathlib` and `ForMathlibExamples` directories are removed; that
relocation preserved public declaration namespaces and mathematical statements.
The later classical-shadow consolidation and retirements are listed below.

| Former module prefix/path | Current location |
| --- | --- |
| `LeanHaar.SupportingDocs.POVM` | `LeanHaar.ForPhyslib.POVM`; retained declaration names are unchanged. |
| `LeanHaar.Applications.ClassicalShadows.HaarShadow` | Import `LeanHaar.Applications.ClassicalShadows.Observation59` for `haarShadow` and `haarShadow_unbiased`; their names and formulas are unchanged. |
| `LeanHaar.Applications.ClassicalShadows.PauliShadow` | Retired from the current scope; available in Git history. |
| `LeanHaar.ForMathlib.*` | `LeanHaar.*`; `Main` becomes `SchurWeyl`. |
| `LeanHaar.ForMathlib.ForMathlibExamples.k1Moment/k2Moment/k4Moment` | `LeanHaar.Moments.k1Moment/k2Moment/k4Moment`. |
| `LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.*` | `LeanHaar.SupportingDocs.*`. |
| `LeanHaar.ForMathlib.ForMathlibExamples.QML/ClassicalShadows/MagicMonotone.*` | `LeanHaar.Applications.QML/ClassicalShadows/MagicMonotone.*`. |

The unused `HilbertSpace` wrapper, `Example` smoke test, original wrapper-based
Schur example, and two duplicate Pauli-twirling implementations were retired.
Their history remains in Git. No forwarding modules preserve the old imports.

## Project notes

- [Definition inventory](DefsSummary.md)
- [Current cleanup and remaining work](TOOD.md)
- [Application dependency map and historical audits](Applications-dependencies.md)
- [Archived initial checklist](docs/history/InitialChecklist.md)

The blueprint still contains declaration references from earlier API versions;
checking the Lean build does not certify those references or the generated site.
