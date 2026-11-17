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
| [Moments](LeanHaar/Moments) | `k1Moment`, `k2Moment`, and `k4Moment`, with matrix/trace corollaries in `TraceMoments`. |
| [Circuits](LeanHaar/Circuits) | Eight modules for register coordinates, local gates, schedules, Haar moments, disjoint layers and periodic brickwork. |
| [SupportingDocs](LeanHaar/SupportingDocs) | Six shared modules for tensor and trace identities, Haar invariance, and algebraic channels. |
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
import LeanHaar.Circuits.Brickwork
import LeanHaar.Applications.ClassicalShadows.SnapshotEnsemble -- Observation 58
import LeanHaar.Applications.ClassicalShadows.Observation59
import LeanHaar.Applications.MagicMonotone.HaarLayers
import LeanHaar.Applications.MagicMonotone.SingleGateMoment -- single-gate fourth-moment formulas
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
| `LeanHaar.PolyIndep` | `LeanHaar.PermutationCentralizer`; `monomial_coeff_zero_of_eval_zero` keeps its public global name. |
| `LeanHaar.Circuits.IndependentMoments` | `LeanHaar.Circuits.Circuit`; the independence theorem keeps its name and statement. |
| `LeanHaar.Circuits.UnitaryTensor` / `LeanHaar.SupportingDocs.UnitaryTensor` | `LeanHaar.Circuits.LocalGate`; the physical tensor construction and laws keep their names. |
| `LeanHaar.SupportingDocs.VectorizedHaar` | Retained action and Haar results are in `LeanHaar.Circuits.HaarMoment`; the unused tensor-averaging route is retired. |
| `LeanHaar.SupportingDocs.Vectorization` | Vectorization entry/inner-product lemmas are in `LeanHaar.Weingarten`; matrix compatibility remains in `LeanHaar.SupportingDocs.TensorPowerBasics`. Names and statements are unchanged. |
| `LeanHaar.SupportingDocs.HaarMomentBridge` | `LeanHaar.Haar`; declaration names and statements are unchanged. |
| `LeanHaar.SupportingDocs.HaarMoments` | General trace/integral bridge in `LeanHaar.Haar`; first/second matrix corollaries in `LeanHaar.Moments.TraceMoments`; inverse/commutator results in `LeanHaar.Applications.QML.CommutatorMoments`. Public names are unchanged. |
| `LeanHaar.SupportingDocs.RankOneCalculus` | `LeanHaar.Applications.MagicMonotone.RankOneCalculus`; declaration names and proofs are unchanged. |
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

The MagicMonotone coordinate aliases `bitsEquiv` and `regIndexEquiv` are now
`SchurWeyl.registerEquiv 2 4` and `SchurWeyl.copySiteEquiv 2 4 4`; write the former
`QubitIdx` type as `Fin 4 → Fin 4 → Fin 2`. The raw `regPermMat` construction and its
lemmas are private to `Circuits.SitePermutation`. Use `endVec_sitePerm_apply` for entries,
`sitePerm_one`/`sitePerm_mul` for composition, and `inner_endVec_sitePerm` for overlaps.
The application's `regPerm_one`, `regPerm_mul` and `hsOverlap_regPerm` remain available.

## Project notes

- [Module map and dependency diagrams](docs/ModuleMap.md)
- [Circuit and brickwork guide](docs/Brickwork.md)
- [Definition inventory](DefsSummary.md)
- [Current cleanup and remaining work](TOOD.md)
- [Application dependency map and historical audits](Applications-dependencies.md)
- [Archived initial checklist](docs/history/InitialChecklist.md)

The blueprint still contains declaration references from earlier API versions;
checking the Lean build does not certify those references or the generated site.
