# Definition summary and cleanup status

Updated: 2026-10-01. Original review: 2026-09-25.

The current `LeanHaar` source tree contains **121 active definitions, abbreviations,
and structures**, plus **24 explicit instances**. This inventory includes private
constructions, local instances, and the older prototype files. It excludes
commented-out declarations and ordinary theorems. The original review counted
134 definitions; the core cleanup removed six, and replacing the four QML
expectation/square-moment wrappers with explicit integrals removed another four.
The classical-shadow cleanup removed the estimator-variance wrapper, the one-use
trace-symmetry predicate, and the scalar third-moment wrapper.

## Current scope

**Keep the core as it is and build shared infrastructure for applications.** The
core means the `ForMathlib` modules outside `ForMathlibExamples`. The latest
application extraction did not change any core Lean file.

- Keep the public `permAction`, `permOp`, and `diagAction` API. `permRep`,
  `PermModule`, and `permAlgHom` are private DCT implementation details. The
  separate public representation module remains deferred in its Git stash.
- Reuse the existing core matrix, vectorization, Gram, and Haar constructions.
  Their possible redesigns below are explicitly deferred.
- Put reusable application support in `ForMathlibExamples/SupportingDocs`.
  Elementary support and the generic Haar bridge remain independent of computed
  moment formulas. Shared `HaarMoments` imports `k1Moment` and `k2Moment` to evaluate
  matrix averages. No supporting module imports QML, ClassicalShadows, or MagicMonotone.
- Keep application coefficients, circuit vocabulary, and ensemble definitions
  in their applications unless a concrete reuse case warrants extraction.

Completed before this shared-layer extraction: the duplicate tensor bases and
matrix conversions were consolidated in `TensorPower/Matrix`; the polynomial
proof moved to `PermutationCentralizer`; `permOp` moved beside `permAction`; and
DCT adapters became private. `permMonoidHom`, `centralizer_to_endModule`, the
primed coordinate duplicates, and the old `DirectProof`/`SmallDim` modules are
removed. DCT semisimplicity and density proofs are now private theorems.

## Shared application layer — completed

| Module | Current contents and role |
| --- | --- |
| [SupportingDocs/TensorPowerBasics](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerBasics.lean) | General permutation identity/composition/dual lemmas and `trace_id_tensV`, reused by the moment examples. No new definitions. |
| [SupportingDocs/Swap](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/Swap.lean) | The existing `𝔽` definition, swap identities, matrix entries, and traces, extracted from the second-moment example and tensor traces. |
| [SupportingDocs/TensorPowerTraces](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean) | The existing `tensorOp`, `tensorPow`, `conjBy`, and `matrixOf` definitions and their trace/conjugation API. It no longer imports `k1Moment` or `k2Moment`. |
| [SupportingDocs/Vectorization](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/Vectorization.lean) | `SchurWeyl.inner_endVec_endVec`, `toEndMatrix_one`, and `toEndMatrix_mul`, extracted from MagicMonotone. It uses the existing core vectorization; no replacement vectorization is defined. |
| [SupportingDocs/RankOneCalculus](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/RankOneCalculus.lean) | Generic rank-one sum composition and kernel theorems under `InnerProductSpace`. Summation bookkeeping is private; composition-of-sums helpers use Mathlib. No new definitions. |
| [SupportingDocs/HaarInvariance](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/HaarInvariance.lean) | The existing four auxiliary Haar instances, compact-group invariance facts, and integration support. Each instance has one declaration. No new measure is defined. |
| [SupportingDocs/HaarMomentBridge](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/HaarMomentBridge.lean) | Generic trace integrability and the trace/integral bridge formerly in `QML/MomentBridge`, now under `SchurWeyl`. No new moment operator is defined. |
| [SupportingDocs/HaarMoments](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/HaarMoments.lean) | First and second Haar moments of arbitrary matrices, including `cId`, `cSwap`, contracted formulas, and the averaged squared-commutator trace. The algebraic commutator identity is private to its proof support; all public results use `SchurWeyl`. |
| [SupportingDocs/TraceContractions](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TraceContractions.lean) | Four bundled trace-contraction maps on formal tensors of endomorphisms, with evaluation lemmas, under `LinearMap`. `traceMulLeft` composes existing Mathlib maps. |
| [SupportingDocs/DepolarizingChannel](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/DepolarizingChannel.lean) | The isotropic linear map, its candidate inverse, and the equivalence with proved inverse laws, under `LinearMap`. Both new support modules require only Mathlib. |

The existing `SupportingDocs` directory retains its name and now contains all
ten shared modules. The former `MagicMonotone/RankOneCalculus`,
`QML/MomentBridge`, and `QML/HaarMoments` paths are replaced by their supporting
modules. The former `QML/CommutatorTrace` is merged into shared `HaarMoments`;
`Swap` remains the elementary tensor-factor swap API. QML imports the shared evaluated Haar formulas; shadows imports its
required moment computation explicitly. The duplicate elementary
proofs in `k1Moment` and `k4Moment` now use the general shared API; the second
moment uses shared swap facts. QML expectation and square-moment statements now
spell out their integrals; their meanings, hypotheses, and scalar formulas are
preserved, including the order of the two iterated Haar integrals.

Validation of the initial extraction: all 36 then-existing modules built without
warnings, with an acyclic import graph and 12 unchanged endpoint axiom reports.
The QML consolidation built 35 modules and passed six old-statement compatibility
checks. The classical-shadow cleanup now builds all 32 remaining modules without
warnings. Seven retained endpoint statements and axiom reports match the original
baseline, and eleven moved definitions pass identity checks. The deliberate helper
API reductions are recorded below. Older prototype files are included in the
inventory, but this build result does not certify them. See [TOOD.md](TOOD.md)
for completed work and [ForMathlibExamples-dependencies.md](ForMathlibExamples-dependencies.md)
for the dependency audit; its original reference tables remain historical.

## Review criteria

“Mathlib standard” here means reusing existing constructions, choosing appropriate
bundled structures, controlling assumptions, and providing clear names and a
coherent API. See Mathlib's [style guide](https://leanprover-community.github.io/contribute/style.html)
and [naming conventions](https://leanprover-community.github.io/contribute/naming.html).
These principles do not require definitions and their basic lemmas to live in
separate files. **Keep** means that a definition earns its place, not necessarily
that it is ready for upstream submission. Existing-API comparisons were made
against this repository's pinned Mathlib source.

## Core algebra — retained unchanged

The tables below describe the current definitions. Suggestions to replace or
rebundle a core construction are deferred; the application shared layer uses
the existing API.

### TensorPower.lean — 6 definitions

Source: [TensorPower.lean](LeanHaar/ForMathlib/TensorPower.lean).

| Definition | Meaning | Current assessment |
| --- | --- | --- |
| `TensV` | Tensor power of `ℂᵈ`. | **Keep.** Generalizing beyond this concrete tensor space is later work. |
| `permAction` | Tensor-factor permutations as a monoid homomorphism into linear equivalences. | **Keep as the underlying action.** Its bundled laws supply the operator identities. |
| `permOp` | Underlying linear endomorphism of `permAction`. | **Keep as the public operator interface.** It is derived directly from `permAction`; a public representation wrapper is unnecessary for current applications. |
| `permImage` | Set of permutation operators. | **Keep.** Used in span and centralizer statements. |
| `diagAction` | Sends an endomorphism to its tensor power, as a monoid homomorphism. | **Keep.** This construction is generally not additive in the input endomorphism. |
| `diagImage` | Set of tensor powers of endomorphisms. | **Keep.** It ranges over all endomorphisms, as required by the polynomial proof. |

`diagActionUnits`, `glAction`, `unitaryAction`, and their conversion lemmas remain
commented out. Restore a wrapper only if a concrete consumer needs its additional
structure; the current application extraction introduces none.

### DCT.lean — 4 private definitions

Source: [DCT.lean](LeanHaar/ForMathlib/DCT.lean).

| Definition | Meaning | Current assessment |
| --- | --- | --- |
| `permRep` | Permutation representation derived from `permAction` through Mathlib's standard conversion. | **Keep private.** Required by the Maschke/density proof. |
| `PermModule` | Group-algebra module associated with `permRep`. | **Keep private.** Uses `Representation.asModule`. |
| `permAlgHom` | Induced group-algebra action. | **Keep private**, with its range/span helpers. |
| `doubleCentralizerToEndEndModule` | Converts a double-centralizer element into an endomorphism over the endomorphism ring. | **Keep private.** Serves the DCT proof. |

`permModule_isSemisimple` and `permModule_toModuleEnd_surjective` are private
theorems, not definitions. `permMonoidHom` and `centralizer_to_endModule` were
removed. Both DCT-specific instances are local; the reusable finite-dimensionality
instance lives beside the tensor basis.

### TensorPower/Matrix.lean — 2 definitions

Source: [TensorPower/Matrix.lean](LeanHaar/ForMathlib/TensorPower/Matrix.lean).

| Definition | Meaning | Current assessment |
| --- | --- | --- |
| `tensorBasis` | Standard tensor-product basis. | **Keep the single canonical basis.** The primed duplicate is removed. |
| `toEndMatrix` | Linear equivalence giving matrix coordinates in that basis. | **Keep the current equivalence and conventions.** An algebra-equivalence redesign is deferred; application compatibility facts live in shared support. |

### PermutationCentralizer.lean — 1 private definition

Source: [PermutationCentralizer.lean](LeanHaar/ForMathlib/PermutationCentralizer.lean).

| Definition | Meaning | Current assessment |
| --- | --- | --- |
| `pairCount` | Joint multiplicities of index pairs as finitely supported exponents. | **Keep private**, with the polynomial/orbit bookkeeping. The proof works for all dimensions. |

### Weingarten.lean — 2 definitions

Source: [Weingarten.lean](LeanHaar/ForMathlib/Weingarten.lean).

| Definition | Meaning | Current assessment |
| --- | --- | --- |
| `permDual` | `permOp` evaluated at the inverse permutation. | **Keep.** Its matrix is the conjugate transpose of the permutation operator. |
| `endVec` | Vectorizes an endomorphism using its matrix entries. | **Keep the core implementation unchanged.** Shared vectorization theorems reuse it; consolidation with `endVecEquiv` is deferred. |

### WeingartenInverse.lean — 10 definitions

Source: [WeingartenInverse.lean](LeanHaar/ForMathlib/WeingartenInverse.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `gramMatrix` | Matrix of inner products of a vector family. | **Keep for now; replacement deferred.** `Matrix.gram` and its invertibility results are candidates for a later core pass. |
| `gramVec` | Inner products of a vector against a family. | **Keep unchanged.** Further bundling or extraction of this generic core infrastructure is deferred. |
| `gramSolutionSet` | Solutions of the Gram linear system. | **Reasonable when public theorems discuss the whole solution set.** Otherwise an equation or fiber of a linear map may suffice. |
| `matrixEntriesEquiv` | Uncurries a matrix into a function on pairs. | **Keep for now; replacement deferred.** The appropriate direction of `LinearEquiv.curry` could replace the handwritten construction in a later core pass. |
| `endVecEquiv` | Bundled linear equivalence implementing vectorization. | **Keep the existing bundled vectorization.** Relocation and consolidation with `endVec` are deferred. |
| `endVecₗ` | Linear-map projection of `endVecEquiv`. | **Keep the existing projection.** It has consumers; removing or changing this convenience definition is deferred. |
| `weingartenGram` | Trace-pairing Gram matrix of permutation operators. | **Keep unchanged.** A connection to `Matrix.gram` is a later core task. |
| `weingartenVec` | Trace pairings of an operator with permutation operators. | **Keep unchanged.** Additional bundling is deferred until a consumer needs it. |
| `weingartenGramNat` | Natural-number counting version of the Gram matrix. | **Keep.** It has distinct computational value. |
| `weingartenSolutionSet` | Solutions of the specialized Weingarten system. | **Keep.** It specifies the current Weingarten system, including singular cases; restructuring the general solution API is deferred. |

The current `endVec` uses a different coordinate ordering from Mathlib's
`Matrix.vec`. A direct substitution would change conventions; transpose/reindexing
must be accounted for.

## Haar and shared application definitions

### Haar.lean — 5 definitions

Source: [Haar.lean](LeanHaar/ForMathlib/Haar.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `haarProb` | Haar measure normalized to mass one. | **Keep.** In the pinned Mathlib, `Measure.haar` has an arbitrary normalization, so this definition has a real purpose. |
| `endOf` | A matrix regarded as an endomorphism. | **Keep unchanged in core.** It is exactly `Matrix.toLin'`; replacement is deferred. |
| `actOn` | Conjugates an operator by the tensor power of a unitary. | **Keep.** This is a meaningful operation. A more descriptive name and linearity in the operator would improve the public API; restoring `unitaryAction` is not required. |
| `momentMatrix` | Entrywise integral defining the Haar-averaged matrix. | **Keep unchanged for now.** Making it private behind a public integral formula is a deferred core proposal. |
| `momentOp` | Haar twirling/moment operator. | **Keep as the principal public moment operator.** Linearity bundling and changes to the coordinate implementation are deferred. |

### SupportingDocs/TensorPowerTraces.lean — 4 definitions

Source: [TensorPowerTraces.lean](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `tensorOp` | Tensor product of a family of matrix operators. | **Keep in shared application support.** Varying tensor factors are useful; the definition and its implementation remain unchanged. |
| `tensorPow` | Constant-family specialization of `tensorOp`. | **Keep as the existing matrix-facing specialization.** `diagAction_eq_tensorPow` already supplies the bridge; no core change or new wrapper is needed. Further simplification is optional. |
| `conjBy` | Matrix conjugation `U M U†`. | **Keep the shared conjugation interface for now.** An existing bundled conjugation API is a possible later application-level simplification, not part of this extraction. |
| `matrixOf` | Matrix of an endomorphism of a function space. | **Candidate for a later shared-layer simplification** using `LinearMap.toMatrix'`. Its definition remains unchanged in this pass. |

### SupportingDocs/Swap.lean — 1 definition

Source: [SupportingDocs/Swap.lean](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/Swap.lean).

| Definition | Meaning | Current assessment |
| --- | --- | --- |
| `𝔽` | Swap operator on the two-factor tensor power. | **Keep the shared operator.** It was extracted from `k2Moment` without changing its name or definition. A searchable namespaced name such as `swapOp`, with scoped notation, remains optional later work. |

### SupportingDocs/HaarMoments.lean — 2 definitions

Source: [HaarMoments.lean](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/HaarMoments.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `cId` | Identity coefficient in the second moment of `M ⊗ M`. | **Keep in shared Haar-moment support**, under `SchurWeyl`. The formula is unchanged; a more descriptive name remains optional. |
| `cSwap` | Corresponding swap coefficient. | **Same assessment.** Both depend on the input matrix and are not universal Weingarten values; the second-moment theorems retain their dimension assumptions. |

### SupportingDocs/TraceContractions.lean — 4 definitions

Source: [TraceContractions.lean](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TraceContractions.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `traceMulLeft` | Linear functional `X ↦ Tr(A X)`. | **Done:** compose `LinearMap.trace` and `LinearMap.mulLeft`; the implementation is definitionally equal to the original. Shared under `LinearMap`. |
| `partialTraceFirst` | Contracts the first factor against `ρ`. | **Keep with precise naming/documentation.** This acts on a tensor product of endomorphism spaces; the usual partial-trace interpretation needs a bridge. |
| `doubleTraceContract` | Product of two trace pairings extended linearly to tensors. | **Keep in shared support.** The existing tensor-map construction and its evaluation lemma are unchanged. |
| `tripleTraceContract` | Three-factor version. | **Keep in shared support.** Preserve the right-associated tensor and the existing evaluation lemma; no arbitrary-order abstraction is introduced. |

### SupportingDocs/DepolarizingChannel.lean — 3 definitions

Source: [DepolarizingChannel.lean](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/DepolarizingChannel.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `depolarizingChannel` | Linear map `(Tr(X) I + X)/(δ+1)`. | **Keep the bundled algebraic map in shared support, under `LinearMap`.** It is a particular isotropic formula, not the full parameterized family of physical depolarizing channels. |
| `depolarizingChannelInv` | Candidate inverse `(δ+1)X − Tr(X)I`. | **Keep.** Inverse status appropriately depends on subsequent hypotheses. |
| `depolarizingChannelEquiv` | Linear equivalence under those hypotheses. | **Keep.** Stronger bundled structure earns a separate definition here. |

The pinned Physlib revision `d150395878c339df15a7a8d264ec73f352ec88ae`
([manifest](lake-manifest.json)) has no named depolarizing-channel construction.
It does provide `CPTPMap`, identity and replacement channels, convex mixtures, and
`MState.uniform`. Over `ℂ^d`, for `d > 0`, the formula corresponds to mixing the
identity with replacement by `I/d`, using identity weight `1/(d+1)`. That connection
is not proved here. A future physical-channel layer should reuse those bundles;
our arbitrary-field linear equivalence is not a bundled CPTP map, and its inverse
need not be positive. The definition fixes the noise coefficient via `δ` rather
than exposing an independent noise parameter.

The other five shared modules contain supporting theorems or instances;
they do not introduce more definitions or alternate core constructions.

## Low-order moments and QML

`k1Moment.lean` and `k2Moment.lean` now contain no active definitions. They prove
their moment formulas using the shared tensor/swap API. `k4Moment` retains its
six application-specific coefficient constructions below.

### k4Moment.lean — 6 definitions

Source: [k4Moment.lean](LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `numCyc` | Number of cycles, including fixed points. | **Connect to the existing permutation partition API.** A generic cycle-count bridge is more reusable than an isolated `S₄` counter. |
| `ctIdx` | Natural-number encoding of the five cycle types. | **Private certificate helper, or use a finite type.** Public `Nat` admits meaningless tags. |
| `Pden` | Polynomial denominator factor for the fourth-order formula. | **Private helper.** Use a descriptive lowerCamelCase name if public. |
| `wgNum` | Numerator selected by a cycle-type tag. | **Improve the input type.** Out-of-range tags currently fall into a default case; a finite enumeration expresses the intended domain. |
| `wgVal` | Explicit fourth-order Weingarten rational formula. | **Keep with clear validity conditions.** Lean's division makes it total at denominator zeros, but those values are not the intended Haar formula. Existing `d ≥ 4` hypotheses matter. |
| `coeff` | Weingarten expansion coefficient for an operator. | **Keep with a more descriptive name.** State the dimension range prominently; expose linearity only if useful. |

These are API interpretation issues, not evidence that theorems with appropriate
dimension assumptions are false.

### QML/CostFunction.lean — 2 definitions

Source: [CostFunction.lean](LeanHaar/ForMathlib/ForMathlibExamples/QML/CostFunction.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `cost` | Trace expectation after unitary conjugation. | **Keep as an application definition.** Add real-valuedness under appropriate Hermitian/density assumptions. |
| `gradient` | Commutator trace expression intended to represent a derivative. | **Needs a mathematical bridge.** Either name it as a gradient formula/component or prove the derivative theorem for a parameterized circuit. |

`haarExp`, `haarExp₂`, `haarVar`, and `haarVar₂` are removed. The cost moment
theorems and Observations 56/57 use ordinary Haar integrals directly. The variance
statements retain the complex square-moment difference `E[X²] − E[X]²`; identifying
it with Mathlib's real-valued variance still requires real-valuedness and
square-integrability proofs. No replacement expectation or variance API is added.

## Classical shadows

The application consists of three modules: `SnapshotEnsemble`, `UnitarySnapshots`,
and `Observation59`. The two finite-ensemble identities of Observation 58 belong
with their definitions in `SnapshotEnsemble`; there is no separate `Observation58`
module. `UnitarySnapshots` defines the physical model and its elementary laws;
Observation59 owns its evaluated Haar results. Generic trace contractions and
isotropic-map inversion live in `SupportingDocs`.

The follow-up adversarial review corrected the initial cleanup, which moved files
without finishing declaration ownership. The pair-index helpers
`toEndMatrix_id_pair` and `toEndMatrix_swap_pair` are deleted: existing matrix and
finite-function lemmas prove the contractions directly. The one remaining
application-specific contraction lemma is private in Observation59. There is no
`MomentContraction` file. The two trivial dimension aliases use Mathlib directly,
and `SupportingDocs/TraceNotation` is removed. The application and the two extracted
support modules now use `LinearMap.trace` directly, with no replacement local notation.

Three one-use wrappers are removed: `observableEstimatorVariance`,
`IsTraceSelfAdjoint`, and scalar `thirdMoment`. The original expressions now occur
in the relevant statements. `secondMoment_observableEstimator` is now a private
scalar calculation; its documentation explains the one Born-weight trace factor
and the two estimator trace factors. `measurementChannel_apply`, a redundant
`rfl` evaluation rule in this minimal API, is removed; the contraction proof
unfolds `measurementChannel` directly. The seven retained public endpoint
statements preserve their hypotheses, formulas, conjugation order, and dimension
restrictions. These are intentional reductions of the helper API, not a claim
that every former public name remains available.

### SnapshotEnsemble.lean — 8 definitions/structures

Source: [SnapshotEnsemble.lean](LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/SnapshotEnsemble.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `SnapshotEnsemble` | Weighted family of operator snapshots. | **Keep.** This is the arbitrary-field algebraic model. Physlib `MEnsemble` instead requires normalized probability weights and physical states, so it is not a replacement under these hypotheses. |
| `outcomeWeight` | `wₓ Tr(ρ Sₓ)`. | **Keep as an algebraic weight.** Positivity and normalization need additional hypotheses before it is a probability. |
| `measurementChannel` | Weighted trace-frame map. | **Keep.** `LinearMap` bundling expresses linearity. Physlib's POVM measurement maps require positive complete effects and have different output types or instrument formulas. |
| `invChannel` | Inverse measurement map under bijectivity. | **Keep.** Directly uses `LinearEquiv.ofBijective`; its name supports the estimator API. |
| `stateEstimator` | Inverse channel applied to a snapshot. | **Keep.** This is the classical shadow; it need not be positive, so a density-state codomain would be wrong. |
| `observableEstimator` | Trace pairing of an observable with the state estimator. | **Keep.** Expresses the estimated observable. Real-valuedness is separate mathematical work. |
| `secondTensorMoment` | Weighted sum of `Sₓ ⊗ Sₓ`. | **Keep with its contraction theorem in this module.** It is the finite sum `∑ₓ wₓ Sₓ ⊗ Sₓ`, not the Haar conjugation operator `momentOp`. |
| `thirdTensorMoment` | Weighted sum of right-associated threefold snapshot tensors. | **Keep beside the second moment and estimator theorem.** Its right association and arbitrary-field formulation are unchanged. |

Probability normalization here uses completeness such as `∑ₓ wₓ Sₓ = I`, together
with positivity and a density state. Merely requiring `∑ₓ wₓ = 1` is insufficient.
The trace-symmetry assumption is written explicitly; there is no replacement
self-adjointness API built solely for this application. The two endpoint theorems
remain separate because they describe different objects and require different
hypotheses; combining them into a conjunction would obscure that distinction.
The finite moments live in tensors of endomorphisms, whereas `momentOp` averages
an endomorphism of a complex tensor state space over Haar measure. `diagAction`
and `tensorPow` form tensor-power operators but do not average them.

### UnitarySnapshots.lean — 5 definitions

Source: [UnitarySnapshots.lean](LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean).

All five definitions appear together before the two elementary projector laws
and the tensor-power orbit identity. This module imports no computed moment
formula. The former single-consumer tensor-trace aliases are removed; their
consumer uses the shared tensor-trace theorems directly.

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `basisProjector` | Rank-one projector onto a computational basis vector. | **Keep here.** It anchors the measurement protocol and directly uses `Matrix.single` and `Matrix.toLin'`. Physlib's `MState.pure (Ket.basis b)` represents the same physical object in a different codomain. |
| `unitarySnapshot` | Conjugated computational-basis projector `U† P_b U`. | **Keep here.** Physlib provides unitary conjugation on matrices/states, but using it here requires an explicit matrix-to-endomorphism bridge. Preserve the `star U` orientation. |
| `unitarySnapshotMoment` | Sum of Haar-averaged tensor powers of basis projectors. | **Keep.** It is unnormalized over basis outcomes and has no state-dependent Born weight. |
| `haarMeasurementChannel` | Actual Born-weighted, entrywise Haar integral. | **Moved from Observation59.** This defines the physical model; Observation59 evaluates it. Bundling its linearity directly remains separate work. |
| `haarMeasurementChannelEquiv` | Explicit invertible isotropic map. | **Moved from Observation59.** Useful access to the inverse, constructed through shared algebra. Defined for every `d`; equality with the integral channel is currently proved for `d ≥ 2`. |

### Observation59.lean — no definitions

[Observation59](LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean)
now owns `unitarySnapshotMoment_two`: it applies the existing `k2_moment` to each
projector tensor square, then sums the `d` equal contributions. It does not
reprove the general second-moment result. Consumers of this corollary import
Observation59 rather than the model module. The entrywise contraction, evaluation
of the integral channel for `d ≥ 2`, and inverse identification follow there.

The finite model uses tensors of endomorphisms; the Haar model uses endomorphisms
of `TensV`. No identification between these spaces or formal instantiation of
the finite-ensemble theorems by the continuous Haar model is proved. Such bridges,
positivity, normalization, and statistical variance interpretation are additional mathematics,
not consequences of reorganizing files.

## Magic monotone and brickwork applications

Fixed four-copy/four-qubit choices are acceptable application vocabulary; they
need not all become generic Mathlib definitions.

### SingleGateMoment.lean — 1 definition

Source: [SingleGateMoment.lean](LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `vecMomentOp` | Fourth-moment formula as a sum of continuous rank-one operators. | **Keep the bundling.** Its genuine Haar-moment interpretation relies on `d ≥ 4`; the totalized rational formula does not supply the desired moment in smaller dimensions. |

### BrickworkLayers.lean — 28 definitions/abbreviations

Source: [BrickworkLayers.lean](LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `Copies` | Four replica labels. | **Keep application shorthand.** |
| `Qubits` | Four qubit labels. | **Keep**, but it is definitionally the same type as `Copies`; the names do not prevent mixing them. |
| `QubitReg` | One qubit's indices across copies. | **Keep.** |
| `QubitIdx` | Qubit-indexed collection of copy indices. | **Keep.** |
| `Reg` | Register indices across copies. | **Keep.** |
| `RegOp` | Endomorphisms of the replicated register. | **Keep.** Direct use of the standard endomorphism type. |
| `Vecs` | Euclidean space of vectorized operator entries. | **Keep**, though a more descriptive public name would help. |
| `PermPair` | Pair of copy permutations. | **Keep.** Useful canonical index type. |
| `bitsEquiv` | Equivalence between register labels and bit strings. | **Keep.** Good reuse of Mathlib's finite-function equivalence. |
| `regIndexEquiv` | Reorganizes register/copy indices into qubit/copy indices. | **Keep.** Appropriate composition of existing equivalences. |
| `regPermMat` | Matrix for independent copy permutations on qubits. | **Keep the operation**, considering the standard permutation-matrix API. Check multiplication orientation. |
| `shift` | Private row-to-column index calculation. | **Appropriately private.** Could be one direction of a single index equivalence. |
| `regPerm` | Corresponding register endomorphism. | **Keep.** Bundle as a monoid homomorphism if composition is central to the API. |
| `gateOn` | Copy permutation supported on chosen qubits. | **Keep**, clarifying that it is a replica permutation operator, not a physical unitary gate parameter. |
| `V12` | Specialization to qubits 1–2. | **Keep as application vocabulary.** Paper notation can be scoped over a descriptive name. |
| `V34` | Specialization to qubits 3–4. | **Same assessment.** |
| `V23` | Specialization to qubits 2–3. | **Same assessment.** |
| `V41` | Specialization across the periodic boundary. | **Same assessment**, documenting the boundary convention. |
| `hsOverlap` | Inner product of vectorized endomorphisms. | **Keep as application vocabulary.** Its general trace identity now comes from `SupportingDocs/Vectorization`; the wrapper itself need not move into the core. |
| `relabel` | Private inverse index calculation. | **Appropriately private.** Prefer the inverse of the same equivalence underlying `shift`. |
| `layerAKet` | Vectorized permutation operator for layer A. | **Keep one canonical family**, preferably indexed by `PermPair`. |
| `layerBKet` | Corresponding family for layer B. | **Same assessment.** |
| `wg` | Fourth-order Weingarten value at gate dimension four. | **Reasonable local specialization.** A transparent abbreviation or local notation may suffice. |
| `layerA` | Rank-one expansion of layer A's moment operator. | **Keep.** Good continuous-linear-map bundling. No independent product-Haar-integral identification for the whole layer was found in the audit. |
| `layerB` | Corresponding layer B operator. | **Same assessment.** |
| `ketA` | Pair-indexed wrapper around `layerAKet`. | **Merge the interfaces.** Choose one canonical argument convention. |
| `ketB` | Pair-indexed wrapper around `layerBKet`. | **Merge likewise.** |
| `wgPair` | Product of two gate weights. | **Keep.** An explicit matrix on `PermPair` may simplify contractions. |

### Equation24.lean — 2 definitions

Source: [Equation24.lean](LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/Equation24.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `twoLayerMoment` | Composition of the two layer operators. | **Keep.** Document composition order; inherit physical interpretation once layer bridges are established. |
| `twoLayerKernel` | Weighted contraction of interlayer overlaps. | **Keep.** A matrix-product formulation may simplify it. The ket families are not established as orthonormal bases, so avoid that interpretation. |

## Older library and prototype files

These need a separate maintenance decision and should not determine the current
core's architecture.

### HilbertSpace.lean — 5 definitions/structures

Source: [HilbertSpace.lean](LeanHaar/HilbertSpace.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `FiniteHilbertSpace` | One-field structure wrapping `EuclideanSpace`. | **Strong candidate for removal.** It adds no mathematical data or distinct semantics while requiring transported instances. Use `EuclideanSpace` unless a specific abstraction boundary is intended. |
| `equivEuclidean` | Underlying equivalence with `EuclideanSpace`. | **Only needed because of the wrapper.** |
| `linearEquivEuclidean` | Linear version of that equivalence. | **Only needed because of the wrapper.** |
| `isometryEquivEuclidean` | Linear isometry equivalence with `EuclideanSpace`. | **Strongest useful bridge if the wrapper stays.** Obtain weaker views from projections where possible. |
| `basisFun` | Transported standard orthonormal basis. | **Use the existing Euclidean-space basis if the wrapper goes.** The transport itself is reasonable. |

The module documentation describes an abbreviation indexed by a natural number,
but the implementation is a structure indexed by a finite type.

### Example.lean — 2 definitions

Source: [Example.lean](LeanHaar/Example.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `hello` | Template string. | **Remove from public library imports.** |
| `basicAdd` | Wrapper around natural-number addition. | **Remove or keep only as an isolated tutorial/test.** |

### Commutants1D-SchursLemma.lean — 2 definitions

Source: [Commutants1D-SchursLemma.lean](LeanHaar/Examples/Commutants1D-SchursLemma.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `UnitaryGroup` | Linear isometric automorphisms of the Hilbert space. | **Legitimate shorthand**, without requiring the custom Hilbert-space wrapper. Generalize to an inner-product space if reused. |
| `unitaryRep` | Natural unitary representation. | **Keep if this proof remains.** It is consumed by Schur/irreducibility machinery, so the wrapper has a concrete purpose. |

### Commutants1D-SchursLemmaV2.lean — 1 definition

Source: [Commutants1D-SchursLemmaV2.lean](LeanHaar/Examples/Commutants1D-SchursLemmaV2.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `stdRep` | Standard two-dimensional unitary representation. | **Keep as an example or consolidate the approaches.** Full generality is not required of a deliberately two-dimensional example. |

### Moments.lean — 4 definitions

Source: [Moments.lean](LeanHaar/Examples/Moments.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `sigmaZ` | Explicit Pauli Z matrix. | **Reuse Physlib's object**, or make it private to a pedagogical example. |
| `U` | Euler-angle matrix formula. | **Use a descriptive namespaced name**, and prove or bundle unitarity if used as a unitary. |
| `U_dagger` | Manually expanded conjugate-transpose formula. | **Define through `star U`/conjugate transpose** rather than maintaining another coordinate formula. |
| `haarIntegral` | Unnormalized angular integral with sine weight. | **Rename or establish the measure bridge.** Its constant mass is `8π²`; it is not a normalized Haar expectation. Coordinate integration alone does not prove the Haar interpretation. |

### Twirling.lean — 6 definitions

Source: [Twirling.lean](LeanHaar/Examples/Twirling.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `pauliI` | Identity matrix. | **Use `1`.** |
| `pauliX` | Pauli X. | **Reuse the existing definition**, or keep private to a standalone example. |
| `pauliY` | Pauli Y. | **Same assessment.** |
| `pauliZ` | Pauli Z. | **Same assessment.** |
| `pauliTwirl` | Average of four Pauli conjugations. | **Keep one canonical implementation.** Bundle linearity if promoted to public infrastructure. |
| `blochState` | Bloch-form matrix with complex coefficients. | **Rename as a matrix expression or restrict parameters.** Arbitrary complex coefficients do not ensure Hermiticity or positivity. |

### Twirling-Physlib.lean — 3 definitions

Source: [Twirling-Physlib.lean](LeanHaar/Examples/Twirling-Physlib.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `pauliI` | Identity matrix again. | **Use `1`.** |
| `pauliTwirl` | Another Pauli-twirl implementation. | **Consolidate the versions.** |
| `blochState` | Another complex-coefficient Bloch expression. | **Same physical-domain issue and duplication.** |

This file and `Twirling.lean` export overlapping root-level names, so they are not
a coherent jointly importable library.

### TwirlingPhyslibV2.lean — 2 definitions

Source: [TwirlingPhyslibV2.lean](LeanHaar/Examples/TwirlingPhyslibV2.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `pauliTwirl` | Namespaced version using existing Pauli matrices. | **Best starting point for consolidation.** Keep one implementation. |
| `blochState` | Bloch expression with real coefficients. | **Improved, but not necessarily a state.** Positivity additionally requires the Bloch vector to be in the unit ball. |

## Instance audit — 24 instances

Instances determine whether the definitions compose cleanly and are included
separately from the 121-definition count. This count includes the two local DCT
instances; shared application support retains each instance once.

| Location / instances | Assessment |
| --- | --- |
| TensorPower/Matrix: `tensV_module_finite` | **Done: keep beside the tensor basis.** Globally available without importing DCT. |
| DCT: `neZero_card_perm` | **Done: local instance.** Characteristic-zero/Maschke support. |
| DCT: `permModule_finite_over_endRing` | **Done: local instance.** Technical density-theorem support. |
| Haar: `instCompactSpaceUnitaryGroup` | **Keep.** Genuine structural fact; generalization to other finite index types is deferred. |
| Haar: `instSecondCountableMatrix` | **Keep the current bridge.** Direct inference with existing Haar imports failed without it. |
| Haar: `instMeasurableSpaceUnitaryGroup`, `instBorelSpaceUnitaryGroup` | **Keep until a tested canonical replacement exists.** Inference failed without these. General subtype APIs alone do not justify deleting them. |
| Haar: `instIsProbabilityMeasureHaarProb`, `instIsMulLeftInvariantHaarProb` | **Keep.** Appropriate properties of the named measure. |
| SupportingDocs/HaarInvariance: `instIsHaarMeasureHaarProb` | **Done: keep in shared application support.** The core Haar file is unchanged. |
| SupportingDocs/HaarInvariance: `instInnerRegularHaarProb` | **Retained unchanged.** A later redundancy check may use Mathlib inference; no instance was removed during extraction. |
| SupportingDocs/HaarInvariance: `instIsMulRightInvariantHaarProb`, `instIsInvInvariantHaarProb` | **Done: keep in shared application support**, each declared once. |
| HilbertSpace: `AddCommGroup`, `Module`, `NormedAddCommGroup`, `InnerProductSpace`, `FiniteDimensional`, `CompleteSpace`, `Nontrivial` | All seven are appropriate **if the wrapper remains**. All become unnecessary when using `EuclideanSpace` directly. |
| Original Schur example: local group-algebra `Module`, local `IsScalarTower` | **Check standard `Representation.asModule` instances.** Avoid duplicates unless required by a specific instance-resolution problem. |
| Original Schur example: `unitary_irreducible` | **Keep.** A mathematical result appropriately exposed as a proposition instance. |
| Schur V2: `IsIrreducible stdRep` | **Keep**, subject to deciding which example/proof is maintained. |

Sources for supporting instances: [HaarInvariance.lean](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/HaarInvariance.lean)
and the corresponding modules linked above.

## Remaining work within the application scope

These are review candidates, not changes already implemented:

1. **Shared conveniences:** assess whether `matrixOf`, `conjBy`, or `tensorPow`
   would become clearer by using existing constructions more directly. Preserve
   useful application names and conversion equations; do not change core `endOf`,
   `diagAction`, or the vectorization implementation for this work.
2. **Fourth-moment API:** review the cycle-type tags and private certificate
   helpers, retain explicit `wgVal` formulas and dimension assumptions, and connect
   `coeff` to `weingarten_solution_eq_inv` with an application theorem if useful.
3. **Circuit interfaces:** choose one argument convention for each pair of
   `layerAKet`/`ketA` and `layerBKet`/`ketB`. Keep readable gate labels and weights.
   General register embeddings should wait for another circuit consumer.
4. **Mathematical interpretation:** clarify QML `gradient` and the square-moment
   variance formulas, preserve the algebraic ensemble layer, and distinguish the
   defined circuit layer sums from a proved independent-gate Haar average. Actual
   derivative, probability, or layer-identification theorems are additional
   mathematical work; moving definitions alone does not establish them.
5. **Classical-shadow interpretation bridges:** relate the formal tensor
   contractions to endomorphisms of the tensor-product state space, and connect
   the Haar model to Physlib's existing physical-state, POVM, and CPTP interfaces.
   Preserve the algebraic inverse, which need not be positive. The named
   trace-symmetry wrapper was removed; do not recreate it without another consumer.

## Deferred core and prototype work

The earlier suggestions to replace `gramMatrix`, `matrixEntriesEquiv`, or `endOf`,
rebundle `toEndMatrix`/`endVec`/`momentOp`, hide `momentMatrix`, generalize the base
field/module, or restore GL/unitary representation wrappers are deferred under
the current decision to keep the core unchanged. There is no pending task to
restore the stashed public permutation representation module.

The older Hilbert-space wrapper and Pauli/twirling prototypes need a separate
maintenance decision. Their review entries above remain a backlog, not a reason
to expand the current application-infrastructure scope.
