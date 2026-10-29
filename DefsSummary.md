# Definition summary and cleanup status

Updated: 2026-10-29. Original review: 2026-09-25.

The current `LeanHaar` source tree contains **101 active definitions, abbreviations,
and structures**, plus **14 explicit instances**, across 35 modules. This includes
private constructions, local instances, and the three retained standalone examples;
it excludes comments and ordinary theorems. The reorganization removed 18 definitions
and 10 instances from five obsolete files. All 32 previously maintained core,
support, moment, and application modules retain their mathematical content.

## Current scope

**Keep the core mathematics and build shared infrastructure for applications.**
Core modules now live directly under `LeanHaar` and `LeanHaar/TensorPower`; moments,
shared support, and applications live under `Moments`, `SupportingDocs`, and
`Applications`. Module moves changed imports, not core definitions or proofs.
See [README.md](README.md) for the import migration map.

- Keep the public `permAction`, `permOp`, and `diagAction` API. `permRep`,
  `PermModule`, and `permAlgHom` are private DCT implementation details. The
  separate public representation module remains deferred in its Git stash.
- Reuse the existing core matrix, vectorization, Gram, and Haar constructions.
  Their possible redesigns below are explicitly deferred.
- Put reusable application support in `LeanHaar/SupportingDocs`.
  Elementary support and the generic Haar bridge remain independent of computed
  moment formulas. Shared `HaarMoments` imports `Moments/k1Moment` and `Moments/k2Moment` to evaluate
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
| [SupportingDocs/TensorPowerBasics](LeanHaar/SupportingDocs/TensorPowerBasics.lean) | General permutation identity/composition/dual lemmas and `trace_id_tensV`, reused by the moment examples. No new definitions. |
| [SupportingDocs/Swap](LeanHaar/SupportingDocs/Swap.lean) | The existing `𝔽` definition, swap identities, matrix entries, and traces, extracted from the second-moment example and tensor traces. |
| [SupportingDocs/TensorPowerTraces](LeanHaar/SupportingDocs/TensorPowerTraces.lean) | The existing `tensorOp`, `tensorPow`, `conjBy`, and `matrixOf` definitions and their trace/conjugation API. It no longer imports `Moments/k1Moment` or `Moments/k2Moment`. |
| [SupportingDocs/Vectorization](LeanHaar/SupportingDocs/Vectorization.lean) | `SchurWeyl.inner_endVec_endVec`, `toEndMatrix_one`, and `toEndMatrix_mul`, extracted from MagicMonotone. It uses the existing core vectorization; no replacement vectorization is defined. |
| [SupportingDocs/RankOneCalculus](LeanHaar/SupportingDocs/RankOneCalculus.lean) | Generic rank-one sum composition and kernel theorems under `InnerProductSpace`. Summation bookkeeping is private; composition-of-sums helpers use Mathlib. No new definitions. |
| [SupportingDocs/HaarInvariance](LeanHaar/SupportingDocs/HaarInvariance.lean) | The existing four auxiliary Haar instances, compact-group invariance facts, and integration support. Each instance has one declaration. No new measure is defined. |
| [SupportingDocs/HaarMomentBridge](LeanHaar/SupportingDocs/HaarMomentBridge.lean) | Generic trace integrability and the trace/integral bridge formerly in `QML/MomentBridge`, now under `SchurWeyl`. No new moment operator is defined. |
| [SupportingDocs/HaarMoments](LeanHaar/SupportingDocs/HaarMoments.lean) | First and second Haar moments of arbitrary matrices, including `cId`, `cSwap`, contracted formulas, and the averaged squared-commutator trace. The algebraic commutator identity is private to its proof support; all public results use `SchurWeyl`. |
| [SupportingDocs/TraceContractions](LeanHaar/SupportingDocs/TraceContractions.lean) | Four bundled trace-contraction maps on formal tensors of endomorphisms, with evaluation lemmas, under `LinearMap`. `traceMulLeft` composes existing Mathlib maps. |
| [SupportingDocs/DepolarizingChannel](LeanHaar/SupportingDocs/DepolarizingChannel.lean) | The isotropic linear map, its candidate inverse, and the equivalence with proved inverse laws, under `LinearMap`. Both new support modules require only Mathlib. |

The existing `SupportingDocs` directory retains its name and now contains all
ten shared modules. The former `MagicMonotone/RankOneCalculus`,
`QML/MomentBridge`, and `QML/HaarMoments` paths are replaced by their supporting
modules. The former `QML/CommutatorTrace` is merged into shared `HaarMoments`;
`Swap` remains the elementary tensor-factor swap API. QML imports the shared evaluated Haar formulas; shadows imports its
required moment computation explicitly. The duplicate elementary
proofs in `Moments/k1Moment` and `Moments/k4Moment` now use the general shared API; the second
moment uses shared swap facts. QML expectation and square-moment statements now
spell out their integrals; their meanings, hypotheses, and scalar formulas are
preserved, including the order of the two iterated Haar integrals.

Validation of the current layout: plain `lake build` checks the 35 retained modules
and the root umbrella, including all three examples. The 32 previously maintained
modules were compared against their original bodies after path substitution.
Representative endpoint axiom reports are compared before and after relocation.
The existing Physlib dependency emits linter warnings; the Euler-angle example
emits two pre-existing tactic suggestions. See [TOOD.md](TOOD.md) for current work
and [Applications-dependencies.md](Applications-dependencies.md) for the module map
and explicitly historical audits.

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

Source: [TensorPower.lean](LeanHaar/TensorPower.lean).

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

Source: [DCT.lean](LeanHaar/DCT.lean).

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

Source: [TensorPower/Matrix.lean](LeanHaar/TensorPower/Matrix.lean).

| Definition | Meaning | Current assessment |
| --- | --- | --- |
| `tensorBasis` | Standard tensor-product basis. | **Keep the single canonical basis.** The primed duplicate is removed. |
| `toEndMatrix` | Linear equivalence giving matrix coordinates in that basis. | **Keep the current equivalence and conventions.** An algebra-equivalence redesign is deferred; application compatibility facts live in shared support. |

### PermutationCentralizer.lean — 1 private definition

Source: [PermutationCentralizer.lean](LeanHaar/PermutationCentralizer.lean).

| Definition | Meaning | Current assessment |
| --- | --- | --- |
| `pairCount` | Joint multiplicities of index pairs as finitely supported exponents. | **Keep private**, with the polynomial/orbit bookkeeping. The proof works for all dimensions. |

### Weingarten.lean — 2 definitions

Source: [Weingarten.lean](LeanHaar/Weingarten.lean).

| Definition | Meaning | Current assessment |
| --- | --- | --- |
| `permDual` | `permOp` evaluated at the inverse permutation. | **Keep.** Its matrix is the conjugate transpose of the permutation operator. |
| `endVec` | Vectorizes an endomorphism using its matrix entries. | **Keep the core implementation unchanged.** Shared vectorization theorems reuse it; consolidation with `endVecEquiv` is deferred. |

### WeingartenInverse.lean — 10 definitions

Source: [WeingartenInverse.lean](LeanHaar/WeingartenInverse.lean).

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

Source: [Haar.lean](LeanHaar/Haar.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `haarProb` | Haar measure normalized to mass one. | **Keep.** In the pinned Mathlib, `Measure.haar` has an arbitrary normalization, so this definition has a real purpose. |
| `endOf` | A matrix regarded as an endomorphism. | **Keep unchanged in core.** It is exactly `Matrix.toLin'`; replacement is deferred. |
| `actOn` | Conjugates an operator by the tensor power of a unitary. | **Keep.** This is a meaningful operation. A more descriptive name and linearity in the operator would improve the public API; restoring `unitaryAction` is not required. |
| `momentMatrix` | Entrywise integral defining the Haar-averaged matrix. | **Keep unchanged for now.** Making it private behind a public integral formula is a deferred core proposal. |
| `momentOp` | Haar twirling/moment operator. | **Keep as the principal public moment operator.** Linearity bundling and changes to the coordinate implementation are deferred. |

### SupportingDocs/TensorPowerTraces.lean — 4 definitions

Source: [TensorPowerTraces.lean](LeanHaar/SupportingDocs/TensorPowerTraces.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `tensorOp` | Tensor product of a family of matrix operators. | **Keep in shared application support.** Varying tensor factors are useful; the definition and its implementation remain unchanged. |
| `tensorPow` | Constant-family specialization of `tensorOp`. | **Keep as the existing matrix-facing specialization.** `diagAction_eq_tensorPow` already supplies the bridge; no core change or new wrapper is needed. Further simplification is optional. |
| `conjBy` | Matrix conjugation `U M U†`. | **Keep the shared conjugation interface for now.** An existing bundled conjugation API is a possible later application-level simplification, not part of this extraction. |
| `matrixOf` | Matrix of an endomorphism of a function space. | **Candidate for a later shared-layer simplification** using `LinearMap.toMatrix'`. Its definition remains unchanged in this pass. |

### SupportingDocs/Swap.lean — 1 definition

Source: [SupportingDocs/Swap.lean](LeanHaar/SupportingDocs/Swap.lean).

| Definition | Meaning | Current assessment |
| --- | --- | --- |
| `𝔽` | Swap operator on the two-factor tensor power. | **Keep the shared operator.** It was extracted from `Moments/k2Moment` without changing its name or definition. A searchable namespaced name such as `swapOp`, with scoped notation, remains optional later work. |

### SupportingDocs/HaarMoments.lean — 2 definitions

Source: [HaarMoments.lean](LeanHaar/SupportingDocs/HaarMoments.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `cId` | Identity coefficient in the second moment of `M ⊗ M`. | **Keep in shared Haar-moment support**, under `SchurWeyl`. The formula is unchanged; a more descriptive name remains optional. |
| `cSwap` | Corresponding swap coefficient. | **Same assessment.** Both depend on the input matrix and are not universal Weingarten values; the second-moment theorems retain their dimension assumptions. |

### SupportingDocs/TraceContractions.lean — 4 definitions

Source: [TraceContractions.lean](LeanHaar/SupportingDocs/TraceContractions.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `traceMulLeft` | Linear functional `X ↦ Tr(A X)`. | **Done:** compose `LinearMap.trace` and `LinearMap.mulLeft`; the implementation is definitionally equal to the original. Shared under `LinearMap`. |
| `partialTraceFirst` | Contracts the first factor against `ρ`. | **Keep with precise naming/documentation.** This acts on a tensor product of endomorphism spaces; the usual partial-trace interpretation needs a bridge. |
| `doubleTraceContract` | Product of two trace pairings extended linearly to tensors. | **Keep in shared support.** The existing tensor-map construction and its evaluation lemma are unchanged. |
| `tripleTraceContract` | Three-factor version. | **Keep in shared support.** Preserve the right-associated tensor and the existing evaluation lemma; no arbitrary-order abstraction is introduced. |

### SupportingDocs/DepolarizingChannel.lean — 3 definitions

Source: [DepolarizingChannel.lean](LeanHaar/SupportingDocs/DepolarizingChannel.lean).

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

`Moments/k1Moment.lean` and `Moments/k2Moment.lean` now contain no active definitions. They prove
their moment formulas using the shared tensor/swap API. `Moments/k4Moment` retains its
six application-specific coefficient constructions below.

### Moments/k4Moment.lean — 6 definitions

Source: [Moments/k4Moment.lean](LeanHaar/Moments/k4Moment.lean).

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

Source: [CostFunction.lean](LeanHaar/Applications/QML/CostFunction.lean).

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

The 2026-10-29 follow-up inlines `secondTensorMoment` and `thirdTensorMoment`
in the two Observation 58 identities, preserving their names, hypotheses, and formulas.

### SnapshotEnsemble.lean — 6 definitions/structures

Source: [SnapshotEnsemble.lean](LeanHaar/Applications/ClassicalShadows/SnapshotEnsemble.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `SnapshotEnsemble` | Weighted family of operator snapshots. | **Keep.** This is the arbitrary-field algebraic model. Physlib `MEnsemble` instead requires normalized probability weights and physical states, so it is not a replacement under these hypotheses. |
| `outcomeWeight` | `wₓ Tr(ρ Sₓ)`. | **Keep as an algebraic weight.** Positivity and normalization need additional hypotheses before it is a probability. |
| `measurementChannel` | Weighted trace-frame map. | **Keep.** `LinearMap` bundling expresses linearity. Physlib's POVM measurement maps require positive complete effects and have different output types or instrument formulas. |
| `invChannel` | Inverse measurement map under bijectivity. | **Keep.** Directly uses `LinearEquiv.ofBijective`; its name supports the estimator API. |
| `stateEstimator` | Inverse channel applied to a snapshot. | **Keep.** This is the classical shadow; it need not be positive, so a density-state codomain would be wrong. |
| `observableEstimator` | Trace pairing of an observable with the state estimator. | **Keep.** Expresses the estimated observable. Real-valuedness is separate mathematical work. |

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

Source: [UnitarySnapshots.lean](LeanHaar/Applications/ClassicalShadows/UnitarySnapshots.lean).

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

[Observation59](LeanHaar/Applications/ClassicalShadows/Observation59.lean)
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

Source: [SingleGateMoment.lean](LeanHaar/Applications/MagicMonotone/SingleGateMoment.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `vecMomentOp` | Fourth-moment formula as a sum of continuous rank-one operators. | **Keep the bundling.** Its genuine Haar-moment interpretation relies on `d ≥ 4`; the totalized rational formula does not supply the desired moment in smaller dimensions. |

### BrickworkLayers.lean — 28 definitions/abbreviations

Source: [BrickworkLayers.lean](LeanHaar/Applications/MagicMonotone/BrickworkLayers.lean).

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

Source: [Equation24.lean](LeanHaar/Applications/MagicMonotone/Equation24.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `twoLayerMoment` | Composition of the two layer operators. | **Keep.** Document composition order; inherit physical interpretation once layer bridges are established. |
| `twoLayerKernel` | Weighted contraction of interlayer overlaps. | **Keep.** A matrix-product formulation may simplify it. The ket families are not established as orthonormal bases, so avoid that interpretation. |

## Retained standalone examples

The user chose to preserve these three independent examples under descriptive
module names. The unused `HilbertSpace` wrapper and its original Schur example,
the `Example` smoke test, and the two duplicate root-namespace Pauli implementations
are removed. The older proofs remain available in Git history.

### Examples/UnitaryCommutant.lean — 1 definition

Source: [UnitaryCommutant.lean](LeanHaar/Examples/UnitaryCommutant.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `stdRep` | Standard two-dimensional unitary representation. | **Retained.** This is the representation used by the standalone irreducibility/Schur-lemma proof, independent of the tensor-power library. |

### Examples/EulerAngleIntegral.lean — 4 definitions

Source: [EulerAngleIntegral.lean](LeanHaar/Examples/EulerAngleIntegral.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `sigmaZ` | Explicit Pauli Z matrix. | **Retained unchanged in this coordinate example.** Reusing Physlib's matrix would be a separate proof cleanup. |
| `U` | Euler-angle matrix formula. | **Retained.** A descriptive namespace and unitarity theorem remain possible improvements. |
| `U_dagger` | Expanded conjugate-transpose formula. | **Retained.** Deriving this through conjugate transpose would avoid maintaining two coordinate formulas. |
| `haarIntegral` | Unnormalized angular integral with sine weight. | **Retained with explicit documentation.** Its constant mass is `8π²`; no identification with normalized Haar measure is proved. |

### Examples/PauliTwirling.lean — 2 definitions

Source: [PauliTwirling.lean](LeanHaar/Examples/PauliTwirling.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `pauliTwirl` | Namespaced four-Pauli conjugation average. | **Retained as the single implementation.** It reuses Physlib's Pauli matrices. |
| `blochState` | Bloch-form matrix with real coefficients. | **Retained with clarified documentation.** Positivity needs the unit-ball condition, which the algebraic twirl identity does not require. |

## Instance audit — 14 instances

Instances determine whether the definitions compose cleanly and are included
separately from the 103-definition count. This count includes the two local DCT
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
| Examples/UnitaryCommutant: `IsIrreducible stdRep` | **Retained.** Supports the preserved standalone Schur-lemma example. |

Sources for supporting instances: [HaarInvariance.lean](LeanHaar/SupportingDocs/HaarInvariance.lean)
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

The obsolete wrappers and duplicate prototypes are now removed. Further changes
to the three retained examples' definitions remain separate mathematical/API work;
their file moves did not alter their proofs.
