# Definition audit

Recorded: 2026-09-25, from the repository-wide review discussed on 2026-09-24.

This document records the original review; the follow-up note identifies completed
work. Its scope is the
`LeanHaar` source tree, including the older examples: **134 active definitions,
abbreviations, and structures**, plus **24 explicit instances**. Commented-out
definitions are excluded. Recommendations below are proposals; they do not imply
that replacement code has been implemented or that every proposed migration has
been build-tested.

The core definitions mostly make sense. The main obstacles to a reusable library
are duplicate constructions, generic machinery hidden in application files, and
names that suggest stronger mathematical meaning than the definitions establish.


**Follow-up, 2026-09-25:** The first structural cleanup is implemented. The tensor
basis and matrix API formerly in `DirectProof.lean` now live in
[`TensorPower/Matrix.lean`](LeanHaar/ForMathlib/TensorPower/Matrix.lean). The polynomial
proof formerly in `SmallDim.lean` now lives in
[`PermutationCentralizer.lean`](LeanHaar/ForMathlib/PermutationCentralizer.lean), and
[`Main.lean`](LeanHaar/ForMathlib/Main.lean) assembles Schur–Weyl duality. The inventory
and recommendations below record the pre-cleanup audit; completed work is tracked
in [TOOD.md](TOOD.md).

**Follow-up, 2026-10-01:** `permOp` is retained beside `permAction` in
[`TensorPower.lean`](LeanHaar/ForMathlib/TensorPower.lean); moment formulas continue
to use this underlying endomorphism, and `permDual` applies it to inverse
permutations. The representation, associated group-algebra module/action, and
range/span helpers are private to [`DCT.lean`](LeanHaar/ForMathlib/DCT.lean), where
Maschke and density need them. There is no separate representation module.
`permMonoidHom` and the unused DCT conversion are removed; density/semisimplicity
proofs are private theorems. The reusable finite-dimensionality instance now
accompanies the tensor basis. The historical inventory below retains the old
names and recommendations to record what was reviewed.

## Review criteria

“Mathlib standard” here means reusing existing constructions, choosing appropriate
bundled structures, controlling assumptions, and providing clear names and a
coherent API. See Mathlib's [style guide](https://leanprover-community.github.io/contribute/style.html)
and [naming conventions](https://leanprover-community.github.io/contribute/naming.html).
These principles do not require definitions and their basic lemmas to live in
separate files. **Keep** means that a definition earns its place, not necessarily
that it is ready for upstream submission. Existing-API comparisons were made
against this repository's pinned Mathlib source.

## Core algebra

### TensorPower.lean — 5 definitions

Source: [TensorPower.lean](LeanHaar/ForMathlib/TensorPower.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `TensV` | Tensor power of `ℂᵈ`. | **Keep as project shorthand.** Mathlib already has `TensorPower`; an upstream construction should usually work over a general module. That generalization need not happen immediately. |
| `permAction` | Permutes tensor factors, bundled as a monoid homomorphism into linear equivalences. | **Keep.** The bundling expresses genuine mathematical structure. A generic tensor-product version is a plausible reusable contribution. |
| `permImage` | Set of permutation operators. | **Keep if it improves span/centralizer statements.** Eventually derive it from one canonical permutation representation. |
| `diagAction` | Sends an endomorphism `g` to its tensor power. | **Keep.** A monoid homomorphism is the correct structure: the operation is generally not additive in `g`. |
| `diagImage` | Set of tensor powers of endomorphisms. | **Keep.** Replacing this set with a subalgebra would change its meaning. |

There is no compelling reason to restore the commented-out `unitaryAction`.
Restricting `diagAction` to unitary matrices deserves another public definition
only when downstream work needs additional bundled structure. `diagActionUnits`,
`glAction`, `unitaryAction`, and their commented conversion lemmas remain outside
the active inventory.

### DCT.lean — 8 definitions

Source: [DCT.lean](LeanHaar/ForMathlib/DCT.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `permMonoidHom` | Permutation action viewed as endomorphisms. | **Merge into the canonical representation construction.** Mathlib supplies `LinearEquiv.automorphismGroup.toLinearMapMonoidHom`; the action laws need not be reproved by tensor induction. |
| `permRep` | Permutation representation. | **Keep.** This unlocks the representation and group-algebra APIs. Define it directly from `permAction` using the standard conversion. |
| `PermModule` | Module associated with `permRep`. | **Keep.** This follows Mathlib's `Representation.asModule` design. |
| `permAlgHom` | Induced group-algebra action. | **Reasonable shorthand.** Keep if repeatedly used; otherwise use `permRep.asAlgebraHom` directly. |
| `centralizer_to_endModule` | Converts a commuting endomorphism into a group-algebra-linear endomorphism. | **Private or remove for now.** No named consumer was found. A future general centralizer equivalence would be more valuable than an isolated specialized conversion. |
| `doubleCentralizer_to_endEndModule` | Converts a double-centralizer element into an endomorphism over the endomorphism ring. | **Private proof helper.** Currently serves DCT. If public, use a data-style lowerCamelCase name. |
| `permModule_isSemisimple` | Proof that the representation module is semisimple. | **Use a theorem or appropriately scoped instance**, rather than a reducible noncomputable `def`. Preserve the carefully chosen module instances during migration. |
| `permModule_toModuleEnd_surjective` | Surjectivity proof used in DCT. | **Use a theorem with an explicit statement.** It is a proposition proof, not a new mathematical construction. |

### DirectProof.lean and SmallDim.lean — 5 definitions

Sources: [DirectProof.lean](LeanHaar/ForMathlib/TensorPower/Matrix.lean),
[SmallDim.lean](LeanHaar/ForMathlib/PermutationCentralizer.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `tensorBasis` | Standard tensor-product basis. | **Keep one shared definition.** It belongs below the proofs that consume it. |
| `tensorBasis'` | Same tensor-product basis. | **Merge with `tensorBasis`.** The prime distinguishes implementations without distinguishing mathematics. |
| `toEndMatrix` | Matrix coordinates for tensor-space endomorphisms. | **Keep one canonical conversion.** Consider `LinearMap.toMatrixAlgEquiv`, which also bundles multiplication and identity compatibility. |
| `toEndMatrix'` | Same conversion using `tensorBasis'`. | **Merge with `toEndMatrix`.** |
| `pairCount` | Joint multiplicities of index pairs, represented as finitely supported exponents. | **Useful proof construction.** Keep private unless another module needs this exact combinatorial object. |

### Weingarten.lean — 3 definitions

Source: [Weingarten.lean](LeanHaar/ForMathlib/Weingarten.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `permOp` | Underlying endomorphism of a permutation action. | **Consolidate with `permRep`/`permMonoidHom`.** Convenient notation is fine; independently maintained definitions are unhelpful. |
| `permDual` | Operator associated with the inverse permutation. | **Reasonable shorthand.** Document that “dual” refers to the inverse/adjoint relationship, not the general dual-space operation. Derive it from the canonical permutation operator. |
| `endVec` | Vectorizes an endomorphism using matrix entries. | **Keep the operation; consolidate its implementation** with `endVecEquiv`. |

### WeingartenInverse.lean — 10 definitions

Source: [WeingartenInverse.lean](LeanHaar/ForMathlib/WeingartenInverse.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `gramMatrix` | Matrix of inner products of a vector family. | **Replace with `Matrix.gram`.** Mathlib also provides relevant invertibility results. |
| `gramVec` | Inner products of a vector against a family. | **Keep if useful.** Expose linearity in the vector if used. General inner-product-space infrastructure should leave the Weingarten-specific file. |
| `gramSolutionSet` | Solutions of the Gram linear system. | **Reasonable when public theorems discuss the whole solution set.** Otherwise an equation or fiber of a linear map may suffice. |
| `matrixEntriesEquiv` | Uncurries a matrix into a function on pairs. | **Replace the handwritten construction** with the appropriate direction of `LinearEquiv.curry`. |
| `endVecEquiv` | Bundled linear equivalence implementing vectorization. | **Keep as the canonical vectorization construction.** Move it below both Weingarten files. |
| `endVecₗ` | Linear-map projection of `endVecEquiv`. | **Use the projection or a transparent convenience abbreviation.** It has consumers, but introduces no additional mathematical object. |
| `weingartenGram` | Trace-pairing Gram matrix of permutation operators. | **Keep.** Connect it to `Matrix.gram` and inherit general theory. |
| `weingartenVec` | Trace pairings of an operator with permutation operators. | **Keep.** A bundled linear map would help if linearity is used repeatedly. |
| `weingartenGramNat` | Natural-number counting version of the Gram matrix. | **Keep.** It has distinct computational value. |
| `weingartenSolutionSet` | Solutions of the specialized Weingarten system. | **Keep if supporting public singular/nonunique theory.** Derive it through common linear-system infrastructure. |

The current `endVec` uses a different coordinate ordering from Mathlib's
`Matrix.vec`. A direct substitution would change conventions; transpose/reindexing
must be accounted for.

## Haar and shared supporting constructions

### Haar.lean — 5 definitions

Source: [Haar.lean](LeanHaar/ForMathlib/Haar.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `haarProb` | Haar measure normalized to mass one. | **Keep.** In the pinned Mathlib, `Measure.haar` has an arbitrary normalization, so this definition has a real purpose. |
| `endOf` | A matrix regarded as an endomorphism. | **Replace or retain only as compatibility shorthand.** It is exactly `Matrix.toLin'`, whose standard API supplies the multiplication and identity properties. |
| `actOn` | Conjugates an operator by the tensor power of a unitary. | **Keep.** This is a meaningful operation. A more descriptive name and linearity in the operator would improve the public API; restoring `unitaryAction` is not required. |
| `momentMatrix` | Entrywise integral defining the Haar-averaged matrix. | **Implementation detail unless independently used.** Consider making it private and exposing coordinate lemmas for `momentOp`. |
| `momentOp` | Haar twirling/moment operator. | **Keep as a principal public definition.** Eventually bundle linearity; the coordinate-based implementation is defensible. |

### SupportingDocs/TensorPowerTraces.lean — 4 definitions

Source: [TensorPowerTraces.lean](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `tensorOp` | Tensor product of a family of matrix operators. | **Keep and move to tensor/matrix infrastructure.** It is not example-specific. |
| `tensorPow` | Constant-family specialization of `tensorOp`. | **Consolidate with `diagAction (Matrix.toLin' M)`.** Keep a matrix-facing name only if it improves usability. |
| `conjBy` | Matrix conjugation `U M U†`. | **Reuse an existing construction where appropriate.** Mathlib has `Unitary.conjStarAlgAut`; Physlib also has matrix conjugation. Move out of trace-specific infrastructure. |
| `matrixOf` | Matrix of an endomorphism of a function space. | **Replace with `LinearMap.toMatrix'`.** |

## Low-order moments and QML

### k2Moment.lean — 1 definition

Source: [k2Moment.lean](LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `𝔽` | Swap operator. | **Keep the object; give it a searchable namespaced name such as `swapOp`.** The symbol can remain scoped notation. |

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

### QML/HaarMoments.lean — 2 definitions

Source: [HaarMoments.lean](LeanHaar/ForMathlib/ForMathlibExamples/QML/HaarMoments.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `cId` | Identity coefficient in the second moment of `M ⊗ M`. | **Keep as a specialization**, with a descriptive name and documented dimension assumptions. Consider shared second-moment infrastructure. |
| `cSwap` | Corresponding swap coefficient. | **Same assessment.** These depend on the input matrix and are not universal Weingarten values. |

### QML/CostFunction.lean — 6 definitions

Source: [CostFunction.lean](LeanHaar/ForMathlib/ForMathlibExamples/QML/CostFunction.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `cost` | Trace expectation after unitary conjugation. | **Keep as an application definition.** Add real-valuedness under appropriate Hermitian/density assumptions. |
| `gradient` | Commutator trace expression intended to represent a derivative. | **Needs a mathematical bridge.** Either name it as a gradient formula/component or prove the derivative theorem for a parameterized circuit. |
| `haarExp` | Integration against `haarProb`. | **Optional shorthand.** Move to shared Haar infrastructure if reused; ordinary integral notation may otherwise suffice. |
| `haarVar` | `E[f²] − E[f]²` for complex-valued functions. | **Clarify or rename.** This is an algebraic second central moment, not usual complex variance involving squared absolute values. Connect the real-valued case to the probability API. |
| `haarExp₂` | Iterated integration over two Haar variables. | **Reasonable shorthand.** Product-measure formulation and integrability/Fubini results would better express independence. |
| `haarVar₂` | Two-variable second central moment. | **Same variance issue**, plus product-measure interpretation. |

## Classical shadows

The deliberately algebraic layer should be preserved. Physical validity should
be supplied by hypotheses or a separate layer, rather than silently assumed.

### SnapshotEnsemble.lean — 8 definitions/structures

Source: [SnapshotEnsemble.lean](LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/SnapshotEnsemble.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `SnapshotEnsemble` | Weighted family of operator snapshots. | **Keep.** `Fintype` is needed for sums rather than fields; some operations need weaker scalars than `Field`. |
| `outcomeWeight` | `wₓ Tr(ρ Sₓ)`. | **Keep as an algebraic weight.** Physical assumptions must establish positivity and normalization before it is a probability. |
| `measurementChannel` | Weighted trace-frame map. | **Keep.** `LinearMap` bundling is appropriate. Arbitrary weights/operators do not automatically define a physical quantum channel. |
| `invChannel` | Inverse measurement map under bijectivity. | **Keep.** Named access to a linear equivalence supports the estimator API. |
| `stateEstimator` | Inverse channel applied to a snapshot. | **Keep.** Individual shadow estimators need not be positive; requiring density states here would be a mistake. |
| `observableEstimator` | Trace pairing of an observable with the state estimator. | **Keep.** A physical real-valuedness result would complement the algebraic definition. |
| `IsTraceSelfAdjoint` | Symmetry for the bilinear trace pairing. | **Move to generic trace-form infrastructure.** It is independent of ensembles and differs from self-adjointness for the sesquilinear Hilbert–Schmidt inner product. |
| `thirdMoment` | Scalar triple-trace contraction of the ensemble. | **Keep if useful.** Distinguish the name from `thirdTensorMoment` and derive this contraction from the canonical tensor object. |

Probability normalization here uses completeness such as `∑ₓ wₓ Sₓ = I`, together
with appropriate positivity and a density state. Merely requiring `∑ₓ wₓ = 1`
would not fix the issue.

### TraceContractions.lean — 4 definitions

Source: [TraceContractions.lean](LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/TraceContractions.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `traceMulLeft` | Linear functional `X ↦ Tr(A X)`. | **Useful, but compose existing maps**: trace and `LinearMap.mulLeft`. Move to general trace infrastructure. |
| `partialTraceFirst` | Contracts the first factor against `ρ`. | **Keep with precise naming/documentation.** This acts on a tensor product of endomorphism spaces; the usual partial-trace interpretation needs a bridge. |
| `doubleTraceContract` | Product of two trace pairings extended linearly to tensors. | **Keep and move to the general layer.** The existing tensor-map construction is appropriate. |
| `tripleTraceContract` | Three-factor version. | **Keep and move likewise.** Arbitrary-order abstraction is optional. |

### Observation58.lean — 3 definitions

Source: [Observation58.lean](LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation58.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `secondTensorMoment` | Weighted sum of `Sₓ ⊗ Sₓ`. | **Keep.** A mathematical module such as snapshot moments is a better permanent home than an observation number. |
| `thirdTensorMoment` | Weighted sum of threefold snapshot tensors. | **Keep**, with the same placement recommendation. |
| `observableEstimatorVariance` | Weighted estimator-square expression minus squared target expectation. | **Keep the algebraic formula; clarify its statistical interpretation.** Arbitrary fields and weights do not establish probability-theoretic variance. |

### UnitarySnapshots.lean — 3 definitions

Source: [UnitarySnapshots.lean](LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `basisProjector` | Rank-one projector onto a standard basis vector. | **Keep.** A sensible domain name over the standard matrix construction. |
| `unitarySnapshot` | Conjugated basis projector. | **Keep.** A meaningful application object. |
| `unitarySnapshotMoment` | Sum of Haar-averaged tensor powers of basis projectors. | **Keep, documenting normalization.** This is a sum over outcomes, not an average, and contains no state-dependent Born weight. |

### DepolarizingChannel.lean — 3 definitions

Source: [DepolarizingChannel.lean](LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/DepolarizingChannel.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `depolarizingChannel` | Linear map `(Tr(X) I + X)/(δ+1)`. | **Keep the bundled algebraic map.** It is a particular isotropic formula, not the full parameterized family of physical depolarizing channels. |
| `depolarizingChannelInv` | Candidate inverse `(δ+1)X − Tr(X)I`. | **Keep.** Inverse status appropriately depends on subsequent hypotheses. |
| `depolarizingChannelEquiv` | Linear equivalence under those hypotheses. | **Keep.** Stronger bundled structure earns a separate definition here. |

### Observation59.lean — 2 definitions

Source: [Observation59.lean](LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean).

| Definition | Meaning | Assessment |
| --- | --- | --- |
| `haarMeasurementChannel` | Actual Born-weighted Haar integral. | **Keep.** Eventually bundle linearity and give it a mathematical module home. |
| `haarMeasurementChannelEquiv` | Explicit invertible isotropic map. | **Keep, documenting identification coverage.** Equality with the integral is established under `d ≥ 2`; the definition has a broader domain. |

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
| `hsOverlap` | Inner product of vectorized endomorphisms. | **Keep the concept; move the generic construction beside vectorization.** |
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
separately from the 134-definition count.

| Location / instances | Assessment |
| --- | --- |
| DCT: `tensV_module_finite` | **Keep; move beside the tensor basis.** Basic finite-dimensional facts should not require a double-centralizer proof import. |
| DCT: `neZero_card_perm` | Valid characteristic-zero/Maschke support. **Consider local scope** if only used there. |
| DCT: `permModule_finite_over_endRing` | Technical density-theorem support. **Prefer local scope** without external consumers. |
| Haar: `instCompactSpaceUnitaryGroup` | **Keep.** Genuine structural fact; general finite index types would improve reuse. |
| Haar: `instSecondCountableMatrix` | **Keep the current bridge.** Direct inference with existing Haar imports failed without it. |
| Haar: `instMeasurableSpaceUnitaryGroup`, `instBorelSpaceUnitaryGroup` | **Keep until a tested canonical replacement exists.** Inference failed without these. General subtype APIs alone do not justify deleting them. |
| Haar: `instIsProbabilityMeasureHaarProb`, `instIsMulLeftInvariantHaarProb` | **Keep.** Appropriate properties of the named measure. |
| HaarInvariance: `instIsHaarMeasureHaarProb` | **Keep and move into the common Haar layer.** |
| HaarInvariance: `instInnerRegularHaarProb` | **Candidate for removal.** Pinned Mathlib supplies inner regularity for Haar measures on compact groups once relevant instances are present. |
| HaarInvariance: `instIsMulRightInvariantHaarProb`, `instIsInvInvariantHaarProb` | **Keep the properties in the common Haar layer**, outside example supporting documents. |
| HilbertSpace: `AddCommGroup`, `Module`, `NormedAddCommGroup`, `InnerProductSpace`, `FiniteDimensional`, `CompleteSpace`, `Nontrivial` | All seven are appropriate **if the wrapper remains**. All become unnecessary when using `EuclideanSpace` directly. |
| Original Schur example: local group-algebra `Module`, local `IsScalarTower` | **Check standard `Representation.asModule` instances.** Avoid duplicates unless required by a specific instance-resolution problem. |
| Original Schur example: `unitary_irreducible` | **Keep.** A mathematical result appropriately exposed as a proposition instance. |
| Schur V2: `IsIrreducible stdRep` | **Keep**, subject to deciding which example/proof is maintained. |

Sources for supporting instances: [HaarInvariance.lean](LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/HaarInvariance.lean)
and the corresponding modules linked above.

## Recommended first consolidation

Start with one tensor basis, one matrix-coordinate equivalence, one canonical
permutation representation, and one bundled vectorization construction. Replace
exact Mathlib duplicates alongside those changes. This simplifies the library
without requiring broad generalization or restoring deliberately removed wrappers.

The first focused design discussion is `DirectProof.lean` and `SmallDim.lean`;
the recommendations in this document are a record of the preceding whole-repo
audit, not approval to implement all of them at once.
