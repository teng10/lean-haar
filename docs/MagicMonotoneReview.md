# MagicMonotone review: interface, core dependence, structure

Date: 2026-11-04, revised 2026-11-05 after the maintainer's response and API/literature follow-up (see §§7–8).
Reviewed state: working tree on `haar-aristotle-examples` at `a8b0c84` with the uncommitted
MagicMonotone changes (modified `BrickworkLayers`, `Equation24`, `SingleGateMoment`; new
`LayerGates`, `HaarLayers`; new `SupportingDocs/EuclideanTensor`, `UnitaryTensor`,
`VectorizedHaar`; umbrella, `DefsSummary.md`, `TOOD.md`).
Status: §§1–9.4 record the review and decisions; §9.5 records the implemented cleanup and its checks.

## 1. Summary

The cleanup plan landed as agreed, and the Haar bridge closes the gap the plan left open:
the layer sums are proved to be averages over independent two-qubit Haar gates, and the
four-gate circuit average is `layerA ∘L layerB` for every operator. The working tree
builds, the umbrella check passes and `lake test` passes. The mathematics is right,
including the Heisenberg order.

Having both an operator picture (`actOn`, `momentOp` on `TensV 16 4`) and a vectorized
picture (`vecActOn`, `vecMomentOp` on `Vecs`) is legitimate: the paper is written in the
second, the library in the first. What costs quality is not their coexistence but (a) the
most reusable theorem of the bridge being private and specialised, (b) a second
definition of the conjugation action with its own coordinate proof, and (c) wrappers and
plumbing that exist only to move between the pictures. §5 gives a narrow recommended
change that addresses (a) and the documentation, and lists the structural options as
deferred work that should not delay the magic-monotone calculation.

## 2. What was verified

| Check | Result |
| --- | --- |
| `lake build` on the working tree | success, 8592 jobs; the only warnings are replayed from the Physlib dependency |
| `lake exe mk_all --lib LeanHaar --check` | no update necessary |
| `lake test` | success |
| Heisenberg order | the sampled circuit is `B * A`; `star_mul` and `vecActOn_mul` turn its inverse conjugation into `vecActOn (star A) ∘ vecActOn (star B)`, whose product-measure integral factorizes into `layerA ∘L layerB` |
| Sampling | each gate is drawn from `haarProb 4`; layers use `(haarProb 4).prod (haarProb 4)`, the circuit the product of the two |
| Cross-module consumers | every lemma listed in §4.2 was grepped for consumers outside its file (table in §6.3) |
| Measure-theory imports | counted the `Mathlib.MeasureTheory.*` modules in the environment of each core import (§3.4, §6.4) |
| `Weingarten.lean` with `Mathlib.Analysis.InnerProductSpace.PiL2` in place of `Mathlib.Analysis.CStarAlgebra.Module.Constructions` | compiles unchanged in 10 s; downstream modules were not rebuilt with that change |

Reported by the maintainer, not verified here: the general Haar-factorization theorem
(arbitrary dimensions and copy number) compiles with no new definitions. Not verified by
anyone: the GitHub axiom audit and `leanchecker` on this tree; whether the transport
definition of `vecActOn` removes the heartbeat override (§3.1).

## 3. Interface and dependence on the core

### 3.1 `vecActOn` as a second definition of the action

`vecActOn` ([VectorizedHaar.lean](../LeanHaar/SupportingDocs/VectorizedHaar.lean), line 31)
is defined as an explicit matrix of products of entries of `U`; `vecActOn_endVec` then
needs a 24-line proof that it agrees with `actOn`. The alternative is a definition by
transport: `LinearEquiv.conj` of the linear map `O ↦ actOn O U` through `endVecEquiv`,
bundled with `LinearMap.toContinuousLinearMap`.

Corrected accounting of what that buys, after the response: the agreement with `actOn` is
then one `simp` step (`LinearEquiv.symm_apply_apply`), not `rfl`; `vecActOn_mul` follows
from `conj_actOn` directly; but `vecActOn_tensorUnitary` still needs the entry formula
`matrix_vecActOn`, so the coordinate computation moves rather than disappears, and
whether the `maxHeartbeats 800000` override on `integral_vecActOn` goes away is
unverified. The gain is conceptual, one definition of the action instead of two, not a
shorter file. Optional; not part of the recommended next change.

### 3.2 Headline statements

`integral_vecActOn_twoLayer` is the clean endpoint: an operator-valued integral in one
picture. `integral_twoLayer_endVec` mixes both pictures and is a one-line corollary;
present it as such, not as the main theorem. Both are worth keeping: the first is the
statement about the moment operator, the second is what a user with an operator `X` in
hand will apply.

### 3.3 What the application takes from the core

| Core module | Used declarations |
| --- | --- |
| `TensorPower`, `TensorPower/Matrix` | `TensV`, `permOp`, `toEndMatrix`, `toEndMatrix_permAction`, `toEndMatrix_diagAction`, `diagAction`, `endOf` |
| `Weingarten`, `WeingartenInverse` | `endVec`, `endVecEquiv`, `endVecₗ`, `inner_endVec_perm_eq_trace`, `weingartenGram`, `weingartenGram_eq_card`, `weingartenVec` |
| `Moments/k4Moment` | `K4.wgVal`, `K4.numCyc`, `K4.weingartenGram_closed`, `K4.wgVal_inverts_gram`, `K4.coeff`, `K4.k4_moment` |
| `Haar`, `SupportingDocs/HaarInvariance` | `haarProb`, `actOn`, `momentOp`, `toEndMatrix_momentOp`, `conj_actOn`, the `IsInvInvariant` instance |
| `SupportingDocs/Vectorization`, `RankOneCalculus` | `inner_endVec_endVec`, `toEndMatrix_mul`, `toEndMatrix_one`, `sumRankOne_comp_sumRankOne`, `sumRankOne_comp_sumRankOne_kernel` |

This is good reuse: permutation operators, Gram entries, Weingarten values and the Haar
moment operator are never re-derived. The one implementation detail the application
reaches into is `K4.coeff`, unfolded by `momentOp_eq_weingarten_sum` to restate
`k4_moment` as a double sum. Stating `k4_moment` in that form in the core would make the
application theorem unnecessary; the maintainer prefers to keep the core statements as
they are, so this is recorded as an option only.

### 3.4 Import weight (corrected)

The algebraic half of the application, `BrickworkLayers` and `Equation24`, uses only
`wgVal`, `numCyc`, `weingartenGram_closed` and `wgVal_inverts_gram`, none of which involve
a measure, yet its environment contains the Lebesgue integral and the Haar measure. The
first version of this review attributed that to `Moments/k4Moment` importing
`LeanHaar.Haar`. The response objected that a `k4Moment` split would not remove the
measure-theory imports, and the measurement confirms it:

| Import | `MeasureTheory` modules in the environment | of which `Integral`/`Haar` |
| --- | --- | --- |
| `Mathlib.Analysis.CStarAlgebra.Module.Constructions` (imported by `Weingarten.lean`) | 132 | 34 |
| `LeanHaar.Weingarten`, `WeingartenInverse`, `SupportingDocs/Vectorization`, `SupportingDocs/TensorPowerBasics` | 132 | 34 |
| `LeanHaar.Moments.k4Moment` | 133 | 35 |
| `Mathlib.Analysis.InnerProductSpace.PiL2`, `Mathlib.Tactic`, `LeanHaar.TensorPower`, `LeanHaar.Commutation`, `LeanHaar.TensorPower.Matrix` | 0 | 0 |

So measure theory enters the algebraic core through one line, the C*-algebra import in
`Weingarten.lean`, which that file uses only for `EuclideanSpace`, `WithLp` and
`PiLp.inner_apply`; `Mathlib.Analysis.InnerProductSpace.PiL2` provides these, and
`Weingarten.lean` compiles with it unchanged. A measure-free algebraic layer therefore
needs two core changes: that import swap, and separating the Weingarten data of
`k4Moment` (`numCyc`, `ctIdx`, `wgVal`, `weingartenGram_closed`, `wgVal_inverts_gram`,
`trace_permOp`, the class sums) from the Haar theorem (`coeff`, `k4_moment`). Both touch
the core and are deferred; neither is needed for the calculation.

### 3.5 Generic results hidden in the application (confirmed)

- `integral_tensorUnitary` ([HaarLayers.lean](../LeanHaar/Applications/MagicMonotone/HaarLayers.lean),
  line 33): the product Haar average of a tensor gate is the tensor of the single-gate
  averages. Private, generic in the register equivalence, hard-coded to `4 ≤ 4`. The
  maintainer confirms this is the main finding and has compiled the general version for
  arbitrary dimensions and copy number; the fourth-moment formula becomes its application.
- `tensorMap_sum_rankOne` (same file, line 44): generic and private; belongs next to
  `tensorMap_rankOne` in the supporting module.
- The `local instance` of `SecondCountableTopology` for the unitary group (line 28)
  belongs in `Haar.lean` with the other unitary-group instances.
- `integral_vecActOn_star` proves inversion invariance of the operator-valued integral
  only at `k = 4`; the generic statement belongs in `VectorizedHaar`, with the `k = 4`
  case as its application.

### 3.6 The kernel (corrected)

The interface ends at `twoLayerKernel`, a sum over four copies of `S₄` (331776 terms of
Weingarten values times powers of two), and nothing evaluates it for concrete labels.
The first version of this review spoke of reducing it "to cycle types"; the response is
right that this is wrong as stated. The kernel is invariant under *simultaneous*
conjugation of all four labels by one permutation, which reduces the label set to the
orbits of that diagonal action, but the four labels cannot be replaced independently by
their cycle types: the relative positions of `σ₁, σ₂, τ₁, τ₂` matter.

Two structural facts are useful for the evaluation task. By `hsOverlap_layer_eq_gram`
the interlayer overlap is a product of four entries of `weingartenGram 2 4`, so the
kernel is a four-index contraction of two 24 × 24 matrices, `wgVal 4` and the `d = 2`
Gram matrix, which is the natural computational formulation (`DefsSummary.md` already
suggests a matrix-product form). And the intralayer overlaps are `weingartenGram 4 4`
entries (`hsOverlap_layerA_layerA`), which `wgVal 4` inverts; the cross terms of the
interlayer kernel are what prevents the same cancellation. Brute-force evaluation by
`decide` or `norm_num` is out of reach at this size, and `native_decide` is excluded
by policy, so an algebraic reduction has to come first.

## 4. Definitions and files: what is unnecessary, what is plumbing, what is API

Code uses are counted over all Lean sources, excluding the definition line and comments.

### 4.1 Wrappers around existing expressions (optional removals)

| Declaration | Uses | Assessment |
| --- | --- | --- |
| `wg σ := wgVal 4 σ` | 10 | a cast-and-specialise wrapper; `DefsSummary.md` itself suggests notation |
| `hsOverlap X Y := ⟪endVec X, endVec Y⟫_ℂ` | 9 | abbreviates an inner product; `hsOverlap_eq_trace` is `inner_endVec_endVec` |
| `Copies`, `Qubits` | 43, 23 | two abbreviations for `Fin 4`; documentation only, no type safety |
| `Reg`, `QubitReg`, `RegOp` | 3, 3, 9 | the canonical types spelled out, or `local notation`, would do |
| `Vecs` | 7 | keep if the vectorized picture stays |

The response is right that Mathlib does not prohibit such abbreviations. The criterion
is the one in `ApplicationCleanupGuide.md` §2: keep a name if it gives users an object,
bundled laws, a distinction or useful vocabulary; a name that only abbreviates an
expression is a candidate for removal. By that criterion `wg` and `hsOverlap` are the
clearest candidates and the type abbreviations a matter of taste. None of this blocks
anything.

### 4.2 Plumbing: which lemmas can be private (corrected)

The first version of this review proposed making a block of lemmas private. The response
objected that several have consumers in other modules; the grep in §6.3 confirms it. The
corrected classification:

| Lemmas | Consumers | Status |
| --- | --- | --- |
| `regPermMat_apply`, `toEndMatrix_regPerm`, `layerA_regPerm`, `layerB_regPerm`, `bitsEquiv` | `LayerGates` (the gate-embedding proofs) as well as `BrickworkLayers` | public API of the register layer; keep public |
| `toEndMatrix_layerA_perm`, `toEndMatrix_layerB_perm` | `HaarLayers` only | public while `LayerGates` is a separate file |
| `PermPair`, `wgPair`, `layerA_eq_pairSum`, `layerB_eq_pairSum`, `inner_layerAKet_layerBKet` | `Equation24` only | public while `Equation24` is a separate file; a curried four-index version of `sumRankOne_comp_sumRankOne` in `RankOneCalculus` would make the pair machinery unnecessary |
| `trace_regPermMat`, `hsOverlap_regPerm`, `hsOverlap_eq_trace`, `regPerm_mul`, `regIndexEquiv` | same file only | could be private today, except `hsOverlap_regPerm`, which is a result in its own right |

### 4.3 Theorems with no code consumer

| Declaration | Uses | Note |
| --- | --- | --- |
| `twoLayerMoment_eq_contraction`, `twoLayerMoment_eq_kernel_sum`, `twoLayerKernel_eq_two_pow_sum` | 0, 0, 1 | paper endpoints, Eqs. (22), (24), (25); keep |
| `wg_inverts_gram`, `hsOverlap_layerA_layerA`, `gram_two_sq_eq_gram_four` | 0, docstring only, 1 | the "why `wgVal 4`" argument; keep as a paper identity if wanted, or fold into the module docstring |
| `gateOn_one` | 0 | unused |
| `tensorMap_apply` | 0 | the definitional formula; keep only as a `simp` lemma if needed |

### 4.4 Files (deferred)

| File | Lines | Observation |
| --- | --- | --- |
| `MagicMonotone/LayerGates.lean` | 134 | exists only to serve `HaarLayers` |
| `MagicMonotone/Equation24.lean` | 142 | exists because of an equation number; it is the last section of the brickwork module |
| `SupportingDocs/EuclideanTensor.lean`, `UnitaryTensor.lean` | 106, 73 | one subject, Kronecker products transported along an index equivalence |

Merging would give three application files and two supporting files. The maintainer
defers renaming and merging; nothing depends on them.

## 5. Recommended next change, and what is deferred

The checklist below records the earlier proposal. **§8 supersedes its public-API
choices and implementation order** following the declaration audit and literature search.

Previously recommended, in agreement with the response:

1. **Expose the generic Haar factorization and inversion invariance** in
   `VectorizedHaar` (§3.5), and derive `integral_vecActOn_layerA`,
   `integral_vecActOn_layerB` from them in `HaarLayers`. This is the one change with
   real reuse value.
2. **Move the two generic pieces to their homes:** the `SecondCountableTopology`
   instance to `Haar.lean` next to the existing unitary-group instances, and
   `tensorMap_sum_rankOne` next to `tensorMap_rankOne`.
3. **Document the new modules** (`LayerGates`, `HaarLayers`, `VectorizedHaar`,
   `EuclideanTensor`, `UnitaryTensor`) with the Main definitions / Main results sections
   the older modules have, and say in `HaarLayers` that
   `integral_vecActOn_twoLayer` is the endpoint and `integral_twoLayer_endVec` its
   corollary.
4. **Then the kernel value the calculation needs**, with the symmetry handled as in
   §3.6: reduce by diagonal conjugation only, and look for an algebraic reduction of
   the four-index contraction before any numeric evaluation.

Refinement from §8 and §9 (2026-11-05): step 1 is implemented by one generic
factorization theorem whose integrand is already the Heisenberg conjugation, so that
inversion invariance is used inside it through Mathlib's `integral_inv_eq_self` and no
separate wrapper is added; `tensorMap_sum_rankOne` stays private; and the Mathlib
`Matrix.vec` bridge of §8.3 is tried first for the coordinate proofs. The reconciled
list is in §9.4.

Deferred, optional, and not blocking the calculation:

- `vecActOn` by transport (§3.1), with its benefits as corrected.
- The wrapper removals of §4.1 and the plumbing changes of §4.2.
- File merges (§4.4) and renaming by content.
- Generalizing the register layer: lines 86–327 of
  [BrickworkLayers.lean](../LeanHaar/Applications/MagicMonotone/BrickworkLayers.lean),
  from `regPermMat` to `hsOverlap_regPerm`, never use `n = 4` or `k = 4` except through
  the abbreviations and would hold for `n` qubits and `k` copies with `d = 2 ^ n`. The
  concrete gate embeddings `layerIndexA`, `layerIndexB` would stay specific, as
  `ApplicationCleanupGuide.md` prescribes.
- Core: the `PiL2` import swap in `Weingarten.lean` and the `k4Moment` split (§3.4);
  stating `k4_moment` as a double sum (§3.3). The maintainer keeps the core statements
  unchanged for now.

## 6. Evidence

### 6.1 Usage counts of the public declarations (code uses outside the definition)

`Copies` 43, `Qubits` 23, `QubitReg` 3, `QubitIdx` 12, `Reg` 3, `RegOp` 9, `Vecs` 7,
`PermPair` 7, `bitsEquiv` 21, `regIndexEquiv` 5, `regPermMat` 17, `regPermMat_apply` 9,
`regPermMat_one` 1, `regPermMat_mul` 1, `regPerm` 7, `toEndMatrix_regPerm` 5,
`regPerm_one` 1, `regPerm_mul` 2, `gateOn` 8, `V12` 12, `V34` 12, `V23` 11, `V41` 11,
`gateOn_one` 0, `hsOverlap` 9, `hsOverlap_eq_trace` 1, `trace_regPermMat` 1,
`hsOverlap_regPerm` 2, `layerA_regPerm` 3, `layerB_regPerm` 2, `hsOverlap_layer_eq_gram` 1,
`hsOverlap_layer_eq_two_pow` 2, `gram_two_sq_eq_gram_four` 1, `hsOverlap_layerA_layerA` 0
(docstring only), `layerAKet` 8, `layerBKet` 9, `inner_layerAKet_layerBKet` 2, `wg` 10,
`wg_inverts_gram` 0, `layerA` 8, `layerB` 8, `wgPair` 11, `layerA_eq_pairSum` 3,
`layerB_eq_pairSum` 3, `twoLayerMoment` 8, `twoLayerKernel` 4,
`twoLayerMoment_eq_contraction` 0, `twoLayerMoment_eq_kernel_sum` 0,
`twoLayerKernel_eq_two_pow_sum` 1, `momentOp_eq_weingarten_sum` 1, `vecMomentOp` 12,
`vecMomentOp_apply` 1, `vecMomentOp_endVec` 1, `integral_vecActOn` 2,
`integral_vecActOn_star` 2, `layerIndexA` 5, `layerIndexB` 5, `layerUnitaryA` 7,
`layerUnitaryB` 7, `continuous_layerUnitaryA` 2, `continuous_layerUnitaryB` 2,
`toEndMatrix_layerA_perm` 1, `toEndMatrix_layerB_perm` 1, `integral_vecActOn_layerA` 3,
`integral_vecActOn_layerB` 3, `integral_vecActOn_twoLayer` 1, `integral_twoLayer_endVec` 2,
`tensorVec` 5, `tensorMap` 6, `tensorMap_apply` 0, `tensorMap_matrix` 2,
`tensorMap_rankOne` 1, `tensorUnitary` 9, `tensorUnitary_star` 1,
`continuous_tensorUnitary` 2, `tensorCopiesEquiv` 4, `tensorEntriesEquiv` 4,
`vecActOn` 25, `matrix_vecActOn` 1, `vecActOn_endVec` 4, `vecActOn_mul` 1,
`continuous_vecActOn` 4, `integrable_vecActOn` 2, `integral_vecActOn_endVec` 1,
`vecActOn_tensorUnitary` 2.

No file under `blueprint/` or `test/` references any MagicMonotone declaration.

### 6.2 Import chains

```
BrickworkLayers: Mathlib.Analysis.InnerProductSpace.LinearMap, SupportingDocs/Vectorization, Moments/k4Moment
Equation24:      BrickworkLayers, SupportingDocs/RankOneCalculus
SingleGateMoment: …, SupportingDocs/Vectorization, SupportingDocs/VectorizedHaar, Moments/k4Moment
LayerGates:      BrickworkLayers, SupportingDocs/UnitaryTensor
HaarLayers:      EuclideanTensor, VectorizedHaar, UnitaryTensor, SingleGateMoment, LayerGates, Equation24, Mathlib.MeasureTheory.Integral.Prod
VectorizedHaar:  WeingartenInverse, EuclideanTensor, UnitaryTensor, HaarInvariance, …
Weingarten:      Mathlib.Analysis.CStarAlgebra.Module.Constructions, Mathlib.Tactic, TensorPower, Commutation, TensorPower/Matrix
k4Moment:        Haar, Weingarten, WeingartenInverse, SupportingDocs/TensorPowerBasics, Mathlib.GroupTheory.Perm.Cycle.Concrete
Haar:            …, Mathlib.MeasureTheory.Group.Integral, Mathlib.Topology.UniformSpace.Matrix, SchurWeyl, Weingarten
```

### 6.3 Consumers of the lemmas discussed in §4.2 (file: number of code uses)

| Lemma | Consumers |
| --- | --- |
| `regPermMat_apply` | BrickworkLayers 7, LayerGates 2 |
| `toEndMatrix_regPerm` | BrickworkLayers 3, LayerGates 2 |
| `layerA_regPerm` / `layerB_regPerm` | BrickworkLayers 2 / 1, LayerGates 1 / 1 |
| `bitsEquiv` | BrickworkLayers 1, LayerGates 20 |
| `toEndMatrix_layerA_perm` / `toEndMatrix_layerB_perm` | HaarLayers 1 / 1 |
| `PermPair` / `wgPair` | BrickworkLayers 3 / 5, Equation24 4 / 6 |
| `layerA_eq_pairSum` / `layerB_eq_pairSum` / `inner_layerAKet_layerBKet` | Equation24 3 / 3 / 2 |
| `trace_regPermMat`, `hsOverlap_regPerm`, `hsOverlap_eq_trace`, `regPerm_mul`, `regIndexEquiv` | BrickworkLayers only |

### 6.4 Measure-theory import measurement

Counted with `#eval` over `env.header.moduleNames` after importing each module alone
(Lean 4.30, pinned Mathlib). Full table in §3.4. `Weingarten.lean` with the import
`Mathlib.Analysis.InnerProductSpace.PiL2` substituted for the C*-algebra import compiles
unchanged (`lake env lean`, 10 s); other modules were not rebuilt with that change.

### 6.5 Option overrides

`BrickworkLayers.lean:79` and `Equation24.lean:72`: `set_option maxRecDepth 8000`
(file-wide); `SingleGateMoment.lean:111`: `set_option maxHeartbeats 800000 in` for
`integral_vecActOn`.

## 7. Response record (2026-11-05)

The maintainer's response, checked by three independent agents, accepted the main
finding (§3.5) and asked for a narrower cleanup. Changes made to this review in reply:

- Accepted: the benefits of transporting `vecActOn` were overstated (§3.1 corrected);
  both pictures are useful and their coexistence is not duplication (§1 reworded);
  several lemmas have cross-module consumers and cannot simply be private (§4.2
  corrected with the consumer table); Eq. (22) is a valid endpoint (§4.3); merges and
  the register generalization are optional (§5); the kernel symmetry statement was
  wrong (§3.6 corrected).
- Checked and refined: the response said a `k4Moment` split would not remove the
  measure-theory imports. The measurement agrees and locates the actual source, the
  C*-algebra import in `Weingarten.lean`, replaceable by `PiL2` (§3.4). Both core
  changes remain deferred.
- Kept: the wrapper candidates of §4.1 as optional, by the criterion of the project's
  own cleanup guide rather than any Mathlib rule.
- The recommended next change in §5 is the response's four steps, with the kernel
  caveat added to step 4.

## 8. Public API and vectorization literature (2026-11-05)

This section refines the next-change proposal in §5 after a declaration audit and
literature/source search, with three independent agents. In particular, it withdraws
the recommendation to make `tensorMap_sum_rankOne` public and to add a separate public
inversion-invariance wrapper. The findings below are verified to the extent stated;
the proposed Lean changes have **not** been implemented.

### 8.1 How much public API was added?

The five new modules expose 33 named declarations: 10 definitions and 23 theorems.
Eight further named declarations are already private. The two added theorems in
`SingleGateMoment` bring the full addition to **35 public names**.

| New module | Public definitions | Public theorems |
| --- | ---: | ---: |
| `EuclideanTensor` | 2 | 4 |
| `UnitaryTensor` | 3 | 4 |
| `VectorizedHaar` | 1 | 7 |
| `LayerGates` | 4 | 4 |
| `HaarLayers` | 0 | 4 |

These are not 35 independent concepts: most are laws about a few constructions.
Calculation users mainly need `layerUnitaryA/B`, a two-layer Haar-average theorem,
and the existing Equation (24) kernel formula. Reusable objects are `tensorUnitary`,
`tensorVec`, `tensorMap`, and `vecActOn`; coordinate equivalences are supporting
infrastructure. Useful compatibility, continuity and composition laws can remain
public without making them required reading for ordinary callers.

The proposed reductions are:

- **Keep `tensorMap_sum_rankOne` private.** Its generic types do not make its particular
  four-sum ordering a useful public interface.
- **Reuse `integral_inv_eq_self` directly.** Do not add another public theorem merely
  specializing inversion invariance to `vecActOn`.
- **Generalize by replacement.** Expose one tensor-Haar factorization theorem for
  arbitrary local dimensions and copy number, with the Heisenberg integrand and the
  forward single-gate averages. It can replace the private fourth-moment helper and
  make the specialized public `integral_vecActOn_star` unnecessary. This exchange
  need not increase the public count.
- **Trim coordinate helpers after checking consumers.** `matrix_vecActOn` is a private
  candidate because its only code consumer is in the same file. Unused
  `tensorMap_apply` is a removal candidate; `tensorMap_matrix` is the actual shared
  coordinate interface.
- **Preserve paper endpoints and useful application names.** Do not force privacy by
  merging files solely to hide cross-module lemmas. A result with no internal consumer
  may still be exactly what a library user needs.

### 8.2 Existing formalizations

The search covered operator vectorization `|A⟩⟩` as well as formal Dirac notation.
These are related subjects, but ordinary ket/bra syntax alone is not an
operator-vectorization API.

| Source | Verified relevant content | Implication for LeanHaar |
| --- | --- | --- |
| [Mathlib: matrix vectorization](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Vec.html) | `Matrix.vec`, `kronecker_mulVec_vec`, and `star_vec_dotProduct_vec`, plus linearity and bijectivity. These declarations are present in our pinned dependency. | First choice for reusing matrix-product and Hilbert–Schmidt identities. |
| [Hayata-Yamasaki Group's Lean-Quantum](https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/main/Quantum/QuantumMechanics/QuantumChannel.lean#L219), with its [2026 paper](https://arxiv.org/abs/2607.05492) | Basis-parametrized `QuantumChannel.vec`, `vecLinearEquiv`, `map_vec_eq_vec`, and `inner_vec_eq_trace`; operators become vectors in a tensor-product Hilbert space. | Direct design precedent for a future abstract interface. Compatibility with our spaces and dependency versions has not been tested. |
| [MathComp matrix library, Coq/Rocq](https://math-comp.github.io/htmldoc/mathcomp.algebra.matrix.html) | `mxvec`, inverse `vec_mx`, and transport of linear maps through vectorization (`lin_mx`, `mul_vec_lin`). | A precedent for one vectorization equivalence and general transport laws. Its row-vector convention requires care. |
| [CoqQ, POPL 2023](https://arxiv.org/abs/2207.11350) | Foundational Hilbert-space/tensor infrastructure and labelled Dirac notation for quantum-program proofs. | Relevant notation and register-design precedent; its Choi correspondence is related to, but distinct from, operator vectorization. |
| [DiracDec, POPL 2025](https://arxiv.org/html/2411.11617v1), and [D-Hammer, 2025](https://arxiv.org/abs/2505.08633) | Equational reasoning for Dirac expressions, including tensor identities. DiracDec mechanizes rewrite-rule soundness in Coq, while its executable uses Mathematica; D-Hammer is an external implementation. | Useful automation research. Their executable answers are not automatically Lean-kernel-certified proofs. |

Physlib also already provides `MatrixMap.toMatrix` and `toMatrix_comp` for transfer
matrices, alongside its separate Choi interface in
[MatrixMap.lean](https://github.com/leanprover-community/physlib/blob/master/QuantumInfo/Channels/MatrixMap.lean).
This is adjacent infrastructure, not a demonstrated replacement for our Euclidean
continuous-linear-map and Haar-integration construction. No additional quantum-library
dependency is proposed.

### 8.3 Compiled compatibility with Mathlib

Mathlib indexes `Matrix.vec A` by `(column, row)`, while LeanHaar's `endVec` uses
`(row, column)`. The convention difference is handled by transpose, without changing
existing LeanHaar definitions. This scratch theorem compiled with `rfl`:

```lean
WithLp.ofLp (endVec X) =
  (toEndMatrix d k X).transpose.vec
```

For arbitrary finite square complex matrices, the corresponding conjugation identity
also compiled using Mathlib's existing theorem:

```lean
(A ⊗ₖ A.map star) *ᵥ X.transpose.vec =
  (A * X * A.conjTranspose).transpose.vec := by
  rw [Matrix.kronecker_mulVec_vec]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rfl
```

Both scratch proofs report only `propext`, `Classical.choice`, and `Quot.sound`.
They establish a concrete route to reuse, not a completed refactor: the full
`vecActOn` implementation, continuity proofs, and downstream application have not
been rebuilt against a replacement. The literature survey is source inspection,
not an audit of the other projects' complete proof assumptions.

### 8.4 Revised implementation order

1. Use the small convention bridge to reuse Mathlib's vectorization identities;
   preserve the existing `endVec` convention and check whether coordinate proofs
   become simpler before changing their implementation.
2. Generalize Haar factorization by replacement as in §8.1, keeping sum bookkeeping
   private and using Mathlib's inversion theorem directly. Move the canonical unitary
   second-countability instance beside the existing instances in `Haar.lean`.
3. Remove or privatize the confirmed helpers, update consumers, and document the
   calculation entry points separately from the coordinate infrastructure. Run the
   affected builds, tests and axiom checks before claiming a smaller implementation.

Core theorem statements, paper identities, file merges, register generalization and
additional dependencies remain outside this cleanup. Kernel evaluation remains a
separate calculation task. This update changes the recommendations and documentation;
it does not modify any Lean source.

## 9. Verification of §8 and reconciliation (2026-11-05)

§8 was added by the maintainer's side after a declaration audit and a literature search.
This section records what of it was re-checked here, where the two parts of the review
now differ, and the resulting single list of next steps. No Lean source was changed.

### 9.1 Checked claims of §8

| Claim | Result |
| --- | --- |
| 10 public definitions, 23 public theorems, 8 private declarations in the five new modules (§8.1) | confirmed by grep: EuclideanTensor 2/4/2, UnitaryTensor 3/4/0, VectorizedHaar 1/7/0, LayerGates 4/4/1, HaarLayers 0/4/5 |
| `matrix_vecActOn` has its only code consumer in the same file (§8.1) | confirmed (`vecActOn_tensorUnitary`) |
| Mathlib's `Matrix.vec`, `kronecker_mulVec_vec`, `star_vec_dotProduct_vec`, `vec_bijective`, `vec_add`, `vec_smul` exist in the pinned Mathlib; `vec A` is indexed by `(column, row)` (§8.2, §8.3) | confirmed in `Mathlib/LinearAlgebra/Matrix/Vec.lean`: `vec A ij = A ij.2 ij.1` |
| The two scratch theorems of §8.3 compile with only the standard axioms | confirmed: `WithLp.ofLp (endVec X) = (toEndMatrix d k X).transpose.vec` by `rfl`, and the Kronecker conjugation identity by `Matrix.kronecker_mulVec_vec`; both report `propext, Classical.choice, Quot.sound` |
| Physlib's `MatrixMap.toMatrix`, `toMatrix_comp` and the Choi interface (§8.2) | confirmed in `.lake/packages/Physlib/QuantumInfo/Channels/MatrixMap.lean` (`toMatrix` line 119, `toMatrix_comp` line 123, `choi_matrix` line 64) |
| The four arXiv references (§8.2) | titles confirmed: 2607.05492 "Lean-Quantum: Toward AI-Assisted Formalization of Quantum Information"; 2505.08633 "D-Hammer"; 2411.11617 "Automating Equational Proofs in Dirac Notation"; 2207.11350 "CoqQ" |
| The lean-quantum link (§8.2) | the repository exists (default branch `main`, last push 2026-10-28), but the cited path `Quantum/QuantumMechanics/QuantumChannel.lean#L219` does not exist at HEAD. The declarations `vec`, `vecLinearEquiv`, `map_vec_eq_vec`, `vec_apply`, `inner_vec_eq_trace` are in `Quantum/QuantumMechanics/Channel/Basic.lean`; `vec` takes a `Module.Basis` and lands in `ℋ₁ ⊗[ℂ] ℋ₂`, as §8.2 describes. The link should be updated. |

Not re-checked: the MathComp and CoqQ/DiracDec/D-Hammer content beyond the titles, and
the maintainer's compiled general factorization theorem.

### 9.2 Where §8 changes the earlier recommendations

- `tensorMap_sum_rankOne` stays private (§8.1) rather than moving next to
  `tensorMap_rankOne` (§3.5, §5 step 2). Accepted: it is sum bookkeeping with one
  consumer; if a second consumer appears it moves then.
- No separate public inversion-invariance theorem (§8.1) rather than a generic
  `integral_vecActOn_star` (§3.5). Accepted: `integral_inv_eq_self` already is that
  lemma up to `star = inv`, and the generic factorization theorem can take the
  Heisenberg integrand directly.
- `matrix_vecActOn` as a private candidate (§8.1). Judgment call, leaning the other way:
  it is the characterization lemma of a public definition, the same role as
  `tensorMap_matrix`, which §8 keeps as "the actual shared coordinate interface".
  Keep it public unless the `Matrix.vec` bridge makes it redundant.
- `tensorMap_apply` removal (§8.1). Agreed; it has no consumer and `tensorMap_matrix`
  carries the coordinate content.

### 9.3 On the `Matrix.vec` bridge (§8.3)

The bridge is sound and cheap: `endVec` differs from Mathlib's `vec` only by the
transpose and by the `WithLp` wrapper, both handled by `rfl`. What it can buy: the matrix
of `U^{⊗k}` is already available with product entries (`toEndMatrix_diagAction`), so the
matrix of `vecActOn U` is a Kronecker product `M ⊗ₖ M.map star` up to the transpose
convention, and `vecActOn_endVec` together with `matrix_vecActOn` could become instances
of `kronecker_mulVec_vec` instead of the 24-line coordinate computation. Two caveats:
`Matrix.vec` is a plain function, so every statement about the continuous linear map on
`EuclideanSpace` still goes through `Matrix.toEuclideanLin` and `WithLp.ofLp`; and whether
the result is shorter is exactly what §8.4 step 1 says to check before changing anything.

### 9.4 Reconciled next change

1. One generic tensor-Haar factorization theorem in `VectorizedHaar`, Heisenberg
   integrand on the left, forward single-gate averages on the right, inversion
   invariance by `integral_inv_eq_self` inside the proof. It replaces the private
   `integral_tensorUnitary` and the public `integral_vecActOn_star`;
   `integral_vecActOn_layerA`, `integral_vecActOn_layerB` become its applications.
2. The `SecondCountableTopology` instance moves to `Haar.lean` beside the existing
   unitary-group instances.
3. Try the `Matrix.vec` bridge for `vecActOn_endVec` and `matrix_vecActOn`; keep the
   current proofs if it is not simpler.
4. Remove `tensorMap_apply`; leave `tensorMap_sum_rankOne` private; decide
   `matrix_vecActOn` after step 3.
5. Module docstrings with Main definitions / Main results for the five new modules,
   separating the calculation entry points (`layerUnitaryA/B`,
   `integral_vecActOn_twoLayer`, `integral_twoLayer_endVec`, `twoLayerMoment_eq_kernel_sum`)
   from the coordinate infrastructure.
6. Then the kernel value, with the diagonal-conjugation symmetry only (§3.6).

Out of scope, unchanged from §5 and §8.4: core theorem statements, paper identities,
file merges, register generalization, new dependencies. Builds, tests and the axiom
audit are to be run before any claim of a smaller implementation.


### 9.5 Implementation and verification (2026-11-11)

Implemented steps 1–5 of §9.4 in the existing working tree:

- `SchurWeyl.integral_vecActOn_tensorUnitary` replaces the private fourth-moment
  factorization helper and `MagicMonotone.integral_vecActOn_star`. It works for
  arbitrary local dimensions and copy number. Layer A/B apply it, then specialize
  the existing computed fourth moment.
- The canonical unitary second-countability instance is in `Haar.lean`.
- `vecActOn_endVec` now uses `Matrix.kronecker_mulVec_vec`; no helper definition or
  convention bridge is added to the public API. The definition of `vecActOn` and
  the public coordinate characterization `matrix_vecActOn` are unchanged.
- Unused `tensorMap_apply` is removed; `tensorMap_sum_rankOne` remains private.
  The five modules document their calculation and coordinate entry points.

All retained definition/theorem signatures and the four-gate Heisenberg order are
unchanged. The separate `Circuits` development was left untouched and rebuilt as
an existing consumer. There are no new data definitions and one fewer public
theorem; the moved topology instance has a global name.

Two independent reviewers checked the candidate's mathematics, API scope and
consumers; a separate agent compiled the vectorization proof experiment. Neither
review found a blocking issue. These checks cover the full working tree, including
the separate, unstaged `Circuits` development:

| Check | Result |
| --- | --- |
| `lake build` | Pass, 8,598 jobs; existing dependency warnings remain. |
| `lake test` | Pass, including existing circuit tests. |
| Library and test `mk_all --check` | Pass. |
| Temporary module-ownership axiom audit | All 51 library/test modules and 911 constants; only `propext`, `Classical.choice`, `Quot.sound`. |
| Retained source signatures | Unchanged. |

No new GitHub CI or `leanchecker` run was performed for this change.

A separate export of the 14 staged files plus the committed baseline also passed
`lake build` (8,592 jobs), `lake test`, both umbrella checks, and a fresh
module-ownership axiom audit: **44 modules and 753 constants**, including
private auxiliaries, with only the same three standard axioms. Its 47 Lean
and configuration files matched the index byte-for-byte. This verifies the
MagicMonotone commit without the six separate `Circuits` modules or their
tests. An independent reviewer also verified the staged import closure.

Step 6 is deferred: the current formalization endpoint is the physical four-gate
Haar moment and its explicit kernel. Its interlayer contraction is already proved.
Contracting with an initial state and the Pauli observable to obtain a scalar
stabilizer purity is a further application, not a requirement of this cleanup.
