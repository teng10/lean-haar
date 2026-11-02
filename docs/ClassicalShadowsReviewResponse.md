# Classical shadows: response to review 13

Date: 2026-11-01. Baseline: `d602272` (`Connect classical shadows to Physlib POVMs`).
Input: `review/13-classical-shadows-api-2026-11.md`, a local, git-ignored review.
The approved scope was implemented on 2026-11-01; completion checks are recorded below.
Three independent agents checked the mathematics, API scope, and Lean-specific findings.

## Subsequent scope reduction — 2026-11-02

The user subsequently requested only the infrastructure needed for Observations 58/59
and the Haar reconstruction. The review and checks below record the earlier implementation.
The current layout is:

- `SnapshotEnsemble.lean`: unchanged finite algebra and both Observation 58 identities.
- `UnitarySnapshots.lean`: the Haar model and named `haarShadow` estimator.
- `Observation59.lean`: the `k2_moment` specialization, channel and inverse formulas,
  and `haarShadow_unbiased`, with its private continuity/integral helpers.
- `ForPhyslib/POVM.lean`: the rotated-basis POVM, its matrix formula, and the Born trace bridge.

The separate `HaarShadow.lean` file is removed after moving its declarations. The independent
`PauliShadow.lean` application and its sole-use `POVM.unitaryBasis_mats_apply` helper are
removed from the current scope. The earlier recommendation to retain Pauli is superseded;
its original implementation remains in Git history. No generic protocol or reconstruction
framework replaces these files. The retained Haar declaration names, formulas, and proofs
are unchanged; import `Observation59` for the complete Haar correctness result.

Validation of the reduced tree: full `lake build`, `lake test`, direct callers importing
only `SnapshotEnsemble` and `Observation59`, and both umbrella checks passed. The axiom
audit checked **647 project/test declarations across 36 modules**, found only standard
axioms, and confirmed that retired declarations and modules are absent from the imports.
Two independent reviewers checked the layout and preservation of the retained proofs.
The application is reduced from five files / 663 lines to three files / 543 lines.

## Recommendation

Adopt the mathematical simplifications and shared conversion lemmas, without implementing
all the proposed infrastructure. The review finds useful omissions and duplication; it does
not establish a soundness defect in the current results. In particular, my earlier treatment
of `hself` as a necessary separate hypothesis was too conservative for this specific finite
channel: its trace symmetry is provable from its definition and bijectivity.

Preserve the named Haar/Pauli estimators, both Observation 58 identities, and the direct
Observation 59 → `k2_moment` proof. Keep the existing distinction between an algebraic
weighted family and physical Born probabilities.

## Decisions on the review

| Finding | Decision | Planned response |
| --- | --- | --- |
| CS-01: derivable `hself` | Accept | Prove channel and inverse trace symmetry; remove the redundant hypothesis from the private calculation and public Observation 58 result. |
| CS-02: missing finite mean identities | Accept with changes | Add reconstruction and observable-mean identities; expose the raw second-moment contraction. Retain the existing Observation 58 subtraction identity as a corollary under its existing name. Do not add another variance-named theorem. |
| CS-03: repeated bridges | Accept a smaller set | Add the four immediately consumed bridges listed below; remove duplicate unfolding proofs. Do not add the unused opposite-direction snapshot alias or change dimension binders. |
| CS-04: Pauli as a finite-model instance | Defer the full rewrite | Keep the current correct endpoint. Consider a separate Pauli frame-identity refactor when its reuse justifies the added proof/API surface. Do not add a finite-design bridge with no consumer. |
| CS-05: bundled Haar channel | Defer | The inverse results already reuse the shared depolarizing algebra. Add no parallel `haarMeasurementChannelₗ`, new equivalence, or suite of corollaries in this cleanup. |
| CS-06: local topology instance | Accept proof cleanup | Use continuity and a private entry-integral lemma to avoid the local instance. Preserve documentation, the public theorem type, and the direct continuous-linear-map import. |
| CS-07: dimension assumptions | Accept locally | Remove redundant `[NeZero d]` from the four Observation 59 results; derive it locally where the existing moment proof needs it. Defer dimension one and the core-wide sweep. |
| CS-08: names and visibility | Selective | Preserve paper-facing names and existing explicit dimensions. Clarify inversion invariance in the contraction documentation. Make the one-consumer coordinate contraction private. Restore a computation lemma only if the new finite proofs actually use it. |
| CS-09: application axiom pins | No additional pins in this pass | Existing CI audits every library and test declaration. Validate changed endpoints with focused caller checks and the existing audit, without duplicating theorem statements or adding five exact-output guards. |
| CS-10: provenance/prose | Accept targeted corrections | Add a stable primary reference, explain proved trace symmetry, and keep dimension/statistical limitations explicit. The TOOD inventory is already labelled historical; do not rewrite it as a current count. |
| CS-11: hygiene | Only small relevant fixes | Remove unused `[DecidableEq Q]`, use existing conversion/nonzero lemmas, and add missing projector docstrings. Defer `CommRing` generalization, upstream `HermitianMat.piProd`, and unrelated proof/style rewrites. |

## Corrections and qualifications

**The proposed variance theorem is still algebraic.** Its coefficients need not be nonnegative
or sum to one. In one real dimension, take one outcome, `S = id`, `w = 2`, and `ρ = O = id`.
The channel is invertible, the outcome coefficient is 2, and the estimator is 1/2. Its weighted
mean is 1, but the proposed second-moment-minus-mean-square expression is −1/2; the weighted
centered square is +1/2. Thus the mean identity alone does not establish probabilistic variance.
A future physical variance result needs a normalized Born law and the appropriate real-valued
or complex absolute-square formulation. Preserve the current honest algebraic interpretation.

**Equal estimator formulas do not identify sampling laws.** At dimension two, the Pauli
estimator equals the Haar formula at the corresponding basis rotation. This does not let the
Haar unbiasedness theorem prove Pauli unbiasedness. Adding that comparison inside PauliShadow
would introduce a dependency on the Haar proof chain: an independent import probe found 18
additional LeanHaar modules. Keep the equality as a possible caller/example calculation, not
a reason to couple the modules or create a comparison module.

**The current inverse proofs already share algebra.** Observation59 specializes
`depolarizingChannelInv_comp` and `depolarizingChannel_comp_inv`; it does not reprove them.
The `hsum` calculation in HaarShadow handles Born-probability normalization, which is still
needed when translating an inverse formula into an expectation theorem.

**The topology workaround is not an invalid proof.** The instance-free candidate compiles,
and the current public unbiasedness theorem already applies downstream without the local
instance. The rewrite avoids an inference problem in helper statements; it does not repair
Physlib's general `Integrable` instance-synthesis issue. Keep any upstream diagnosis separate.

**Axiom pins are not the safety boundary.** The current workflow configures library-wide and
test-wide axiom audits, umbrella checks, and kernel checking. Missing application-specific
`#print axioms` guards are not an uncovered class of unsafe proofs. This is verified workflow
configuration, not a claim that a new GitHub run was performed during this review.

## Approved implementation sequence

### 1. Complete the finite algebra, preserving the paper identities

File: `LeanHaar/Applications/ClassicalShadows/SnapshotEnsemble.lean`.

- Add `trace_comp_measurementChannel_comm` and `trace_comp_invChannel_comm`.
- Add `sum_smul_invChannel_eq` and `sum_mul_observableEstimator_eq`.
- Introduce the public raw square-moment contraction
  `sum_mul_observableEstimator_sq_eq`, replacing the private expanded-sum helper as the
  central result. Keep any necessary scalar expansion local/private.
- Derive `observableEstimatorVariance_eq_thirdTensorMoment` as a short corollary. Keep its
  name and formula, removing only `hself`. Keep the other Observation 58 identity unchanged.
- Keep routine inverse equations local unless multiple proofs justify named API lemmas.
  Add `measurementChannel_apply` only if it replaces repeated structure/coercion unfolding
  in these actual proofs; do not add a bundle of speculative evaluation lemmas.
- Update DefsSummary's discussion of trace symmetry and the algebraic mean/second moment.

The removed `hself` argument is an intentional API change; check all callers. No new
structure, probability field, or protocol definition is needed.

### 2. Share only conversion lemmas with immediate consumers

| Location | Addition | Replaces |
| --- | --- | --- |
| `ForPhyslib/POVM.lean` | `POVM.unitaryBasis_mats_mat`, `POVM.unitaryBasis_mats_apply` | Repeated effect unfolding and the qubit-only entry helper. |
| `SupportingDocs/TensorPowerTraces.lean` | `SchurWeyl.matrixOf_endOf`, beside its converse | Repeated matrix/endomorphism cancellation proofs. |
| `ClassicalShadows/UnitarySnapshots.lean` | `matrixOf_unitarySnapshot` | HaarShadow's private bridge and repeated Born-rule conversion. |

Update the current consumers and delete the superseded private helpers in the same change.
Use one deliberate simplification direction; do not introduce competing rewrite forms.
Skip `unitarySnapshot_eq_endOf` unless an actual remaining proof needs it. Keep the raw
snapshot and POVM effect definitions in their respective existing carriers.

### 3. Simplify the Haar proof and local assumptions

Files: `HaarShadow.lean`, `Observation59.lean`, with small touched-file hygiene elsewhere.

- Replace the explicit Hermitian-valued `Integrable` helper with continuity-based reasoning
  and the private entry-integral bridge. Keep the entry functional local or private according
  to its actual uses. Remove the local `ContinuousENorm` instance, not the direct
  `Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap` import.
- Preserve `haarShadow` and the exact statement of `haarShadow_unbiased`; the proof must
  still use the existing channel evaluation, Physlib normalization, and Haar probability.
- Remove `[NeZero d]` from `unitarySnapshotMoment_two`, `haarMeasurementChannel_apply`,
  and both inverse theorems. Introduce a local instance only where the old moment theorem
  requires it. Do not register a global `Fact (2 ≤ d) → NeZero d` instance.
- Replace the opaque matrix cancellation at the end of the channel proof with the existing
  conversion identity. Make `sum_integral_bornWeighted_snapshot` private after checking
  consumers, and explain its use of inversion invariance without renaming the moment theorem.
- Remove unused `[DecidableEq Q]` from `localPauliShadow` and its application theorem.
  Add the missing elementary-projector docstrings; leave unrelated style alone.

### 4. Validate and finish the documentation

Build affected modules after each layer; then run the full `lake build`, `lake test`, umbrella
check, and the existing all-declaration axiom audit on the final tree. Use small temporary
caller checks to confirm the retained Observation 58 names, absence of `hself`/redundant
`NeZero` requirements, and downstream use of Haar unbiasedness without a local instance.
Check that PauliShadow has gained no Haar import and the generic Reconstruction API stays absent.
No new headline-test framework is needed. Record any deliberate signature/visibility changes.

Add Huang, Kueng, and Preskill's primary reference,
[Predicting Many Properties of a Quantum System from Very Few Measurements](https://arxiv.org/abs/2002.08953),
*Nature Physics* 16, 1050–1057 (2020), where the physical protocols are introduced. Preserve
Observation 58/59 as the project's labels; do not attribute those numbers to HKP without checking.
Update DefsSummary and the relevant TODOs, leaving explicitly historical inventories historical.
The implementation follows these layers; its validation is recorded below.

## Decisions on the larger design questions

- **Q1 — carrier:** keep `HermitianMat` for physical reconstructed samples and `Module.End`
  for arbitrary-operator/core algebra. Shared conversions solve the current problem; a
  project-wide choice or migration is unnecessary.
- **Q2 — finite model:** retain the algebraic finite model and its estimator vocabulary.
  A Pauli instance could be useful later, but it is not required to justify correct paper
  identities. Reconsider a structural Pauli frame identity or finite-model client separately,
  with a concrete consumer and a measured replacement diff. The proposed finite `TensV`
  design lemma is not consumed even by the review's Pauli prototypes; defer it.
- **Q3 — dimension one:** defer it. The current `d ≥ 2` assumption is explicit and honest.
  A dimension-one result is a mathematical extension, not a prerequisite for this cleanup.

Also defer a second spelling of the Haar channel, new inverse wrappers, a generic reconstruction
framework, blanket simp attributes, dimension-binder renames, and upstream changes. If a future
consumer genuinely needs a bundled channel, migrate the existing definition in a dedicated
change rather than permanently maintaining both a function and a suffixed wrapper.

## Plan-stage verification

- Independently recompiled the review's `api-design/HselfProbe.lean`: exit 0, no output.
  This checks the symmetry, reconstruction, mean, and second-moment algebra under the current
  assumptions. The variance counterexample above is mathematical reasoning, not a Lean fixture.
- Independently recompiled `lean-quality/HaarShadowClean.lean`: exit 0, no output.
  Additional probes reproduced the topology inference issue and verified downstream use of
  the current Haar theorem without the local instance.
- Compiled import-closure probes: adding the finite model and depolarizing support to Pauli
  adds three modules; adding HaarShadow adds 18 LeanHaar modules. The finite Pauli route's
  main cost is extra proof/API machinery, not a large import increase.
- Read the actual inverse proofs, CI configuration, documentation, consumers, and Pauli/design
  prototypes. The full finite-model rewrite, all four weakened Observation59 signatures,
  dimension-one results, no-DecidableEq variant, and full lint session were not independently
  rebuilt in this response. Validate accepted edits during implementation.

The review's scratch evidence is temporary and was used as feasibility evidence, not as a
patch to apply wholesale. No full build or GitHub run was initiated for this planning pass.

## Implementation verification — 2026-11-01

The accepted scope is complete. No new public definitions or structures were added.
The original estimator bodies and Haar/Pauli unbiasedness statements are unchanged.
Both Observation 58 names and formulas remain; only the redundant `hself` hypothesis
is removed. The four Observation 59 results no longer take `NeZero d`, local Pauli
construction no longer takes `DecidableEq Q`, and the coordinate contraction is private.
Deferred design changes remain deferred.

- Targeted builds, full `lake build`, and `lake test`: passed.
- Library and test umbrella checks: passed.
- Temporary caller checks: both Observation 58 identities and the new finite identities
  work without `hself`; all four Observation 59 results work with only `Fact (2 ≤ d)`;
  Haar unbiasedness works without a local instance; local Pauli construction and its entry
  formula work without `DecidableEq Q`.
- Axiom audit: all **700 project/test declarations across 38 modules** use only
  `propext`, `Classical.choice`, and `Quot.sound`; retired public declarations are absent.
- Independent cross-reviews found no mathematical or scope issues. Pauli imports are
  unchanged, the original ten other public definition bodies are unchanged, and the
  local Pauli definition differs only in removal of its unused binder.
- Documentation and whitespace checks: passed. No GitHub run was performed.
