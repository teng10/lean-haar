# MagicMonotone cleanup plan

Date: 2026-11-03. Reviewed baseline: `a8b0c8419d5b9771dea0461730d878f1c316aaac`.
Status: minimal cleanup implemented locally on 2026-11-03; validation and API assessment are in §6. The circuit Haar bridge in §5 was implemented on 2026-11-04; see §7. Sections 1–6 retain the earlier cleanup record.

Make one small application cleanup: remove two redundant ket adapters and clarify
which Haar interpretations are proved. Preserve the existing paper-facing results.
Proving that the circuit layer sums equal independent Haar averages is a separate
mathematical task.

## 1. Chosen API change

Keep the curried definitions `layerAKet σ₁ σ₂` and `layerBKet γ₁ γ₂` unchanged.
Delete only the public pair adapters `ketA` and `ketB`.

The adapters occur only in the two pair-sum lemmas in
[BrickworkLayers](../LeanHaar/Applications/MagicMonotone/BrickworkLayers.lean) and
the two contraction proofs in
[Equation24](../LeanHaar/Applications/MagicMonotone/Equation24.lean).
Use `layerAKet s.1 s.2` directly in pair-sum statements and the matching typed
lambda when passing a family to the shared rank-one lemmas:

```lean
sumRankOne_comp_sumRankOne
  (fun s : PermPair => layerAKet s.1 s.2)
  (fun s : PermPair => layerAKet s.1 s.2) wgPair
  (fun s : PermPair => layerBKet s.1 s.2)
  (fun s : PermPair => layerBKet s.1 s.2) wgPair
```

Use the same arguments with `sumRankOne_comp_sumRankOne_kernel` in the second
proof. Remove `ketA`/`ketB` from the existing `simp only` lists; keep the remaining
simplifications. This is the prescribed migration, not a fallback. The reviewer's
probe found that mixing projection-based statements with `Function.uncurry` at
these `rw` calls fails to match. Both spellings are definitionally equal; this
plan consistently uses projections and typed lambdas.

This deliberately removes two public names. No other repository Lean consumers
were found; external consumers have not been surveyed. The migration is
`ketA` → `(fun s : PermPair => layerAKet s.1 s.2)` and similarly for `ketB`.
The two pair-sum statements change spelling but remain definitionally equal.

Retyping the canonical kets as `PermPair → Vecs` would also change paper-facing
statements and layer definitions. It offers no benefit needed by this cleanup.
Keep `PermPair`, `wgPair`, `wg`, the gate labels, `hsOverlap`, and both pair-sum
lemmas: they provide useful vocabulary or serve the existing proofs.

## 2. File-by-file scope

| File | Planned change |
| --- | --- |
| `BrickworkLayers.lean` | Remove `ketA`/`ketB`; update the pair-sum statements and proofs. Clarify the layer sums' interpretation and that `gateOn` applies copy permutations, not arbitrary physical gates. |
| `Equation24.lean` | Adapt the two proof bodies to the canonical kets. Correct the module and `twoLayerMoment` documentation; preserve all definitions and endpoint statements. |
| [SingleGateMoment.lean](../LeanHaar/Applications/MagicMonotone/SingleGateMoment.lean) | At most clarify documentation: the Haar identification is proved for `4 ≤ d` and concerns the single gate. Keep every definition, theorem statement, and proof. |
| [DefsSummary.md](../DefsSummary.md) | Record the two removals, update the affected inventory, and replace the earlier preference for pair-indexed canonical kets with this lower-churn decision. |
| [TOOD.md](../TOOD.md) | Record the completed interface cleanup and the separate, still-unproved circuit Haar bridge after implementation. |

Documentation locations to check at the reviewed baseline:

- `BrickworkLayers.lean:53–56`, `431–434`, `439–441`: the module summary and both
  layer docstrings imply an established independent-Haar identification.
- `Equation24.lean:11–17`, `76–78`: the introduction and `twoLayerMoment` docstring
  need the proof boundary and Heisenberg explanation in §3.
- `SingleGateMoment.lean:38–40`: narrow “all the vectorized manipulations” to the
  proved single-gate identification. Keep `4 ≤ d` explicit.

Some passages cite `MagicMonotone.vecMomentOp` without importing its module.
Cross-references can remain as context, but must not imply a proof dependency.
Do not add an import to make an unproved identification appear established.

Keep all three application modules and reuse the existing
[RankOneCalculus](../LeanHaar/SupportingDocs/RankOneCalculus.lean).
There are no planned import or ownership changes; leave historical dependency
reports intact. Update a current dependency note only if implementation reveals
an actual change.

Keep the bodies of `layerAKet`, `layerBKet`, `layerA`, `layerB`, `twoLayerMoment`,
and `twoLayerKernel` unchanged. Preserve names, hypotheses and formulas for:

- `momentOp_eq_weingarten_sum` and `vecMomentOp_endVec` (Equations 14/17);
- `hsOverlap_layer_eq_gram` and `hsOverlap_layer_eq_two_pow` (Equation 23);
- `twoLayerMoment_eq_contraction` (Equation 22);
- `twoLayerMoment_eq_kernel_sum` (Equation 24);
- `twoLayerKernel_eq_two_pow_sum` (the explicit Equation 25 kernel).

## 3. Correct account of the mathematics

**Already proved:** `vecMomentOp_endVec` identifies the single-gate rank-one sum
with the vectorized `SchurWeyl.momentOp` for `4 ≤ d`. The layer-overlap theorems
evaluate Gram entries, and Equation24 proves contraction and regrouping
identities for the defined layer sums using shared rank-one calculus.

**Not yet proved:** those layer sums equal averages of independently sampled,
embedded two-qubit Haar gates. `BrickworkLayers` does not import
`SingleGateMoment`, and the Equation24 proofs do not use its identification.
The application does use LeanHaar's permutation operators, vectorization, Gram
results and fourth-order Weingarten coefficients; the missing link is specifically
the circuit-average identification. Adding an import would not prove it.

Describe `layerA` and `layerB` as the explicit algebraic layer sums of the paper,
with the intended independent-Haar interpretation awaiting that bridge. Describe
`twoLayerMoment` as their defined composition, whose contraction formulas are
proved. Keep the paper equation references.

**Composition order is intentional.** `layerA ∘L layerB` applies B first to its
argument. The local manuscript sources explicitly use the Heisenberg picture:
physical gates act A then B, while observables evolve backwards. Restore that
explanation in the Lean documentation; do not reverse the composition. This was
checked in `schur-weyl-haar/magic_monotones.tex:264–274` and the current
`schur-weyl-haar/lean_haar_draft.tex:891–901`. It explains the intended convention,
not a circuit theorem already formalized.

## 4. Implementation and acceptance

1. Recheck Git status and declaration consumers at the implementation baseline.
   Preserve unrelated work and stashes. Use the recorded baseline to compare
   endpoint statements; establish whether the existing application builds before
   attributing any failure to this change.
2. Make only the changes in §2, then review the diff against the preserved
   formulas. No coefficients, adjoints, permutation order, dimensions or
   composition order may change.
3. Keep the migration check to one small temporary probe: verify the old/new
   pair-sum statement equalities by `rfl` while the old adapters are available,
   and re-prove Equations 22 and 24 using the projection-based pair-sum lemmas
   and typed lambdas above. This probe has been independently reproduced;
   rebuild the actual edited proofs after implementation. No audit namespace,
   copied endpoint suite, or permanent duplicate theorem tests are needed.
   Check the unchanged endpoint statements in the source diff.
4. Build the changed application and run the normal repository checks:

   ```sh
   lake build LeanHaar.Applications.MagicMonotone.SingleGateMoment LeanHaar.Applications.MagicMonotone.Equation24
   lake build
   lake test
   lake exe mk_all --lib LeanHaar --check
   git diff --check
   ```

   Equation24 builds BrickworkLayers transitively. The current Lake configuration
   already makes project warnings fail; keep its dependency-warning policy.
   Existing CI's library/test axiom audits and kernel check remain unchanged.
   Report local results separately from any actual GitHub run.
5. Search for surviving executable references to the deleted names. Confirm
   exactly two intended public-name removals, no added axioms or unsafe tactics,
   unchanged retained endpoint types, and no unrelated source changes. Update the
   current documentation and report explicitly that the circuit Haar bridge is
   still pending.

Completion of this cleanup means the smaller API compiles, the retained results
are preserved, and the documentation states the actual proof boundary. It does
not mean the independent-gate model has been formalized.

## 5. Separate follow-up: the circuit Haar bridge

Scope this only after the small cleanup, using the concrete four-qubit example:

1. Define the required embeddings of two-qubit unitaries and their four-copy
   action, compatible with the existing register indexing and vectorization.
2. Define the independent-gate average using existing `haarProb 4`. Establish
   the continuity/integrability and tensor/coordinate identities actually needed
   to derive each layer equality from `vecMomentOp_endVec` at `d = 4`.
3. Handle the Heisenberg convention explicitly: core `actOn` uses `U X U†`,
   whereas backwards observable evolution uses `U† X U`. Reuse the inversion
   invariance in [HaarInvariance](../LeanHaar/SupportingDocs/HaarInvariance.lean);
   its scalar integral theorem may be used componentwise if appropriate.
4. Prove the independent-integral composition identity in the established order,
   then apply the existing Equation24 theorem. An iterated-integral formulation
   is enough unless a product-measure statement has a concrete consumer.

No general circuit framework, new probability infrastructure, representation
rebundling, matrix-kernel redesign, space renaming, or changes to core,
`k4Moment`, QML, ClassicalShadows, dependencies or CI belong to the first cleanup.
The older L2–L4 design roadmap remains separate.

## Review record

Three independent agents reviewed minimal API choices, mathematical meaning and
Haar dependence, and compatibility/scope. All recommended retaining the curried
kets and removing only the pair adapters. The mathematical review checked the
manuscript and resolved the apparent order issue through its Heisenberg convention.
This plan follows the current application scope in `DefsSummary.md` and the
existing application cleanup guide; older design proposals are evidence, not
additional implementation instructions.

Follow-up feedback corrected the rewrite recipe: typed lambdas replace the
mixed `Function.uncurry` spelling. It also reduced the migration check to the
`rfl` statement checks and two rebuilt proofs, and identified the exact docstrings
above. Retaining `ketA`/`ketB` as abbreviations is a compatibility alternative if
an actual consumer needs the names; it is not part of this two-name cleanup.

The follow-up was independently checked with temporary Lean probes: both migrated
proofs and both `rfl` statement checks pass with `warningAsError=true`, and their
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The mixed `Function.uncurry` rewrite fails in both proofs as reported; this does
not rule out a different, consistently spelled `uncurry` formulation.
These planning checks preceded implementation. The implementation results below
supersede that earlier status.


## 6. Implementation results and API assessment

Implemented the two adapter removals and their four immediate consumers. All
retained definition bodies, imports and paper-facing endpoint statements are
unchanged; `SingleGateMoment` changes only documentation. `DefsSummary.md` and
`TOOD.md` record the outcome. No new Lean declarations, modules or test framework
were added.

Three independent agents reviewed API minimality, mathematical meaning, and
compatibility. The first diff review found two further documentation issues:
interlayer overlaps are products of Gram entries, and the kets vectorize products
of full-register operators. Both were corrected, along with the distinction
between the tensor state space and vectorized operator space. A further review
found no remaining actionable issues.

Local validation passed:

- Targeted build before and after the code changes; full build after the final
  source edits (8,587 jobs), `lake test`, umbrella check, and `git diff --check`.
- Seven temporary clients using the original endpoint statements and direct
  module imports, with warnings treated as errors; the earlier pair-sum `rfl`
  checks also passed. No permanent duplicate theorem tests were added.
- Official `axiom-audit` v0.1.2 audited all **643** declarations selected under
  the `LeanHaar` module root, with no violations and only `propext`,
  `Classical.choice`, and `Quot.sound`. The seven client witnesses use the same
  allowed axioms. Existing dependency warnings remain advisory.

No GitHub workflow or separate kernel re-check was run for this change. Changes
are left uncommitted.

| User entry point | What it supports | Connection to LeanHaar |
| --- | --- | --- |
| `SingleGateMoment` | Rewriting a fourth Haar moment, in operator or vectorized form, for `4 ≤ d`. | Direct proof: `vecMomentOp_endVec` uses `k4_moment`, which derives from the actual Haar moment operator defined using `haarProb`. |
| `BrickworkLayers` | Copy-permutation operators, named layer kets, evaluated overlaps and layer sums for four qubits/four copies. | Uses the core `permOp`, matrix coordinates, `endVec`, Gram identities and Weingarten values. The coefficient inversion certificate is proved, but identification of the layer sums with independent-gate Haar averages is still missing. |
| `Equation24` | Named contraction and kernel formulas that callers can use without unfolding register matrices. | Applies shared rank-one calculus to the concrete layer sums and uses the evaluated overlaps. Its proof does not invoke the single-gate Haar identification. |

The interface is suitable for this concrete algebraic application: curried kets
match the paper formulas, and only generic pair-indexed proof calls need typed
lambdas. It is not yet an interface for supplying sampled unitary gates or
arbitrary circuits. The next substantive improvement is the concrete Haar-layer
identification in §5; no additional abstraction is needed for this cleanup.

## 7. Four-qubit Haar bridge — 2026-11-04

The follow-up in §5 is implemented. `LayerGates` gives ordered decompositions and
actual unitary gates for both pairings. `HaarLayers` proves the two independent
Haar layer identities and `integral_twoLayer_endVec` for every global `RegOp`.
Its measure is the product of four `haarProb 4` measures, and its integrand is
`endVec (actOn X (star (layerUnitaryB p.2 * layerUnitaryA p.1)))`.

The proof uses `vecActOn_endVec` → the single-gate Haar fourth moment → tensor
transport and independent integration → the existing layer sums. Composition
uses Mathlib's continuous bilinear composition map and product-integral theorem.
The resulting `twoLayerMoment` can be rewritten with `twoLayerMoment_eq_kernel_sum`.
No assumption that `X` factors across the gates is needed.

Shared support consists of ordered unitary tensoring, finite-coordinate tensor
maps, and vectorized conjugation. The exact tensor-conjugation transport theorem
is public; fourth-moment specialization and sum bookkeeping stay in the application.
There is no general circuit structure or custom probability wrapper. Existing
layer formulas and Equation (24) statements/proofs are preserved.

Two independent reviews found no mathematical issue in gate ordering, independence,
arbitrary-operator coverage, or connection to the core Haar definition. They prompted
removal of an unused transport lemma, consolidation of the single-gate integral
results into `SingleGateMoment`, and exposing the reusable conjugation transport law.

Validation: the full library build (8,592 jobs), `lake test`, and the umbrella
check passed. A temporary client derives Equation (24) from the four-gate integral
with two rewrites. Axiom checks of that client, both layer identities, the
four-gate identities, the generic transport law, and the gate constructors report
only `propext`, `Classical.choice`, and `Quot.sound`. Dependency warnings remain
advisory. No GitHub run or separate kernel re-check was performed.
