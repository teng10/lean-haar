**Dependency audit of `LeanHaar/ForMathlib/ForMathlibExamples`**

**Current follow-up, 2026-10-01:** The original audit below is historical. Its
`DirectProof`/`SmallDim` references and public permutation-representation advice
were superseded by the completed core cleanup. The reported missing-argument build
failure is fixed. The subsequent application cleanup keeps the core unchanged:

- Shared support keeps the existing `ForMathlibExamples/SupportingDocs` location.
  It now also contains the generic part of `MagicMonotone/RankOneCalculus` and
  the bridge formerly in `QML/MomentBridge`.
- Tensor trace support imports shared swap facts and the core, not `k1Moment` or
  `k2Moment`. Applications import the required moment computations explicitly.
- Moment examples reuse the shared tensor identities. Matrix/vectorization facts
  and rank-one composition theorems are shared application infrastructure.
- The generic trace/integral bridge now uses the `SchurWeyl` namespace; the generic
  rank-one composition results use `InnerProductSpace`. Application endpoint
  statements and scalar formulas are preserved.
- All 36 core and example modules build without warnings, and 12 checked application
  endpoint axiom reports match the baseline. The original source-reference tables, absolute links,
  and elaborated dependency appendix below have not been regenerated.

See `TOOD.md` for the current shared-module responsibilities. The representation
file remains deferred in its separate Git stash; no core source is changed by
this application extraction.

Audited 2026-09-25 at commit `3d15f07`. All **24 current `.lean` files** are addressed separately, including the shared support files. “Upstream” means the `.lean` files immediately under `LeanHaar/ForMathlib`, excluding `ForMathlibExamples`. Ownership is determined by file, not namespace: for example, `SchurWeyl.tensorPow` and `SchurWeyl.K4.wgVal` are example declarations.

No Lean source or configuration was modified. The audit rebuilt requested targets (updating generated `.lake` artifacts) and wrote this report plus its JSON evidence file.

**How to read the tables**

Each table enumerates declarations explicitly referenced in executable Lean source (types, definitions, and proofs), with comments/import names excluded. Names in these tables have the prefix `SchurWeyl.`. Declaration links point to the upstream definition; use-site links point to the example. Each file also records its helper/indirect dependencies and redundancy observations. A direct reference can be in a type even when no upstream theorem is called.

For the 14 targets that built successfully or were current in the successful portion of the build, explicit references were checked against Lean’s `.ilean` resolved references. The appendix separately records additional constants in elaborated types/proofs, including implicit instances, and the transitive upstream declaration closure. The other 10 files were audited from current source: their implicit dependencies and complete proof closure are not certified. Imported-but-unused theorems are not counted as proof dependencies. The JSON companion contains every source-use line and the verified dependency edges.

**Build limitation**

The all-example build fails at [TensorPowerTraces.lean:110](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:110): `permAction d (Equiv.swap 0 1)` supplies a permutation where the current API expects the natural-number tensor power `k`. The apparent correction would supply `2` between `d` and the permutation; this is only a recommendation and was not applied. This blocks that file, all six QML files, and `UnitarySnapshots`, `MomentContraction`, and `Observation59`. The three moment files and all four MagicMonotone files compiled successfully. No stale preexisting artifacts were used to certify the blocked files.

**Application-level map**

| Result | Actual route to upstream mathematics |
|---|---|
| First moment | `k1_moment → weingarten_moment_haar`. |
| Second moment | `k2_moment → weingarten_moment_haar`. |
| Fourth moment | `K4.k4_moment → weingarten_moment_haar` and `weingarten_solution_unique`. |
| QML Observation 56 | Cost-moment helpers → first/second moment examples; the observation names no upstream declaration directly. |
| QML Observation 57 | Cost/commutator Haar helpers → first/second moment examples; inversion invariance is supplied by shared support code. |
| Classical shadows Observation 58 | Generic finite-ensemble tensor algebra; no upstream dependency. |
| Classical shadows Observation 59 | Haar entrywise integral bridge → second snapshot moment → `k2_moment`; inverse packaged through the generic depolarizing equivalence. |
| MagicMonotone single gate | `K4.k4_moment` plus upstream vectorization and the permutation trace bridge. |
| MagicMonotone Equation 24 | Rank-one sum composition and local-permutation Gram overlaps. Its proof does not use the imported single-gate Haar-identification theorem. |

**1. [k1Moment.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k1Moment.lean)**

First Haar moment: `momentOp O = (Tr O / d) • id`, assuming `NeZero d`.

Validation: resolved source references checked against the current successful build.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [tensorBasis](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:33) (def) | `DirectProof.lean` | Computational tensor basis for traces and matrix conversion. Lines [24](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k1Moment.lean:24). |
| [momentOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:194) (def) | `Haar.lean` | The Haar moment operator being evaluated or reused. Lines [39](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k1Moment.lean:39). |
| [weingarten_moment_haar](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:595) (theorem) | `Haar.lean` | Produces the permutation expansion and coefficient equations. Lines [40](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k1Moment.lean:40). |
| [TensV](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:30) (abbrev) | `TensorPower.lean` | Tensor-space type in statements and constructions. Lines [22](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k1Moment.lean:22), [38](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k1Moment.lean:38), [39](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k1Moment.lean:39). |
| [permAction](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:38) (def) | `TensorPower.lean` | Underlying tensor-factor permutation action. Lines [31](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k1Moment.lean:31). |
| [permOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Weingarten.lean:91) (def) | `Weingarten.lean` | Permutation endomorphisms. Lines [29](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k1Moment.lean:29), [31](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k1Moment.lean:31), [35](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k1Moment.lean:35). |
| [permDual](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Weingarten.lean:97) (def) | `Weingarten.lean` | Inverse-permutation endomorphisms used in trace contractions. Lines [34](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k1Moment.lean:34), [35](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k1Moment.lean:35). |

**Helper and indirect dependencies.** The proof calls `weingarten_moment_haar` directly and collapses its permutation sum. No other example file is imported.

**Overlap/reuse.** The root-namespace `permOp_one` and `permDual_one` repeat the general identities in `SupportingDocs/TensorPowerBasics`; `trace_id_k1` is the case `k = 1` of `SchurWeyl.trace_id_tensV`. These shared declarations are currently example code, not upstream code.

- Replace the two local identity proofs with specializations of `SchurWeyl.permOp_one` and `SchurWeyl.permDual_one`; derive `trace_id_k1` from `trace_id_tensV`. **Impact:** `k1_moment` can keep its present rewrites if the old names remain as forwarding lemmas; deleting them requires updating callers and qualifying names where namespaces overlap.
- Import the shared basics module, or its future upstream replacement, before making those substitutions. **Impact:** keep that module independent of `k1Moment` to avoid an import cycle; the first-moment statement and dimension assumption need not change.

**2. [k2Moment.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean)**

Second Haar moment as an identity/swap combination, assuming `NeZero d` and `Fact (2 ≤ d)`.

Validation: resolved source references checked against the current successful build.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [permMonoidHom](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DCT.lean:37) (def) | `DCT.lean` | Permutation multiplication/identity laws via the monoid homomorphism. Lines [26](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:26), [27](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:27), [45](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:45); more in JSON. |
| [permRep](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DCT.lean:52) (def) | `DCT.lean` | Defines the swap alias through the permutation representation. Lines [18](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:18). |
| [tensorBasis](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:33) (def) | `DirectProof.lean` | Computational tensor basis for traces and matrix conversion. Lines [51](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:51), [52](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:52), [53](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:53); more in JSON. |
| [toEndMatrix](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:38) (def) | `DirectProof.lean` | Coordinates of tensor-space endomorphisms. Lines [62](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:62), [64](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:64). |
| [toEndMatrix_permAction](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:49) (theorem) | `DirectProof.lean` | Permutation matrix entries as equality indicators. Lines [66](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:66). |
| [momentOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:194) (def) | `Haar.lean` | The Haar moment operator being evaluated or reused. Lines [92](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:92), [152](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:152). |
| [weingarten_moment_haar](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:595) (theorem) | `Haar.lean` | Produces the permutation expansion and coefficient equations. Lines [94](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:94). |
| [TensV](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:30) (abbrev) | `TensorPower.lean` | Tensor-space type in statements and constructions. Lines [18](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:18), [50](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:50), [60](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:60); more in JSON. |
| [permAction](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:38) (def) | `TensorPower.lean` | Underlying tensor-factor permutation action. Lines [62](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:62), [64](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:64). |
| [permOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Weingarten.lean:91) (def) | `Weingarten.lean` | Permutation endomorphisms. Lines [25](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:25), [30](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:30), [104](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:104); more in JSON. |
| [permDual](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Weingarten.lean:97) (def) | `Weingarten.lean` | Inverse-permutation endomorphisms used in trace contractions. Lines [34](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:34), [38](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:38), [39](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k2Moment.lean:39); more in JSON. |

**Helper and indirect dependencies.** The proof calls `weingarten_moment_haar` directly and solves its two scalar equations. The swap is constructed through `permRep`/`permMonoidHom`.

**Overlap/reuse.** `𝔽 d` is definitionally `permOp d (Equiv.swap 0 1)`; `permOp_k2_swap` already proves this by `rfl`. It is a useful domain alias, not a new action. `permOp_k2_id`, `permDual_k2_id`, and `trace_k2_id` specialize the generic support lemmas; `swap_swap` follows from the generic multiplication law.

- Keep `𝔽` as the public swap alias, but obtain its identity, composition, and trace facts from the generic permutation API. **Impact:** `k2_moment` becomes shorter while QML and classical-shadow callers can retain their existing swap notation and lemma names.
- Move the swap alias and elementary swap facts into a module below the moment examples. **Impact:** `TensorPowerTraces` can import those facts without importing the second-moment computation; retain a forwarding import from `k2Moment` so existing clients continue to see `𝔽`.

**3. [k4Moment.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean)**

Explicit fourth Haar moment for `4 ≤ d`, with five conjugacy-class formulas for the Weingarten coefficients.

Validation: resolved source references checked against the current successful build.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [permMonoidHom](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DCT.lean:37) (def) | `DCT.lean` | Permutation multiplication/identity laws via the monoid homomorphism. Lines [86](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:86), [87](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:87), [88](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:88). |
| [momentOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:194) (def) | `Haar.lean` | The Haar moment operator being evaluated or reused. Lines [490](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:490). |
| [weingarten_moment_haar](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:595) (theorem) | `Haar.lean` | Produces the permutation expansion and coefficient equations. Lines [491](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:491). |
| [TensV](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:30) (abbrev) | `TensorPower.lean` | Tensor-space type in statements and constructions. Lines [245](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:245), [246](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:246), [462](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:462); more in JSON. |
| [permOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Weingarten.lean:91) (def) | `Weingarten.lean` | Permutation endomorphisms. Lines [85](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:85), [87](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:87), [88](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:88); more in JSON. |
| [permDual](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Weingarten.lean:97) (def) | `Weingarten.lean` | Inverse-permutation endomorphisms used in trace contractions. Lines [85](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:85), [86](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:86). |
| [weingartenGram](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/WeingartenInverse.lean:243) (def) | `WeingartenInverse.lean` | Gram entries of permutation operators. Lines [246](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:246), [247](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:247), [257](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:257); more in JSON. |
| [weingartenVec](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/WeingartenInverse.lean:247) (def) | `WeingartenInverse.lean` | Trace contractions forming the linear-system target vector. Lines [464](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:464), [470](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:470), [473](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:473). |
| [weingartenGramNat](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/WeingartenInverse.lean:283) (def) | `WeingartenInverse.lean` | Computable natural-number coincidence counts. Lines [93](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:93), [94](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:94), [227](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:227). |
| [weingartenGram_eq_natCast](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/WeingartenInverse.lean:289) (theorem) | `WeingartenInverse.lean` | Connects the complex Gram matrix to natural counts. Lines [250](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:250). |
| [weingartenSolutionSet](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/WeingartenInverse.lean:313) (def) | `WeingartenInverse.lean` | Specifies the coefficient equations. Lines [468](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:468), [493](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:493), [495](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:495). |
| [weingarten_solution_unique](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/WeingartenInverse.lean:330) (theorem) | `WeingartenInverse.lean` | Identifies the explicit fourth-moment coefficients by uniqueness. Lines [497](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean:497). |

**Helper and indirect dependencies.** `k4_moment` combines `weingarten_moment_haar`, the local `coeff_mem_solutionSet`, and upstream `weingarten_solution_unique`. The explicit inverse certificate is `K4.wgVal_inverts_gram`.

**Overlap/reuse.** `K4.permDual_comp_permOp` repeats the `k = 4` case of the general support lemma. `wgVal` is an explicit scalar class-function formula; it is not a redefinition of the upstream Gram matrix. `coeff` is a concrete candidate for the upstream inverse-Gram solution. An equality to `(weingartenGram d 4)⁻¹ *ᵥ weingartenVec d 4 O` could be obtained from `weingarten_solution_eq_inv`, avoiding a separate uniqueness argument in future clients. `numCyc_conj'` and `numCyc_conj` also repeat the same local statement.

- Replace `K4.permDual_comp_permOp` with a specialization of the general lemma, and make one of `numCyc_conj`/`numCyc_conj'` forward to the other. **Impact:** existing rewrite sites can remain intact with compatibility lemmas; removing the old names instead requires updating local proofs and any qualified callers.
- Add a theorem identifying `coeff` with the upstream inverse-Gram solution, using `coeff_mem_solutionSet` and `weingarten_solution_eq_inv`. **Impact:** later uniqueness arguments can reuse this bridge; retain `wgVal` and its inversion certificate because MagicMonotone depends on the explicit coefficients, not just existence of an inverse.

**4. [QML/MomentBridge.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/MomentBridge.lean)**

Moves a scalar trace contraction through the entrywise Haar average.

Validation: source audit; build blocked by `TensorPowerTraces`.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [haarProb](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:108) (def) | `Haar.lean` | The existing normalized Haar measure. Lines [26](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/MomentBridge.lean:26), [34](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/MomentBridge.lean:34). |
| [actOn](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:141) (def) | `Haar.lean` | Unitary tensor-power conjugation. Lines [26](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/MomentBridge.lean:26), [34](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/MomentBridge.lean:34). |
| [integrable_actOn_entry](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:180) (theorem) | `Haar.lean` | Integrability used to exchange finite sums and integrals. Lines [29](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/MomentBridge.lean:29), [38](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/MomentBridge.lean:38), [40](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/MomentBridge.lean:40). |
| [momentOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:194) (def) | `Haar.lean` | The Haar moment operator being evaluated or reused. Lines [35](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/MomentBridge.lean:35). |
| [toEndMatrix_momentOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:198) (theorem) | `Haar.lean` | Identifies moment-matrix entries with scalar Haar integrals. Lines [42](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/MomentBridge.lean:42). |
| [TensV](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:30) (abbrev) | `TensorPower.lean` | Tensor-space type in statements and constructions. Lines [25](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/MomentBridge.lean:25), [26](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/MomentBridge.lean:26), [33](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/MomentBridge.lean:33); more in JSON. |

**Helper and indirect dependencies.** Uses `SchurWeyl.trace_comp_eq_sum_toEndMatrix` from `SupportingDocs/TensorPowerTraces`. Its own analytic work uses upstream `integrable_actOn_entry` and `toEndMatrix_momentOp`; it does not invoke a moment-decomposition theorem.

**Overlap/reuse.** Both bridge theorems are generic in `d` and `k`, with no QML-specific hypotheses. They are good candidates for the shared Haar API.

- Promote the two trace-integral bridge theorems to shared Haar support after extracting the tensor-coordinate trace identity they use. **Impact:** the shared module must not import `QML` or completed moment examples; otherwise moving the declarations would introduce a dependency cycle.
- Keep forwarding theorems in the `QML` namespace during migration. **Impact:** `HaarMoments` and `CommutatorTrace` can preserve their statements and calls while other applications gain access to the same integration lemmas.

**5. [QML/HaarMoments.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/HaarMoments.lean)**

First and second Haar moments of a conjugated matrix, including inverse-unitary integration.

Validation: source audit; build blocked by `TensorPowerTraces`.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [haarProb](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:108) (def) | `Haar.lean` | The existing normalized Haar measure. Lines [34](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/HaarMoments.lean:34), [73](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/HaarMoments.lean:73), [85](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/HaarMoments.lean:85). |
| [actOn](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:141) (def) | `Haar.lean` | Unitary tensor-power conjugation. Lines [37](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/HaarMoments.lean:37), [73](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/HaarMoments.lean:73), [85](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/HaarMoments.lean:85); more in JSON. |
| [momentOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:194) (def) | `Haar.lean` | The Haar moment operator being evaluated or reused. Lines [59](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/HaarMoments.lean:59). |
| [TensV](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:30) (abbrev) | `TensorPower.lean` | Tensor-space type in statements and constructions. Lines [37](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/HaarMoments.lean:37), [60](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/HaarMoments.lean:60), [62](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/HaarMoments.lean:62); more in JSON. |

**Helper and indirect dependencies.** Uses root-level `k1_moment`, `k2_moment`, and `𝔽`; `QML.haar_integral_trace_comp_actOn`; shared `tensorOp`, `tensorPow`, and their trace identities. Inversion invariance comes from the instance in `SupportingDocs/HaarInvariance`. The upstream decomposition is reached through the moment examples.

**Overlap/reuse.** `cId` and `cSwap` name the `k2_moment` coefficients after specializing to `tensorPow d 2 M`. They are useful specializations, not new general Weingarten definitions. Preserve the bridge `momentOp_tensorPow_two` rather than independently re-proving these coefficients.

- Keep `cId` and `cSwap` as named specializations and continue proving their operator formula through `k2_moment`. **Impact:** cost and commutator proofs keep readable coefficients; no second coefficient-solving proof needs maintenance.
- If general second-moment coefficient functions are extracted, define these wrappers through them and retain equations exposing the current scalar formulas. **Impact:** proofs using `simp only [cId, cSwap]` may need those new equations or an additional unfold; `Observation56` and `Observation57` should retain their final formulas.

**6. [QML/CostFunction.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/CostFunction.lean)**

Defines cost, gradient, scalar Haar expectations/variances, and computes the first two cost moments.

Validation: source audit; build blocked by `TensorPowerTraces`.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [haarProb](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:108) (def) | `Haar.lean` | The existing normalized Haar measure. Lines [43](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/CostFunction.lean:43), [52](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/CostFunction.lean:52). |
| [actOn](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:141) (def) | `Haar.lean` | Unitary tensor-power conjugation. Lines [69](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/CostFunction.lean:69). |
| [TensV](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:30) (abbrev) | `TensorPower.lean` | Tensor-space type in statements and constructions. Lines [69](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/CostFunction.lean:69). |

**Helper and indirect dependencies.** Calls `haar_integral_trace_conj` and `haar_integral_trace_comp_actOn_tensorPow_two` from `QML/HaarMoments`, plus shared tensor trace identities. Thus its evaluated moments ultimately use `k1_moment`/`k2_moment` and upstream `weingarten_moment_haar`.

**Overlap/reuse.** `haarExp`/`haarExp₂` are scalar integrals over upstream `haarProb`; they do not duplicate the operator-valued `momentOp`. `cost` and `gradient` add the application-specific trace expressions.

- Keep the scalar expectation wrappers and application-specific `cost`/`gradient` definitions. **Impact:** no downstream migration is needed; replacing them with `momentOp` would change the types rather than remove duplication.
- If more applications need scalar Haar expectations, move only the expectation operations into shared support and retain the QML names as wrappers. **Impact:** the observation proofs can keep their interface, but unfolding-based proofs may need a shared integral-expansion lemma. Preserve the present complex square-moment convention when moving the variance definitions.

**7. [QML/CommutatorTrace.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/CommutatorTrace.lean)**

Algebraic commutator trace identities and the Haar average of a squared commutator.

Validation: source audit; build blocked by `TensorPowerTraces`.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [haarProb](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:108) (def) | `Haar.lean` | The existing normalized Haar measure. Lines [54](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/CommutatorTrace.lean:54). |
| [actOn](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:141) (def) | `Haar.lean` | Unitary tensor-power conjugation. Lines [57](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/CommutatorTrace.lean:57), [64](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/CommutatorTrace.lean:64), [66](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/CommutatorTrace.lean:66). |
| [TensV](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:30) (abbrev) | `TensorPower.lean` | Tensor-space type in statements and constructions. Lines [63](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/CommutatorTrace.lean:63), [65](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/CommutatorTrace.lean:65), [68](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/CommutatorTrace.lean:68); more in JSON. |

**Helper and indirect dependencies.** The purely algebraic `trace_commutator` and `trace_commutator_sq` need no upstream theorem. The integral theorem calls `haar_integral_trace_comp_actOn_inv_tensorPow_two`, `integrable_trace_comp_actOn`, shared tensor/swap trace identities, and root-level `swap_swap`; this reaches the second-moment decomposition.

**Overlap/reuse.** The algebraic lemmas could live separately from the Haar imports if a lightweight reusable matrix API is desired. The commutator average is an application, not a duplicate of an upstream theorem.

- Optionally extract `trace_commutator` and `trace_commutator_sq` into a matrix-algebra support file that imports only their algebraic prerequisites. **Impact:** other clients can use them without Haar infrastructure; leave the integral theorem in this application.
- Preserve the existing theorem names through forwarding declarations or imports. **Impact:** `Observation57` can continue using the same commutator identities; renaming them would require updating its rewrites.

**8. [QML/Observation56.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/Observation56.lean)**

Expectation and variance of the cost on `d = 2^n`, with the stated trace hypotheses.

Validation: source audit; build blocked by `TensorPowerTraces`.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| None explicitly named | — | Upstream dependence is through the helper declarations described below. |

**Helper and indirect dependencies.** Uses `haarExp`, `haarVar`, `cost`, `haar_expectation_cost`, `haar_expectation_cost_sq`, `cId`, and `cSwap` from the QML helpers. Its source names no upstream declaration directly, but these helper proofs reach `k1_moment`, `k2_moment`, and `weingarten_moment_haar`.

**Overlap/reuse.** No new upstream-like definitions. Keep the observation as a thin specialization of the helper theorems.

- No local deduplication is needed. Keep the observation expressed through the cost-moment helpers. **Impact:** changes to the upstream moment implementation remain confined to those helpers.
- When changing `cId`/`cSwap` or their namespaces, update this file’s explicit coefficient simplifications, or preserve the old equations. **Impact:** this is a downstream proof-maintenance task; the observation statements need not change.

**9. [QML/Observation57.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/Observation57.lean)**

Expectation and variance of the gradient for two independent Haar unitaries.

Validation: source audit; build blocked by `TensorPowerTraces`.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [haarProb](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:108) (def) | `Haar.lean` | The existing normalized Haar measure. Lines [27](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/Observation57.lean:27), [49](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/QML/Observation57.lean:49). |

**Helper and indirect dependencies.** Uses the QML cost/gradient/expectation definitions; `haar_integral_trace_conj`, `haar_expectation_cost_sq`, `trace_commutator`, and `haar_integral_trace_commutator_sq`. The evaluated results reach the first and second moment examples.

**Overlap/reuse.** No new upstream-like definitions. The direct `haarProb` occurrences specify the inner integrals; most mathematical dependencies are deliberately hidden behind the QML helpers.

- No new shared definition is needed here; retain the calls to the cost and commutator moment helpers. **Impact:** the two-unitary calculation continues to reuse the first/second moment results.
- After relocating expectation wrappers or commutator lemmas, check the integral expansions and coefficient simplifications in this file. **Impact:** compatibility names should keep most proofs unchanged; removing them requires updating qualified references and unfolds.

**10. [ClassicalShadows/SnapshotEnsemble.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/SnapshotEnsemble.lean)**

Finite weighted snapshots over an arbitrary field/module, measurement channel, inverse, and estimators.

Validation: resolved source references checked against the current successful build.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| None explicitly named | — | No upstream import or helper dependency. |

**Helper and indirect dependencies.** Only Mathlib and shared trace notation are imported. There is no upstream dependency, even through its import chain.

**Overlap/reuse.** `measurementChannel` is a finite sum with arbitrary weights. It is not upstream `momentOp`, which averages unitary conjugations, and is not literally the continuous Haar ensemble in `Observation59`. A future common averaging abstraction would need to support both finite sums and measures.

- Keep the finite weighted ensemble separate from the Haar-integrated ensemble. **Impact:** `Observation58` retains its arbitrary-field/module generality and avoids new measure-theoretic or integrability assumptions.
- If a common averaging interface is later introduced, first add an adapter for finite weighted sums and prove it preserves `measurementChannel`. **Impact:** estimators and the inverse-channel API can then remain stable; replacing the structure outright would affect every `SnapshotEnsemble` consumer.

**11. [ClassicalShadows/TraceContractions.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/TraceContractions.lean)**

Generic linear trace contractions on tensor products of endomorphism spaces.

Validation: resolved source references checked against the current successful build.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| None explicitly named | — | No upstream import or helper dependency. |

**Helper and indirect dependencies.** Only Mathlib and shared trace notation are imported. There is no upstream dependency.

**Overlap/reuse.** `partialTraceFirst`, `doubleTraceContract`, and `tripleTraceContract` act on tensor products of endomorphisms. They do not duplicate `toEndMatrix` or `TensV`. Reusing them in the entrywise Haar proof requires an explicit bridge to endomorphisms of tensor powers.

- Add a separate bridge from tensors of endomorphisms to endomorphisms of tensor products, with trace-contraction compatibility lemmas. **Impact:** concrete Haar proofs could reuse these contractions, while the existing generic statements remain unchanged.
- Place finite-dimensional hypotheses needed for an equivalence on that bridge, not on this entire file. **Impact:** `SnapshotEnsemble` and `Observation58` keep their broader hypotheses; only clients requiring the concrete identification take on the stronger assumptions.

**12. [ClassicalShadows/DepolarizingChannel.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/DepolarizingChannel.lean)**

The abstract depolarizing map, its explicit inverse, and a linear equivalence.

Validation: resolved source references checked against the current successful build.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| None explicitly named | — | No upstream import or helper dependency. |

**Helper and indirect dependencies.** Only Mathlib and shared trace notation are imported. There is no upstream dependency.

**Overlap/reuse.** This is an algebraic formula, not a new Haar integral. `Observation59.haarMeasurementChannelEquiv` already reuses it and proves agreement with the physical Haar channel under the dimension assumptions.

- Keep `depolarizingChannelEquiv` as the single implementation of the explicit inverse. **Impact:** `Observation59` continues to specialize it instead of maintaining another inverse proof.
- If this file is promoted to general support, retain its namespace or supply compatibility declarations. **Impact:** the Haar channel identification only needs an import adjustment; its dimension and nonzero-denominator obligations remain unchanged.

**13. [ClassicalShadows/Observation58.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation58.lean)**

Expresses a finite ensemble channel and estimator variance as second/third tensor-moment contractions.

Validation: resolved source references checked against the current successful build.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| None explicitly named | — | No upstream import or helper dependency. |

**Helper and indirect dependencies.** Uses `SnapshotEnsemble`, `measurementChannel`, `outcomeWeight`, `invChannel`, `secondMoment_observableEstimator`, and the generic trace contractions. Neither this file nor those dependencies uses the upstream code.

**Overlap/reuse.** `secondTensorMoment` and `thirdTensorMoment` are tensors in `End(V) ⊗ End(V)` and `End(V) ⊗ (End(V) ⊗ End(V))`, not upstream endomorphisms of `TensV`. `thirdMoment` is their scalar contraction, not a second competing tensor definition. Preserve the general field/module formulation.

- Keep `secondTensorMoment` and `thirdTensorMoment` in their current tensor-of-endomorphisms form; connect them to concrete tensor-space operators through separate bridge theorems. **Impact:** the existing contraction proofs and arbitrary-field statements survive unchanged.
- If more tensor orders are needed, introduce a general finite-ensemble tensor-moment construction and prove the order-two/order-three specializations. **Impact:** handle tensor association explicitly before replacing these definitions; direct replacement can break existing `rfl` and simplification proofs.

**14. [ClassicalShadows/UnitarySnapshots.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean)**

Computational-basis snapshots and their Haar tensor moments; evaluates the second moment.

Validation: source audit; build blocked by `TensorPowerTraces`.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [endOf](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:128) (def) | `Haar.lean` | Matrix-to-endomorphism conversion. Lines [51](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean:51), [52](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean:52). |
| [actOn](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:141) (def) | `Haar.lean` | Unitary tensor-power conjugation. Lines [60](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean:60), [61](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean:61). |
| [momentOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:194) (def) | `Haar.lean` | The Haar moment operator being evaluated or reused. Lines [69](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean:69). |
| [TensV](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:30) (abbrev) | `TensorPower.lean` | Tensor-space type in statements and constructions. Lines [68](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean:68), [72](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean:72), [76](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean:76); more in JSON. |
| [diagAction](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:61) (def) | `TensorPower.lean` | Tensor power of an endomorphism. Lines [59](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean:59), [60](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean:60), [69](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean:69); more in JSON. |
| [diagAction_comp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:76) (theorem) | `TensorPower.lean` | Multiplicativity of tensor powers. Lines [61](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/UnitarySnapshots.lean:61). |

**Helper and indirect dependencies.** Uses root-level `k2_moment`/`𝔽` and shared `trace_diagAction`/`trace_swap_comp_diagAction`. `diagAction_unitarySnapshot` identifies the tensor snapshot with upstream `actOn` at `star U`.

**Overlap/reuse.** `unitarySnapshotMoment d k` is defined directly as a sum of upstream `momentOp` values, so it reuses rather than rebuilds Haar integration. `basisProjector` uses `Matrix.toLin'` directly, the same conversion wrapped by upstream `endOf`. The physical integral identification is completed using inversion invariance in `Observation59`.

- Optionally express `basisProjector` through `endOf (Matrix.single b b 1)` to use the common conversion API. **Impact:** the underlying map is unchanged by unfolding `endOf`, but the projector proofs may need that extra unfold or conversion lemmas.
- Retain the definition of `unitarySnapshotMoment` as a sum of `momentOp` values, and expose the physical-integral identity as a reusable bridge. **Impact:** `Observation59` could reuse the bridge while `unitarySnapshotMoment_two` and its contraction clients retain their current interface.

**15. [ClassicalShadows/MomentContraction.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/MomentContraction.lean)**

Contracts the explicit second snapshot moment against a state in matrix coordinates.

Validation: source audit; build blocked by `TensorPowerTraces`.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [tensorBasis](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:33) (def) | `DirectProof.lean` | Computational tensor basis for traces and matrix conversion. Lines [38](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/MomentContraction.lean:38). |
| [toEndMatrix](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:38) (def) | `DirectProof.lean` | Coordinates of tensor-space endomorphisms. Lines [35](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/MomentContraction.lean:35), [37](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/MomentContraction.lean:37), [48](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/MomentContraction.lean:48); more in JSON. |
| [TensV](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:30) (abbrev) | `TensorPower.lean` | Tensor-space type in statements and constructions. Lines [35](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/MomentContraction.lean:35), [37](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/MomentContraction.lean:37). |

**Helper and indirect dependencies.** Uses `unitarySnapshotMoment_two`, shared `matrixOf`, `trace_eq_sum_diag`, and `toEndMatrix_swap`, plus root-level `𝔽`. Hence the numerical channel formula reaches `k2_moment` and upstream `weingarten_moment_haar`.

**Overlap/reuse.** `toEndMatrix_id_pair` and `toEndMatrix_swap_pair` specialize general matrix entries to the indices needed for partial trace. They are useful corollaries. A tensor-product/operator equivalence would allow reuse of the generic `partialTraceFirst` API.

- Keep the pair-index entry lemmas as convenience corollaries of the shared identity/swap matrix API. **Impact:** centralizing the underlying facts can shorten their proofs without changing `Observation59` callers.
- Once the tensor/operator bridge exists, reprove the contraction using `partialTraceFirst` and derive the current entrywise theorem as a corollary. **Impact:** this could remove repeated index summations, but requires a real representation-conversion proof before the present calculation can be replaced.

**16. [ClassicalShadows/Observation59.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean)**

Defines the Born-weighted Haar measurement channel and identifies its explicit map and inverse.

Validation: source audit; build blocked by `TensorPowerTraces`.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [toEndMatrix](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:38) (def) | `DirectProof.lean` | Coordinates of tensor-space endomorphisms. Lines [52](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean:52), [55](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean:55), [61](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean:61); more in JSON. |
| [haarProb](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:108) (def) | `Haar.lean` | The existing normalized Haar measure. Lines [50](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean:50), [54](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean:54), [84](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean:84); more in JSON. |
| [actOn](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:141) (def) | `Haar.lean` | Unitary tensor-power conjugation. Lines [61](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean:61), [70](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean:70). |
| [continuous_actOn_entry](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:163) (theorem) | `Haar.lean` | Continuity used to justify scalar integration. Lines [72](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean:72). |
| [momentOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:194) (def) | `Haar.lean` | The Haar moment operator being evaluated or reused. Lines [55](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean:55). |
| [toEndMatrix_momentOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:198) (theorem) | `Haar.lean` | Identifies moment-matrix entries with scalar Haar integrals. Lines [68](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean:68). |
| [diagAction](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:61) (def) | `TensorPower.lean` | Tensor power of an endomorphism. Lines [55](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean:55), [61](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean:61), [70](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/ClassicalShadows/Observation59.lean:70); more in JSON. |

**Helper and indirect dependencies.** Uses `unitarySnapshot`, `diagAction_unitarySnapshot`, `unitarySnapshotMoment`, `contract_unitarySnapshotMoment_two`, shared `trace_comp_mul_matrixOf`, `integral_star_haarProb`, `integrable_haarProb_of_continuous`, and the abstract `depolarizingChannelEquiv`/`depolarizingChannel_apply`. The channel formula reaches the second moment example.

**Overlap/reuse.** `haarMeasurementChannel` repeats the entrywise-integration construction pattern of upstream `momentMatrix`/`momentOp`, but with a different integrand and output space. A generic entrywise integral/linear-map-commutes-with-integral API could remove this scaffolding. `haarMeasurementChannelEquiv` already avoids duplicating the inverse proof.

- Extract a basis-indexed entrywise averaging helper, with finite-sum and contraction compatibility under the required integrability hypotheses. **Impact:** both this channel and upstream `momentOp` could share integration infrastructure; retain their current public definitions or prove compatibility equations before changing implementations.
- Continue constructing `haarMeasurementChannelEquiv` through `depolarizingChannelEquiv`. **Impact:** the inverse formula remains centralized; only the proof identifying the averaged channel with that equivalence should need adjustment after an integration refactor.

**17. [MagicMonotone/RankOneCalculus.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/RankOneCalculus.lean)**

Hilbert–Schmidt inner product of vectorized operators and generic rank-one composition calculus.

Validation: resolved source references checked against the current successful build.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [tensorBasis](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:33) (def) | `DirectProof.lean` | Computational tensor basis for traces and matrix conversion. Lines [79](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/RankOneCalculus.lean:79), [84](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/RankOneCalculus.lean:84). |
| [toEndMatrix](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:38) (def) | `DirectProof.lean` | Coordinates of tensor-space endomorphisms. Lines [59](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/RankOneCalculus.lean:59), [60](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/RankOneCalculus.lean:60), [61](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/RankOneCalculus.lean:61); more in JSON. |
| [TensV](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:30) (abbrev) | `TensorPower.lean` | Tensor-space type in statements and constructions. Lines [57](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/RankOneCalculus.lean:57), [82](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/RankOneCalculus.lean:82). |
| [endVec](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Weingarten.lean:129) (def) | `Weingarten.lean` | Existing Euclidean vectorization of tensor-space operators. Lines [58](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/RankOneCalculus.lean:58), [63](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/RankOneCalculus.lean:63), [65](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/RankOneCalculus.lean:65). |

**Helper and indirect dependencies.** Directly reuses upstream `endVec` and tensor-basis matrix conversion. The rank-one summation theorems themselves are generic Mathlib inner-product-space results and do not need a Haar moment theorem.

**Overlap/reuse.** `inner_endVec_endVec` generalizes upstream `inner_endVec_perm_eq_trace` from permutation operators to arbitrary operators; promote the general bridge and derive the old one using `permDual_eq_conjTranspose`. `toEndMatrix_mul` has the same mathematical content as upstream `toEndMatrix_comp` (`X * Y` is composition). Vectorization itself is not redefined.

- Move `inner_endVec_endVec` beside upstream `endVec` and derive the permutation trace bridge from it. **Impact:** keep the general proof independent of the old specialization to avoid a proof cycle; a forwarding lemma under `MagicMonotone` preserves `BrickworkLayers` callers.
- Centralize `toEndMatrix_one` and the multiplication/composition compatibility lemmas beside the matrix conversion, with aliases for the existing interfaces. **Impact:** layer proofs can retain their rewrite names; placing these facts below Haar prevents clients from needing a Haar import for basic matrix algebra.
- Optionally split the generic rank-one sum calculus from vectorization-specific lemmas. **Impact:** `Equation24` can reuse the calculus without requiring the whole vectorization development, although its concrete layer definitions still need that development.

**18. [MagicMonotone/SingleGateMoment.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean)**

Writes the fourth moment as a double Weingarten sum and proves its vectorized rank-one representation.

Validation: resolved source references checked against the current successful build.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [momentOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:194) (def) | `Haar.lean` | The Haar moment operator being evaluated or reused. Lines [61](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:61), [94](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:94), [96](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:96). |
| [TensV](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:30) (abbrev) | `TensorPower.lean` | Tensor-space type in statements and constructions. Lines [60](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:60), [83](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:83), [93](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:93). |
| [permOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Weingarten.lean:91) (def) | `Weingarten.lean` | Permutation endomorphisms. Lines [63](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:63), [78](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:78), [86](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:86); more in JSON. |
| [endVec](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Weingarten.lean:129) (def) | `Weingarten.lean` | Existing Euclidean vectorization of tensor-space operators. Lines [78](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:78), [84](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:84), [86](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:86); more in JSON. |
| [inner_endVec_perm_eq_trace](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Weingarten.lean:135) (theorem) | `Weingarten.lean` | Identifies a vectorized permutation inner product with its trace contraction. Lines [88](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:88). |
| [endVecₗ_apply](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/WeingartenInverse.lean:187) (theorem) | `WeingartenInverse.lean` | Uses linear vectorization to commute with sums/scalars. Lines [99](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:99), [100](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:100). |
| [weingartenVec](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/WeingartenInverse.lean:247) (def) | `WeingartenInverse.lean` | Trace contractions forming the linear-system target vector. Lines [63](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:63), [86](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:86), [88](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/SingleGateMoment.lean:88); more in JSON. |

**Helper and indirect dependencies.** Uses `K4.k4_moment`, `K4.coeff`, and `K4.wgVal`. `momentOp_eq_weingarten_sum` unfolds the existing coefficient; `vecMomentOp_endVec` uses upstream vectorization linearity and `inner_endVec_perm_eq_trace`.

**Overlap/reuse.** `vecMomentOp` is a new representation on Euclidean vectors, not an independent Haar construction: `vecMomentOp_endVec` proves compatibility for `4 ≤ d`. A generic version using the upstream inverse Gram matrix and `endVecEquiv` could support other `k ≤ d`.

- Add a generic vectorized moment theorem for `k ≤ d`, using `endVecEquiv` and inverse-Gram coefficients, then recover the fourth-order formula through the explicit `K4` coefficient bridge. **Impact:** other moment orders gain the same interface; establishing the generic theorem is additional work, not a direct rename.
- Keep `vecMomentOp` and `vecMomentOp_endVec` as the fourth-order public interface. **Impact:** current callers retain their types and explicit `wgVal` sums; replacing those sums outright by an abstract transported map would require new expansion lemmas for rewriting.

**19. [MagicMonotone/BrickworkLayers.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean)**

Embeds local copy permutations in a four-qubit register, computes overlaps, and defines two layer operators.

Validation: resolved source references checked against the current successful build.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [toEndMatrix](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:38) (def) | `DirectProof.lean` | Coordinates of tensor-space endomorphisms. Lines [139](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean:139), [203](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean:203), [206](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean:206); more in JSON. |
| [toEndMatrix_permAction](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:49) (theorem) | `DirectProof.lean` | Permutation matrix entries as equality indicators. Lines [145](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean:145). |
| [TensV](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:30) (abbrev) | `TensorPower.lean` | Tensor-space type in statements and constructions. Lines [107](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean:107). |
| [permOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Weingarten.lean:91) (def) | `Weingarten.lean` | Permutation endomorphisms. Lines [139](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean:139), [145](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean:145). |
| [endVec](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Weingarten.lean:129) (def) | `Weingarten.lean` | Existing Euclidean vectorization of tensor-space operators. Lines [249](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean:249), [399](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean:399), [403](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean:403). |
| [weingartenGram](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/WeingartenInverse.lean:243) (def) | `WeingartenInverse.lean` | Gram entries of permutation operators. Lines [292](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean:292), [300](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean:300), [320](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean:320); more in JSON. |
| [weingartenGram_eq_card](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/WeingartenInverse.lean:270) (theorem) | `WeingartenInverse.lean` | Evaluates a Gram entry as a coincidence count. Lines [294](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/BrickworkLayers.lean:294). |

**Helper and indirect dependencies.** Uses `inner_endVec_endVec`, matrix compatibility helpers, and `K4.weingartenGram_closed`, `K4.numCyc`, `K4.wgVal`, `K4.wgVal_inverts_gram`. The overlap proof directly uses `weingartenGram_eq_card`. Although `SingleGateMoment` is imported, the layer definitions/proofs do not call `vecMomentOp_endVec`.

**Overlap/reuse.** `regPermMat` is built from upstream single-qubit `permOp` matrices, then reindexed by `regIndexEquiv`; it is not a duplicate global `permOp 16`, since different qubits can receive different permutations. `hsOverlap` merely wraps the existing `endVec` inner product, and `wg` specializes `K4.wgVal` at 4. A reusable local-operator embedding API could reduce the bespoke index manipulation.

- Extract a reusable local-operator embedding/reindexing construction and derive `regPerm` and its multiplicativity from it. **Impact:** this can reduce index proofs for later circuits, but preserve `toEndMatrix_regPerm` so the current overlap computations still reduce to the same entries.
- Keep `hsOverlap`, `wg`, and the gate labels as lightweight application wrappers. **Impact:** `Equation24` retains readable formulas; if their implementations change, provide expansion lemmas used by existing simplifications.
- Add a theorem identifying each defined layer with the appropriate embedded independent-gate Haar average. **Impact:** this supplies a missing semantic bridge without changing the current algebraic kernel result; use invertibility at gate dimension 4, not at the single-qubit Gram dimension 2.

**20. [MagicMonotone/Equation24.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/MagicMonotone/Equation24.lean)**

Composition of the two defined layer sums, its contracted form, and the explicit kernel.

Validation: resolved source references checked against the current successful build.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| None explicitly named | — | Upstream dependence is through the helper declarations described below. |

**Helper and indirect dependencies.** Calls `sumRankOne_comp_sumRankOne`, `sumRankOne_comp_sumRankOne_kernel`, `layerA_eq_pairSum`, `layerB_eq_pairSum`, `inner_layerAKet_layerBKet`, and `hsOverlap_layer_eq_two_pow`; uses local layer/ket/weight definitions and `K4.numCyc`. It reaches upstream `endVec`, matrix/permutation operators, and the Gram-count identity through those helpers. It does not directly invoke `momentOp`, `k4_moment`, or `vecMomentOp_endVec`.

**Overlap/reuse.** `twoLayerMoment` is defined as `layerA ∘L layerB`, not as a fresh Haar integral. The kernel is a derived coefficient formula. A formal identification of the embedded layer maps with independent local-gate Haar averages would be an additional bridge; importing `SingleGateMoment` does not by itself supply that theorem.

- Keep `twoLayerMoment` and `twoLayerKernel` as the algebraic interface, and prove a separate identification with the physical ensemble after the layer/Haar bridges are available. **Impact:** the current contraction and kernel proofs can remain unchanged; the added theorem would justify applying them directly to that ensemble.
- If the generic rank-one calculus is moved, preserve its theorem names or update the two calls in the contraction proofs. **Impact:** no new kernel calculation should be necessary; this file depends on those composition identities rather than a fresh moment computation.

**21. [SupportingDocs/TensorPowerBasics.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerBasics.lean)**

Generic permutation identities and trace of the tensor-space identity.

Validation: resolved source references checked against the current successful build.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [permMonoidHom](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DCT.lean:37) (def) | `DCT.lean` | Permutation multiplication/identity laws via the monoid homomorphism. Lines [33](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerBasics.lean:33). |
| [tensorBasis](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:33) (def) | `DirectProof.lean` | Computational tensor basis for traces and matrix conversion. Lines [56](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerBasics.lean:56). |
| [TensV](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:30) (abbrev) | `TensorPower.lean` | Tensor-space type in statements and constructions. Lines [55](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerBasics.lean:55). |
| [permOp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Weingarten.lean:91) (def) | `Weingarten.lean` | Permutation endomorphisms. Lines [33](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerBasics.lean:33), [36](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerBasics.lean:36), [41](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerBasics.lean:41); more in JSON. |
| [permDual](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Weingarten.lean:97) (def) | `Weingarten.lean` | Inverse-permutation endomorphisms used in trace contractions. Lines [40](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerBasics.lean:40), [41](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerBasics.lean:41), [50](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerBasics.lean:50); more in JSON. |

**Helper and indirect dependencies.** Directly uses `permMonoidHom`, `permOp`/`permDual`, `tensorBasis`, and `TensV`. No current example file imports this support file.

**Overlap/reuse.** The intended deduplication API already exists here but is unused. Move/reuse its generic facts in a shared upstream layer, then replace the repetitions in `k1Moment`, `k2Moment`, and `k4Moment` with specializations. Keep root/`SchurWeyl`/`SchurWeyl.K4` namespaces explicit during a migration.

- Promote the generic identities to an upstream module whose imports are limited to the permutation and tensor-coordinate infrastructure. **Impact:** moment examples can reuse the lemmas without importing one another; keeping it below Haar avoids unnecessary analytic dependencies.
- Replace duplicated proofs with specializations, retaining temporary forwarding lemmas in the old namespaces. **Impact:** downstream rewrite sites can migrate gradually; qualify `permOp_one`, `permDual_one`, and `permDual_comp_permOp` where the existing root, `SchurWeyl`, and `K4` names would otherwise compete.

**22. [SupportingDocs/TensorPowerTraces.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean)**

Shared matrix tensor products, tensor powers, trace formulas, conjugation, and coordinate contractions.

Validation: source audit; build blocked by `TensorPowerTraces`.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [tensorBasis](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:33) (def) | `DirectProof.lean` | Computational tensor basis for traces and matrix conversion. Lines [69](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:69), [75](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:75), [76](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:76); more in JSON. |
| [toEndMatrix](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:38) (def) | `DirectProof.lean` | Coordinates of tensor-space endomorphisms. Lines [66](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:66), [67](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:67), [108](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:108); more in JSON. |
| [toEndMatrix_permAction](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:49) (theorem) | `DirectProof.lean` | Permutation matrix entries as equality indicators. Lines [111](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:111). |
| [toEndMatrix_diagAction](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:58) (theorem) | `DirectProof.lean` | Tensor-power matrix entries as products. Lines [222](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:222). |
| [endOf](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:128) (def) | `Haar.lean` | Matrix-to-endomorphism conversion. Lines [53](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:53), [70](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:70), [92](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:92); more in JSON. |
| [endOf_mul](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:131) (theorem) | `Haar.lean` | Converts matrix multiplication to composition. Lines [88](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:88). |
| [actOn](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:141) (def) | `Haar.lean` | Unitary tensor-power conjugation. Lines [97](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:97), [100](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:100). |
| [toEndMatrix_comp](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:506) (theorem) | `Haar.lean` | Converts composition into matrix multiplication. Lines [119](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:119), [203](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:203). |
| [TensV](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:30) (abbrev) | `TensorPower.lean` | Tensor-space type in statements and constructions. Lines [52](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:52), [56](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:56), [74](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:74); more in JSON. |
| [permAction](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:38) (def) | `TensorPower.lean` | Underlying tensor-factor permutation action. Lines [110](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:110). |
| [diagAction](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/TensorPower.lean:61) (def) | `TensorPower.lean` | Tensor power of an endomorphism. Lines [92](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:92), [166](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:166), [181](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TensorPowerTraces.lean:181); more in JSON. |

**Helper and indirect dependencies.** Imports `k1Moment` and `k2Moment`; the algebra uses the latter's swap alias `𝔽`, not either moment formula. Direct upstream facts provide matrix entries, conversion, and multiplicativity.

**Overlap/reuse.** `tensorPow d k M` is definitionally upstream `diagAction d k (endOf M)`, explicitly witnessed by `diagAction_eq_tensorPow := rfl`. `tensorOp` genuinely generalizes identical factors to differing matrices. `matrixOf` is the inverse computational-basis conversion to `endOf`, not `toEndMatrix` on a tensor space. Extract the swap alias/basic facts upstream to remove the support file's dependency on completed moment examples.

- Keep `tensorPow` as a matrix-facing wrapper around `diagAction (endOf M)`, with `diagAction_eq_tensorPow` as the stable bridge; retain the more general `tensorOp`. **Impact:** QML statements keep their matrix notation while the underlying tensor-power action has one implementation.
- Extract swap basics first, then replace imports of completed moment examples with the lower-level prerequisites. **Impact:** QML `HaarMoments` and classical-shadow `UnitarySnapshots` will need explicit imports of the moment results they currently receive transitively; check those imports when removing this accidental re-export.
- Keep `matrixOf`/`endOf` conversion equations public when moving the coordinate API. **Impact:** the entrywise shadow proofs can retain their rewrite interface. Separately repair the already reported `permAction` argument mismatch before validating the affected QML/shadow refactors.

**23. [SupportingDocs/HaarInvariance.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/HaarInvariance.lean)**

Right/inverse invariance and regularity instances for the existing Haar probability measure.

Validation: resolved source references checked against the current successful build.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| [haar_univ_ne_zero](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:94) (theorem) | `Haar.lean` | Positivity needed for the normalized Haar-measure instance. Lines [91](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/HaarInvariance.lean:91). |
| [haar_univ_ne_top](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:102) (theorem) | `Haar.lean` | Finiteness needed for the normalized Haar-measure instance. Lines [90](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/HaarInvariance.lean:90). |
| [haarProb](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/Haar.lean:108) (def) | `Haar.lean` | The existing normalized Haar measure. Lines [89](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/HaarInvariance.lean:89), [94](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/HaarInvariance.lean:94), [95](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/HaarInvariance.lean:95); more in JSON. |

**Helper and indirect dependencies.** Uses upstream `haarProb`, `haar_univ_ne_zero`, and `haar_univ_ne_top`, together with the upstream compactness/measurability/probability infrastructure supplied through typeclass inference. The first three abstract compact-group theorems are generic Mathlib-based results.

**Overlap/reuse.** No new Haar measure is defined. These instances and `integral_star_haarProb`/continuous integrability belong naturally alongside `haarProb` in the shared Haar API.

- Move the specialized `haarProb` invariance/regularity instances and integration facts to shared Haar support; keep the abstract compact-group lemmas in a suitable general support module. **Impact:** both QML and shadows can obtain the same instances without importing example code.
- Remove the old instance declarations when relocating them, and let the old module forward imports. **Impact:** this avoids competing instance registrations while preserving existing import paths; recheck inverse-integral rewrites and integrability proofs after changing instance availability.

**24. [SupportingDocs/TraceNotation.lean](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/ForMathlibExamples/SupportingDocs/TraceNotation.lean)**

Scoped notation `ClassicalShadows.Tr[A]` for Mathlib's `LinearMap.trace`.

Validation: resolved source references checked against the current successful build.

| Upstream declaration | Defined in | Use in this file |
|---|---|---|
| None explicitly named | — | No upstream import or helper dependency. |

**Helper and indirect dependencies.** Only Mathlib is imported. There is no upstream dependency.

**Overlap/reuse.** A notation alias, not a new trace definition. It is already centralized and should stay shared.

- Keep the existing scoped notation and shared import. **Impact:** there is no duplicate trace implementation to remove, and classical-shadow statements remain unchanged.
- If the notation module moves, preserve the `ClassicalShadows` scope and forward the old import. **Impact:** consumers avoid parsing or scope-resolution changes; replacing every notation occurrence with an expanded trace expression would add churn without reducing mathematical redundancy.

**Prioritized redundancy recommendations (not applied)**

| Priority | Existing overlap | Suggested consolidation |
|---|---|---|
| 1 | Identity/multiplication/dual identities repeated in `k1Moment`, `k2Moment`, `K4`, and the unused `SupportingDocs/TensorPowerBasics`. | Promote/reuse the general support API, specialize it for each `k`, and move the swap alias/basic facts below the moment examples in the import hierarchy. This also removes the inverted dependency of `TensorPowerTraces` on completed applications. |
| 1 | `MagicMonotone.toEndMatrix_mul` versus upstream `Haar.toEndMatrix_comp`; identity-matrix facts scattered across clients. | Provide one matrix-conversion API beside `tensorBasis`/`toEndMatrix` in `DirectProof`. Multiplication and composition versions should be small aliases, avoiding a Haar import merely for a linear-algebra fact. |
| 1 | `inner_endVec_endVec` versus upstream `inner_endVec_perm_eq_trace`. | Move the arbitrary-operator Hilbert–Schmidt identity beside `endVec`; derive the permutation specialization from it and `permDual_eq_conjTranspose`. |
| 2 | `tensorPow` versus upstream `diagAction (endOf M)`. | Keep one implementation and expose a matrix-facing alias plus the existing `rfl` bridge. Keep `tensorOp` as the genuinely more general varying-factor API; promote the useful trace laws. |
| 2 | Haar support and integral bridges live in applications. | Move `HaarInvariance` instances and generic `QML/MomentBridge` facts to shared Haar support; consider a generic entrywise averaging helper for both `momentOp` and `haarMeasurementChannel`. |
| 2 | `K4.coeff` and the general upstream inverse-Gram solution. | Add a theorem equating the explicit coefficient to the inverse-Gram formula using `weingarten_solution_eq_inv`. Retain the explicit `wgVal` formulas: they are computational content missing from the abstract inverse API. |
| 3 | Abstract tensor-of-endomorphism contractions versus concrete tensor-space matrix contractions. | Add the appropriate tensor-product/operator conversion theorem before attempting to share proofs. Finite weighted ensembles and continuous Haar ensembles are not definitionally the same object. |
| 3 | `regPermMat`/`regPerm` and layer constructions. | Extract reusable register-reindexing/local-operator embeddings if more circuits will use them. Retain `wg`, `hsOverlap`, and the gate labels as readable application aliases rather than treating each alias as harmful duplication. |

There is also redundancy inside upstream itself: [SmallDim.tensorBasis' / toEndMatrix'](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/SmallDim.lean:31) and [DirectProof.tensorBasis / toEndMatrix](/Users/melod/Desktop/research/lean-haar/LeanHaar/ForMathlib/DirectProof.lean:33) use the same computational tensor basis and matrix conversion construction. These primed/unprimed APIs can be centralized in a lower-level coordinate module to avoid cycles. Similarly, `permAction`, `permMonoidHom`, `permRep`, and `permOp` expose the same permutation action in different structures; preserve the useful interfaces but derive their laws from a single canonical action.

- Move the common tensor basis and matrix conversion into a module imported by both `SmallDim` and `DirectProof`, and retain the primed/unprimed names as wrappers initially. **Impact:** this avoids making either existing module depend on the other; preserve conversion equations so example proofs that unfold the basis continue to work.
- Derive `permMonoidHom` and the representation-facing interfaces from the canonical permutation action while preserving their public types. **Impact:** downstream uses of `map_one` and `map_mul` can remain stable, but check proofs relying on `rfl` between `permRep`, `permOp`, and the underlying action before changing reducibility or implementation details.

**What the deeper upstream dependencies mean**

The call `weingarten_moment_haar` uses `momentOp_mem_span`, `momentOp_trace`, and `weingarten_moment_decomposition_of_props`. `momentOp_mem_span` reaches `schur_weyl` in `Main`, which reaches the commutation and double-centralizer development through `DirectProof`/`SmallDim`, `DCT`, and `PolyIndep`. Those modules therefore matter to the evaluated Haar moments even though no example explicitly names `schur_weyl`. The pure rank-one/overlap calculations do not acquire this proof dependency merely by importing a module that also contains it.

For the fourth moment, `weingarten_solution_unique` separately reaches `linearIndependent_endVec_permOp`, the Gram/vector bridges, and `gram_system_unique`. The explicit example proof calls uniqueness, not `weingarten_solution_eq_inv` directly. In particular, do not describe every occurrence of `weingartenGram` as a use of matrix inversion: the Gram matrix is valid even when `k > d`, such as local qubits with `d = 2, k = 4` in `BrickworkLayers`. The inverse certificate used for the gate coefficients is at `d = 4, k = 4`.

**Elaborated dependency appendix**

For each verified file, the following table gives additional direct upstream constants present in elaborated types/proofs but not explicitly named in source, and the transitive upstream closure grouped by owning file. The closure starts from every declaration belonging to that example file, including private/generated declarations, then recursively follows constant references through local and upstream declarations. It stops at external-library declarations. Generated implementation constants are retained in JSON but omitted from these human-readable lists. This is proof/definition reachability, not an import closure; definitionally unfolded constants can make the direct set differ from the explicit-reference table.

**k1Moment.lean**

Additional elaborated direct constants: `SchurWeyl.tensV_module_finite`.

| Upstream file | Transitively used declarations |
|---|---|
| Commutation.lean | `permAction_diagAction_comm`, `permAction_diagAction_tprod`, `permImage_subset_centralizer_diagImage` |
| DCT.lean | `PermModule`, `doubleCentralizer_to_endEndModule`, `double_centralizer_permImage'`, `endModule_mem_centralizer`, `mem_span_permImage_of_mem_range`, `neZero_card_perm`, `permAlgHom`, `permAlgHom_of`, `permAlgHom_range_eq`, `permModule_finite_over_endRing`, `permModule_isSemisimple`, `permModule_toModuleEnd_surjective`, `permMonoidHom`, `permRep`, `tensV_module_finite` |
| DirectProof.lean | `centralizer_diagImage_le_span_permImage`, `diagAction_diagonal`, `tensorBasis`, `toEndMatrix`, `toEndMatrix_diagAction` |
| Haar.lean | `actOn`, `cols_mul_diag_sqrt`, `comm_diagAction_diagonal`, `comm_diagAction_diagonal_entry`, `conjTranspose_mul_self_of_spectral`, `conj_actOn`, `continuous_actOn_entry`, `diagAction_endOf_unitary_left`, `diagonal_mem_unitaryGroup`, `endOf`, `endOf_mul`, `endOf_one`, `exists_orthonormalBasis_cols`, `exists_unitary_of_orthonormalBasis`, `haarProb`, `instBorelSpaceUnitaryGroup`, `instCompactSpaceUnitaryGroup`, `instIsMulLeftInvariantHaarProb`, `instIsProbabilityMeasureHaarProb`, `instMeasurableSpaceUnitaryGroup`, `integrable_actOn_entry`, `isCompact_unitaryGroup`, `mem_centralizer_of_comm_unitary`, `momentMatrix`, `momentOp`, `momentOp_comm_unitary`, `momentOp_conj_unitary`, `momentOp_mem_span`, `momentOp_trace`, `prod_eq_of_torus`, `svd_exists`, `svd_spectral`, `toEndMatrix_comp`, `toEndMatrix_diagAction_diagonal`, `toEndMatrix_momentOp`, `trace_permDual_actOn`, `unitary_entry_norm_le_one`, `weingarten_moment_haar` |
| Main.lean | `schur_weyl`, `span_permImage_le_centralizer_diagImage` |
| PolyIndep.lean | `monomial_coeff_zero_of_eval_zero` |
| SmallDim.lean | `centralizer_diagImage_le_span_permImage_small`, `centralizer_permImage_le_span_diagImage`, `double_centralizer_permImage`, `exists_functional_separation`, `matrix_orbit_invariant`, `pairCount`, `permAction_tensorBasis'`, `prod_eq_monomial_eval`, `sum_group_by_pairCount`, `sum_vanishes_of_coeff_and_const`, `tensorBasis'`, `toEndMatrix'`, `toEndMatrix'_diagAction` |
| TensorPower.lean | `TensV`, `diagAction`, `diagAction_comp`, `diagAction_tprod`, `diagImage`, `permAction`, `permAction_tprod`, `permImage` |
| Weingarten.lean | `permDual`, `permOp`, `trace_permDual_comp_sum`, `weingarten_moment_decomposition_of_props` |

**k2Moment.lean**

Additional elaborated direct constants: none.

| Upstream file | Transitively used declarations |
|---|---|
| Commutation.lean | `permAction_diagAction_comm`, `permAction_diagAction_tprod`, `permImage_subset_centralizer_diagImage` |
| DCT.lean | `PermModule`, `doubleCentralizer_to_endEndModule`, `double_centralizer_permImage'`, `endModule_mem_centralizer`, `mem_span_permImage_of_mem_range`, `neZero_card_perm`, `permAlgHom`, `permAlgHom_of`, `permAlgHom_range_eq`, `permModule_finite_over_endRing`, `permModule_isSemisimple`, `permModule_toModuleEnd_surjective`, `permMonoidHom`, `permRep`, `tensV_module_finite` |
| DirectProof.lean | `centralizer_diagImage_le_span_permImage`, `diagAction_diagonal`, `permAction_tensorBasis`, `tensorBasis`, `toEndMatrix`, `toEndMatrix_diagAction`, `toEndMatrix_permAction` |
| Haar.lean | `actOn`, `cols_mul_diag_sqrt`, `comm_diagAction_diagonal`, `comm_diagAction_diagonal_entry`, `conjTranspose_mul_self_of_spectral`, `conj_actOn`, `continuous_actOn_entry`, `diagAction_endOf_unitary_left`, `diagonal_mem_unitaryGroup`, `endOf`, `endOf_mul`, `endOf_one`, `exists_orthonormalBasis_cols`, `exists_unitary_of_orthonormalBasis`, `haarProb`, `instBorelSpaceUnitaryGroup`, `instCompactSpaceUnitaryGroup`, `instIsMulLeftInvariantHaarProb`, `instIsProbabilityMeasureHaarProb`, `instMeasurableSpaceUnitaryGroup`, `integrable_actOn_entry`, `isCompact_unitaryGroup`, `mem_centralizer_of_comm_unitary`, `momentMatrix`, `momentOp`, `momentOp_comm_unitary`, `momentOp_conj_unitary`, `momentOp_mem_span`, `momentOp_trace`, `prod_eq_of_torus`, `svd_exists`, `svd_spectral`, `toEndMatrix_comp`, `toEndMatrix_diagAction_diagonal`, `toEndMatrix_momentOp`, `trace_permDual_actOn`, `unitary_entry_norm_le_one`, `weingarten_moment_haar` |
| Main.lean | `schur_weyl`, `span_permImage_le_centralizer_diagImage` |
| PolyIndep.lean | `monomial_coeff_zero_of_eval_zero` |
| SmallDim.lean | `centralizer_diagImage_le_span_permImage_small`, `centralizer_permImage_le_span_diagImage`, `double_centralizer_permImage`, `exists_functional_separation`, `matrix_orbit_invariant`, `pairCount`, `permAction_tensorBasis'`, `prod_eq_monomial_eval`, `sum_group_by_pairCount`, `sum_vanishes_of_coeff_and_const`, `tensorBasis'`, `toEndMatrix'`, `toEndMatrix'_diagAction` |
| TensorPower.lean | `TensV`, `diagAction`, `diagAction_comp`, `diagAction_tprod`, `diagImage`, `permAction`, `permAction_tprod`, `permImage` |
| Weingarten.lean | `permDual`, `permOp`, `trace_permDual_comp_sum`, `weingarten_moment_decomposition_of_props` |

**k4Moment.lean**

Additional elaborated direct constants: none.

| Upstream file | Transitively used declarations |
|---|---|
| Commutation.lean | `permAction_diagAction_comm`, `permAction_diagAction_tprod`, `permImage_subset_centralizer_diagImage` |
| DCT.lean | `PermModule`, `doubleCentralizer_to_endEndModule`, `double_centralizer_permImage'`, `endModule_mem_centralizer`, `mem_span_permImage_of_mem_range`, `neZero_card_perm`, `permAlgHom`, `permAlgHom_of`, `permAlgHom_range_eq`, `permModule_finite_over_endRing`, `permModule_isSemisimple`, `permModule_toModuleEnd_surjective`, `permMonoidHom`, `permRep`, `tensV_module_finite` |
| DirectProof.lean | `centralizer_diagImage_le_span_permImage`, `diagAction_diagonal`, `permAction_tensorBasis`, `tensorBasis`, `toEndMatrix`, `toEndMatrix_diagAction`, `toEndMatrix_permAction` |
| Haar.lean | `actOn`, `cols_mul_diag_sqrt`, `comm_diagAction_diagonal`, `comm_diagAction_diagonal_entry`, `conjTranspose_mul_self_of_spectral`, `conj_actOn`, `continuous_actOn_entry`, `diagAction_endOf_unitary_left`, `diagonal_mem_unitaryGroup`, `endOf`, `endOf_mul`, `endOf_one`, `exists_orthonormalBasis_cols`, `exists_unitary_of_orthonormalBasis`, `haarProb`, `instBorelSpaceUnitaryGroup`, `instCompactSpaceUnitaryGroup`, `instIsMulLeftInvariantHaarProb`, `instIsProbabilityMeasureHaarProb`, `instMeasurableSpaceUnitaryGroup`, `integrable_actOn_entry`, `isCompact_unitaryGroup`, `mem_centralizer_of_comm_unitary`, `momentMatrix`, `momentOp`, `momentOp_comm_unitary`, `momentOp_conj_unitary`, `momentOp_mem_span`, `momentOp_trace`, `prod_eq_of_torus`, `svd_exists`, `svd_spectral`, `toEndMatrix_comp`, `toEndMatrix_diagAction_diagonal`, `toEndMatrix_momentOp`, `trace_permDual_actOn`, `unitary_entry_norm_le_one`, `weingarten_moment_haar` |
| Main.lean | `schur_weyl`, `span_permImage_le_centralizer_diagImage` |
| PolyIndep.lean | `monomial_coeff_zero_of_eval_zero` |
| SmallDim.lean | `centralizer_diagImage_le_span_permImage_small`, `centralizer_permImage_le_span_diagImage`, `double_centralizer_permImage`, `exists_functional_separation`, `matrix_orbit_invariant`, `pairCount`, `permAction_tensorBasis'`, `prod_eq_monomial_eval`, `sum_group_by_pairCount`, `sum_vanishes_of_coeff_and_const`, `tensorBasis'`, `toEndMatrix'`, `toEndMatrix'_diagAction` |
| TensorPower.lean | `TensV`, `diagAction`, `diagAction_comp`, `diagAction_tprod`, `diagImage`, `permAction`, `permAction_tprod`, `permImage` |
| Weingarten.lean | `endVec`, `gram_system_solvable`, `inner_endVec_perm_eq_trace`, `permDual`, `permOp`, `trace_permDual_comp_sum`, `weingarten_moment_decomposition_of_props` |
| WeingartenInverse.lean | `gramMatrix`, `gramMatrix_apply`, `gramMatrix_det_ne_zero`, `gramMatrix_isUnit_det`, `gramVec`, `gramVec_apply`, `gram_solution_eq_inv`, `gram_system_unique`, `isGramSolution_iff_mulVec`, `linearIndependent_endVec_permOp`, `weingartenGram`, `weingartenGramNat`, `weingartenGram_eq_card`, `weingartenGram_eq_gramMatrix`, `weingartenGram_eq_natCast`, `weingartenSolutionSet`, `weingartenVec`, `weingartenVec_eq_gramVec`, `weingarten_solution_unique` |

**ClassicalShadows/SnapshotEnsemble.lean**

Additional elaborated direct constants: none.

| Upstream file | Transitively used declarations |
|---|---|
| None | No upstream constant dependency. |

**ClassicalShadows/TraceContractions.lean**

Additional elaborated direct constants: none.

| Upstream file | Transitively used declarations |
|---|---|
| None | No upstream constant dependency. |

**ClassicalShadows/DepolarizingChannel.lean**

Additional elaborated direct constants: none.

| Upstream file | Transitively used declarations |
|---|---|
| None | No upstream constant dependency. |

**ClassicalShadows/Observation58.lean**

Additional elaborated direct constants: none.

| Upstream file | Transitively used declarations |
|---|---|
| None | No upstream constant dependency. |

**MagicMonotone/RankOneCalculus.lean**

Additional elaborated direct constants: none.

| Upstream file | Transitively used declarations |
|---|---|
| DirectProof.lean | `tensorBasis`, `toEndMatrix` |
| TensorPower.lean | `TensV` |
| Weingarten.lean | `endVec` |

**MagicMonotone/SingleGateMoment.lean**

Additional elaborated direct constants: `SchurWeyl.endVecₗ`, `SchurWeyl.permDual`.

| Upstream file | Transitively used declarations |
|---|---|
| Commutation.lean | `permAction_diagAction_comm`, `permAction_diagAction_tprod`, `permImage_subset_centralizer_diagImage` |
| DCT.lean | `PermModule`, `doubleCentralizer_to_endEndModule`, `double_centralizer_permImage'`, `endModule_mem_centralizer`, `mem_span_permImage_of_mem_range`, `neZero_card_perm`, `permAlgHom`, `permAlgHom_of`, `permAlgHom_range_eq`, `permModule_finite_over_endRing`, `permModule_isSemisimple`, `permModule_toModuleEnd_surjective`, `permMonoidHom`, `permRep`, `tensV_module_finite` |
| DirectProof.lean | `centralizer_diagImage_le_span_permImage`, `diagAction_diagonal`, `permAction_tensorBasis`, `tensorBasis`, `toEndMatrix`, `toEndMatrix_diagAction`, `toEndMatrix_permAction` |
| Haar.lean | `actOn`, `cols_mul_diag_sqrt`, `comm_diagAction_diagonal`, `comm_diagAction_diagonal_entry`, `conjTranspose_mul_self_of_spectral`, `conj_actOn`, `continuous_actOn_entry`, `diagAction_endOf_unitary_left`, `diagonal_mem_unitaryGroup`, `endOf`, `endOf_mul`, `endOf_one`, `exists_orthonormalBasis_cols`, `exists_unitary_of_orthonormalBasis`, `haarProb`, `instBorelSpaceUnitaryGroup`, `instCompactSpaceUnitaryGroup`, `instIsMulLeftInvariantHaarProb`, `instIsProbabilityMeasureHaarProb`, `instMeasurableSpaceUnitaryGroup`, `integrable_actOn_entry`, `isCompact_unitaryGroup`, `mem_centralizer_of_comm_unitary`, `momentMatrix`, `momentOp`, `momentOp_comm_unitary`, `momentOp_conj_unitary`, `momentOp_mem_span`, `momentOp_trace`, `prod_eq_of_torus`, `svd_exists`, `svd_spectral`, `toEndMatrix_comp`, `toEndMatrix_diagAction_diagonal`, `toEndMatrix_momentOp`, `trace_permDual_actOn`, `unitary_entry_norm_le_one`, `weingarten_moment_haar` |
| Main.lean | `schur_weyl`, `span_permImage_le_centralizer_diagImage` |
| PolyIndep.lean | `monomial_coeff_zero_of_eval_zero` |
| SmallDim.lean | `centralizer_diagImage_le_span_permImage_small`, `centralizer_permImage_le_span_diagImage`, `double_centralizer_permImage`, `exists_functional_separation`, `matrix_orbit_invariant`, `pairCount`, `permAction_tensorBasis'`, `prod_eq_monomial_eval`, `sum_group_by_pairCount`, `sum_vanishes_of_coeff_and_const`, `tensorBasis'`, `toEndMatrix'`, `toEndMatrix'_diagAction` |
| TensorPower.lean | `TensV`, `diagAction`, `diagAction_comp`, `diagAction_tprod`, `diagImage`, `permAction`, `permAction_tprod`, `permImage` |
| Weingarten.lean | `endVec`, `gram_system_solvable`, `inner_endVec_perm_eq_trace`, `permDual`, `permOp`, `trace_permDual_comp_sum`, `weingarten_moment_decomposition_of_props` |
| WeingartenInverse.lean | `endVecEquiv`, `endVecₗ`, `endVecₗ_apply`, `gramMatrix`, `gramMatrix_apply`, `gramMatrix_det_ne_zero`, `gramMatrix_isUnit_det`, `gramVec`, `gramVec_apply`, `gram_solution_eq_inv`, `gram_system_unique`, `isGramSolution_iff_mulVec`, `linearIndependent_endVec_permOp`, `matrixEntriesEquiv`, `weingartenGram`, `weingartenGramNat`, `weingartenGram_eq_card`, `weingartenGram_eq_gramMatrix`, `weingartenGram_eq_natCast`, `weingartenSolutionSet`, `weingartenVec`, `weingartenVec_eq_gramVec`, `weingarten_solution_unique` |

**MagicMonotone/BrickworkLayers.lean**

Additional elaborated direct constants: none.

| Upstream file | Transitively used declarations |
|---|---|
| DCT.lean | `permMonoidHom` |
| DirectProof.lean | `permAction_tensorBasis`, `tensorBasis`, `toEndMatrix`, `toEndMatrix_permAction` |
| TensorPower.lean | `TensV`, `permAction`, `permAction_tprod` |
| Weingarten.lean | `endVec`, `inner_endVec_perm_eq_trace`, `permDual`, `permOp` |
| WeingartenInverse.lean | `weingartenGram`, `weingartenGramNat`, `weingartenGram_eq_card`, `weingartenGram_eq_natCast` |

**MagicMonotone/Equation24.lean**

Additional elaborated direct constants: `SchurWeyl.TensV`.

| Upstream file | Transitively used declarations |
|---|---|
| DCT.lean | `permMonoidHom` |
| DirectProof.lean | `permAction_tensorBasis`, `tensorBasis`, `toEndMatrix`, `toEndMatrix_permAction` |
| TensorPower.lean | `TensV`, `permAction`, `permAction_tprod` |
| Weingarten.lean | `endVec`, `inner_endVec_perm_eq_trace`, `permDual`, `permOp` |
| WeingartenInverse.lean | `weingartenGram`, `weingartenGramNat`, `weingartenGram_eq_card`, `weingartenGram_eq_natCast` |

**SupportingDocs/TensorPowerBasics.lean**

Additional elaborated direct constants: `SchurWeyl.permAction`, `SchurWeyl.tensV_module_finite`.

| Upstream file | Transitively used declarations |
|---|---|
| DCT.lean | `permMonoidHom`, `tensV_module_finite` |
| DirectProof.lean | `tensorBasis` |
| TensorPower.lean | `TensV`, `permAction`, `permAction_tprod` |
| Weingarten.lean | `permDual`, `permOp` |

**SupportingDocs/HaarInvariance.lean**

Additional elaborated direct constants: `SchurWeyl.instBorelSpaceUnitaryGroup`, `SchurWeyl.instCompactSpaceUnitaryGroup`, `SchurWeyl.instIsProbabilityMeasureHaarProb`, `SchurWeyl.instMeasurableSpaceUnitaryGroup`.

| Upstream file | Transitively used declarations |
|---|---|
| Haar.lean | `haarProb`, `haar_univ_ne_top`, `haar_univ_ne_zero`, `instBorelSpaceUnitaryGroup`, `instCompactSpaceUnitaryGroup`, `instIsProbabilityMeasureHaarProb`, `instMeasurableSpaceUnitaryGroup`, `isCompact_unitaryGroup`, `unitary_entry_norm_le_one` |

**SupportingDocs/TraceNotation.lean**

Additional elaborated direct constants: none.

| Upstream file | Transitively used declarations |
|---|---|
| None | No upstream constant dependency. |

For the ten source-only files, the per-file helper descriptions give the reviewed indirect routes. No complete elaborated closure is claimed until the existing build error is repaired and those targets are rebuilt.

Evidence: [ForMathlibExamples-dependencies.json](/Users/melod/Desktop/research/lean-haar/ForMathlibExamples-dependencies.json).
