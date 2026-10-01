# LeanHaar tensor-power foundations cleanup

Updated: 2026-10-01.

`TensorPower.lean` owns the tensor space, its permutation and diagonal actions,
their images, and their elementary computation rules. Its six active definitions
and five elementary lemmas form one mathematical API. The former `Defs.lean` and
`ActionLemmas.lean` have been replaced by this module.

## Completed

- [x] Combine the definitions and their elementary API in `TensorPower.lean`,
  grouping each action with its computation rules and image. Preserve declaration
  names, statements, definition/proof bodies, and attributes.
- [x] Update all ten consumers to import `LeanHaar.ForMathlib.TensorPower`.
- [x] Keep the substantive commutation results in `Commutation.lean`, the double
  commutant theorem in `DCT.lean`, and Haar averaging in `Haar.lean`.
- [x] Remove nine redundant or unused helper lemmas after auditing their consumers.
- [x] Keep `diagAction` as the underlying tensor-power construction. Preserve
  `diagActionUnits`, `glAction`, `unitaryAction`, and their conversion lemmas in
  the commented future-API section of `TensorPower.lean`.
- [x] Rewrite both unitary cancellation proofs in `Haar.lean` using
  `diagAction_comp`, matrix unitarity, `endOf_one`, and `map_one` directly.
- [x] Keep the unitary-group import in `Haar.lean`; the tensor-power foundation
  does not directly import the GL/unitary wrapper modules.
- [x] Correct the comments about degree-k homogeneity, the current polynomial
  proof's use of all endomorphisms, and the optional wrappers' return type.
- [x] Check the core and application endpoint axiom reports during the earlier
  lemma cleanup; dependencies were unchanged.
- [x] Rebuild all 34 current modules under `ForMathlib`, including examples,
  after combining the two foundation modules.

- [x] Consolidate `tensorBasis`/`tensorBasis'` and `toEndMatrix`/`toEndMatrix'`
  into the single public coordinate API in `TensorPower/Matrix.lean`, preserving
  names, types, and coordinate conventions for the unprimed declarations.
- [x] Replace `SmallDim.lean` with `PermutationCentralizer.lean`. Its polynomial
  proof works for every `d` and `k` and does not import the double-centralizer proof.
- [x] Make `pairCount` and polynomial/orbit bookkeeping private, extract the
  simultaneous-orbit classification as `pairCount_eq_iff_exists_perm`, and use
  Mathlib's linear-functional separation theorem directly.
- [x] Put the canonical `double_centralizer_permImage` in `DCT.lean` and move
  the hard-inclusion assembly into `Main.lean`; remove `DirectProof.lean` and
  the obsolete `_small`/primed theorem aliases.
- [x] Import tensor coordinates directly from Haar and Weingarten; document each
  module's mathematical role rather than a historical proof strategy.

- [x] Rebuild all 34 core and example modules after the coordinate/polynomial
  cleanup. Check all local imports and confirm the four centralizer/duality
  endpoint axiom reports remain `[propext, Classical.choice, Quot.sound]`.

- [x] Keep `permOp` beside `permAction` in `TensorPower.lean`, as the underlying
  endomorphism used by core and example formulas. Define `permDual` using `permOp`
  at inverse permutations.
- [x] Keep `permRep`, `PermModule`, `permAlgHom`, and the range/span helpers private
  to `DCT.lean`, where they support Maschke and density. Derive `permRep` from
  `permAction` using Mathlib's standard conversion and remove `permMonoidHom`.
  No separate representation module is needed.
- [x] Remove the unused `centralizer_to_endModule`; make the remaining DCT
  conversion private and turn semisimplicity/density proof definitions into
  private theorems with explicit result types. Keep explicit module-instance
  choices where needed and localize the two DCT-specific instances.
- [x] Move the reusable `tensV_module_finite` instance beside `tensorBasis` in
  `TensorPower/Matrix.lean`, retaining its name and global availability.

- [x] Rebuild all 34 core and example modules after the permutation/DCT cleanup,
  with no warnings. Confirm the five centralizer/duality/Weingarten endpoint axiom
  reports match the baseline and no local imports or removed-definition references
  remain unresolved. Validation uses the working tree, including the pre-existing
  `TensorPowerTraces.lean` fix, which this cleanup leaves unchanged.

## Module responsibilities

| Module | Purpose |
| --- | --- |
| `TensorPower.lean` | Construct the tensor space and its two actions, including `permOp` and their elementary API. |
| `TensorPower/Matrix.lean` | Standard tensor basis, matrix coordinates, and coordinate formulas for both actions. |
| `PermutationCentralizer.lean` | Polynomial proof that the permutation centralizer lies in the span of tensor powers, for all dimensions. |
| `Main.lean` | Assemble the polynomial and double-centralizer arguments into Schur–Weyl duality. |
| `Commutation.lean` | Prove that the actions commute and obtain the centralizer inclusions. |
| `DCT.lean` | Prove the double-commutant theorem, with private group-algebra and density machinery. |
| `Haar.lean` | Construct Haar averaging and prove its properties. |

## Retained API

`TensorPower.lean` exports `TensV`, `permAction`, `permOp`, `diagAction`, `permImage`,
and `diagImage`, together with:

- `permAction_tprod`
- `diagAction_apply`
- `diagAction_tprod`
- `diagAction_comp`
- `diagAction_smul`

Use Mathlib's `map_one` and `map_pow` directly instead of the removed
`diagAction_id` and `diagAction_pow` aliases.

`glAction_toLinearMap`, `unitaryAction_toLinearMap`, and
`unitaryAction_symm_toLinearMap` remain commented out with their associated
wrappers. The active unitary cancellation results remain in `Haar.lean`.

The unused `diagActionUnits_toLinearMap`, `diagActionUnits_symm_toLinearMap`,
`diagActionUnits_apply_tprod`, `glAction_symm_toLinearMap`, `glAction_apply_tprod`,
`unitaryAction_apply_tprod`, and `unitaryAction_symm_apply_tprod` lemmas were also
removed. Introduce wrapper-specific conveniences only when a consumer needs them.

## Remaining follow-ups

- [ ] Reconsider `diagActionUnits`, `glAction`, and `unitaryAction` only when a
  concrete consumer needs a bundled `LinearEquiv` or repeatedly uses its API.
  Direct cancellation alone does not justify the wrappers.
- [ ] If that need arises, restore the relevant commented definitions and conversion
  lemmas in a focused core module (for example `UnitaryAction.lean`) importing
  `TensorPower.lean`. Keep them derived from `diagAction`.
- [ ] When restoring wrappers, document that they package invertibility; their
  `LinearEquiv` return type does not encode norm preservation. Add only the helper
  lemmas required by actual consumers.
- [ ] Review uses of `unfold diagAction` in downstream proofs and use public
  evaluation/conversion lemmas where that improves stability.
- [ ] Require a concrete consumer before adding future GL/unitary representation
  wrappers; derive them from the existing action. Keep the current `permRep`
  adapter private to DCT until another proof actually needs it.
- [ ] Make the default release/CI build cover every supported module. The current
  default root build still omits the `ForMathlib` tree.

The broader project checklist remains in `LeanHaar-TODO.md`.
