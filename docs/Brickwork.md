# Circuit and brickwork moments

Import `LeanHaar.Circuits.Circuit` and open `SchurWeyl` and `SchurWeyl.Circuits`.
The API supports arbitrary local dimension, register size, block arity, and copy
number. In particular, moments do **not** require `k ≤ d`.

```lean
import LeanHaar.Circuits.Circuit

open MeasureTheory SchurWeyl SchurWeyl.Circuits

noncomputable section

-- Two ordered local blocks on four qubits, including a periodic gate.
def firstBlock : Fin 2 ↪ Fin 4 := Function.Embedding.embFinTwo (a := 0) (b := 1) (by decide)
def wrapBlock : Fin 2 ↪ Fin 4 := Function.Embedding.embFinTwo (a := 3) (b := 0) (by decide)

-- A chronological two-gate schedule. Its second moment acts on all four qubits.
def twoGateMoment : MomentOperator (2 ^ 4) 2 :=
  circuitMoment 2 2 ![firstBlock, wrapBlock]

-- Four qubits, second moment, three matching layers (six independent gates).
def threeLayerMoment : MomentOperator (2 ^ 4) 2 :=
  brickworkMoment 2 2 2 3

-- The ordinary-operator interface needs no vectorization at the call site.
def averageThreeLayers (X : Module.End ℂ (TensV (2 ^ 4) 2)) :=
  operatorMap (brickworkMoment 2 2 2 3) X
```

## Selecting the interface

| Task | Entry point |
|---|---|
| Choose an ordered block of distinct sites | `Fin s ↪ Fin n`; `Function.Embedding.embFinTwo h` |
| Place a sampled local unitary | `placeUnitary q sites U` |
| Inspect its physical matrix entries | `placeUnitary_apply` |
| Average any continuously placed Haar gate | `gateMoment J k` |
| Compose a chronological sequence | `scheduleProduct`; `scheduleProduct_append` |
| Construct a sampled local circuit | `circuitUnitary q sites samples` |
| Its moment / ordinary-operator action | `circuitMoment q k sites`; `operatorMap (circuitMoment q k sites)` |
| Periodic brickwork on `2*m` sites | `brickworkMoment q k m depth`; `brickworkMoment_layers` |
| General independent ensembles | `integral_scheduleProduct`; `integral_vecActOn_placed_schedule` |

Schedules are functions `Fin length → (Fin s ↪ Fin n)`. Vector notation
`![block₀, block₁, ...]` is convenient for short schedules. All occurrences in
this interface have the same block arity; arbitrary placement homomorphisms are
also supported by `gateMoment`.

## Conventions with proved guarantees

**Time order.** The first listed gate acts first. Two gates `[A, B]` have physical
unitary `B * A` and moment `M_B * M_A`. This is Schrödinger conjugation
`X ↦ U^{⊗k} X (U†)^{⊗k}`. Existing Heisenberg examples use the opposite action;
`MagicMonotone.twoLayerMoment_eq_adjoint_brickworkMoment` identifies the four-copy,
four-qubit calculation with `(brickworkMoment 2 4 2 2).adjoint`.
`circuitMoment_append` composes schedules, `brickworkMoment_layers` decomposes matching
layers, and `circuitMoment_adjoint` identifies the adjoint with the reversed Haar schedule.

**Register order.** `registerEquiv q n` uses `finFunctionFinEquiv`: site `i`
has numeric weight `q^i`. Site zero is the least significant digit. An ordered
block `![i,j]` reads `i` into local coordinate zero and `j` into local coordinate
one. `placeUnitary_apply` states the complete matrix formula and hides the
choice of complement enumeration. `copySiteEquiv` exposes copy/site regrouping.

**Independence.** Random variables are indexed by occurrence. Using the same
support twice gives two independent Haar samples. `integral_circuitUnitary`
proves equality of the full averaged superoperator with `circuitMoment`.
`circuitMoment_endVec` applies this to every input operator, and
`circuitChannel_entry` states the result directly in matrix entries.
These statements include operators entangled with the complement.

**Depth.** `depth` is the literal number of matching layers, starting with odd.
There are `depth * m` independent two-site gates. On four sites the odd pairs
are `(0,1),(2,3)` and the even pairs are `(1,2),(3,0)`. On two sites the even
pair is `(1,0)`, with its ordering preserved. Zero depth gives the identity
moment. Geometry also admits the empty register `m = 0`.

**Haar algebra.** Both `haarMoment` and `gateMoment` are idempotent and
Hilbert–Schmidt self-adjoint. Global Haar averaging absorbs every local Haar
moment on either side. `operatorMap_haarMoment` connects the ordinary-operator
interface to the existing `momentOp`.

## Scope and further work

This initial version proves the physical ensemble/composition bridge and generic
Haar algebra. It does not yet prove arbitrary-disjoint-support gate commutation,
within-layer order independence, matching projection/palindrome theorems, the
two-copy sector/CP comparison, or an approximate-design convergence bound.
`operatorMap` expresses moments as linear maps; complete positivity is
not yet exposed as a theorem or a bundled channel structure.

See [the reviewed implementation plan](BrickworkPlan.md) for the mathematical
repairs and next acceptance gates, and [Claude's full plan review](BrickworkClaudeReview.txt)
with its [exact input](BrickworkClaudeReviewInput.txt). Regression examples and
axiom guards are in `test/LeanHaarTest/Circuits.lean`.
