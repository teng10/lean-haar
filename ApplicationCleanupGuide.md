# Application cleanup guide

Build small, coherent modules with useful interfaces. Applications should express
their own concepts while relying on shared mathematics or functionality below
them. Cleanup should make those boundaries clearer without changing behavior or
mathematical meaning.

## Give each module a clear purpose

A module should own a mathematical object, a coherent operation or a recognizable
result. Keep its basic laws and computation rules close to the definitions they
support. Separate prerequisites, derived results and application-specific
calculations when they have distinct roles.

Choose names that explain the subject. Prefer a section in an existing coherent
module over a separate file for every helper. File count is a consequence of the
design, not a measure of quality; merging files can broaden dependencies.

Keep dependency direction clear: shared foundations support applications.
Foundations should not depend on application vocabulary or results. Check the
actual imports and declarations needed, including dependencies that consumers
currently receive indirectly.

## Design for reuse through a useful interface

- **Start with concrete uses.** Extract an abstraction when it expresses a useful
  mathematical structure, removes duplication or simplifies a real consumer.
  Generic hypotheses alone do not require a shared module.
- **Use natural assumptions.** State what the result needs without baking in
  incidental application parameters. Generalize when the mathematics or clients
  benefit; avoid unused parameters and speculative frameworks.
- **Provide the complete interface.** Review constructors, conversions, inverse
  maps, evaluation rules and essential laws together. Users should not need to
  unfold implementation details for routine operations.
- **Make definitions earn their place.** A definition should name an object,
  encode a useful distinction, bundle meaningful laws or provide readable
  application vocabulary. Avoid layers of aliases that add no useful interface.
- **Reuse established infrastructure.** Check the standard library and pinned
  dependencies before introducing another construction or proof.

A generic helper can remain with its sole application consumer. Conversely,
application-facing names can remain as thin specializations of shared machinery
when they make the mathematics easier to read. Reassess ownership when use expands.

## Keep representations and assumptions explicit

Distinguish mathematical objects from their coordinate representations and from
the structures that package their laws. Similar formulas or notation do not make
two types interchangeable; provide a conversion or identification theorem when
one is needed.

Document conventions that affect meaning: index order, conjugation, multiplication
order, normalization and composition direction. State the interpretation actually
proved. An algebraic expression does not acquire a probabilistic, physical or
derivative interpretation merely from its name.

Keep temporary proof bookkeeping local. Expose results that support a meaningful
interface, rather than every intermediate step.

## Make structural changes separately from mathematical changes

Classify each declaration deliberately: keep, relocate, replace with existing
infrastructure, remove an unnecessary wrapper, restrict visibility, or defer for
new mathematical work. Moving a declaration does not by itself justify changing
its public name, assumptions or visibility.

Preserve useful interfaces even when two statements are mathematically equivalent:
different syntactic forms can serve different proof patterns. For formalization
libraries, also preserve namespace boundaries, implicit arguments, scoped notation,
instances and simplification behavior. Moving declarations upstream can change
which automation becomes available downstream.

Treat stronger theorems, broader parameter ranges and new interpretation bridges
as separate work. Keep structural cleanup small enough to review independently.

## Complete and verify each change

Record the baseline and preserve unrelated work. Inspect all consumers, not just
the original application. Update imports, references and documentation together;
remove obsolete modules only after migration is complete. Use compatibility
wrappers only when a concrete compatibility requirement warrants them.

Verify public interfaces and representative client usage, then run the project's
required coverage and safety checks. For proof libraries, check theorem statements,
trusted assumptions and kernel validation as well as compilation. Named
compatibility witnesses make preservation claims auditable. Diagnose generated
metadata differences narrowly rather than discarding substantive type differences.

Do not weaken checks to make a reorganization pass. Measure dependency or build-cost
claims instead of inferring them from fewer files. Use independent review to check
both the change and the claims made about it.

Keep project-specific plans, findings, validation evidence and history in separate
review records. Distinguish proposed work from completed work. Update the project's
module map and migration notes when ownership changes; keep this guide focused on
reusable design principles.
