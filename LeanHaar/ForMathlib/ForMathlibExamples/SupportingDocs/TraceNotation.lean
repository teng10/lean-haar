/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Trace

/-!
# Notation for the trace of an endomorphism

Every file of the classical-shadow example writes traces of endomorphisms, so they all share
the same abbreviation `Tr[A]` for `LinearMap.trace _ _ A`, with the ring and the module
inferred. It is declared once here, as a notation scoped to the `ClassicalShadows` namespace,
instead of being repeated as a `local notation` in each file.
-/

namespace ClassicalShadows

/-- Notation for the trace of an endomorphism, with the ring and the module inferred. -/
scoped notation:max "Tr[" A "]" => LinearMap.trace _ _ A

end ClassicalShadows
