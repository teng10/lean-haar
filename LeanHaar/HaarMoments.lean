import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.Complex.Basic

/-!
# The Haar-twirl interface

`IsHaarTwirl 𝒯 K` abstracts the two coordinate-free properties of the Haar twirl
`𝒯(O) = ∫ U^{⊗k} O U^{†⊗k} dμ`, for *every* `k`:

* `mem` — `𝒯 O ∈ K`: the twirl lands in the commutant `K`;
* `trace_match` — `Tr(B · 𝒯 O) = Tr(B · O)` for every `B ∈ K`: it preserves trace pairings against `K`.

This is the hypothesis consumed by the Schur–Weyl bridge (`HaarSchurBridge`) and the moment
corollaries. The linear algebra that *solves* for `𝒯 O` within a finite-dimensional commutant lives
alongside those corollaries in `Examples/UnitaryMoments.lean`, since that is its only consumer.
-/

namespace LeanHaar.HaarMoments

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- `IsHaarTwirl 𝒯 K`: the linear map `𝒯` is the trace-matching projection onto the commutant `K` —
the two `k`-independent properties of the Haar twirl. -/
structure IsHaarTwirl (𝒯 : Module.End ℂ V →ₗ[ℂ] Module.End ℂ V)
    (K : Submodule ℂ (Module.End ℂ V)) : Prop where
  /-- The twirl lands in the commutant. -/
  mem : ∀ O, 𝒯 O ∈ K
  /-- The twirl preserves the trace pairing against every element of the commutant. -/
  trace_match : ∀ B ∈ K, ∀ O, LinearMap.trace ℂ V (B * 𝒯 O) = LinearMap.trace ℂ V (B * O)

end LeanHaar.HaarMoments
