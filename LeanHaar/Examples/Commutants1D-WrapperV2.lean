import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Center

import LeanHaar.SchurWeylAbstract

namespace Moment.SchurWeyl

open LeanHaar.SchurWeylAbstract
-- Schur Weyl duality example for single qubit -!
-- Yan: This file states k=1 commutant as a set equality.

-- We first want to show `Comm(U(W)) = ℂ • 1`, where `U(W)` is the unitary group of a 2-dimensional Hilbert space `W`.
-- This is the content of the following theorem, which is a special case of Schur–Weyl duality for `k = 1` and `W` of dimension 2.

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ W] in
/-- At `k = 1` the symmetric group `S₁` is trivial, so `permSpan` is the line `ℂ ∙ 1` of scalar
operators. -/
lemma permSpan_one_eq_span_one :
    permSpan (V := W) (k := 1)
      = Submodule.span ℂ {(1 : Module.End ℂ (TensorPower ℂ 1 W))} := by
  unfold permSpan
  congr 1
  ext Y
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨π, rfl⟩
    rw [Subsingleton.elim π 1]
    exact map_one permRep
  · rintro rfl
    exact ⟨1, map_one permRep⟩

/-- **Schur–Weyl at `k = 1`** (the `1`-design / twirl fact): an operator commutes with every
single-system unitary iff it is a scalar multiple of the identity. -/
lemma commutant_unitary_eq_scalars (X : Module.End ℂ (TensorPower ℂ 1 W)) :
    X ∈ Set.centralizer ↑(unitaryTensorSpan (W := W) (k := 1))
      ↔ ∃ c : ℂ, X = c • 1 := by
  rw [← permSpan_eq_centralizer_unitaryTensorSpan, SetLike.mem_coe, permSpan_one_eq_span_one,
    Submodule.mem_span_singleton]
  exact exists_congr fun c => eq_comm

end Moment.SchurWeyl
