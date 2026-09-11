/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.ForMathlibExamples.MagicMonotone.RankOneCalculus
import LeanHaar.ForMathlib.ForMathlibExamples.k4Moment

/-!
# Two brickwork layers on four qubits: the vectorized layer moment operators

This file sets up the concrete example of Section III C of `magic_monotones.pdf`: `n = 4`
qubits, `k = 4` copies, and two brickwork layers of Haar-random two-qubit gates,

* layer `A`: gates on the qubit pairs `(1,2)` and `(3,4)`;
* layer `B`: gates on the staggered pairs `(2,3)` and `(4,1)`.

Qubits are numbered `0, 1, 2, 3` here, so the four pairs are `{0,1}`, `{2,3}`, `{1,2}`
and `{3,0}`.

## Main definitions

* `MagicMonotone.copyPerm S σ`: the permutation operator that permutes the `k = 4` copies by
  `σ` on the qubits in `S` and acts as the identity on the other qubits. This is
  `V₂(σ)^{(j)}` of Eq. (7)/(9) of the source, tensored over `j ∈ S` as in Eq. (13); the
  two-qubit gate operators `V₄^{(12)}(σ) = V₂(σ)^{(1)} ⊗ V₂(σ)^{(2)}` of Eq. (15) are
  `MagicMonotone.V12` and friends.
* `MagicMonotone.hsOverlap A B = Tr(A† B)`: the Hilbert–Schmidt overlap `⟨⟨A|B⟩⟩`, Eq. (11).
* `MagicMonotone.layerAKet σ₁ σ₂ = |V₄^{(12)}(σ₁) V₄^{(34)}(σ₂)⟩⟩` and
  `MagicMonotone.layerBKet γ₁ γ₂ = |V₄^{(23)}(γ₁) V₄^{(41)}(γ₂)⟩⟩`: the vectorized
  permutation operators of the two layers.
* `MagicMonotone.layerA` and `MagicMonotone.layerB`: the vectorized layer moment operators,
  Eqs. (21) and (20) of the source, written with the Weingarten coefficients `Wg(·, 4)` of
  `LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean`.

## Main results

* `MagicMonotone.copyPerm_one`: `copyPerm S 1 = 1`, a sanity check on the definition.
* `MagicMonotone.layerA_eq_pairSum`, `MagicMonotone.layerB_eq_pairSum`: the layer moment
  operators written as double sums over *pairs* of permutations, the form in which the
  ket-bra calculus of `RankOneCalculus.lean` applies.
-/

noncomputable section

open scoped InnerProductSpace Matrix
open InnerProductSpace ContinuousLinearMap

namespace MagicMonotone

/-! ### The four copies of the four-qubit register -/

/-- The `k = 4` copies of the system. -/
abbrev Copies : Type := Fin 4

/-- The `n = 4` qubits of the register. -/
abbrev Qubits : Type := Fin 4

/-- A computational basis index of the four copies of the four-qubit register: one bit for
each copy and each qubit. -/
abbrev Reg : Type := Copies → Qubits → Fin 2

/-- An operator on the four copies of the four-qubit register. -/
abbrev RegOp : Type := Matrix Reg Reg ℂ

/-- The vectorized operator space of the register, where the moment operators live. -/
abbrev Vecs : Type := EuclideanSpace ℂ (Reg × Reg)

/-- A pair of permutations of the four copies: the label of one brickwork layer, one
permutation per gate of the layer. -/
abbrev PermPair : Type := Equiv.Perm Copies × Equiv.Perm Copies

/-! ### Permutation operators -/

/-- The permutation operator that permutes the `k = 4` copies by `σ` on the qubits in `S`,
and acts as the identity on the remaining qubits:
`⨂_{j ∈ S} V₂(σ)^{(j)}`, cf. Eqs. (9) and (13) of `magic_monotones.pdf`.

Its entries are `1` exactly when the row index is obtained from the column index by relabelling
the copies of the qubits in `S` by `σ⁻¹`. -/
def copyPerm (S : Finset Qubits) (σ : Equiv.Perm Copies) : RegOp :=
  Matrix.of fun I J => if ∀ c j, I c j = (if j ∈ S then J (σ⁻¹ c) j else J c j) then 1 else 0

/-- The identity permutation gives the identity operator. -/
lemma copyPerm_one (S : Finset Qubits) : copyPerm S 1 = 1 := by
  ext I J
  have hcond : (∀ c j, I c j = (if j ∈ S then J ((1 : Equiv.Perm Copies)⁻¹ c) j else J c j))
      ↔ I = J := by
    constructor
    · intro h; funext c j; simpa using h c j
    · rintro rfl; intro c j; simp
  simp only [copyPerm, Matrix.of_apply, hcond, Matrix.one_apply]

/-- The gate operator `V₄^{(12)}(σ)` of the first gate of layer `A` (qubits `0, 1`). -/
def V12 (σ : Equiv.Perm Copies) : RegOp := copyPerm {0, 1} σ

/-- The gate operator `V₄^{(34)}(σ)` of the second gate of layer `A` (qubits `2, 3`). -/
def V34 (σ : Equiv.Perm Copies) : RegOp := copyPerm {2, 3} σ

/-- The gate operator `V₄^{(23)}(σ)` of the first gate of layer `B` (qubits `1, 2`). -/
def V23 (σ : Equiv.Perm Copies) : RegOp := copyPerm {1, 2} σ

/-- The gate operator `V₄^{(41)}(σ)` of the second gate of layer `B` (qubits `3, 0`). -/
def V41 (σ : Equiv.Perm Copies) : RegOp := copyPerm {3, 0} σ

/-! ### Vectorized kets and their overlaps -/

/-- The Hilbert–Schmidt overlap `⟨⟨A|B⟩⟩ = Tr(A† B)` of Eq. (11) of `magic_monotones.pdf`. -/
def hsOverlap (A B : RegOp) : ℂ := (Aᴴ * B).trace

/-- The vectorized permutation operator of layer `A`,
`|V₄^{(12)}(σ₁)⟩⟩|V₄^{(34)}(σ₂)⟩⟩ = |V₄^{(12)}(σ₁) V₄^{(34)}(σ₂)⟩⟩`. -/
def layerAKet (σ₁ σ₂ : Equiv.Perm Copies) : Vecs := vecOp (V12 σ₁ * V34 σ₂)

/-- The vectorized permutation operator of layer `B`,
`|V₄^{(23)}(γ₁)⟩⟩|V₄^{(41)}(γ₂)⟩⟩ = |V₄^{(23)}(γ₁) V₄^{(41)}(γ₂)⟩⟩`. -/
def layerBKet (γ₁ γ₂ : Equiv.Perm Copies) : Vecs := vecOp (V23 γ₁ * V41 γ₂)

/-- The inner product of two layer kets is the Hilbert–Schmidt overlap of the corresponding
permutation operators: `⟨⟨V(π₁)V(π₂)|V(γ₁)V(γ₂)⟩⟩`, the quantity appearing in Eqs. (22)–(25). -/
lemma inner_layerAKet_layerBKet (π₁ π₂ γ₁ γ₂ : Equiv.Perm Copies) :
    (inner ℂ (layerAKet π₁ π₂) (layerBKet γ₁ γ₂) : ℂ)
      = hsOverlap (V12 π₁ * V34 π₂) (V23 γ₁ * V41 γ₂) :=
  inner_vecOp_vecOp _ _

/-! ### The layer moment operators -/

/-- The Weingarten coefficient `Wg(σ, 4)` of a two-qubit Haar gate (`d = 4`, `k = 4`), taken
from the fourth-moment computation of `k4Moment.lean`. -/
def wg (σ : Equiv.Perm Copies) : ℂ := SchurWeyl.K4.wgVal 4 σ

/-- **Layer `A`**, Eq. (21) of `magic_monotones.pdf`: the vectorized moment operator of the
two independent Haar gates on the qubit pairs `(1,2)` and `(3,4)`,
`∑ Wg(σ₁⁻¹π₁, 4) Wg(σ₂⁻¹π₂, 4) |V^{(12)}(σ₁)⟩⟩|V^{(34)}(σ₂)⟩⟩⟨⟨V^{(12)}(π₁)|⟨⟨V^{(34)}(π₂)|`. -/
def layerA : Vecs →L[ℂ] Vecs :=
  ∑ σ₁, ∑ σ₂, ∑ π₁, ∑ π₂,
    (wg (σ₁⁻¹ * π₁) * wg (σ₂⁻¹ * π₂)) • rankOne ℂ (layerAKet σ₁ σ₂) (layerAKet π₁ π₂)

/-- **Layer `B`**, Eq. (20) of `magic_monotones.pdf`: the vectorized moment operator of the
two independent Haar gates on the staggered qubit pairs `(2,3)` and `(4,1)`,
`∑ Wg(γ₁⁻¹τ₁, 4) Wg(γ₂⁻¹τ₂, 4) |V^{(23)}(γ₁)⟩⟩|V^{(41)}(γ₂)⟩⟩⟨⟨V^{(23)}(τ₁)|⟨⟨V^{(41)}(τ₂)|`. -/
def layerB : Vecs →L[ℂ] Vecs :=
  ∑ γ₁, ∑ γ₂, ∑ τ₁, ∑ τ₂,
    (wg (γ₁⁻¹ * τ₁) * wg (γ₂⁻¹ * τ₂)) • rankOne ℂ (layerBKet γ₁ γ₂) (layerBKet τ₁ τ₂)

/-- The layer ket indexed by a pair of permutations, `|V^{(12)}(σ₁)⟩⟩|V^{(34)}(σ₂)⟩⟩`. -/
def ketA (s : PermPair) : Vecs := layerAKet s.1 s.2

/-- The layer ket indexed by a pair of permutations, `|V^{(23)}(γ₁)⟩⟩|V^{(41)}(γ₂)⟩⟩`. -/
def ketB (s : PermPair) : Vecs := layerBKet s.1 s.2

/-- The Weingarten weight of a layer, `Wg(σ₁⁻¹π₁, 4) Wg(σ₂⁻¹π₂, 4)`, as a function of the two
pairs of permutations labelling the layer. -/
def wgPair (s p : PermPair) : ℂ := wg (s.1⁻¹ * p.1) * wg (s.2⁻¹ * p.2)

/-- Layer `A` as a double sum over pairs of permutations. -/
lemma layerA_eq_pairSum :
    layerA = ∑ s : PermPair, ∑ p : PermPair, wgPair s p • rankOne ℂ (ketA s) (ketA p) := by
  simp only [layerA, ketA, wgPair, Fintype.sum_prod_type]

/-- Layer `B` as a double sum over pairs of permutations. -/
lemma layerB_eq_pairSum :
    layerB = ∑ g : PermPair, ∑ t : PermPair, wgPair g t • rankOne ℂ (ketB g) (ketB t) := by
  simp only [layerB, ketB, wgPair, Fintype.sum_prod_type]

end MagicMonotone

end
