/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.Circuits.SitePermutation
import LeanHaar.Moments.k4Moment

/-!
# Two brickwork layers on four qubits: algebraic layer moment sums

This file constructs the explicit layer sums of Section III C of `magic_monotones.pdf`:
`n = 4` qubits, `k = 4` copies, and the two pairings of two-qubit gates,

* layer `A`: gates on the qubit pairs `(1,2)` and `(3,4)`;
* layer `B`: gates on the staggered pairs `(2,3)` and `(4,1)`.

Qubits are numbered `0, 1, 2, 3` here, so the four pairs are `{0,1}`, `{2,3}`, `{1,2}`
and `{3,0}`. `HaarLayers` identifies these layer sums with averages over independent
Haar-random gates through `integral_vecActOn_layerA` and `integral_vecActOn_layerB`.

The copy-permutation operators act on the repository's `SchurWeyl.TensV 16 4`, the four
copies of the four-qubit register. Their vectorizations use `SchurWeyl.endVec` and belong
to `MagicMonotone.Vecs`; `layerA` and `layerB` are continuous linear maps on this vectorized
operator space. Concretely:

* an operator is described by its matrix in the computational basis through the repository's
  `SchurWeyl.toEndMatrix 16 4`, and the computational basis index `Fin 4 → Fin 16` is read
  qubit by qubit through the shared coordinates `SchurWeyl.copySiteEquiv 2 4 4`;
* the copy-permutation operators are built qubit by qubit out of
  `SchurWeyl.permOp 2` (this is Eq. (13) of the source);
* the Weingarten weights are the `k = 4` Weingarten values `SchurWeyl.K4.wgVal`, and the
  interlayer overlaps are products of entries of the repository's Weingarten Gram matrix
  `SchurWeyl.weingartenGram 2 4`, whose closed form `SchurWeyl.K4.weingartenGram_closed`
  supplies the powers of `2` of Eq. (23).

## Main definitions

* `MagicMonotone.regPerm g`: the permutation operator `⨂_j V₂(g j)^{(j)}` of Eq. (13) that
  permutes the `k = 4` copies of qubit `j` by `g j`; each tensor factor is the matrix of the
  repository's permutation operator `SchurWeyl.permOp 2 (g j)` on `(ℂ²)^{⊗4}`.
* `MagicMonotone.gateOn S σ`: the copy-permutation operator supported on the qubits in `S`.
  The operators `V₄^{(12)}(σ)` etc. of Eq. (15) are `MagicMonotone.V12`, `V34`, `V23`, `V41`;
  their parameter is a permutation of the copies, not a sampled two-qubit unitary.
* `MagicMonotone.hsOverlap X Y = ⟨⟨X|Y⟩⟩`: the Hilbert–Schmidt overlap of Eq. (11), i.e. the
  inner product of the two vectorizations `SchurWeyl.endVec`.
* `MagicMonotone.layerAKet σ₁ σ₂ = |V₄^{(12)}(σ₁) V₄^{(34)}(σ₂)⟩⟩` and
  `MagicMonotone.layerBKet γ₁ γ₂ = |V₄^{(23)}(γ₁) V₄^{(41)}(γ₂)⟩⟩`: the vectorized
  permutation operators of the two layers.
* `MagicMonotone.layerA` and `MagicMonotone.layerB`: the explicit rank-one sums of
  Eqs. (21) and (20). The weight `MagicMonotone.wgPair` is a product of two values of
  `SchurWeyl.K4.wgVal`, as prescribed by the single-gate formula. This file establishes
  algebraic overlap identities; `HaarLayers` proves their independent-gate Haar interpretation.

## Main results

* `MagicMonotone.regPerm_one`, `MagicMonotone.regPerm_mul`: the operators of Eq. (13) form a
  representation of the group of qubitwise permutations.
* `MagicMonotone.hsOverlap_regPerm`: the overlap of two such operators factorizes over the
  qubits into entries of the repository's Weingarten Gram matrix `weingartenGram 2 4`.
* `MagicMonotone.hsOverlap_layer_eq_gram`, `MagicMonotone.hsOverlap_layer_eq_two_pow`:
  **Eq. (23)**, the interlayer overlap of the two brickwork layers, first as a product of
  four Gram entries and then, through the repository's closed form for those entries, as
  `2^{#(π₁⁻¹γ₁) + #(π₁⁻¹γ₂) + #(π₂⁻¹γ₁) + #(π₂⁻¹γ₂)}`.
* `MagicMonotone.hsOverlap_layerA_layerA`, `MagicMonotone.wg_inverts_gram`: two labellings of
  the *same* layer overlap in the `d = 4` Gram entries of the repository's fourth-moment
  system, which the weights `MagicMonotone.wg` invert.
* `MagicMonotone.layerA_eq_pairSum`, `MagicMonotone.layerB_eq_pairSum`: the layer moment
  operators written as double sums over *pairs* of permutations, the form in which the
  ket-bra calculus of `Applications/MagicMonotone/RankOneCalculus.lean` applies.
-/

noncomputable section

open scoped Matrix
open InnerProductSpace SchurWeyl SchurWeyl.Circuits SchurWeyl.K4

namespace MagicMonotone

/-! ### The four copies of the four-qubit register -/

/-- The `k = 4` copies of the system. -/
abbrev Copies : Type := Fin 4

/-- The `n = 4` qubits of the register. -/
abbrev Qubits : Type := Fin 4

/-- An operator on the four copies of the four-qubit register: an endomorphism of the
repository's tensor power `SchurWeyl.TensV 16 4`. -/
abbrev RegOp : Type := Module.End ℂ (TensV 16 4)

/-- The vectorized operator space of the register, where the moment operators live. It is
the codomain of the repository's vectorization `SchurWeyl.endVec` for `d = 16`, `k = 4`. -/
abbrev Vecs : Type := EuclideanSpace ℂ ((Copies → Fin 16) × (Copies → Fin 16))

/-- A pair of permutations of the four copies: the label of one brickwork layer, one
permutation per gate of the layer. -/
abbrev PermPair : Type := Equiv.Perm Copies × Equiv.Perm Copies

/-! ### Permutation operators, qubit by qubit (Eq. (13)) -/

/-- **The qubitwise permutation operator of Eq. (13)**, `⨂_{j} V₂(g j)^{(j)}`:
the shared site-permutation operator specialized to four qubits and four copies. -/
def regPerm (g : Qubits → Equiv.Perm Copies) : RegOp :=
  sitePerm 2 g

/-- Every qubit carrying the identity permutation gives the identity operator. -/
lemma regPerm_one : regPerm (fun _ => 1) = 1 :=
  sitePerm_one

/-- Applying `h` and then `g`, qubit by qubit, multiplies the local permutations. -/
lemma regPerm_mul (g h : Qubits → Equiv.Perm Copies) :
    regPerm g * regPerm h = regPerm (fun j => g j * h j) :=
  sitePerm_mul g h

/-- The copy-permutation operator supported on `S`: it permutes the copies of each qubit
in `S` by `σ` and leaves the others untouched. The operators
`V₄^{(12)}(σ) = V₂(σ)^{(1)} ⊗ V₂(σ)^{(2)}` of Eq. (15) are of this form. -/
def gateOn (S : Finset Qubits) (σ : Equiv.Perm Copies) : RegOp :=
  regPerm fun j => if j ∈ S then σ else 1

/-- The copy permutation `V₄^{(12)}(σ)` supported on qubits `0, 1` of layer `A`. -/
def V12 (σ : Equiv.Perm Copies) : RegOp := gateOn {0, 1} σ

/-- The copy permutation `V₄^{(34)}(σ)` supported on qubits `2, 3` of layer `A`. -/
def V34 (σ : Equiv.Perm Copies) : RegOp := gateOn {2, 3} σ

/-- The copy permutation `V₄^{(23)}(σ)` supported on qubits `1, 2` of layer `B`. -/
def V23 (σ : Equiv.Perm Copies) : RegOp := gateOn {1, 2} σ

/-- The copy permutation `V₄^{(41)}(σ)` supported on qubits `3, 0` of layer `B`. -/
def V41 (σ : Equiv.Perm Copies) : RegOp := gateOn {3, 0} σ

/-- A gate with the identity permutation is the identity operator. -/
lemma gateOn_one (S : Finset Qubits) : gateOn S 1 = 1 := by
  rw [gateOn, show (fun j => if j ∈ S then (1 : Equiv.Perm Copies) else 1) = fun _ => 1 from
    funext fun j => by simp, regPerm_one]

/-! ### Hilbert–Schmidt overlaps and the Weingarten Gram matrix -/

/-- The Hilbert–Schmidt overlap `⟨⟨X|Y⟩⟩ = Tr(X† Y)` of Eq. (11) of `magic_monotones.pdf`:
the inner product of the two vectorizations `SchurWeyl.endVec`. -/
def hsOverlap (X Y : RegOp) : ℂ := inner ℂ (endVec X) (endVec Y)

/-- The overlap in trace form, by `SchurWeyl.inner_endVec_endVec`. -/
lemma hsOverlap_eq_trace (X Y : RegOp) :
    hsOverlap X Y = ((toEndMatrix 16 4 X)ᴴ * toEndMatrix 16 4 Y).trace :=
  inner_endVec_endVec X Y

/-- **The overlap of two qubitwise permutation operators factorizes over the qubits**, each
factor being an entry of the repository's Weingarten Gram matrix
`weingartenGram 2 4 σ π = Tr(V₂(σ)† V₂(π))`. This is the "local qubit dimension enters
Eq. (11)" step of `magic_monotones.pdf`. -/
theorem hsOverlap_regPerm (a b : Qubits → Equiv.Perm Copies) :
    hsOverlap (regPerm a) (regPerm b) = ∏ j : Qubits, weingartenGram 2 4 (a j) (b j) := by
  rw [hsOverlap, regPerm, regPerm, inner_endVec_sitePerm]

/-! ### Equation (23): the interlayer overlap -/

/-- The qubitwise permutation data of the first layer: qubits `0, 1` carry `π₁`, qubits
`2, 3` carry `π₂`. -/
lemma layerA_regPerm (π₁ π₂ : Equiv.Perm Copies) :
    V12 π₁ * V34 π₂ = regPerm ![π₁, π₁, π₂, π₂] := by
  rw [V12, V34, gateOn, gateOn, regPerm_mul]
  congr 1
  funext j
  fin_cases j <;> simp

/-- The qubitwise permutation data of the second layer: qubits `1, 2` carry `γ₁`, qubits
`3, 0` carry `γ₂`. -/
lemma layerB_regPerm (γ₁ γ₂ : Equiv.Perm Copies) :
    V23 γ₁ * V41 γ₂ = regPerm ![γ₂, γ₁, γ₁, γ₂] := by
  rw [V23, V41, gateOn, gateOn, regPerm_mul]
  congr 1
  funext j
  fin_cases j <;> simp

/-- **Equation (23) of `magic_monotones.pdf`, Gram form.** The interlayer overlap couples all
four labels, one Gram factor per qubit: qubit `1` carries `(π₁, γ₂)`, qubit `2` carries
`(π₁, γ₁)`, qubit `3` carries `(π₂, γ₁)` and qubit `4` carries `(π₂, γ₂)`. -/
theorem hsOverlap_layer_eq_gram (π₁ π₂ γ₁ γ₂ : Equiv.Perm Copies) :
    hsOverlap (V12 π₁ * V34 π₂) (V23 γ₁ * V41 γ₂)
      = weingartenGram 2 4 π₁ γ₁ * weingartenGram 2 4 π₁ γ₂ *
          (weingartenGram 2 4 π₂ γ₁ * weingartenGram 2 4 π₂ γ₂) := by
  rw [layerA_regPerm, layerB_regPerm, hsOverlap_regPerm, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]
  ring

/-- **Equation (23) of `magic_monotones.pdf`.** Through the repository's closed form for the
Gram entries (`SchurWeyl.K4.weingartenGram_closed` at local dimension `d = 2`), the interlayer
overlap is the power of two
`2^{#(π₁⁻¹γ₁) + #(π₁⁻¹γ₂) + #(π₂⁻¹γ₁) + #(π₂⁻¹γ₂)}`,
where `#(τ)` is the number of cycles of `τ` (fixed points included). -/
theorem hsOverlap_layer_eq_two_pow (π₁ π₂ γ₁ γ₂ : Equiv.Perm Copies) :
    hsOverlap (V12 π₁ * V34 π₂) (V23 γ₁ * V41 γ₂)
      = 2 ^ (numCyc (π₁⁻¹ * γ₁) + numCyc (π₁⁻¹ * γ₂) +
          numCyc (π₂⁻¹ * γ₁) + numCyc (π₂⁻¹ * γ₂)) := by
  rw [hsOverlap_layer_eq_gram]
  simp only [weingartenGram_closed]
  push_cast
  ring

/-! ### The two-qubit gate seen through its two qubits (Eq. (15)) -/

/-- **Two qubits of local dimension `2` make one gate of dimension `d = 4`.** A gate operator
`V₄(σ) = V₂(σ)^{(A)} ⊗ V₂(σ)^{(B)}` contributes one Gram factor per qubit, and their product
is the Gram entry of the repository's `d = 4`, `k = 4` Weingarten system: `2^{#τ} · 2^{#τ} =
4^{#τ}`. -/
theorem gram_two_sq_eq_gram_four (σ π : Equiv.Perm Copies) :
    weingartenGram 2 4 σ π * weingartenGram 2 4 σ π = weingartenGram 4 4 σ π := by
  simp only [weingartenGram_closed, ← mul_pow]
  norm_num

/-- **The intralayer overlap is the `d = 4` Gram matrix of the two gates.** Two labellings of
the *same* layer overlap in the product of the Gram entries of the repository's fourth-moment
system for two-qubit (`d = 4`) gates, one factor per gate. This is why the layer weights are
the `d = 4` Weingarten values `SchurWeyl.K4.wgVal 4`. -/
theorem hsOverlap_layerA_layerA (π₁ π₂ γ₁ γ₂ : Equiv.Perm Copies) :
    hsOverlap (V12 π₁ * V34 π₂) (V12 γ₁ * V34 γ₂)
      = weingartenGram 4 4 π₁ γ₁ * weingartenGram 4 4 π₂ γ₂ := by
  rw [layerA_regPerm, layerA_regPerm, hsOverlap_regPerm, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]
  rw [mul_assoc, gram_two_sq_eq_gram_four π₂ γ₂, gram_two_sq_eq_gram_four π₁ γ₁]

/-! ### Vectorized kets and their overlaps -/

/-- The vectorized permutation operator of layer `A`,
`|V₄^{(12)}(σ₁) V₄^{(34)}(σ₂)⟩⟩`, using the repository's `SchurWeyl.endVec` on the
product of the two full-register copy-permutation operators. -/
def layerAKet (σ₁ σ₂ : Equiv.Perm Copies) : Vecs := endVec (V12 σ₁ * V34 σ₂)

/-- The vectorized permutation operator of layer `B`,
`|V₄^{(23)}(γ₁) V₄^{(41)}(γ₂)⟩⟩`, vectorizing the product of the two full-register
copy-permutation operators. -/
def layerBKet (γ₁ γ₂ : Equiv.Perm Copies) : Vecs := endVec (V23 γ₁ * V41 γ₂)

/-- The inner product of two layer kets is the Hilbert–Schmidt overlap of the corresponding
permutation operators: `⟨⟨V(π₁)V(π₂)|V(γ₁)V(γ₂)⟩⟩`, the quantity appearing in Eqs. (22)–(25). -/
lemma inner_layerAKet_layerBKet (π₁ π₂ γ₁ γ₂ : Equiv.Perm Copies) :
    (inner ℂ (layerAKet π₁ π₂) (layerBKet γ₁ γ₂) : ℂ)
      = hsOverlap (V12 π₁ * V34 π₂) (V23 γ₁ * V41 γ₂) :=
  rfl

/-! ### The layer moment operators -/

/-- The Weingarten coefficient `Wg(σ, 4)` of a two-qubit Haar gate (`d = 4`, `k = 4`), taken
from the fourth-moment computation of `LeanHaar/Moments/k4Moment.lean`. It is the coefficient appearing in the
single-gate moment operator `MagicMonotone.vecMomentOp 4` of Eq. (17). -/
def wg (σ : Equiv.Perm Copies) : ℂ := wgVal 4 σ

/-- **The layer weights invert the intralayer Gram matrix.** This is the repository's
`SchurWeyl.K4.wgVal_inverts_gram` at `d = 4`, the defining property of the Weingarten
coefficients: paired with `MagicMonotone.hsOverlap_layerA_layerA`, it says that the weights
`wg` used in `layerA` and `layerB` are exactly the ones that invert the overlaps of the
gate operators of a layer. -/
theorem wg_inverts_gram (σ ρ : Equiv.Perm Copies) :
    ∑ π : Equiv.Perm Copies, wg (π⁻¹ * ρ) * weingartenGram 4 4 σ π = if σ = ρ then 1 else 0 := by
  simpa [wg] using wgVal_inverts_gram 4 (by norm_num) σ ρ

/-- **The algebraic layer `A` sum**, Eq. (21) of `magic_monotones.pdf`, for pairs `(1,2)`
and `(3,4)`:
`∑ Wg(σ₁⁻¹π₁, 4) Wg(σ₂⁻¹π₂, 4) |V^{(12)}(σ₁) V^{(34)}(σ₂)⟩⟩⟨⟨V^{(12)}(π₁) V^{(34)}(π₂)|`.
Its identification with the average over two independent Haar gates is proved in
`HaarLayers` (`integral_vecActOn_layerA`). -/
def layerA : Vecs →L[ℂ] Vecs :=
  ∑ σ₁, ∑ σ₂, ∑ π₁, ∑ π₂,
    (wg (σ₁⁻¹ * π₁) * wg (σ₂⁻¹ * π₂)) • rankOne ℂ (layerAKet σ₁ σ₂) (layerAKet π₁ π₂)

/-- **The algebraic layer `B` sum**, Eq. (20) of `magic_monotones.pdf`, for staggered
pairs `(2,3)` and `(4,1)`:
`∑ Wg(γ₁⁻¹τ₁, 4) Wg(γ₂⁻¹τ₂, 4) |V^{(23)}(γ₁) V^{(41)}(γ₂)⟩⟩⟨⟨V^{(23)}(τ₁) V^{(41)}(τ₂)|`.
Its identification with the average over two independent Haar gates is proved in
`HaarLayers` (`integral_vecActOn_layerB`). -/
def layerB : Vecs →L[ℂ] Vecs :=
  ∑ γ₁, ∑ γ₂, ∑ τ₁, ∑ τ₂,
    (wg (γ₁⁻¹ * τ₁) * wg (γ₂⁻¹ * τ₂)) • rankOne ℂ (layerBKet γ₁ γ₂) (layerBKet τ₁ τ₂)

/-- The Weingarten weight of a layer, `Wg(σ₁⁻¹π₁, 4) Wg(σ₂⁻¹π₂, 4)`, as a function of the two
pairs of permutations labelling the layer. -/
def wgPair (s p : PermPair) : ℂ := wg (s.1⁻¹ * p.1) * wg (s.2⁻¹ * p.2)

set_option maxRecDepth 1024 in
/-- Layer `A` as a double sum over pairs of permutations. -/
lemma layerA_eq_pairSum :
    layerA = ∑ s : PermPair, ∑ p : PermPair,
      wgPair s p • rankOne ℂ (layerAKet s.1 s.2) (layerAKet p.1 p.2) := by
  simp only [layerA, wgPair, Fintype.sum_prod_type]

set_option maxRecDepth 1024 in
/-- Layer `B` as a double sum over pairs of permutations. -/
lemma layerB_eq_pairSum :
    layerB = ∑ g : PermPair, ∑ t : PermPair,
      wgPair g t • rankOne ℂ (layerBKet g.1 g.2) (layerBKet t.1 t.2) := by
  simp only [layerB, wgPair, Fintype.sum_prod_type]

end MagicMonotone

end
