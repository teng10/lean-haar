/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.ForMathlibExamples.MagicMonotone.SingleGateMoment

/-!
# Two brickwork layers on four qubits: the vectorized layer moment operators

This file sets up the concrete example of Section III C of `magic_monotones.pdf`: `n = 4`
qubits, `k = 4` copies, and two brickwork layers of Haar-random two-qubit gates,

* layer `A`: gates on the qubit pairs `(1,2)` and `(3,4)`;
* layer `B`: gates on the staggered pairs `(2,3)` and `(4,1)`.

Qubits are numbered `0, 1, 2, 3` here, so the four pairs are `{0,1}`, `{2,3}`, `{1,2}`
and `{3,0}`.

Everything is expressed through the repository's own objects. The four-qubit register is the
system of local dimension `d = 2^4 = 16`, so its `k = 4` copies are the repository's
`SchurWeyl.TensV 16 4`, the layer operators are honest endomorphisms of that space, and their
vectorizations `|·⟩⟩` are the repository's `SchurWeyl.endVec` — no separate vectorization is
introduced. Concretely:

* an operator is described by its matrix in the computational basis through the repository's
  `SchurWeyl.toEndMatrix 16 4`, and the computational basis index `Fin 4 → Fin 16` is read
  qubit by qubit through the bit decomposition `MagicMonotone.regIndexEquiv`;
* the gate operators are built qubit by qubit out of the single-qubit permutation operators
  `SchurWeyl.permOp 2` (this is Eq. (13) of the source);
* the Weingarten weights are the `k = 4` Weingarten values `SchurWeyl.K4.wgVal`, and the
  interlayer overlaps are entries of the repository's Weingarten Gram matrix
  `SchurWeyl.weingartenGram 2 4`, whose closed form `SchurWeyl.K4.weingartenGram_closed`
  supplies the powers of `2` of Eq. (23).

## Main definitions

* `MagicMonotone.regIndexEquiv`: the identification of a computational basis index of the
  four copies of the register, `Fin 4 → Fin 16`, with its qubitwise bit pattern.
* `MagicMonotone.regPerm g`: the permutation operator `⨂_j V₂(g j)^{(j)}` of Eq. (13) that
  permutes the `k = 4` copies of qubit `j` by `g j`; each tensor factor is the matrix of the
  repository's permutation operator `SchurWeyl.permOp 2 (g j)` on `(ℂ²)^{⊗4}`.
* `MagicMonotone.gateOn S σ`: the gate operator that applies `σ` to the copies of the qubits
  in `S` and leaves the other qubits alone; the two-qubit gate operators `V₄^{(12)}(σ)` etc.
  of Eq. (15) are `MagicMonotone.V12`, `V34`, `V23`, `V41`.
* `MagicMonotone.hsOverlap X Y = ⟨⟨X|Y⟩⟩`: the Hilbert–Schmidt overlap of Eq. (11), i.e. the
  inner product of the two vectorizations `SchurWeyl.endVec`.
* `MagicMonotone.layerAKet σ₁ σ₂ = |V₄^{(12)}(σ₁) V₄^{(34)}(σ₂)⟩⟩` and
  `MagicMonotone.layerBKet γ₁ γ₂ = |V₄^{(23)}(γ₁) V₄^{(41)}(γ₂)⟩⟩`: the vectorized
  permutation operators of the two layers.
* `MagicMonotone.layerA` and `MagicMonotone.layerB`: the vectorized layer moment operators,
  Eqs. (21) and (20) of the source. Each gate contributes a copy of the vectorized
  single-gate moment operator of Eq. (17) (`MagicMonotone.vecMomentOp`), so the Weingarten
  weight `MagicMonotone.wgPair` is a product of two values of `SchurWeyl.K4.wgVal`.

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
  ket-bra calculus of `RankOneCalculus.lean` applies.
-/

noncomputable section

-- The register index type `Fin 4 → Fin 16` makes elaboration of the layer sums deep.
set_option maxRecDepth 8000

open scoped InnerProductSpace Matrix
open InnerProductSpace ContinuousLinearMap SchurWeyl SchurWeyl.K4

namespace MagicMonotone

/-! ### The four copies of the four-qubit register -/

/-- The `k = 4` copies of the system. -/
abbrev Copies : Type := Fin 4

/-- The `n = 4` qubits of the register. -/
abbrev Qubits : Type := Fin 4

/-- A computational basis index of the four copies of a *single* qubit. This is the index
type `Fin k → Fin d` of the repository's matrices for `k = 4` copies of a `d = 2`
dimensional system, so single-qubit permutation operators are literally matrices over it. -/
abbrev QubitReg : Type := Copies → Fin 2

/-- The qubitwise reading of a computational basis index of the four copies of the register:
one bit for each qubit and each copy. -/
abbrev QubitIdx : Type := Qubits → QubitReg

/-- A computational basis index of the four copies of the four-qubit register, in the form
`Fin k → Fin d` used by the repository: the four-qubit register has local dimension
`d = 2^4 = 16`, and there are `k = 4` copies of it. -/
abbrev Reg : Type := Copies → Fin 16

/-- An operator on the four copies of the four-qubit register: an endomorphism of the
repository's tensor power `SchurWeyl.TensV 16 4`. -/
abbrev RegOp : Type := Module.End ℂ (TensV 16 4)

/-- The vectorized operator space of the register, where the moment operators live. It is
the codomain of the repository's vectorization `SchurWeyl.endVec` for `d = 16`, `k = 4`. -/
abbrev Vecs : Type := EuclideanSpace ℂ (Reg × Reg)

/-- A pair of permutations of the four copies: the label of one brickwork layer, one
permutation per gate of the layer. -/
abbrev PermPair : Type := Equiv.Perm Copies × Equiv.Perm Copies

/-- The bit decomposition of a register state: a state of the four-qubit register
(`Fin 16`) is a bit for each of the four qubits. -/
def bitsEquiv : Fin 16 ≃ (Qubits → Fin 2) :=
  (finCongr (show (16 : ℕ) = 2 ^ 4 by norm_num)).trans finFunctionFinEquiv.symm

/-- **Reading a basis index qubit by qubit.** A computational basis index of the four copies
of the register, `Fin 4 → Fin 16`, is the same thing as a bit for each qubit and each copy.
This is the only bookkeeping needed to see the register as a system of local dimension
`2^4 = 16` in the sense of the repository. -/
def regIndexEquiv : Reg ≃ QubitIdx :=
  ((Equiv.refl Copies).arrowCongr bitsEquiv).trans (Equiv.piComm _)

/-! ### Permutation operators, qubit by qubit (Eq. (13))

The matrix of a qubitwise permutation operator is written first in the qubitwise index
`QubitIdx`, where it visibly factorizes over the qubits, and is then transported to the
register index `Reg` by `regIndexEquiv`. -/

/-- The matrix of the qubitwise permutation operator of Eq. (13) in the qubitwise index: the
product over the qubits `j` of the matrices of the repository's permutation operators
`SchurWeyl.permOp 2 (g j)` acting on the four copies of a single qubit. -/
def regPermMat (g : Qubits → Equiv.Perm Copies) : Matrix QubitIdx QubitIdx ℂ :=
  Matrix.of fun I J => ∏ j : Qubits, toEndMatrix 2 4 (permOp 2 (g j)) (I j) (J j)

/-- The entries of `regPermMat g` are `0/1`: the entry is `1` exactly when, for every qubit,
the row index is obtained from the column index by relabelling the copies by `(g j)⁻¹`. -/
lemma regPermMat_apply (g : Qubits → Equiv.Perm Copies) (I J : QubitIdx) :
    regPermMat g I J = if ∀ j, I j = J j ∘ (g j).symm then 1 else 0 := by
  simp only [regPermMat, Matrix.of_apply, permOp, toEndMatrix_permAction]
  rw [Fintype.prod_boole]
  congr 1

/-- The column index determined by a row index: `regPermMat g I J = 1` exactly for
`J = shift g I`. -/
private def shift (g : Qubits → Equiv.Perm Copies) (I : QubitIdx) : QubitIdx :=
  fun j => I j ∘ (g j)

/-- Undoing a product of permutations, one factor at a time. -/
private lemma perm_mul_symm_apply (g h : Equiv.Perm Copies) (c : Copies) :
    (g * h).symm c = h.symm (g.symm c) := by
  rw [← Equiv.Perm.inv_def, mul_inv_rev]
  simp [Equiv.Perm.mul_apply]

private lemma regPermMat_apply_shift (g : Qubits → Equiv.Perm Copies) (I : QubitIdx) :
    regPermMat g I (shift g I) = 1 := by
  rw [regPermMat_apply, if_pos]
  intro j
  funext c
  simp [shift]

private lemma regPermMat_eq_zero_of_ne (g : Qubits → Equiv.Perm Copies) (I J : QubitIdx)
    (h : J ≠ shift g I) : regPermMat g I J = 0 := by
  rw [regPermMat_apply, if_neg]
  intro hI
  refine h (funext fun j => funext fun c => ?_)
  have := congrFun (hI j) ((g j) c)
  simpa [shift] using this.symm

/-- Every qubit carrying the identity permutation gives the identity matrix. -/
lemma regPermMat_one : regPermMat (fun _ => 1) = 1 := by
  ext I J
  rw [regPermMat_apply, Matrix.one_apply]
  refine if_congr ⟨fun h => funext fun j => by simpa using h j,
    fun h j => by simp [h, ← Equiv.Perm.inv_def]⟩ rfl rfl

/-- Applying `h` and then `g`, qubit by qubit, is the matrix of the qubitwise product. -/
lemma regPermMat_mul (g h : Qubits → Equiv.Perm Copies) :
    regPermMat g * regPermMat h = regPermMat (fun j => g j * h j) := by
  ext I K
  rw [Matrix.mul_apply, Finset.sum_eq_single (shift g I)]
  · rw [regPermMat_apply_shift, one_mul, regPermMat_apply, regPermMat_apply]
    refine if_congr ⟨fun hI j => funext fun c => ?_, fun hI j => funext fun c => ?_⟩ rfl rfl
    · have := congrFun (hI j) ((g j).symm c)
      simpa [shift, perm_mul_symm_apply] using this
    · have := congrFun (hI j) ((g j) c)
      simpa [shift, perm_mul_symm_apply] using this
  · intro J _ hJ
    rw [regPermMat_eq_zero_of_ne g I J hJ, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-- **The qubitwise permutation operator of Eq. (13)**, `⨂_{j} V₂(g j)^{(j)}`: it permutes
the `k = 4` copies of qubit `j` by `g j`. It is the operator on the repository's
`TensV 16 4` whose matrix in the computational basis is `regPermMat g`, read qubit by qubit
through `regIndexEquiv`. -/
def regPerm (g : Qubits → Equiv.Perm Copies) : RegOp :=
  (toEndMatrix 16 4).symm ((regPermMat g).submatrix regIndexEquiv regIndexEquiv)

@[simp] lemma toEndMatrix_regPerm (g : Qubits → Equiv.Perm Copies) :
    toEndMatrix 16 4 (regPerm g) = (regPermMat g).submatrix regIndexEquiv regIndexEquiv :=
  (toEndMatrix 16 4).apply_symm_apply _

/-- Every qubit carrying the identity permutation gives the identity operator. -/
lemma regPerm_one : regPerm (fun _ => 1) = 1 := by
  refine (toEndMatrix 16 4).injective ?_
  rw [toEndMatrix_regPerm, regPermMat_one, Matrix.submatrix_one_equiv, toEndMatrix_one]

/-- **The operators of Eq. (13) form a representation**: applying `h` and then `g`, qubit by
qubit, is the operator of the qubitwise product `g · h`. -/
lemma regPerm_mul (g h : Qubits → Equiv.Perm Copies) :
    regPerm g * regPerm h = regPerm (fun j => g j * h j) := by
  refine (toEndMatrix 16 4).injective ?_
  rw [toEndMatrix_mul, toEndMatrix_regPerm, toEndMatrix_regPerm, toEndMatrix_regPerm,
    Matrix.submatrix_mul_equiv, regPermMat_mul]

/-- The gate operator that permutes the copies of the qubits in `S` by `σ`, leaving the
other qubits untouched. The two-qubit gate operators `V₄^{(12)}(σ) = V₂(σ)^{(1)} ⊗ V₂(σ)^{(2)}`
of Eq. (15) are of this form. -/
def gateOn (S : Finset Qubits) (σ : Equiv.Perm Copies) : RegOp :=
  regPerm fun j => if j ∈ S then σ else 1

/-- The gate operator `V₄^{(12)}(σ)` of the first gate of layer `A` (qubits `0, 1`). -/
def V12 (σ : Equiv.Perm Copies) : RegOp := gateOn {0, 1} σ

/-- The gate operator `V₄^{(34)}(σ)` of the second gate of layer `A` (qubits `2, 3`). -/
def V34 (σ : Equiv.Perm Copies) : RegOp := gateOn {2, 3} σ

/-- The gate operator `V₄^{(23)}(σ)` of the first gate of layer `B` (qubits `1, 2`). -/
def V23 (σ : Equiv.Perm Copies) : RegOp := gateOn {1, 2} σ

/-- The gate operator `V₄^{(41)}(σ)` of the second gate of layer `B` (qubits `3, 0`). -/
def V41 (σ : Equiv.Perm Copies) : RegOp := gateOn {3, 0} σ

/-- A gate with the identity permutation is the identity operator. -/
lemma gateOn_one (S : Finset Qubits) : gateOn S 1 = 1 := by
  rw [gateOn, show (fun j => if j ∈ S then (1 : Equiv.Perm Copies) else 1) = fun _ => 1 from
    funext fun j => by simp, regPerm_one]

/-! ### Hilbert–Schmidt overlaps and the Weingarten Gram matrix -/

/-- The Hilbert–Schmidt overlap `⟨⟨X|Y⟩⟩ = Tr(X† Y)` of Eq. (11) of `magic_monotones.pdf`:
the inner product of the two vectorizations `SchurWeyl.endVec`. -/
def hsOverlap (X Y : RegOp) : ℂ := inner ℂ (endVec X) (endVec Y)

/-- The overlap in trace form, by `MagicMonotone.inner_endVec_endVec`. -/
lemma hsOverlap_eq_trace (X Y : RegOp) :
    hsOverlap X Y = ((toEndMatrix 16 4 X)ᴴ * toEndMatrix 16 4 Y).trace :=
  inner_endVec_endVec X Y

/-- Relabelling the rows and columns of a matrix by an equivalence does not change its
trace. -/
private lemma trace_submatrix_equiv {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix n n ℂ) (e : m ≃ n) : (A.submatrix e e).trace = A.trace :=
  Equiv.sum_comp e fun j => A j j

/-- The row index that contributes to the overlap: it is the unique `J` with
`regPermMat a J I = 1`. -/
private def relabel (a : Qubits → Equiv.Perm Copies) (I : QubitIdx) : QubitIdx :=
  fun j => I j ∘ (a j).symm

/-- Contracting one summation index: for a fixed column index `I`, only the row
`relabel a I` contributes to the overlap, and it contributes exactly when relabelling the
copies of each qubit `j` by `a j` and by `b j` gives the same result. -/
private lemma trace_regPermMat_inner_sum (a b : Qubits → Equiv.Perm Copies) (I : QubitIdx) :
    ∑ J : QubitIdx, star (regPermMat a J I) * regPermMat b J I
      = ∏ j : Qubits, (if I j ∘ (a j).symm = I j ∘ (b j).symm then (1 : ℂ) else 0) := by
  classical
  have hzero : ∀ J : QubitIdx, J ≠ relabel a I → star (regPermMat a J I) * regPermMat b J I = 0 := by
    intro J hJ
    have : regPermMat a J I = 0 := by
      rw [regPermMat_apply, if_neg]
      exact fun hI => hJ (funext fun j => hI j)
    rw [this, star_zero, zero_mul]
  rw [Finset.sum_eq_single (relabel a I) (fun J _ hJ => hzero J hJ)
    (fun h => absurd (Finset.mem_univ _) h)]
  have hone : regPermMat a (relabel a I) I = 1 := by
    rw [regPermMat_apply, if_pos]
    exact fun j => rfl
  rw [hone, star_one, one_mul, regPermMat_apply, Fintype.prod_boole]
  congr 1

/-- Summing a single-qubit coincidence indicator gives an entry of the repository's
Weingarten Gram matrix for `d = 2`, `k = 4`, by `SchurWeyl.weingartenGram_eq_card`. -/
private lemma sum_indicator_eq_gram (σ π : Equiv.Perm Copies) :
    ∑ x : QubitReg, (if x ∘ σ.symm = x ∘ π.symm then (1 : ℂ) else 0)
      = weingartenGram 2 4 σ π := by
  classical
  rw [weingartenGram_eq_card, Finset.sum_boole, Fintype.card_subtype]

/-- **The Hilbert–Schmidt overlap of two qubitwise permutation matrices factorizes over the
qubits**, each factor being an entry of the repository's Weingarten Gram matrix
`weingartenGram 2 4 σ π = Tr(V₂(σ)† V₂(π))`. -/
theorem trace_regPermMat (a b : Qubits → Equiv.Perm Copies) :
    ((regPermMat a)ᴴ * regPermMat b).trace = ∏ j : Qubits, weingartenGram 2 4 (a j) (b j) := by
  classical
  have hsum : ((regPermMat a)ᴴ * regPermMat b).trace
      = ∑ I : QubitIdx, ∑ J : QubitIdx, star (regPermMat a J I) * regPermMat b J I := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  -- Contract the row index, one column index at a time.
  rw [hsum]
  simp only [trace_regPermMat_inner_sum a b]
  -- The remaining sum over the register factorizes over the qubits.
  have hfactor := Finset.prod_univ_sum (fun _ : Qubits => (Finset.univ : Finset QubitReg))
    (fun j x => if x ∘ (a j).symm = x ∘ (b j).symm then (1 : ℂ) else 0)
  rw [Fintype.piFinset_univ] at hfactor
  rw [← hfactor]
  exact Finset.prod_congr rfl fun j _ => sum_indicator_eq_gram (a j) (b j)

/-- **The overlap of two qubitwise permutation operators factorizes over the qubits**, each
factor being an entry of the repository's Weingarten Gram matrix
`weingartenGram 2 4 σ π = Tr(V₂(σ)† V₂(π))`. This is the "local qubit dimension enters
Eq. (11)" step of `magic_monotones.pdf`. -/
theorem hsOverlap_regPerm (a b : Qubits → Equiv.Perm Copies) :
    hsOverlap (regPerm a) (regPerm b) = ∏ j : Qubits, weingartenGram 2 4 (a j) (b j) := by
  rw [hsOverlap_eq_trace, toEndMatrix_regPerm, toEndMatrix_regPerm,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    trace_submatrix_equiv, trace_regPermMat]

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
`|V₄^{(12)}(σ₁)⟩⟩|V₄^{(34)}(σ₂)⟩⟩ = |V₄^{(12)}(σ₁) V₄^{(34)}(σ₂)⟩⟩`, i.e. the repository's
`SchurWeyl.endVec` of the layer operator. -/
def layerAKet (σ₁ σ₂ : Equiv.Perm Copies) : Vecs := endVec (V12 σ₁ * V34 σ₂)

/-- The vectorized permutation operator of layer `B`,
`|V₄^{(23)}(γ₁)⟩⟩|V₄^{(41)}(γ₂)⟩⟩ = |V₄^{(23)}(γ₁) V₄^{(41)}(γ₂)⟩⟩`. -/
def layerBKet (γ₁ γ₂ : Equiv.Perm Copies) : Vecs := endVec (V23 γ₁ * V41 γ₂)

/-- The inner product of two layer kets is the Hilbert–Schmidt overlap of the corresponding
permutation operators: `⟨⟨V(π₁)V(π₂)|V(γ₁)V(γ₂)⟩⟩`, the quantity appearing in Eqs. (22)–(25). -/
lemma inner_layerAKet_layerBKet (π₁ π₂ γ₁ γ₂ : Equiv.Perm Copies) :
    (inner ℂ (layerAKet π₁ π₂) (layerBKet γ₁ γ₂) : ℂ)
      = hsOverlap (V12 π₁ * V34 π₂) (V23 γ₁ * V41 γ₂) :=
  rfl

/-! ### The layer moment operators -/

/-- The Weingarten coefficient `Wg(σ, 4)` of a two-qubit Haar gate (`d = 4`, `k = 4`), taken
from the fourth-moment computation of `k4Moment.lean`. It is the coefficient appearing in the
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

/-- **Layer `A`**, Eq. (21) of `magic_monotones.pdf`: the vectorized moment operator of the
two independent Haar gates on the qubit pairs `(1,2)` and `(3,4)`,
`∑ Wg(σ₁⁻¹π₁, 4) Wg(σ₂⁻¹π₂, 4) |V^{(12)}(σ₁)⟩⟩|V^{(34)}(σ₂)⟩⟩⟨⟨V^{(12)}(π₁)|⟨⟨V^{(34)}(π₂)|`.
Each of the two gates contributes one copy of the single-gate moment operator of Eq. (17). -/
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
