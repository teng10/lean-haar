/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Aesop

/-!
# Singular Value Decomposition (SVD) for Square Complex Matrices

This file contains the construction of the Singular Value Decomposition (SVD)
for square complex matrices, showing that any such matrix factors as `U₁ · diagonal s · U₂`
with `U₁, U₂` unitary and `s` complex diagonal.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace ForMathlib.Tensor

variable {d : ℕ}

/-- **Orthonormal completion of the normalized columns.** If `Nᴴ * N` is the diagonal
matrix with nonnegative real entries `D`, then the columns of `N` are pairwise orthogonal
and the `i`-th column has squared norm `D i`. Normalizing the columns with `D i ≠ 0` gives
an orthonormal family, which extends to an orthonormal basis `b` of `EuclideanSpace ℂ (Fin d)`
with `b i` equal to the normalized `i`-th column whenever `D i ≠ 0`. -/
theorem exists_orthonormalBasis_cols (D : Fin d → ℝ) (hD : ∀ i, 0 ≤ D i)
    (N : Matrix (Fin d) (Fin d) ℂ)
    (hN : Nᴴ * N = Matrix.diagonal (fun i => (D i : ℂ))) :
    ∃ b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)),
      ∀ i, D i ≠ 0 → ∀ j, b i j = (1 / (Real.sqrt (D i) : ℂ)) * N j i := by
  have h_orthonormal : Orthonormal ℂ (fun i : { i : Fin d // D i ≠ 0 } => WithLp.toLp 2 (fun j => (1 / Real.sqrt (D i) : ℂ) • N j i)) := by
    refine' ⟨ _, _ ⟩;
    · simp +decide [ EuclideanSpace.norm_eq ];
      intro i hi; simp +decide [ mul_pow, abs_of_nonneg ( Real.sqrt_nonneg _ ) ] ;
      have := congr_fun ( congr_fun hN i ) i; simp_all +decide [ Matrix.mul_apply, Complex.ext_iff ] ;
      simp_all +decide [ Complex.normSq, Complex.sq_norm, ← Finset.mul_sum _ _ _ ];
    · intro i j hij; simp_all +decide [ inner ] ;
      replace hN := congr_fun ( congr_fun hN i ) j; simp_all +decide [ Matrix.mul_apply, Matrix.diagonal ] ;
      convert congr_arg ( fun x : ℂ => ( Real.sqrt ( D j ) : ℂ ) ⁻¹ * ( Real.sqrt ( D i ) : ℂ ) ⁻¹ * x ) hN using 1;
      · rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by ring;
      · grind;
  obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)), ∀ i : { i : Fin d // D i ≠ 0 }, b i = WithLp.toLp 2 (fun j => (1 / Real.sqrt (D i) : ℂ) • N j i) := by
    have := @Orthonormal.exists_orthonormalBasis_extension_of_card_eq;
    contrapose! this;
    refine' ⟨ ℂ, inferInstance, EuclideanSpace ℂ ( Fin d ), inferInstance, inferInstance, _, Fin d, inferInstance, _, _ ⟩ <;> norm_num;
    · infer_instance;
    · refine' ⟨ fun i => WithLp.toLp 2 ( fun j => ( 1 / Real.sqrt ( D i ) : ℂ ) • N j i ), { i : Fin d | D i ≠ 0 }, _, _ ⟩ <;> aesop;
  exact ⟨ b, fun i hi j => by simpa using congr_fun ( congr_arg ( fun x => x.ofLp ) ( hb ⟨ i, hi ⟩ ) ) j ⟩

set_option maxHeartbeats 1000000 in
/-- **Singular value decomposition (existence).** Every complex square matrix factors as
`U₁ · diagonal s · U₂` with U₁, U₂ unitary and s a (complex) diagonal. -/
theorem svd_exists (M : Matrix (Fin d) (Fin d) ℂ) :
    ∃ (U₁ U₂ : Matrix.unitaryGroup (Fin d) ℂ) (s : Fin d → ℂ),
      M = (U₁ : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal s *
        (U₂ : Matrix (Fin d) (Fin d) ℂ) := by
  by_contra h_contra;
  set A : Matrix (Fin d) (Fin d) ℂ := M.conjTranspose * M;
  -- Since A is positive semidefinite, it has a spectral decomposition A = Q D Q* where Q is unitary and D is diagonal with non-negative entries.
  obtain ⟨Q, D, hQ, hD⟩ : ∃ Q : Matrix (Fin d) (Fin d) ℂ, ∃ D : Fin d → ℝ, (∀ i, 0 ≤ D i) ∧ Qᴴ * Q = 1 ∧ A = Q * Matrix.diagonal (fun i => (D i : ℂ)) * Qᴴ := by
    have h_pos_semidef : Matrix.IsHermitian A := by
      simp [A, Matrix.IsHermitian];
    have := Matrix.IsHermitian.spectral_theorem h_pos_semidef;
    refine' ⟨ h_pos_semidef.eigenvectorUnitary, fun i => h_pos_semidef.eigenvalues i, _, _, _ ⟩;
    · intro i; exact eigenvalues_conjTranspose_mul_self_nonneg M i;
    · simp +decide [ Matrix.IsHermitian.eigenvectorUnitary ];
    · convert this using 1;
  -- Let N = M Q. Then Nᴴ N = Qᴴ Mᴴ M Q = Qᴴ A Q = D.
  set N : Matrix (Fin d) (Fin d) ℂ := M * Q
  have hN : Nᴴ * N = Matrix.diagonal (fun i => (D i : ℂ)) := by
    simp +zetaDelta at *;
    grind;
  obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)), ∀ i, D i ≠ 0 → ∀ j, b i j = (1 / (Real.sqrt (D i) : ℂ)) * N j i := by
    convert ForMathlib.Tensor.exists_orthonormalBasis_cols D hQ N hN using 1;
  -- Let U₁ be the matrix whose columns are the vectors b_i.
  obtain ⟨U₁, hU₁⟩ : ∃ U₁ : Matrix (Fin d) (Fin d) ℂ, U₁ ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ ∀ i j, U₁ j i = b i j := by
    refine' ⟨ _, _, _ ⟩;
    exact ( EuclideanSpace.basisFun ( Fin d ) ℂ ).toBasis.toMatrix b;
    · convert OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary ( EuclideanSpace.basisFun ( Fin d ) ℂ ) b using 1;
    · aesop;
  -- Then U₁ * diagonal s = N where s_i = \sqrt{D_i}.
  have hU₁_diag : U₁ * Matrix.diagonal (fun i => (Real.sqrt (D i) : ℂ)) = N := by
    ext i j; by_cases hi : D j = 0 <;> simp_all +decide [ Matrix.mul_apply, Matrix.diagonal ] ;
    · replace hN := congr_fun ( congr_fun hN j ) j; simp_all +decide [ Matrix.mul_apply, Complex.ext_iff ] ;
      simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, add_nonneg, mul_self_nonneg ];
      constructor <;> nlinarith only [ hN.1 i ];
    · rw [ inv_mul_eq_div, div_mul_cancel₀ _ ( Complex.ofReal_ne_zero.mpr <| ne_of_gt <| Real.sqrt_pos.mpr <| lt_of_le_of_ne ( hQ j ) <| Ne.symm hi ) ];
  refine' h_contra ⟨ ⟨ U₁, hU₁.1 ⟩, ⟨ Qᴴ, _ ⟩, fun i => Real.sqrt ( D i ), _ ⟩ <;> simp_all +decide [ Matrix.mul_assoc ];
  · simp_all +decide [ Matrix.mem_unitaryGroup_iff ];
    simp_all +decide [ Matrix.star_eq_conjTranspose ];
  · rw [ Matrix.mul_assoc, mul_eq_one_comm.mp hD.1, Matrix.mul_one ]

end ForMathlib.Tensor
