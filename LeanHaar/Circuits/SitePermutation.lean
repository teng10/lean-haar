/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap
import LeanHaar.SupportingDocs.TensorPowerBasics
import LeanHaar.Circuits.Register
import LeanHaar.WeingartenInverse

/-!
# Site-wise copy permutations

`sitePerm q g` permutes the copies of each register site independently, with local
permutation `g j` at site `j`. Its vectorized entries and Hilbert–Schmidt overlaps
factor over sites. These facts hold for arbitrary local dimension, register size
and copy number, without a stable-range assumption.
-/

noncomputable section

open scoped InnerProductSpace Matrix
open SchurWeyl

namespace SchurWeyl.Circuits

variable {q n k : ℕ}

/-- Matrix of the operator permuting the `k` copies of site `j` by `g j`, in site coordinates. -/
private def sitePermMat (q : ℕ) (g : Fin n → Equiv.Perm (Fin k)) :
    Matrix (Fin n → Fin k → Fin q) (Fin n → Fin k → Fin q) ℂ :=
  Matrix.of fun I J => ∏ j : Fin n, toEndMatrix q k (permOp q (g j)) (I j) (J j)

/-- The entries are `0/1`: site by site, the row is the column relabelled by `(g j)⁻¹`. -/
private theorem sitePermMat_apply (g : Fin n → Equiv.Perm (Fin k)) (I J : Fin n → Fin k → Fin q) :
    sitePermMat q g I J = if ∀ j, I j = J j ∘ (g j).symm then 1 else 0 := by
  simp only [sitePermMat, Matrix.of_apply, permOp, toEndMatrix_permAction]
  rw [Fintype.prod_boole]
  congr 1

private def shift (g : Fin n → Equiv.Perm (Fin k)) (I : Fin n → Fin k → Fin q) :
    Fin n → Fin k → Fin q := fun j => I j ∘ (g j)

private theorem sitePermMat_apply_shift (g : Fin n → Equiv.Perm (Fin k))
    (I : Fin n → Fin k → Fin q) : sitePermMat q g I (shift g I) = 1 := by
  rw [sitePermMat_apply, if_pos]
  intro j
  funext c
  simp [shift]

private theorem sitePermMat_eq_zero_of_ne (g : Fin n → Equiv.Perm (Fin k))
    (I J : Fin n → Fin k → Fin q) (h : J ≠ shift g I) : sitePermMat q g I J = 0 := by
  rw [sitePermMat_apply, if_neg]
  intro hI
  refine h (funext fun j => funext fun c => ?_)
  have := congrFun (hI j) ((g j) c)
  simpa [shift] using this.symm

private theorem sitePermMat_one : sitePermMat q (fun _ : Fin n => (1 : Equiv.Perm (Fin k))) = 1 := by
  ext I J
  rw [sitePermMat_apply, Matrix.one_apply]
  refine if_congr ⟨fun h => funext fun j => by simpa using h j,
    fun h j => by simp [h, ← Equiv.Perm.inv_def]⟩ rfl rfl

private theorem sitePermMat_mul (g h : Fin n → Equiv.Perm (Fin k)) :
    sitePermMat q g * sitePermMat q h = sitePermMat q (fun j => g j * h j) := by
  ext I K
  rw [Matrix.mul_apply, Finset.sum_eq_single (shift g I)]
  · rw [sitePermMat_apply_shift, one_mul, sitePermMat_apply, sitePermMat_apply]
    refine if_congr ⟨fun hI j => funext fun c => ?_, fun hI j => funext fun c => ?_⟩ rfl rfl
    · have := congrFun (hI j) ((g j).symm c)
      simpa [shift, Equiv.Perm.mul_def] using this
    · have := congrFun (hI j) ((g j) c)
      simpa [shift, Equiv.Perm.mul_def] using this
  · intro J _ hJ
    rw [sitePermMat_eq_zero_of_ne g I J hJ, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-- The operator on `k` copies of an `n`-site register that permutes the copies of site `j`
by `g j`. -/
def sitePerm (q : ℕ) (g : Fin n → Equiv.Perm (Fin k)) : Module.End ℂ (TensV (q ^ n) k) :=
  (toEndMatrix (q ^ n) k).symm
    ((sitePermMat q g).submatrix (copySiteEquiv q n k) (copySiteEquiv q n k))

private theorem toEndMatrix_sitePerm (g : Fin n → Equiv.Perm (Fin k)) :
    toEndMatrix (q ^ n) k (sitePerm q g) =
      (sitePermMat q g).submatrix (copySiteEquiv q n k) (copySiteEquiv q n k) :=
  (toEndMatrix (q ^ n) k).apply_symm_apply _

/-- Entries of the vectorized site permutation, in the register's own coordinates. -/
theorem endVec_sitePerm_apply (g : Fin n → Equiv.Perm (Fin k))
    (p : (Fin k → Fin (q ^ n)) × (Fin k → Fin (q ^ n))) :
    endVec (sitePerm q g) p =
      if ∀ j c, registerEquiv q n (p.1 c) j = registerEquiv q n (p.2 ((g j).symm c)) j
      then 1 else 0 := by
  rw [endVec_apply, toEndMatrix_sitePerm, Matrix.submatrix_apply, sitePermMat_apply]
  refine if_congr ⟨fun h j c => congrFun (h j) c, fun h j => funext fun c => h j c⟩ rfl rfl

/-- Applying one copy permutation at every site is the global copy permutation. -/
theorem sitePerm_const (σ : Equiv.Perm (Fin k)) :
    sitePerm q (fun _ : Fin n => σ) = permOp (q ^ n) σ := by
  apply (endVecEquiv (q ^ n) k).injective
  change endVec _ = endVec _
  ext p
  rw [endVec_sitePerm_apply, endVec_apply]
  simp only [permOp, toEndMatrix_permAction]
  refine if_congr ⟨fun h => funext fun c => (registerEquiv q n).injective (funext fun j => h j c),
    fun h j c => by rw [h]; rfl⟩ rfl rfl

/-- The identity permutation at every site acts as the identity. -/
theorem sitePerm_one : sitePerm q (fun _ : Fin n => (1 : Equiv.Perm (Fin k))) = 1 := by
  refine (toEndMatrix (q ^ n) k).injective ?_
  rw [toEndMatrix_sitePerm, sitePermMat_one, Matrix.submatrix_one_equiv, toEndMatrix_one]

/-- Composing site-wise copy permutations multiplies their local permutations. -/
theorem sitePerm_mul (g h : Fin n → Equiv.Perm (Fin k)) :
    sitePerm q g * sitePerm q h = sitePerm q (fun j => g j * h j) := by
  refine (toEndMatrix (q ^ n) k).injective ?_
  rw [toEndMatrix_mul, toEndMatrix_sitePerm, toEndMatrix_sitePerm, toEndMatrix_sitePerm,
    Matrix.submatrix_mul_equiv, sitePermMat_mul]

private theorem trace_submatrix_equiv {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix n n ℂ) (e : m ≃ n) : (A.submatrix e e).trace = A.trace :=
  Equiv.sum_comp e fun j => A j j

private def relabel (a : Fin n → Equiv.Perm (Fin k)) (I : Fin n → Fin k → Fin q) :
    Fin n → Fin k → Fin q := fun j => I j ∘ (a j).symm

private theorem trace_sitePermMat_inner_sum (a b : Fin n → Equiv.Perm (Fin k))
    (I : Fin n → Fin k → Fin q) :
    ∑ J : Fin n → Fin k → Fin q, star (sitePermMat q a J I) * sitePermMat q b J I
      = ∏ j : Fin n, (if I j ∘ (a j).symm = I j ∘ (b j).symm then (1 : ℂ) else 0) := by
  classical
  have hzero : ∀ J : Fin n → Fin k → Fin q, J ≠ relabel a I →
      star (sitePermMat q a J I) * sitePermMat q b J I = 0 := by
    intro J hJ
    have : sitePermMat q a J I = 0 := by
      rw [sitePermMat_apply, if_neg]
      exact fun hI => hJ (funext fun j => hI j)
    rw [this, star_zero, zero_mul]
  rw [Finset.sum_eq_single (relabel a I) (fun J _ hJ => hzero J hJ)
    (fun h => absurd (Finset.mem_univ _) h)]
  have hone : sitePermMat q a (relabel a I) I = 1 := by
    rw [sitePermMat_apply, if_pos]
    exact fun j => rfl
  rw [hone, star_one, one_mul, sitePermMat_apply, Fintype.prod_boole]
  congr 1

private theorem sum_indicator_eq_gram (σ π : Equiv.Perm (Fin k)) :
    ∑ x : Fin k → Fin q, (if x ∘ σ.symm = x ∘ π.symm then (1 : ℂ) else 0)
      = weingartenGram q k σ π := by
  classical
  rw [weingartenGram_eq_card, Finset.sum_boole, Fintype.card_subtype]

private theorem trace_sitePermMat (a b : Fin n → Equiv.Perm (Fin k)) :
    ((sitePermMat q a)ᴴ * sitePermMat q b).trace =
      ∏ j : Fin n, weingartenGram q k (a j) (b j) := by
  classical
  have hsum : ((sitePermMat q a)ᴴ * sitePermMat q b).trace
      = ∑ I : Fin n → Fin k → Fin q, ∑ J : Fin n → Fin k → Fin q,
          star (sitePermMat q a J I) * sitePermMat q b J I := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hsum]
  simp only [trace_sitePermMat_inner_sum a b]
  have hfactor := Finset.prod_univ_sum
    (fun _ : Fin n => (Finset.univ : Finset (Fin k → Fin q)))
    (fun j x => if x ∘ (a j).symm = x ∘ (b j).symm then (1 : ℂ) else 0)
  rw [Fintype.piFinset_univ] at hfactor
  rw [← hfactor]
  exact Finset.prod_congr rfl fun j _ => sum_indicator_eq_gram (a j) (b j)

/-- **Gram factorization.** The Hilbert–Schmidt overlap of two site permutations is a
product over sites of single-site Weingarten Gram entries, at the local dimension `q`. -/
theorem inner_endVec_sitePerm (a b : Fin n → Equiv.Perm (Fin k)) :
    (inner ℂ (endVec (sitePerm q a)) (endVec (sitePerm q b)) : ℂ) =
      ∏ j : Fin n, weingartenGram q k (a j) (b j) := by
  rw [inner_endVec_endVec, toEndMatrix_sitePerm, toEndMatrix_sitePerm,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    trace_submatrix_equiv, trace_sitePermMat]

end SchurWeyl.Circuits

end
