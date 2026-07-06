/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.CategoryTheory.Category.Basic
import Aesop

import LeanHaar.ForMathlib.TensorV2
import LeanHaar.ForMathlib.Commutation
import LeanHaar.ForMathlib.PolyIndep
import LeanHaar.ForMathlib.DCT
import LeanHaar.ForMathlib.MatrixRepresentation

/-!
# Schur-Weyl duality: the d < k case

We prove `centralizer(diagImage d k) ⊆ Span(permImage d k)` for all `d, k`,
using the First Fundamental Theorem (FFT) and the Double Commutant Theorem (DCT).
-/

noncomputable section

open scoped TensorProduct

open ForMathlib.Tensor

namespace SchurWeyl

variable {d k : ℕ}


/-! ### FFT helper: the pairCount function -/

/-- The coincidence type of a pair `(I, J)`: for each pair `(a, b) ∈ Fin d × Fin d`,
counts the number of indices `m` with `(I m, J m) = (a, b)`. -/
def pairCount (I J : Fin k → Fin d) : (Fin d × Fin d) →₀ ℕ :=
  Finsupp.onFinset Finset.univ
    (fun p => (Finset.univ.filter (fun m => (I m, J m) = p)).card)
    (fun _ _ => Finset.mem_univ _)

/-
The product `∏_m g_{I(m),J(m)}` equals the monomial of the pair count.
-/
theorem prod_eq_monomial_eval (I J : Fin k → Fin d)
    (g : Fin d → Fin d → ℂ) :
    ∏ m : Fin k, g (I m) (J m) =
    ∏ p ∈ (pairCount I J).support, g p.1 p.2 ^ (pairCount I J) p := by
  unfold pairCount;
  simp +decide [ Finsupp.support_onFinset ];
  rw [ Finset.prod_image' ];
  exact fun i _ => by rw [ Finset.prod_congr rfl fun j hj => by aesop ] ; simp +decide ;

/-! ### FFT helper lemmas -/

/-
Orbit invariance of matrix entries: if X commutes with all W_σ,
then M_X[I ∘ σ, J ∘ σ] = M_X[I, J].
-/
theorem matrix_orbit_invariant (X : Module.End ℂ (TensV d k))
    (hX : X ∈ (permImage d k).centralizer)
    (I J : Fin k → Fin d) (σ : Equiv.Perm (Fin k)) :
    toEndMatrix d k X (I ∘ σ) (J ∘ σ) = toEndMatrix d k X I J := by
  have h_comm : X ∘ₗ (permAction d σ⁻¹).toLinearMap = (permAction d σ⁻¹).toLinearMap ∘ₗ X := by
    convert hX _ ( Set.mem_range_self σ⁻¹ ) using 1;
    · exact hX _ ( Set.mem_range_self _ ) ▸ rfl;
    · exact hX _ ( Set.mem_range_self _ );
  apply_fun fun f => f ( tensorBasis d k J ) at h_comm;
  convert congr_arg ( fun x => ( tensorBasis d k |> Module.Basis.repr ) x ( I ∘ σ ) ) h_comm using 1 <;> norm_num [ toEndMatrix, permAction_tensorBasis ];
  · unfold LinearMap.toMatrix; aesop;
  · rw [ show ( permAction d σ⁻¹ ) ( X ( tensorBasis d k J ) ) = ∑ m, ( tensorBasis d k |> Module.Basis.repr ) ( X ( tensorBasis d k J ) ) m • ( tensorBasis d k ) ( m ∘ σ ) from ?_ ];
    · simp +decide [ LinearMap.toMatrix_apply, Finsupp.single_apply ];
      rw [ Finset.sum_eq_single I ] <;> simp +contextual [ funext_iff ];
      exact fun b x hx₁ hx₂ => False.elim <| hx₁ <| by simpa using hx₂ ( σ.symm x ) ;
    · conv_lhs => rw [ ← ( tensorBasis d k ).sum_repr ( X ( tensorBasis d k J ) ) ];
      rw [ map_sum ];
      refine' Finset.sum_congr rfl fun m hm => _;
      rw [ map_smul, permAction_tensorBasis ] ; aesop

/-
Permuting indices preserves the pair count.
-/
theorem pairCount_perm (I J : Fin k → Fin d) (σ : Equiv.Perm (Fin k)) :
    pairCount (I ∘ σ) (J ∘ σ) = pairCount I J := by
  ext p;
  simp +decide [ pairCount ];
  rw [ Finset.card_filter, Finset.card_filter ];
  conv_rhs => rw [ ← Equiv.sum_comp σ ] ;

/-
Grouping the polynomial evaluation by coincidence type:
the sum `Σ_{I,J} C(I,J) ∏_m g(I(m),J(m))` equals
`Σ_c (Σ_{pairCount I J = c} C(I,J)) · mono(c, g)`.
-/
theorem sum_group_by_pairCount
    (C : (Fin k → Fin d) → (Fin k → Fin d) → ℂ)
    (g : Fin d → Fin d → ℂ) :
    ∑ I : Fin k → Fin d, ∑ J : Fin k → Fin d,
      C I J * ∏ m : Fin k, g (I m) (J m) =
    ∑ c ∈ (Finset.univ.image (fun p : (Fin k → Fin d) × (Fin k → Fin d) =>
      pairCount p.1 p.2)),
      (∑ I : Fin k → Fin d, ∑ J : Fin k → Fin d,
        if pairCount I J = c then C I J else 0) *
      ∏ p ∈ c.support, g p.1 p.2 ^ c p := by
  simp +decide [ Finset.sum_mul, prod_eq_monomial_eval ];
  rw [ Finset.sum_comm, Finset.sum_image' ];
  convert Finset.sum_comm using 1;
  rotate_left;
  use fun p => C p.1 p.2 * ∏ p_1 ∈ (pairCount p.1 p.2).support, g p_1.1 p_1.2 ^ (pairCount p.1 p.2) p_1;
  · simp +decide [ Finset.sum_filter ];
    intro a b; rw [ ← Finset.sum_product' ] ; congr; ext; aesop;
  · exact
      Fintype.sum_prod_type fun x =>
        C x.1 x.2 * ∏ p_1 ∈ (pairCount x.1 x.2).support, g p_1.1 p_1.2 ^ (pairCount x.1 x.2) p_1

/-
Separation lemma: if `x ∉ S` for a submodule `S` of a finite-dimensional
space over ℂ, there exists a linear functional vanishing on `S` but not on `x`.
-/
theorem exists_functional_separation
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ V) (x : V) (hx : x ∉ S) :
    ∃ φ : V →ₗ[ℂ] ℂ, φ x ≠ 0 ∧ ∀ s ∈ S, φ s = 0 := by
  exact Submodule.exists_le_ker_of_notMem hx

/-
If `M_X` is constant on coincidence types and the coincidence-type sums
of `C` all vanish, then `Σ C(I,J) M_X[I,J] = 0`.
-/
theorem sum_vanishes_of_coeff_and_const
    (M C : (Fin k → Fin d) → (Fin k → Fin d) → ℂ)
    (hM : ∀ I J I' J' : Fin k → Fin d,
      pairCount I J = pairCount I' J' → M I J = M I' J')
    (hC : ∀ c ∈ (Finset.univ.image (fun p : (Fin k → Fin d) × (Fin k → Fin d) =>
      pairCount p.1 p.2)),
      ∑ I : Fin k → Fin d, ∑ J : Fin k → Fin d,
        (if pairCount I J = c then C I J else 0) = 0) :
    ∑ I : Fin k → Fin d, ∑ J : Fin k → Fin d, C I J * M I J = 0 := by
  -- By partitioning the sum into coincidence types, we can rewrite the sum as a sum over each type's contribution.
  have h_partition : ∑ I : Fin k → Fin d, ∑ J : Fin k → Fin d, C I J * M I J = ∑ c ∈ Finset.image (fun p : (Fin k → Fin d) × (Fin k → Fin d) => pairCount p.1 p.2) (Finset.univ : Finset ((Fin k → Fin d) × (Fin k → Fin d))), ∑ I : Fin k → Fin d, ∑ J : Fin k → Fin d, if pairCount I J = c then C I J * M I J else 0 := by
    simp +decide only [← Finset.sum_product'];
    rw [ ← Finset.sum_filter ];
    refine' Finset.sum_bij ( fun p hp => ( pairCount p.1 p.2, p ) ) _ _ _ _ <;> simp +decide;
  convert h_partition using 1;
  refine' Eq.symm ( Finset.sum_eq_zero fun c hc => _ );
  convert congr_arg ( fun x : ℂ => x * M ( Classical.choose ( Finset.mem_image.mp hc ) |> Prod.fst ) ( Classical.choose ( Finset.mem_image.mp hc ) |> Prod.snd ) ) ( hC c hc ) using 1;
  · simp +decide only [Finset.sum_mul _ _ _];
    refine' Finset.sum_congr rfl fun I hI => Finset.sum_congr rfl fun J hJ => _;
    grind;
  · ring

/-! ### FFT: Main theorem -/

/-
**First Fundamental Theorem**: `centralizer(permImage) ⊆ Span(diagImage)`.

Proof: By finite-dimensional duality, it suffices to show that any linear
functional vanishing on `Span(diagImage)` also vanishes on `centralizer(permImage)`.

Let φ be such a functional. Then φ(g^{⊗k}) = 0 for all g ∈ End(ℂ^d).

In the tensor basis: φ(g^{⊗k}) = Σ_{I,J} φ_{I,J} ∏_m g_{I(m),J(m)} = 0 for all g.

This is a polynomial in d² variables. By `MvPolynomial.funext`, it's the zero
polynomial, so the coefficient for each coincidence type (monomial) is zero:
Σ_{(I,J) with pairCount I J = c} φ_{I,J} = 0 for each c.

For X ∈ centralizer(permImage), M_X is constant on S_k-orbits (coincidence types):
φ(X) = Σ_{I,J} φ_{I,J} M_X[I,J] = Σ_c M_X[c] · (Σ_{pairCount I J = c} φ_{I,J}) = 0.

Hence X ∈ Span(diagImage).
-/
theorem centralizer_permImage_le_span_diagImage :
    (permImage d k).centralizer ⊆
    (↑(Submodule.span ℂ (diagImage d k)) : Set (Module.End ℂ (TensV d k))) := by
  intro X hX
  by_contra h_not_in_span
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.End ℂ (TensV d k) →ₗ[ℂ] ℂ, φ X ≠ 0 ∧ ∀ s ∈ Submodule.span ℂ (diagImage d k), φ s = 0 := by
    convert exists_functional_separation _ X h_not_in_span using 1;
  -- Define the coefficients $C(I,J)$ such that $\varphi(T) = \sum_{I,J} C(I,J) \cdot M_T[I,J]$ for any endomorphism $T$.
  obtain ⟨C, hC⟩ : ∃ C : (Fin k → Fin d) → (Fin k → Fin d) → ℂ, ∀ T : Module.End ℂ (TensV d k), φ T = ∑ I : Fin k → Fin d, ∑ J : Fin k → Fin d, C I J * (toEndMatrix d k T) I J := by
    use fun I J => φ ((toEndMatrix d k).symm (Matrix.single I J 1));
    intro T
    have h_decomp : T = ∑ I : Fin k → Fin d, ∑ J : Fin k → Fin d, (toEndMatrix d k T) I J • (toEndMatrix d k).symm (Matrix.single I J 1) := by
      apply (toEndMatrix d k).injective;
      ext I J; simp +decide [ Matrix.single ] ;
      simp +decide [ Matrix.sum_apply, Matrix.of_apply ];
      rw [ Finset.sum_eq_single I ] <;> aesop;
    conv_lhs => rw [ h_decomp ];
    simp +decide [ mul_comm, map_sum, map_smul ];
  -- By the First Fundamental Theorem, since $\varphi$ vanishes on $\text{diagImage}$, the coefficients $C(I,J)$ must satisfy $\sum_{(I,J) \text{ with pairCount } I J = c} C(I,J) = 0$ for each coincidence type $c$.
  have h_coeff_zero : ∀ c ∈ Finset.univ.image (fun p : (Fin k → Fin d) × (Fin k → Fin d) => pairCount p.1 p.2), ∑ I : Fin k → Fin d, ∑ J : Fin k → Fin d, (if pairCount I J = c then C I J else 0) = 0 := by
    -- By the First Fundamental Theorem, since $\varphi$ vanishes on $\text{diagImage}$, the coefficients $C(I,J)$ must satisfy $\sum_{(I,J) \text{ with pairCount } I J = c} C(I,J) = 0$ for each coincidence type $c$. This follows from the fact that $\varphi(g^{⊗k}) = 0$ for all $g \in \text{End}(ℂ^d)$.
    have h_coeff_zero : ∀ g : Module.End ℂ (Fin d → ℂ), ∑ I : Fin k → Fin d, ∑ J : Fin k → Fin d, C I J * (∏ m : Fin k, (LinearMap.toMatrix (Pi.basisFun ℂ (Fin d)) (Pi.basisFun ℂ (Fin d)) g) (I m) (J m)) = 0 := by
      intro g
      have h_diag_zero : φ (diagAction d k g) = 0 := by
        exact hφ.2 _ <| Submodule.subset_span <| Set.mem_range_self _;
      rw [ ← h_diag_zero, hC ];
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ toEndMatrix_diagAction ] ;
    intro c hc
    have h_poly_zero : ∀ g : Fin d → Fin d → ℂ, ∑ I : Fin k → Fin d, ∑ J : Fin k → Fin d, C I J * (∏ m : Fin k, g (I m) (J m)) = 0 := by
      intro g
      specialize h_coeff_zero (Matrix.toLin (Pi.basisFun ℂ (Fin d)) (Pi.basisFun ℂ (Fin d)) (Matrix.of g));
      convert h_coeff_zero using 4 ; simp +decide [ Matrix.toLin_apply ];
      simp +decide [ Matrix.mulVec, dotProduct, Pi.single_apply ];
    have h_poly_zero : ∀ g : Fin d → Fin d → ℂ, ∑ c ∈ Finset.univ.image (fun p : (Fin k → Fin d) × (Fin k → Fin d) => pairCount p.1 p.2), (∑ I : Fin k → Fin d, ∑ J : Fin k → Fin d, if pairCount I J = c then C I J else 0) * (∏ p ∈ c.support, g p.1 p.2 ^ c p) = 0 := by
      intro g
      have := h_poly_zero g
      rw [sum_group_by_pairCount] at this
      exact this;
    convert monomial_coeff_zero_of_eval_zero ( fun c => ∑ I : Fin k → Fin d, ∑ J : Fin k → Fin d, if pairCount I J = c then C I J else 0 ) ( Finset.image ( fun p : ( Fin k → Fin d ) × ( Fin k → Fin d ) => pairCount p.1 p.2 ) Finset.univ ) ( fun g => ?_ ) c hc using 1;
    convert h_poly_zero ( fun i j => g ( i, j ) ) using 1;
  -- Since $X$ is in the centralizer of $\text{permImage}$, the matrix $M_X$ is constant on coincidence types.
  have h_const : ∀ I J I' J' : Fin k → Fin d, pairCount I J = pairCount I' J' → (toEndMatrix d k X) I J = (toEndMatrix d k X) I' J' := by
    intros I J I' J' h_pairCount
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin k), I' = I ∘ σ ∧ J' = J ∘ σ := by
      have h_exists_perm : ∃ σ : Fin k ≃ Fin k, ∀ m : Fin k, (I' m, J' m) = (I (σ m), J (σ m)) := by
        have h_multiset : Multiset.ofList (List.ofFn (fun m => (I' m, J' m))) = Multiset.ofList (List.ofFn (fun m => (I m, J m))) := by
          ext p;
          simp +decide [ List.ofFn_eq_map, Multiset.count ];
          convert congr_arg ( fun f => f p ) h_pairCount.symm using 1;
          · simp +decide [ List.countP_eq_length_filter, pairCount ];
            congr with m ; simp +decide [ eq_comm ];
          · simp +decide [ List.countP_eq_length_filter, pairCount ];
            congr with m ; simp +decide [ eq_comm ]
        have h_exists_perm : ∀ (l1 l2 : List (Fin d × Fin d)), List.Perm l1 l2 → ∃ σ : Fin l1.length ≃ Fin l2.length, ∀ m : Fin l1.length, l1.get m = l2.get (σ m) := by
          intros l1 l2 h_perm
          induction' h_perm with l1 l2 h_perm ih;
          · exact ⟨ Equiv.refl _, by simp +decide ⟩;
          · obtain ⟨ σ, hσ ⟩ := ‹_›;
            refine' ⟨ Equiv.ofBijective ( fun m => Fin.cases ⟨ 0, by simp +decide ⟩ ( fun m => Fin.succ ( σ m ) ) m ) ⟨ _, _ ⟩, _ ⟩ <;> simp +decide [ Fin.forall_fin_succ ];
            · intro m n hmn; induction m using Fin.inductionOn <;> induction n using Fin.inductionOn <;> simp +decide at hmn ⊢;
              · exact absurd hmn ( ne_of_lt ( Fin.succ_pos _ ) );
              · exact hmn;
            · intro m; induction' m using Fin.inductionOn with m ih; simp +decide [ Fin.exists_fin_succ ] ;
              exact ⟨ Fin.succ ( σ.symm m ), by simp +decide ⟩;
            · exact hσ;
          · refine' ⟨ Equiv.swap ⟨ 0, by simp +decide ⟩ ⟨ 1, by simp +decide ⟩, _ ⟩ ; simp +decide [ Fin.forall_fin_succ ];
            exact fun i => by cases i ; rfl;
          · rename_i h₁ h₂ h₃ h₄;
            obtain ⟨ σ₁, hσ₁ ⟩ := h₃
            obtain ⟨ σ₂, hσ₂ ⟩ := h₄
            use σ₁.trans σ₂
            intro m
            grind;
        obtain ⟨ σ, hσ ⟩ := h_exists_perm ( List.ofFn fun m => ( I' m, J' m ) ) ( List.ofFn fun m => ( I m, J m ) ) ( by simpa using h_multiset );
        simp +zetaDelta at *;
        use Equiv.ofBijective (fun m : Fin k => ⟨σ ⟨m, by simp⟩, by
          exact lt_of_lt_of_le ( Fin.is_lt _ ) ( by simp )⟩) (by
        exact ⟨ fun m n h => by simpa [ Fin.ext_iff ] using σ.injective ( Fin.ext <| by simpa [ Fin.ext_iff ] using h ), Finite.injective_iff_surjective.mp <| fun m n h => by simpa [ Fin.ext_iff ] using σ.injective ( Fin.ext <| by simpa [ Fin.ext_iff ] using h ) ⟩);
        exact fun m => hσ ⟨ m, by simp ⟩;
      exact ⟨ h_exists_perm.choose, funext fun m => congr_arg Prod.fst ( h_exists_perm.choose_spec m ), funext fun m => congr_arg Prod.snd ( h_exists_perm.choose_spec m ) ⟩;
    rw [ hσ.1, hσ.2, ← matrix_orbit_invariant X hX I J σ ];
  exact hφ.1 ( by rw [ hC ] ; exact sum_vanishes_of_coeff_and_const _ _ h_const h_coeff_zero )

/-! ### DCT -/

/-- **Double Commutant Theorem** for the permutation algebra. -/
theorem double_centralizer_permImage :
    ((↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))).centralizer).centralizer ⊆
    (↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))) :=
  double_centralizer_permImage' d k

/-! ### Assembly -/

/-- `centralizer(diagImage) ⊆ Span(permImage)` for all `d` and `k`. -/
theorem centralizer_diagImage_le_span_permImage_small :
    (diagImage d k).centralizer ⊆
    (↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))) := by
  intro X hX
  have hX_in_A'' : X ∈ ((↑(Submodule.span ℂ (permImage d k)) : Set _).centralizer).centralizer := by
    intro Y hY
    have hY' : Y ∈ (permImage d k).centralizer := by
      intro z hz; exact hY z (Submodule.subset_span hz)
    have hY_diag := centralizer_permImage_le_span_diagImage hY'
    revert hY_diag
    apply Submodule.span_induction
    · intro y hy; obtain ⟨g, rfl⟩ := hy; exact hX _ ⟨g, rfl⟩
    · simp
    · intro a b _ _ ha hb; simp [mul_add, add_mul, ha, hb]
    · intro c a _ ha; simp [ha]
  exact double_centralizer_permImage hX_in_A''

end SchurWeyl

end
