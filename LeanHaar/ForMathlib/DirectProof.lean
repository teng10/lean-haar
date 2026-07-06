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
import Mathlib.Tactic.LinearCombination
import Mathlib.CategoryTheory.Category.Basic
import Aesop

import LeanHaar.ForMathlib.TensorV2
import LeanHaar.ForMathlib.Commutation
import LeanHaar.ForMathlib.MatrixRepresentation

/-!
# Direct proof of the hard direction of Schur-Weyl duality

We prove: if `X ∈ End(V^{⊗k})` commutes with all `g^{⊗k}`, then `X ∈ Span{W_σ}`.
-/

noncomputable section

open scoped TensorProduct

namespace ForMathlib.Tensor
variable {d k : ℕ}


/-- `∑ σ, c σ • W_σ ∈ Span(permImage)`. -/
theorem sum_smul_perm_mem_span (c : Equiv.Perm (Fin k) → ℂ) :
    ∑ σ : Equiv.Perm (Fin k), c σ • (permAction d σ).toLinearMap ∈
    Submodule.span ℂ (permImage d k) :=
  Submodule.sum_mem _ fun σ _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)

/-! ### Matrix commutation condition -/

/-
The commutation `X * g^{⊗k} = g^{⊗k} * X` at the matrix level.
-/
theorem matrix_comm_of_centralizer (X : Module.End ℂ (TensV d k))
    (hX : X ∈ (diagImage d k).centralizer) (g : Module.End ℂ (Fin d → ℂ)) :
    toEndMatrix d k X * toEndMatrix d k (diagAction d k g) =
    toEndMatrix d k (diagAction d k g) * toEndMatrix d k X := by
  convert congr_arg ( fun x => toEndMatrix d k x ) ( hX _ ⟨ g, rfl ⟩ ) using 1;
  · -- By definition of `toEndMatrix`, we know that `toEndMatrix d k (X * Y) = toEndMatrix d k X * toEndMatrix d k Y`.
    simp [toEndMatrix];
    convert LinearMap.toMatrix_mul _ _ _ using 1;
    convert rfl;
    convert LinearMap.toMatrix_mul _ _ _ using 1;
    rw [ ← LinearMap.toMatrix_comp ];
    exact congr_arg _ ( hX _ ⟨ g, rfl ⟩ );
  · simp +decide [ toEndMatrix, LinearMap.toMatrix_mul ];
    rw [ ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp ];
    convert congr_arg _ ( hX ( diagAction d k g ) ( Set.mem_range_self g ) ) using 1



/-
If `X` commutes with all diagonal actions, then `X_{I,J} = 0` unless
`I` and `J` are rearrangements (define the same `Finsupp`/multiset).
-/
theorem matrix_zero_unless_rearrangement (X : Module.End ℂ (TensV d k))
    (hX : X ∈ (diagImage d k).centralizer)
    (I J : Fin k → Fin d)
    (hIJ : ¬ (∀ a : Fin d, (Finset.univ.filter (fun m => I m = a)).card =
                            (Finset.univ.filter (fun m => J m = a)).card)) :
    toEndMatrix d k X I J = 0 := by
  contrapose! hIJ with h_contra;
  intro a
  by_contra h_neq_card
  have h_diff : ∃ f : Fin d → ℂ, (∏ m, f (I m)) ≠ (∏ m, f (J m)) := by
    use fun i => if i = a then 2 else 1;
    simp_all +decide [ Finset.prod_ite ];
    exact fun h => h_neq_card <| Nat.pow_right_injective ( by decide ) <| mod_cast h;
  obtain ⟨ f, hf ⟩ := h_diff
  have h_eq : (toEndMatrix d k X) I J * (∏ m, f (J m)) = (∏ m, f (I m)) * (toEndMatrix d k X) I J := by
    have h_eq : (toEndMatrix d k X) * (toEndMatrix d k (diagAction d k (LinearMap.pi (fun i => f i • LinearMap.proj i)))) = (toEndMatrix d k (diagAction d k (LinearMap.pi (fun i => f i • LinearMap.proj i)))) * (toEndMatrix d k X) := by
      convert matrix_comm_of_centralizer X hX ( LinearMap.pi fun i => f i • LinearMap.proj i ) using 1;
    convert congr_fun ( congr_fun h_eq I ) J using 1 <;> simp +decide [ Matrix.mul_apply, diagAction_diagonal ];
  exact hf ( mul_left_cancel₀ h_contra <| by linear_combination h_eq.symm )

/-! ### Full constraint: coefficient constancy -/

set_option maxHeartbeats 400000 in
/-
For X commuting with all g^{⊗k}: if `J = I ∘ σ` and `J' = I' ∘ σ`, and both
`I` and `I'` are injective, then `X_{I,J} = X_{I',J'}`.
-/
theorem matrix_coeff_constancy (X : Module.End ℂ (TensV d k))
    (hX : X ∈ (diagImage d k).centralizer)
    (I I' : Fin k → Fin d) (σ : Equiv.Perm (Fin k))
    (hI : Function.Injective I) (hI' : Function.Injective I') :
    toEndMatrix d k X I (I ∘ σ) = toEndMatrix d k X I' (I' ∘ σ) := by
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin d), I' = τ ∘ I := by
    obtain ⟨τ, hτ⟩ : ∃ τ : Fin k ↪ Fin d, I' = τ ∧ ∃ τ' : Fin k ↪ Fin d, I = τ' := by
      exact ⟨ ⟨ I', hI' ⟩, rfl, ⟨ I, hI ⟩, rfl ⟩;
    rcases hτ with ⟨ rfl, τ', rfl ⟩;
    -- Since τ and τ' are both embeddings, we can extend them to permutations of Fin d.
    obtain ⟨τ_ext, hτ_ext⟩ : ∃ τ_ext : Equiv.Perm (Fin d), ∀ i : Fin k, τ_ext (τ' i) = τ i := by
      have h_ext : ∃ τ_ext : Fin d → Fin d, Function.Injective τ_ext ∧ ∀ i : Fin k, τ_ext (τ' i) = τ i := by
        have h_card : Finset.card (Finset.univ \ Finset.image τ' Finset.univ) = Finset.card (Finset.univ \ Finset.image τ Finset.univ) := by
          simp +decide [ Finset.card_sdiff, Finset.card_image_of_injective _ hI, Finset.card_image_of_injective _ hI' ]
        obtain ⟨f, hf⟩ : ∃ f : {x : Fin d | x ∉ Finset.image τ' Finset.univ} ≃ {x : Fin d | x ∉ Finset.image τ Finset.univ}, True := by
          have h_ext : Nonempty ({x : Fin d | x ∉ Finset.image τ' Finset.univ} ≃ {x : Fin d | x ∉ Finset.image τ Finset.univ}) := by
            refine' ⟨ Fintype.equivOfCardEq _ ⟩;
            convert h_card using 1; all_goals rw [ Fintype.card_of_subtype ] ; aesop;
          exact ⟨ h_ext.some, trivial ⟩;
        refine' ⟨ fun x => if hx : x ∈ Finset.image τ' Finset.univ then τ ( Classical.choose ( Finset.mem_image.mp hx ) ) else f ⟨ x, by simpa using hx ⟩, _, _ ⟩;
        · intro x y; by_cases hx : x ∈ Finset.image τ' Finset.univ <;> by_cases hy : y ∈ Finset.image τ' Finset.univ <;> simp +decide [ hx, hy ] ;
          · grind;
          · grind;
          · grind;
          · exact fun h => by simpa [ Subtype.ext_iff ] using f.injective ( Subtype.ext h ) ;
        · simp +decide [ hI.eq_iff ];
      exact ⟨ Equiv.ofBijective h_ext.choose ( ⟨ h_ext.choose_spec.1, Finite.injective_iff_surjective.mp h_ext.choose_spec.1 ⟩ ), h_ext.choose_spec.2 ⟩;
    exact ⟨ τ_ext, funext fun i => hτ_ext i ▸ rfl ⟩;
  -- Let g : End(V) be the permutation matrix of τ (i.e., g(e_a) = e_{τ(a)}).
  set g : Module.End ℂ (Fin d → ℂ) := LinearMap.pi (fun i => LinearMap.proj (τ.symm i));
  have h_comm : toEndMatrix d k X * toEndMatrix d k (diagAction d k g) = toEndMatrix d k (diagAction d k g) * toEndMatrix d k X := by
    convert matrix_comm_of_centralizer X hX g using 1;
  -- By definition of $g$, we know that $(toEndMatrix d k (diagAction d k g))_{K,L} = \delta(K, \tau \circ L)$.
  have h_g_matrix : ∀ K L : Fin k → Fin d, toEndMatrix d k (diagAction d k g) K L = if K = τ ∘ L then 1 else 0 := by
    intro K L; rw [ toEndMatrix_diagAction ] ; simp +decide [ g ] ;
    split_ifs <;> simp_all +decide [ funext_iff, Pi.single_apply ];
    rw [ Finset.prod_eq_zero ( Finset.mem_univ ( Classical.choose ‹∃ x, ¬K x = τ ( L x ) › ) ) ] ; simp +decide [ Classical.choose_spec ‹∃ x, ¬K x = τ ( L x ) ›, Equiv.symm_apply_eq ];
  replace h_comm := congr_fun ( congr_fun h_comm ( τ ∘ I ) ) ( I ∘ σ ) ; simp_all +decide [ Matrix.mul_apply ] ;
  rw [ Finset.sum_eq_single ( I ) ] at h_comm <;> simp_all +decide [ funext_iff ];
  · exact h_comm.symm;
  · exact fun b x hx₁ hx₂ => False.elim <| hx₁ <| hx₂ x ▸ rfl

/-! ### Helper: rearrangements come from permutations -/

/-
If `I` and `J` define the same multiset, then there exists a permutation `σ`
such that `J = I ∘ σ`.
-/
theorem exists_perm_of_rearrangement (I J : Fin k → Fin d)
    (h : ∀ a : Fin d, (Finset.univ.filter (fun m => I m = a)).card =
                       (Finset.univ.filter (fun m => J m = a)).card) :
    ∃ σ : Equiv.Perm (Fin k), J = I ∘ σ := by
  revert h;
  induction' k with k ih;
  · simp +decide [ funext_iff ];
  · intro h
    obtain ⟨σ, hσ⟩ : ∃ σ : Fin (k + 1) ≃ Fin (k + 1), J 0 = I (σ 0) := by
      obtain ⟨m, hm⟩ : ∃ m : Fin (k + 1), I m = J 0 := by
        contrapose! h;
        use J 0;
        simp_all +decide;
        exact ne_of_lt ( Finset.card_pos.mpr ⟨ 0, by simp +decide ⟩ );
      exact ⟨ Equiv.swap 0 m, by simpa using hm.symm ⟩;
    obtain ⟨τ, hτ⟩ : ∃ τ : Fin k ≃ Fin k, ∀ m : Fin k, J (Fin.succ m) = I (σ (Fin.succ (τ m))) := by
      have h_card : ∀ a : Fin d, (Finset.univ.filter (fun m : Fin k => I (σ (Fin.succ m)) = a)).card = (Finset.univ.filter (fun m : Fin k => J (Fin.succ m) = a)).card := by
        intro a
        have h_card_eq : (Finset.univ.filter (fun m => I (σ m) = a)).card = (Finset.univ.filter (fun m => J m = a)).card := by
          rw [ ← h a, Finset.card_filter, Finset.card_filter ];
          conv_rhs => rw [ ← Equiv.sum_comp σ ] ;
        rw [ Finset.card_filter, Finset.card_filter ] at *;
        rw [ Fin.sum_univ_succ, Fin.sum_univ_succ ] at h_card_eq ; aesop;
      obtain ⟨ τ, hτ ⟩ := ih ( fun m => I ( σ ( Fin.succ m ) ) ) ( fun m => J ( Fin.succ m ) ) h_card;
      exact ⟨ τ, fun m => congr_fun hτ m ⟩;
    use σ * Equiv.ofBijective (Fin.cons 0 (fun m => Fin.succ (τ m))) (by
    constructor;
    · intro m n hmn;
      induction m using Fin.cases <;> induction n using Fin.cases <;> simp_all +decide [ Fin.cons ];
      exact absurd hmn ( ne_of_lt ( Fin.succ_pos _ ) );
    · intro x; induction x using Fin.inductionOn <;> simp +decide [ *, Fin.cons ] ;
      · exact ⟨ 0, rfl ⟩;
      · exact ⟨ Fin.succ ( τ.symm ‹_› ), by simp +decide ⟩)
    generalize_proofs at *;
    ext m; induction m using Fin.inductionOn <;> aesop;

/-! ### Spanning lemma -/

/-
The set `{g^{⊗k}(e_{I₀}) | g ∈ End(V)}` spans `V^{⊗k}` when `I₀` is injective.
-/
theorem diagAction_spans_of_injective (I₀ : Fin k → Fin d) (hI₀ : Function.Injective I₀) :
    Submodule.span ℂ (Set.range (fun g : Module.End ℂ (Fin d → ℂ) =>
      diagAction d k g (tensorBasis d k I₀))) = ⊤ := by
  refine' Submodule.eq_top_iff'.mpr fun x => _;
  induction' x using PiTensorProduct.induction_on with x y hx hy;
  · -- For any tuple y : Fin k → (Fin d → ℂ), we can find g ∈ End(V) such that g(e_{I₀(i)}) = y(i) for all i.
    have h_exists_g : ∀ y : Fin k → (Fin d → ℂ), ∃ g : Module.End ℂ (Fin d → ℂ), ∀ i, g (Pi.basisFun ℂ (Fin d) (I₀ i)) = y i := by
      intro y;
      use (Pi.basisFun ℂ (Fin d)).constr ℂ (fun i => if h : ∃ j, I₀ j = i then y (Classical.choose h) else 0);
      intro i; simp +decide ;
      rw [ Finset.sum_eq_single ( I₀ i ) ] <;> simp +decide [ hI₀.eq_iff ];
      exact fun b hb x hx => Or.inl <| Pi.single_eq_of_ne ( by aesop ) _;
    obtain ⟨ g, hg ⟩ := h_exists_g y;
    refine' Submodule.smul_mem _ _ ( Submodule.subset_span ⟨ g, _ ⟩ );
    unfold diagAction tensorBasis; aesop;
  · exact Submodule.add_mem _ ‹_› ‹_›

/-
If `Z` commutes with all `g^{⊗k}` and `Z(v) = 0` for some `v` whose orbit
under diagonal actions spans `V^{⊗k}`, then `Z = 0`.
-/
theorem eq_zero_of_comm_and_vanish_on_orbit
    (Z : Module.End ℂ (TensV d k))
    (hcomm : ∀ g : Module.End ℂ (Fin d → ℂ), Z ∘ₗ diagAction d k g = diagAction d k g ∘ₗ Z)
    (v : TensV d k) (hv : Z v = 0)
    (hspan : Submodule.span ℂ (Set.range (fun g : Module.End ℂ (Fin d → ℂ) =>
      diagAction d k g v)) = ⊤) :
    Z = 0 := by
  -- Since $Z$ commutes with all $diagAction g$, we have $Z(diagAction g v) = diagAction g (Z v)$.
  have h_comm : ∀ g : Module.End ℂ (Fin d → ℂ), Z (diagAction d k g v) = diagAction d k g (Z v) := by
    exact fun g => LinearMap.congr_fun ( hcomm g ) v;
  refine' LinearMap.ext fun x => _;
  rw [ Submodule.eq_top_iff' ] at hspan;
  specialize hspan x;
  rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at hspan;
  obtain ⟨ c, rfl ⟩ := hspan; simp +decide [ hv, h_comm, Finsupp.sum ] ;

/-! ### Key identity for assembly -/

/-
For injective `I₀` and `X` in the centralizer, `X(e_{I₀})` equals `(∑ c(σ) W_σ)(e_{I₀})`
where `c(σ) = toEndMatrix X I₀ (I₀ ∘ σ)`.
-/
theorem apply_eq_sum_of_centralizer (X : Module.End ℂ (TensV d k))
    (hX : X ∈ (diagImage d k).centralizer)
    (I₀ : Fin k → Fin d) (hI₀ : Function.Injective I₀) :
    X (tensorBasis d k I₀) =
    (∑ σ : Equiv.Perm (Fin k),
      toEndMatrix d k X I₀ (I₀ ∘ σ) • (permAction d σ).toLinearMap) (tensorBasis d k I₀) := by
  -- By definition of matrix multiplication and the basis representation, we can expand both sides.
  have h_expand : X (tensorBasis d k I₀) = ∑ I, (toEndMatrix d k X) I I₀ • (tensorBasis d k I) := by
    unfold toEndMatrix;
    simp +decide [ LinearMap.toMatrix_apply ];
  -- By definition of matrix multiplication and the basis representation, we can expand the right-hand side.
  have h_expand_rhs : (∑ σ : Equiv.Perm (Fin k), (toEndMatrix d k X) I₀ (I₀ ∘ σ) • (permAction d σ).toLinearMap) (tensorBasis d k I₀) = ∑ σ : Equiv.Perm (Fin k), (toEndMatrix d k X) I₀ (I₀ ∘ σ) • (tensorBasis d k (I₀ ∘ σ.symm)) := by
    simp +decide [ permAction_tensorBasis ];
  -- By definition of matrix multiplication and the basis representation, we can expand the left-hand side.
  have h_expand_lhs : ∑ I, (toEndMatrix d k X) I I₀ • (tensorBasis d k I) = ∑ σ : Equiv.Perm (Fin k), (toEndMatrix d k X) (I₀ ∘ σ) I₀ • (tensorBasis d k (I₀ ∘ σ)) := by
    have h_expand_lhs : ∀ I : Fin k → Fin d, (toEndMatrix d k X) I I₀ ≠ 0 → ∃ σ : Equiv.Perm (Fin k), I = I₀ ∘ σ := by
      intro I hI
      have h_rearrange : ∀ a : Fin d, (Finset.univ.filter (fun m => I m = a)).card = (Finset.univ.filter (fun m => I₀ m = a)).card := by
        contrapose! hI;
        apply matrix_zero_unless_rearrangement X hX I I₀;
        exact fun h => hI.choose_spec <| h _;
      have := exists_perm_of_rearrangement I I₀ h_rearrange;
      obtain ⟨ σ, hσ ⟩ := this; use σ.symm; ext m; simp +decide [ hσ ] ;
    rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun σ : Equiv.Perm ( Fin k ) => I₀ ∘ ⇑σ ) Finset.univ ) ) ];
    · rw [ Finset.sum_image ];
      exact fun σ _ τ _ h => Equiv.Perm.ext fun x => hI₀ <| by simpa using congr_fun h x;
    · exact fun I _ hI => by rw [ show ( toEndMatrix d k ) X I I₀ = 0 from Classical.not_not.1 fun h => hI <| Finset.mem_image.2 <| by obtain ⟨ σ, rfl ⟩ := h_expand_lhs I h; exact ⟨ σ, Finset.mem_univ _, rfl ⟩ ] ; simp +decide ;
  rw [ h_expand, h_expand_lhs, h_expand_rhs ];
  -- By definition of matrix multiplication and the basis representation, we can rewrite the right-hand side.
  have h_rewrite_rhs : ∀ σ : Equiv.Perm (Fin k), (toEndMatrix d k X) (I₀ ∘ σ) I₀ = (toEndMatrix d k X) I₀ (I₀ ∘ σ.symm) := by
    intro σ;
    convert matrix_coeff_constancy X hX ( I₀ ∘ σ ) I₀ σ.symm ( hI₀.comp σ.injective ) hI₀ using 1;
    simp +decide [ Function.comp_def ];
  rw [ ← Equiv.sum_comp ( Equiv.inv _ ) ] ; aesop

/-! ### Assembly for d ≥ k -/

/-
When `d ≥ k`, we can find injective tuples and the hard direction follows.
-/
theorem centralizer_diagImage_le_span_permImage_of_le (hdk : k ≤ d) :
    (diagImage d k).centralizer ⊆
    (↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))) := by
  intro X hX;
  -- For X ∈ centralizer(diagImage):
  -- Define Y = ∑ σ, toEndMatrix X I₀ (I₀∘σ) • W_σ.
  set I₀ : Fin k → Fin d := fun i => ⟨i.val, by linarith [Fin.is_lt i]⟩
  set Y : Module.End ℂ (TensV d k) := ∑ σ : Equiv.Perm (Fin k), toEndMatrix d k X I₀ (I₀ ∘ σ) • (permAction d σ).toLinearMap;
  -- Set Z = X - Y.
  set Z : Module.End ℂ (TensV d k) := X - Y;
  have hZ_comm : ∀ g : Module.End ℂ (Fin d → ℂ), Z ∘ₗ diagAction d k g = diagAction d k g ∘ₗ Z := by
    intro g;
    simp +zetaDelta at *;
    simp_all +decide [ LinearMap.ext_iff, Set.centralizer ];
    intro x; congr! 1;
    · exact hX _ ( Set.mem_range_self _ ) _ ▸ rfl;
    · exact Finset.sum_congr rfl fun _ _ => congr_arg _ ( permAction_diagAction_comm _ _ |> congr_arg ( fun f => f x ) );
  have hZ_zero : Z (tensorBasis d k I₀) = 0 := by
    convert sub_eq_zero.mpr ( apply_eq_sum_of_centralizer X hX I₀ ( by aesop_cat ) ) using 1;
  have hZ_span : Submodule.span ℂ (Set.range (fun g : Module.End ℂ (Fin d → ℂ) => diagAction d k g (tensorBasis d k I₀))) = ⊤ := by
    apply diagAction_spans_of_injective;
    exact fun i j hij => Fin.ext <| by simpa using congr_arg Fin.val hij;;
  have hZ_zero_map : Z = 0 := by
    apply eq_zero_of_comm_and_vanish_on_orbit Z hZ_comm (tensorBasis d k I₀) hZ_zero hZ_span;
  have hX_eq_Y : X = Y := by
    exact eq_of_sub_eq_zero hZ_zero_map;
  have hY_in_span : Y ∈ Submodule.span ℂ (permImage d k) := by
    exact sum_smul_perm_mem_span _;
  exact hX_eq_Y ▸ hY_in_span;

-- end SchurWeyl

end ForMathlib.Tensor

end
