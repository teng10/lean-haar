import LeanHaar.ForMathlib.Haar
import LeanHaar.ForMathlib.Defs

/-!
# Example: Computing moments for k = 1

We seek to use Antonio's notes to write an expression for the first order moment of the Haar measure.
-/

open SchurWeyl

/-! The first three lemmas seem redundant, but I think it because I need to show 1 = LinearMap.id and that the set characterization holds.
There is probably a good way to simplify this into fewer lemmas. -/

/-- The permutation of a single element is the identity 1. -/
lemma perm_k1_eq_one (π : Equiv.Perm (Fin 1)) : π = 1 := by
  ext x -- do this element-by-element
  change (π x).val = x.val -- the permutation of an element is merely itself
  rw [Subsingleton.elim (π x) x]

/-- The set of permutations is a singleton. -/
lemma sum_perm_k1_eq_set_id : (Finset.univ : Finset (Equiv.Perm (Fin 1))) = {1} := by
  ext π
  simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
  exact perm_k1_eq_one π

/-- The permutation operator is the identity linear map. -/
lemma permOp_k1_eq_id (d : ℕ) : permOp d 1 = (LinearMap.id : TensV d 1 →ₗ[ℂ] TensV d 1) := by
  unfold permOp permAction
  change (PiTensorProduct.reindex ℂ (fun _ => Fin d → ℂ) (Equiv.refl (Fin 1))).toLinearMap = LinearMap.id
  rw [PiTensorProduct.reindex_refl]
  rfl

/-- Tr(Id) = d.-/
lemma trace_id_eq_d (d : ℕ) : LinearMap.trace ℂ (TensV d 1) LinearMap.id = d := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (tensorBasis d 1)]
  -- Show that LinearMap.id is the generic identity 1.
  have hid : LinearMap.toMatrix (tensorBasis d 1) (tensorBasis d 1) LinearMap.id = 1 := by
    exact LinearMap.toMatrix_id (tensorBasis d 1)
  -- Substitute intermediate hypothesis
  rw [hid]
  rw [Matrix.trace_one]
  simp only [Fintype.card_fun, Fintype.card_fin, pow_one]

/-- The permutation dual operator is the identity linear map. -/
lemma permDual_k1_eq_id (d : ℕ) : permDual d (1 : Equiv.Perm (Fin 1)) = LinearMap.id := by
      unfold permDual
      rw [inv_one]
      exact permOp_k1_eq_id d

/-- The moment of a single operator O for tensor power k = 1 is Tr(O) / d • Id.-/
theorem k1_moment (d : ℕ) [NeZero d] (O : Module.End ℂ (TensV d 1)) :
  momentOp O = (LinearMap.trace ℂ (TensV d 1) O / (d : ℂ)) • LinearMap.id := by
  obtain ⟨c, hmoment, hperm⟩ := weingarten_moment_haar O
  -- Rewrite momentOp O as a linear combination
  rw [hmoment]
  rw [sum_perm_k1_eq_set_id]
  -- Substitute the single element into the summation
  simp only [Finset.sum_singleton]
  rw [permOp_k1_eq_id]

  -- Here, we "specialize" some relation to a specific input parameter. "have" introduces a new hypothesis
  -- Intermediate hypothesis 1: Want to show TODO
  have h_trace_one : LinearMap.trace ℂ (TensV d 1) (permDual d 1 ∘ₗ O) =
    c 1 * LinearMap.trace ℂ (TensV d 1) (permDual d 1 ∘ₗ permOp d 1) := by
      specialize hperm 1 -- hperm was pulled from weingarten_moment_haar
      rw [sum_perm_k1_eq_set_id] at hperm
      simp only [Finset.sum_singleton] at hperm
      exact hperm

  -- Rearrange goal statement to match that of h_trace_one
  -- Intermediate hypothesis 2: (LHS) Want to show composition of (id with 0) is 0
  have h_lhs : permDual d (1 : Equiv.Perm (Fin 1)) ∘ₗ O = O := by
    rw [permDual_k1_eq_id, LinearMap.id_comp]

  -- Intermediate hyptoehss 3: (RHS) Want to show composition of (id with id) is id.
  have h_rhs : permDual d (1 : Equiv.Perm (Fin 1)) ∘ₗ permOp d (1 : Equiv.Perm (Fin 1)) = LinearMap.id := by
    rw [permDual_k1_eq_id, permOp_k1_eq_id, LinearMap.id_comp]

  -- Simplify using the intermediate hypotheses
  rw [h_lhs, h_rhs] at h_trace_one
  -- Substitute intermediate hypothesis into bigger goal
  rw [h_trace_one]
  -- Substitute Tr(Id) = d
  rw [trace_id_eq_d]
  simp -- Simplify d/d = 1
