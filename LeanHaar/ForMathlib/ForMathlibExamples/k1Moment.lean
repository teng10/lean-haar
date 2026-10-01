import LeanHaar.ForMathlib.Haar
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.TensorPowerBasics

/-!
# Example: Computing moments for k = 1

We seek to use Antonio's notes to write an expression for the first order moment of the Haar measure.
-/

open SchurWeyl

variable (d : ℕ)

/-- `Equiv.Perm (Fin 1)` is a subsingleton, so a sum over it is just its value at `1`. -/
private lemma sum_perm_k1 {M : Type*} [AddCommMonoid M] (f : Equiv.Perm (Fin 1) → M) :
    ∑ π, f π = f 1 :=
  Fintype.sum_subsingleton f 1

/-- The moment of a single operator O for tensor power k = 1 is Tr(O) / d • Id.-/
theorem k1_moment [NeZero d] (O : Module.End ℂ (TensV d 1)) :
    momentOp O = (LinearMap.trace ℂ (TensV d 1) O / (d : ℂ)) • LinearMap.id := by
  obtain ⟨c, hmoment, hperm⟩ := weingarten_moment_haar O
  specialize hperm 1
  -- Both sums collapse to their `π = 1` term, where `permOp d 1 = permDual d 1 = id`:
  -- `hmoment : momentOp O = c 1 • id` and `hperm : Tr O = c 1 * Tr id = c 1 * d`.
  simp only [sum_perm_k1, permDual_one, permOp_one, LinearMap.id_comp, trace_id_tensV, pow_one]
    at hmoment hperm
  -- `NeZero d` gives `(d : ℂ) ≠ 0`, so `c 1 * d / d = c 1`.
  rw [hmoment, hperm, mul_div_cancel_right₀ (c 1) (NeZero.natCast_ne d ℂ)]
