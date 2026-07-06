import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Polynomial independence of monomials

We prove that distinct monomials over ℂ are linearly independent as functions.
This is the key ingredient for the First Fundamental Theorem of invariant theory.
-/

noncomputable section

/-! ### Key lemma: monomial independence -/

/-
If a linear combination of distinct monomials in `d²` variables over ℂ evaluates
to zero at all points, then all coefficients are zero.

This follows from `MvPolynomial.funext` (polynomial vanishing over infinite domains)
and the fact that monomials form a basis of `MvPolynomial`.
-/
theorem monomial_coeff_zero_of_eval_zero {ι : Type*} [DecidableEq ι]
    (c : Finsupp ι ℕ → ℂ) (s : Finset (Finsupp ι ℕ))
    (h : ∀ x : ι → ℂ, ∑ m ∈ s, c m * ∏ i ∈ m.support, x i ^ m i = 0) :
    ∀ m ∈ s, c m = 0 := by
  have h_poly_zero : ∑ m ∈ s, MvPolynomial.monomial m (c m) = 0 := by
    refine' MvPolynomial.funext fun x => _;
    simp +decide [ MvPolynomial.eval_monomial ];
    convert h x using 1;
  intro m hm; replace h_poly_zero := congr_arg ( fun p => MvPolynomial.coeff m p ) h_poly_zero; simp_all +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial ] ;

end
