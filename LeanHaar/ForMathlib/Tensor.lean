import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

noncomputable section

open scoped TensorProduct

namespace ForMathlib.Tensor

/-- The `k`-fold tensor power of `ℂ^d`, defined as `⨂[ℂ] (i : Fin k), (Fin d → ℂ)`. -/
abbrev TensV (d k : ℕ) : Type :=
  PiTensorProduct ℂ (fun (_ : Fin k) => (Fin d → ℂ))

/-- The standard basis of `V^{⊗k}`. -/
def tensorBasis (d k : ℕ) :
    Module.Basis ((i : Fin k) → Fin d) ℂ (TensV d k) :=
  Basis.piTensorProduct (fun (_ : Fin k) => Pi.basisFun ℂ (Fin d))

  /-- Matrix representation of endomorphisms. -/
def toEndMatrix (d k : ℕ) :
    Module.End ℂ (TensV d k) ≃ₗ[ℂ]
    Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ :=
  LinearMap.toMatrix (tensorBasis d k) (tensorBasis d k)

/-- The diagonal action `g^{⊗k}` on the tensor power `V^{⊗k}`.
Given `g : End(V)`, this acts as `g` on each tensor factor:
`g^{⊗k} (v₁ ⊗ ⋯ ⊗ vₖ) = g(v₁) ⊗ ⋯ ⊗ g(vₖ)`. -/
def diagAction (d k : ℕ) (g : Module.End ℂ (Fin d → ℂ)) :
    Module.End ℂ (TensV d k) :=
  PiTensorProduct.map (fun (_ : Fin k) => g)

variable {d k : ℕ}

  /-- Matrix of `g^{⊗k}`. -/
theorem toEndMatrix_diagAction (g : Module.End ℂ (Fin d → ℂ)) (I J : Fin k → Fin d) :
    toEndMatrix d k (diagAction d k g) I J =
    ∏ m : Fin k,
      LinearMap.toMatrix (Pi.basisFun ℂ (Fin d)) (Pi.basisFun ℂ (Fin d)) g (I m) (J m) := by
  unfold toEndMatrix
  rw [LinearMap.toMatrix_apply]
  unfold diagAction tensorBasis
  simp +decide [PiTensorProduct.map_tprod, Basis.piTensorProduct_apply]
