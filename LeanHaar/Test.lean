import LeanHaar.TensorPower

-- Test file

open LeanHaar
open HilbertTensorPower

-- The `k`-fold tensor power of `ℂ²` (i.e. `ℂ² ⊗ ℂ² ⊗ ℂ²`), as our wrapper type `𝓗⊗[Fin 2, 3]`.
#check (𝓗⊗[Fin 2, 3] : Type)

-- It is a finite-dimensional `ℂ`-vector space (instances synthesize).
#synth Module ℂ 𝓗⊗[Fin 2, 3]
#synth FiniteDimensional ℂ 𝓗⊗[Fin 2, 3]
