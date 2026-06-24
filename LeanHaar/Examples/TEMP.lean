import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.FDRep
import LeanHaar.HilbertSpace

import LeanHaar.SchurWeylAbstract
import Mathlib.Data.Complex.Basic
-- import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.FDRep
-- import Mathlib.CategoryTheory.Simple
-- import Mathlib.LinearAlgebra.Dimension.Finrank

open LeanHaar

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-- The unitary group of the finite Hilbert space `𝓗[d]`. -/
abbrev UnitaryGroup (d : Type*) [Fintype d] [DecidableEq d] :=
  FiniteHilbertSpace d ≃ₗᵢ[ℂ] FiniteHilbertSpace d

#check FDRep ℂ (UnitaryGroup d)

#check UnitaryGroup d
