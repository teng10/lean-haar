-- test imports
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

import Physlib.StringTheory.Basic

-- verify basic functions
def hello := "Hello"

def basicAdd (x y : Nat) : Nat :=
  x + y

#eval basicAdd 101 202 -- 303

-- the identity matrix, named two equivalent ways
#check (1 : Matrix (Fin 2) (Fin 2) Nat)

-- it literally is ![![1,0],![0,1]]
example : (1 : Matrix (Fin 2) (Fin 2) Nat) = ![![1, 0], ![0, 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp
