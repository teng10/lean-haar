-- test imports
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

import Physlib.StringTheory.Basic

-- verify basic functions
def hello := "Hello"

def basicAdd (x y : Nat) : Nat :=
  x + y

#eval basicAdd 101 202 -- 303
