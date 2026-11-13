/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Fin

/-!
# Site and copy coordinates of a finite register

The register encoding reads site zero as the least significant digit. `copySiteEquiv`
regroups replicated register coordinates by site without changing that encoding.
-/

namespace SchurWeyl

/-- Read a computational basis index site by site. -/
def registerEquiv (q n : ℕ) : Fin (q ^ n) ≃ (Fin n → Fin q) :=
  finFunctionFinEquiv.symm

/-- Read a replicated register site by site, then copy by copy. -/
def copySiteEquiv (q n k : ℕ) :
    (Fin k → Fin (q ^ n)) ≃ (Fin n → Fin k → Fin q) :=
  (Equiv.arrowCongr (Equiv.refl (Fin k)) (registerEquiv q n)).trans
    (Equiv.piComm (fun _ : Fin k => fun _ : Fin n => Fin q))

@[simp] theorem copySiteEquiv_apply (q n k : ℕ) (x : Fin k → Fin (q ^ n))
    (i : Fin n) (c : Fin k) :
    copySiteEquiv q n k x i c = registerEquiv q n (x c) i := rfl

end SchurWeyl
