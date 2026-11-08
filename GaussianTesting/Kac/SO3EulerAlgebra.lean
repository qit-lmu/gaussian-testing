module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SO3Rotations

@[expose] public section

/-!
# Euler coordinates for a conjugated axis rotation

This algebraic calculation supplies the local coordinate factorization used
to differentiate a strongly continuous finite-dimensional SO(3) representation.
-/

namespace GaussianTesting.SO3

open Matrix

theorem rotX_rotY_conjugation_factorization (s t a b c r : ℝ)
    (hr : r ≠ 0) (hr2 : r ^ 2 = 1 - (Real.cos s * Real.sin t) ^ 2)
    (haSin : Real.sin a = (-Real.sin s * Real.cos s * (1 - Real.cos t)) / r)
    (haCos : Real.cos a = (Real.sin s ^ 2 + Real.cos s ^ 2 * Real.cos t) / r)
    (hbSin : Real.sin b = Real.cos s * Real.sin t) (hbCos : Real.cos b = r)
    (hcSin : Real.sin c = Real.sin s * Real.sin t / r)
    (hcCos : Real.cos c = Real.cos t / r) :
    rotX s * rotY t * rotX (-s) = rotX a * rotY b * rotZ c := by
  have hs : Real.sin s ^ 2 = 1 - Real.cos s ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq s]
  have ht : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotXMatrix, rotYMatrix, rotZMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      haSin, haCos, hbSin, hbCos, hcSin, hcCos] <;>
    field_simp [hr] <;>
    (try simp only [hr2, mul_pow, hs, ht]) <;> ring

end GaussianTesting.SO3
