import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.NumberField.Basic

import QuadraticIntegers.Mathlib.QuadraticAlgebra

namespace QuadraticInteger

open QuadraticAlgebra NumberField Set Polynomial Algebra

variable (d : ℤ) [NeZero d] [d.natAbs.AtLeastTwo] [Fact (Squarefree d)]

local notation3 "K" => QuadraticAlgebra ℚ d 0

instance field : Fact (∀ (r : ℚ), r ^2 ≠ d + 0 * r) := by
  constructor
  sorry

lemma d_congr : d ≡ 1 [ZMOD 4] ∨ d ≡ 3 [ZMOD 4] := by
  sorry

local notation3 "R" => QuadraticAlgebra ℤ d 0

lemma easy_incl : IsIntegral ℤ (algebraMap R K ω) := by
  sorry

section computation

variable {a b : ℚ}

local notation3 "t" => a + b • (ω : K)

lemma rational_iff : t ∈ range (algebraMap ℚ K) ↔ b = 0 := by
  sorry

lemma minpoly (hb : b  ≠ 0) : minpoly ℚ t = X ^ 2 - C (2 * a) * X + C (a ^ 2 - d * b ^ 2) := by
  sorry

lemma trace : trace ℚ K t = 2 * a := by
  sorry

lemma norm : norm ℚ t = a ^ 2 - d * b ^ 2 := by
  sorry

end computation

end QuadraticInteger
