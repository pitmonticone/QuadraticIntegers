import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.NumberField.Basic

import QuadraticIntegers.Mathlib.QuadraticAlgebra

suppress_compilation

namespace QuadraticInteger

open QuadraticAlgebra NumberField Set Polynomial Algebra

variable {d : ℤ} [NeZero d] [d.natAbs.AtLeastTwo] [Fact (Squarefree d)]

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

local notation3 "z" => a + b • (ω : K)

lemma rational_iff : z ∈ range (algebraMap ℚ K) ↔ b = 0 := by
  sorry

lemma minpoly (hb : b  ≠ 0) : minpoly ℚ z = X ^ 2 - C (2 * a) * X + C (a ^ 2 - d * b ^ 2) := by
  sorry

lemma trace : trace ℚ K z = 2 * a := by
  sorry

lemma norm : norm ℚ z = a ^ 2 - d * b ^ 2 := by
  sorry

section RingOfIntegers

lemma trace_int (hz : IsIntegral ℤ z) : ∃ (t : ℤ), t = 2 * a := by
  sorry

def t (hz : IsIntegral ℤ z) := (trace_int hz).choose

lemma t_spec (hz : IsIntegral ℤ z) : t hz = 2 * a := (trace_int hz).choose_spec

lemma norm_int (hz : IsIntegral ℤ z) : ∃ (n : ℤ), n = a ^ 2 - d * b ^ 2 := by
  sorry

def n (hz : IsIntegral ℤ z) := (norm_int hz).choose

lemma n_spec (hz : IsIntegral ℤ z) : n hz = a ^ 2 - d * b ^ 2 := (norm_int hz).choose_spec

end RingOfIntegers

end computation

end QuadraticInteger
