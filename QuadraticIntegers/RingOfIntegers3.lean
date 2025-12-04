import QuadraticIntegers.Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.NumberField.Basic

import QuadraticIntegers.Mathlib.QuadraticAlgebra

suppress_compilation

namespace QuadraticInteger

open QuadraticAlgebra NumberField Set Polynomial Algebra

variable {d : ℤ} [NeZero d] [d.natAbs.AtLeastTwo] [Fact (Squarefree d)]

local notation3 "K" => QuadraticAlgebra ℚ d 0

local notation3 "R" => QuadraticAlgebra ℤ d 0

instance field : Fact (∀ (r : ℚ), r ^2 ≠ d + 0 * r) := by
  sorry

lemma d_congr : d ≡ 1 [ZMOD 4] ∨ d ≡ 2 [ZMOD 4] ∨ d ≡ 3 [ZMOD 4] := by
  sorry

lemma easy_incl : IsIntegral ℤ (algebraMap R K ω) := by
  sorry

section trace_and_norm

variable {a b : ℚ}

local notation3 "z" => a + b • (ω : K)

lemma rational_iff : z ∈ range (algebraMap ℚ K) ↔ b = 0 := by
  sorry

lemma minpoly (hb : b ≠ 0) : minpoly ℚ z = X ^ 2 - C (2 * a) * X + C (a ^ 2 - d * b ^ 2) := by
  sorry

lemma trace : trace ℚ K z = 2 * a := by
  sorry

lemma norm : norm ℚ z = a ^ 2 - d * b ^ 2 := by
  sorry

section integrality

lemma trace_int (hz : IsIntegral ℤ z) : ∃ (t : ℤ), t = 2 * a := by
  sorry

def t (hz : IsIntegral ℤ z) := (trace_int hz).choose

lemma t_spec (hz : IsIntegral ℤ z) : t hz = 2 * a := (trace_int hz).choose_spec

lemma norm_int (hz : IsIntegral ℤ z) : ∃ (n : ℤ), n = a ^ 2 - d * b ^ 2 := by
  sorry

def n (hz : IsIntegral ℤ z) := (norm_int hz).choose

lemma n_spec (hz : IsIntegral ℤ z) : n hz = a ^ 2 - d * b ^ 2 := (norm_int hz).choose_spec

lemma four_n (hz : IsIntegral ℤ z) : 4 * n hz = (2 * a)^2 - d * (2 * b) ^ 2 := by
  sorry

lemma squarefree_mul {n : ℤ} {r : ℚ} (hn : Squarefree n) (hnr : ∃ (m : ℤ), n * r ^ 2 = m) :
    ∃ (t : ℤ), t = r := by
  sorry

lemma two_b_int (hz : IsIntegral ℤ z) : ∃ (B₂ : ℤ), B₂ = 2 * b := by
  sorry

def B₂ (hz : IsIntegral ℤ z) := (two_b_int hz).choose

lemma B₂_spec (hz : IsIntegral ℤ z) : B₂ hz = 2 * b := (two_b_int hz).choose_spec

lemma b_int_of_a_int (hz : IsIntegral ℤ z) (ha : ∃ (A : ℤ), A = a) : ∃ (B : ℤ), B = b := by
  sorry

def B (hz : IsIntegral ℤ z) (ha : ∃ (A : ℤ), A = a) := (b_int_of_a_int hz ha).choose

lemma B_spec (hz : IsIntegral ℤ z) (ha : ∃ (A : ℤ), A = a) : B hz ha = b :=
  (b_int_of_a_int hz ha).choose_spec

lemma a_not_int (hz : IsIntegral ℤ z) (ha : ¬∃ (A : ℤ), A = a) : d ≡ 1 [ZMOD 4] := by
  sorry

end integrality

end trace_and_norm

section d_2_3

theorem d_2_or_3 (hd : d ≡ 2 [ZMOD 4] ∨ d ≡ 3 [ZMOD 4]) : IsIntegralClosure ℤ R K := by
  sorry

end d_2_3

section d_1

variable [Fact (d ≡ 1 [ZMOD 4])]

local notation3 "e" => (d - 1) / 4

lemma e_spec : 4 * e = d - 1 := by
  sorry

local notation3 "S" => QuadraticAlgebra ℤ e 1

lemma algebra_R_S : (2 * (ω : S) - 1) * (2 * ω - 1) = d • 1 + 0 • ((2 * ω - 1)) := by
  sorry

instance : Algebra R S := (lift ⟨2 * ω - 1, algebra_R_S⟩).toRingHom.toAlgebra

lemma algebra_S_K : ((1 + (ω : K)) / 2) * ((1 + ω) / 2) = e • 1 + 1 • ((1 + ω) / 2) := by
  sorry

instance : Algebra S K := (lift ⟨(1 + ω) / 2, algebra_S_K⟩).toRingHom.toAlgebra

instance commutes_R_S_K : IsScalarTower R S K := by
  sorry

lemma easy_incl_d_1 : IsIntegral ℤ (algebraMap S K ω) := by
  sorry

lemma d_1_int {a b : ℚ} (hz : IsIntegral ℤ (a + b • (ω : K))) (ha : ∃ (A : ℤ), A = a) :
    a + b • (ω : K) ∈ range (algebraMap S K) := by
  sorry

theorem d_1 : IsIntegralClosure ℤ S K := by
  sorry

end d_1

end QuadraticInteger
