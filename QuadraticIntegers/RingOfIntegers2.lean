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

local notation3 "R" => QuadraticAlgebra ℤ d 0

/--
For all rational $r$, we have $r^2 \neq d$, so $K$ is a field.
-/
instance field : Fact (∀ (r : ℚ), r ^2 ≠ d + 0 * r) := by
  sorry

/--
We have that $d = \pm 1 \bmod 4$ or $d = 2 \bmod 4$.
-/
lemma d_congr : d ≡ 1 [ZMOD 4] ∨ d ≡ 2 [ZMOD 4] ∨ d ≡ 3 [ZMOD 4] := by
  sorry

/--
We have that $\sqrt{d}$ is an integral element of $K$.
-/
lemma easy_incl : IsIntegral ℤ (algebraMap R K ω) := by
  sorry

section trace_and_norm

variable {a b : ℚ}

local notation3 "z" => a + b • (ω : K)

/--
We have that $z \in \Q$ if and only if $b = 0$.
-/
lemma rational_iff : z ∈ range (algebraMap ℚ K) ↔ b = 0 := by
  sorry

/--
If $b \neq 0$ then the minimal polynomial of $z$ over $\Q$ is $$X^2-2aX+(a^2-db^2)$$.
-/
lemma minpoly (hb : b ≠ 0) : minpoly ℚ z = X ^ 2 - C (2 * a) * X + C (a ^ 2 - d * b ^ 2) := by
  sorry

/--
We have that the trace of $z$ is $2a$.
-/
lemma trace : trace ℚ K z = 2 * a := by
  sorry

/--
We have that the norm of $z$ is $a^2-db^2$.
-/
lemma norm : norm ℚ z = a ^ 2 - d * b ^ 2 := by
  sorry

section integrality

/--
We have that $2a \in \Z$.
-/
lemma trace_int (hz : IsIntegral ℤ z) : ∃ (t : ℤ), t = 2 * a := by
  sorry

def t (hz : IsIntegral ℤ z) := (trace_int hz).choose

/--
We write $t$ (for trace) to denote $2a$ as an integer. Mathematically we have $t = 2a$.
-/
lemma t_spec (hz : IsIntegral ℤ z) : t hz = 2 * a := (trace_int hz).choose_spec

/--
We have that $a^2-db^2 \in \Z$.
-/
lemma norm_int (hz : IsIntegral ℤ z) : ∃ (n : ℤ), n = a ^ 2 - d * b ^ 2 := by
  sorry

def n (hz : IsIntegral ℤ z) := (norm_int hz).choose

/--
We write $n$ (for norm) to denote $a^2-db^2$ as an integer. Mathematically we have $n = a^2-db^2$.
-/
lemma n_spec (hz : IsIntegral ℤ z) : n hz = a ^ 2 - d * b ^ 2 := (norm_int hz).choose_spec

/--
We have that $4n = (2a)^2 - d(2b)^2$.
-/
lemma four_n (hz : IsIntegral ℤ z) : 4 * n hz = (2 * a)^2 - d * (2 * b) ^ 2 := by
  sorry

/--
Let $n$ be a squarefree integer and let $r$ be a rational such that $b r^2$ is an integer.
Then $r$ is itself an integer.
-/
lemma squarefree_mul {n : ℤ} {r : ℚ} (hn : Squarefree n) (hnr : ∃ (m : ℤ), n * r ^ 2 = m) :
    ∃ (t : ℤ), t = r := by
  sorry

/--
We have that $2b \in \Z$.
-/
lemma two_b_int (hz : IsIntegral ℤ z) : ∃ (B₂ : ℤ), B₂ = 2 * b := by
  sorry

def B₂ (hz : IsIntegral ℤ z) := (two_b_int hz).choose

/--
We write $B_2$ to denote $2b$ as an integer. Mathematically we have $B_2 = 2b$.
-/
lemma B₂_spec (hz : IsIntegral ℤ z) : B₂ hz = 2 * b := (two_b_int hz).choose_spec

/--
If $a \in \Z$ then $b \in \Z$.
-/
lemma b_int_of_a_int (hz : IsIntegral ℤ z) (ha : ∃ (A : ℤ), A = a) : ∃ (B : ℤ), B = b := by
  sorry

def B (hz : IsIntegral ℤ z) (ha : ∃ (A : ℤ), A = a) := (b_int_of_a_int hz ha).choose

/--
If $a$ is an integer, we write $B$ to denote $b$ as an integer. Mathematically we have $B = b$.
-/
lemma B_spec (hz : IsIntegral ℤ z) (ha : ∃ (A : ℤ), A = a) : B hz ha = b :=
  (b_int_of_a_int hz ha).choose_spec

/--
If $a \not\in \Z$ then $d = 1 \bmod{4}$.
-/
lemma a_not_int (hz : IsIntegral ℤ z) (ha : ¬∃ (A : ℤ), A = a) : d ≡ 1 [ZMOD 4] := by
  sorry

end integrality

end trace_and_norm

section d_2_3

/--
Assume that $d = 2 \bmod{4}$ or $d = 3 \bmod{4}$. Then $$\mathcal{O}_K = \Z[\sqrt{d}]$$.
-/
theorem d_2_or_3 (hd : d ≡ 2 [ZMOD 4] ∨ d ≡ 3 [ZMOD 4]) : IsIntegralClosure ℤ R K := by
  sorry

end d_2_3

section d_1

variable [Fact (d ≡ 1 [ZMOD 4])]

local notation3 "e" => (d - 1) / 4

/--
We have that $e$ is an integer and $4e = d - 1$.
-/
lemma e_spec : 4 * e = d - 1 := by
  sorry

local notation3 "S" => QuadraticAlgebra ℤ e 1

/--
We have that $$\left(2 \left( \frac{1+\sqrt{d}}{2} \right) - 1 \right)^2 = d$$
so that $S$ is an $R$-algebra.
-/
lemma algebra_R_S : (2 * (ω : S) - 1) * (2 * ω - 1) = d • 1 + 0 • ((2 * ω - 1)) := by
  sorry

instance : Algebra R S := (lift ⟨2 * ω - 1, algebra_R_S⟩).toRingHom.toAlgebra

/--
We have that $$\left(\frac{1+\sqrt{d}}{2} \right)^2 = \left( \frac{1+\sqrt{d}}{2} \right) + e$$
so that $K$ is an $S$-algebra.
-/
lemma algebra_S_K : ((1 + (ω : K)) / 2) * ((1 + ω) / 2) = e • 1 + 1 • ((1 + ω) / 2) := by
  sorry

instance : Algebra S K := (lift ⟨(1 + ω) / 2, algebra_S_K⟩).toRingHom.toAlgebra

/--
The obvious diagram between $R$, $S$ and $K$ commutes.
-/
instance commutes_R_S_K : IsScalarTower R S K := by
  sorry

/--
We have that $\frac{1+\sqrt{d}}{2} \in \mathcal{O}_K$..
-/
lemma easy_incl_d_1 : IsIntegral ℤ (algebraMap S K ω) := by
  sorry

/--
Take $z = a + b \sqrt{d} \in \mathcal{O}_K$ with $a, b \in \Q$.
If $a \in \Z$ then $z \in \Z\left[ \frac{1+\sqrt{d}}{2} \right]$.
-/
lemma d_1_int {a b : ℚ} (hz : IsIntegral ℤ (a + b • (ω : K))) (ha : ∃ (A : ℤ), A = a) :
    a + b • (ω : K) ∈ range (algebraMap S K) := by
  sorry

/--
We have $$\mathcal{O}_K = \Z\left[ \frac{1+\sqrt{d}}{2} \right]$$.
-/
theorem d_1 : IsIntegralClosure ℤ S K := by
  sorry

end d_1

end QuadraticInteger
