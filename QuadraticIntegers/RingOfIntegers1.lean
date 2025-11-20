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

PROVIDED SOLUTION:
Clear since we assume that $d$ is squarefree.
-/
instance field : Fact (∀ (r : ℚ), r ^2 ≠ d + 0 * r) := by
  sorry

/--
We have that $d = \pm 1 \bmod 4$ or $d = 2 \bmod 4$.

PROVIDED SOLUTION:
If $d = 0 \bmod 4$ then $d$ would not be squarefree.
-/
lemma d_congr : d ≡ 1 [ZMOD 4] ∨ d ≡ 2 [ZMOD 4] ∨ d ≡ 3 [ZMOD 4] := by
  sorry

/--
We have that $\sqrt{d}$ is an integral element of $K$.

PROVIDED SOLUTION:
Clear since $\sqrt{d}$ is a root of $x^2-d$.
-/
lemma easy_incl : IsIntegral ℤ (algebraMap R K ω) := by
  sorry

section trace_and_norm

variable {a b : ℚ}

local notation3 "z" => a + b • (ω : K)

/--
We have that $z \in \Q$ if and only if $b = 0$.

PROVIDED SOLUTION:
Clear.
-/
lemma rational_iff : z ∈ range (algebraMap ℚ K) ↔ b = 0 := by
  sorry

/--
If $b \neq 0$ then the minimal polynomial of $z$ over $\Q$ is $$X^2-2aX+(a^2-db^2)$$.

PROVIDED SOLUTION:
It's clear that $z$ is a root of $P$ and that $P \in \Q[X]$ is monic.
Irreducibility follows by the fact that $P$ has a root that is irrational.
The proof uses `rational_iff`.
-/
lemma minpoly (hb : b ≠ 0) : minpoly ℚ z = X ^ 2 - C (2 * a) * X + C (a ^ 2 - d * b ^ 2) := by
  sorry

/--
We have that the trace of $z$ is $2a$.

PROVIDED SOLUTION:
If $b = 0$ then $z = a \in \Q$ and the trace is $2a$ since $[K : \Q] = 2$.
Otherwise this is clear by lemma `minpoly`.
This proof uses `minpoly` and `field`.
-/
lemma trace : trace ℚ K z = 2 * a := by
  sorry

/--
We have that the norm of $z$ is $a^2-db^2$.

PROVIDED SOLUTION:
If $b = 0$ then $z = a \in \Q$ and the norm is $a^2$ since $[K : \Q] = 2$.
Otherwise this is clear by lemma `minpoly`.
This proof uses `minpoly` and `field`.
-/
lemma norm : norm ℚ z = a ^ 2 - d * b ^ 2 := by
  sorry

section integrality

/--
We have that $2a \in \Z$.

PROVIDED SOLUTION:
Since the trace of an algebraic integer is an integers, this follows by lemma `trace`.
This proof uses `trace`.
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

PROVIDED SOLUTION:
Since the norm of an algebraic integer is an integers, this follows by lemma `norm`.
This proof uses `norm`.
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

PROVIDED SOLUTION:
Obvious by applying `n_spec`.
-/
lemma four_n (hz : IsIntegral ℤ z) : 4 * n hz = (2 * a)^2 - d * (2 * b) ^ 2 := by
  sorry

/--
Let $n$ be a squarefree integer and let $r$ be a rational such that $b r^2$ is an integer.
Then $r$ is itself an integer.

PROVIDED SOLUTION:
Easy.
-/
lemma squarefree_mul {n : ℤ} {r : ℚ} (hn : Squarefree n) (hnr : ∃ (m : ℤ), n * r ^ 2 = m) :
    ∃ (t : ℤ), t = r := by
  sorry

/--
We have that $2b \in \Z$.

PROVIDED SOLUTION:
By lemma `four_n`, $(2a)^2 - d(2b)^2$ is an integer and so, by lemma `trace_int`,
we know that $d(2b)^2 \in \Z$. Since $d$ is squarefree, we conclude that $2b \in \Z$ by
lemma `squarefree_mul`.
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

PROVIDED SOLUTION:
By Lemma `four_n` and our assumption, both $(2a)^2$ and $(2a)^2 - d(2b)^2$ are integers
divisible by $4$, so the same holds for $d(2b)^2$. In particular $db^2 \in \Z$ and $b \in \Z$ by
Lemma `squarefree_mul` since $d$ is squarefree.
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

PROVIDED SOLUTION:
We have that $2a$, that is an integer, must be odd. By Lemmas `four_n` and `two_b_int`,
we have $(2a)^2 = d(2b)^2 \bmod{4}$, so $2b$ must be odd and $d = 1 \bmod{4}$ as required.
This proof uses `four_n`, `B₂_spec` and `two_b_int`.
-/
lemma a_not_int (hz : IsIntegral ℤ z) (ha : ¬∃ (A : ℤ), A = a) : d ≡ 1 [ZMOD 4] := by
  sorry

end integrality

end trace_and_norm

section d_2_3

/--
Assume that $d = 2 \bmod{4}$ or $d = 3 \bmod{4}$. Then $$\mathcal{O}_K = \Z[\sqrt{d}]$$.

PROVIDED SOLUTION:
\uses{easy_incl, a_not_int, d_congr, B_spec, b_int_of_a_int}
By Lemma `easy_incl` we know that $\Z[\sqrt{d}] \subseteq \mathcal{O}_K$. Let $z = a + b \sqrt{d} \in \mathcal{O}_K$, with
$a, b \in \Q$. By Lemma `a_not_int` we have that $a \in \Z$ (since by Lemma `d_congr` we cannot have
$d = 1 \bmod{4}$), and so by Lemma `b_int_of_a_int` we have $b \in \Z$, so $z \in \Z[\sqrt{d}]$.
-/
theorem d_2_or_3 (hd : d ≡ 2 [ZMOD 4] ∨ d ≡ 3 [ZMOD 4]) : IsIntegralClosure ℤ R K := by
  sorry

end d_2_3

section d_1

variable [Fact (d ≡ 1 [ZMOD 4])]

local notation3 "e" => (d - 1) / 4

/--
We have that $e$ is an integer and $4e = d - 1$.

PROVIDED SOLUTION:
It's obvious.
-/
lemma e_spec : 4 * e = d - 1 := by
  sorry

local notation3 "S" => QuadraticAlgebra ℤ e 1

/--
We have that $$\left(2 \left( \frac{1+\sqrt{d}}{2} \right) - 1 \right)^2 = d$$
so that $S$ is an $R$-algebra.

PROVIDED SOLUTION:
Obvious by Lemma `e_spec`.
-/
lemma algebra_R_S : (2 * (ω : S) - 1) * (2 * ω - 1) = d • 1 + 0 • ((2 * ω - 1)) := by
  sorry

instance : Algebra R S := (lift ⟨2 * ω - 1, algebra_R_S⟩).toRingHom.toAlgebra

/--
We have that $$\left(\frac{1+\sqrt{d}}{2} \right)^2 = \left( \frac{1+\sqrt{d}}{2} \right) + e$$
so that $K$ is an $S$-algebra.

PROVIDED SOLUTION:
Obvious by Lemma `e_spec`.
-/
lemma algebra_S_K : ((1 + (ω : K)) / 2) * ((1 + ω) / 2) = e • 1 + 1 • ((1 + ω) / 2) := by
  sorry

instance : Algebra S K := (lift ⟨(1 + ω) / 2, algebra_S_K⟩).toRingHom.toAlgebra

/--
The obvious diagram between $R$, $S$ and $K$ commutes.

PROVIDED SOLUTION:
Clear by `algebra_R_S` and `algebra_S_K`.
-/
instance commutes_R_S_K : IsScalarTower R S K := by
  sorry

/--
We have that $\frac{1+\sqrt{d}}{2} \in \mathcal{O}_K$.

PROVIDED SOLUTION:
Clear since $\frac{1+\sqrt{d}}{2}$ is a root of $X^2 - X - e \in \Z[X]$.
This proof uses `e_spec` and `algebra_S_K`.
-/
lemma easy_incl_d_1 : IsIntegral ℤ (algebraMap S K ω) := by
  sorry

/--
Take $z = a + b \sqrt{d} \in \mathcal{O}_K$ with $a, b \in \Q$.
If $a \in \Z$ then $z \in \Z\left[ \frac{1+\sqrt{d}}{2} \right]$.

PROVIDED SOLUTION:
By Lemma `b_int_of_a_int` we have that $b \in \Z$ and so
$z \in \Z[\sqrt{d}] \subseteq \Z\left[ \frac{1+\sqrt{d}}{2} \right]$.
-/
lemma d_1_int {a b : ℚ} (hz : IsIntegral ℤ (a + b • (ω : K))) (ha : ∃ (A : ℤ), A = a) :
    a + b • (ω : K) ∈ range (algebraMap S K) := by
  sorry

/--
We have $$\mathcal{O}_K = \Z\left[ \frac{1+\sqrt{d}}{2} \right]$$.

PROVIDED SOLUTION:
By Lemma `easy_incl_d_1` we know that $\Z\left[ \frac{1+\sqrt{d}}{2} \right] \subseteq \mathcal{O}_K$.
Let $z = a + b \sqrt{d} \in \mathcal{O}_K$, with $a, b \in \Q$.
\begin{itemize}
  \item If $ a \in \Z$ we conclude by Lemma `d_1_int`.
  \item If $a \notin \Z$, let us consider
  $$z' = z - \frac{1+\sqrt{d}}{2} = a - \frac{1}{2} + \left( b - \frac{1}{2} \right) \sqrt{d} \in \mathcal{O}_K$$
  Since $2a \in \Z$ and $a \notin \Z$, we have that $a - \frac{1}{2} \in \Z$, so by Lemma `d_1_int`,
  we have that $z' \in \Z\left[ \frac{1+\sqrt{d}}{2} \right]$ and so $z \in \Z\left[ \frac{1+\sqrt{d}}{2} \right]$.
\end{itemize}
This proof uses `easy_incl_d_1`, `d_1_int` and `t_spec`.
-/
theorem d_1 : IsIntegralClosure ℤ S K := by
  sorry

end d_1

end QuadraticInteger
