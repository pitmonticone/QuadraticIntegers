import QuadraticIntegers.Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.ModCases
import Mathlib.RingTheory.Norm.Transitivity

import QuadraticIntegers.Mathlib.QuadraticAlgebra

attribute [-instance] DivisionRing.toRatAlgebra

suppress_compilation

namespace QuadraticInteger

open QuadraticAlgebra NumberField Set Polynomial Algebra

variable {d : ℤ} [NeZero d] [alt : d.natAbs.AtLeastTwo] [sf : Fact (Squarefree d)]

local notation3 "K" => QuadraticAlgebra ℚ d 0

local notation3 "R" => QuadraticAlgebra ℤ d 0

/--
For all rational $r$, we have $r^2 \neq d$, so $K$ is a field.

PROVIDED SOLUTION:
Clear since we assume that $d$ is squarefree.
-/
instance field : Fact (∀ (r : ℚ), r ^2 ≠ d + 0 * r) := by
 constructor
 intro r h
 have step3 := alt.prop
 rw [zero_mul, add_zero] at h
 have foo : IsSquare d := by
  rw [pow_two] at h
  replace h : IsSquare (d : ℚ) := ⟨r,h.symm⟩
  exact (@Rat.isSquare_intCast_iff d).mp h
 rcases foo with ⟨s,hs⟩
 have goo: s * s ∣ d := by exact dvd_of_eq hs.symm
 have step := sf.out _ goo
 have step2 : s * s = 1 := by exact Int.isUnit_mul_self step
 grind

omit [NeZero d] alt in
/--
We have that $d = \pm 1 \bmod 4$ or $d = 2 \bmod 4$.

PROVIDED SOLUTION:
If $d = 0 \bmod 4$ then $d$ would not be squarefree.
-/
lemma d_congr : d ≡ 1 [ZMOD 4] ∨ d ≡ 2 [ZMOD 4] ∨ d ≡ 3 [ZMOD 4] := by
  have h_not_zero: ¬ d ≡ 0 [ZMOD 4] := by
    intro h
    have foo: 2 * 2 ∣ d := Int.modEq_zero_iff_dvd.mp h
    have bar := sf.out _ foo
    apply Int.isUnit_mul_self at bar
    linarith
  mod_cases d % 4 <;> tauto

omit [NeZero d] in
/--
We have that $\sqrt{d}$ is an integral element of $K$.

PROVIDED SOLUTION:
Clear since $\sqrt{d}$ is a root of $x^2-d$.
-/
lemma easy_incl : IsIntegral ℤ (algebraMap R K ω) := by
  apply IsIntegral.algebraMap
  exact IsIntegral.isIntegral ω

section trace_and_norm

variable {a b : ℚ}

local notation3 "z" => a + b • (ω : K)

omit [NeZero d] in
/--
We have that $z \in \Q$ if and only if $b = 0$.

PROVIDED SOLUTION:
Clear.
-/
lemma rational_iff : z ∈ range (algebraMap ℚ K) ↔ b = 0 := by
  simp
  constructor
  · intro ⟨y, hy⟩
    obtain ⟨_, im_eq_im⟩ := QuadraticAlgebra.ext_iff.mp hy
    have im_eq_0 := QuadraticAlgebra.im_coe («R» := ℚ) (a := (d : ℚ)) (b := 0)
    have y_im_eq_0 := im_eq_0 y
    simp at y_im_eq_0
    rw [y_im_eq_0] at im_eq_im
    have : b = (z : K).im := by
      have a_coe := im_eq_0 a
      simpa using a_coe
    grind
  · intro h
    simp [h]

omit [NeZero d] in
/--
If $b \neq 0$ then the minimal polynomial of $z$ over $\Q$ is $$X^2-2aX+(a^2-db^2)$$.

PROVIDED SOLUTION:
It's clear that $z$ is a root of $P$ and that $P \in \Q[X]$ is monic.
Irreducibility follows by the fact that $P$ has a root that is irrational.
The proof uses `rational_iff`.
-/
lemma minpoly (hb : b ≠ 0) : minpoly ℚ z = X ^ 2 - C (2 * a) * X + C (a ^ 2 - d * b ^ 2) := by
  symm
  apply minpoly.unique'
  · monicity <;> grind
  · simp
    field_simp
    ring_nf
    calc (b • ω) ^ 2 - (d : K) * (b : K) ^ 2
    _ = ((b : K) * ω) ^ 2 - (d : K) * (b : K) ^ 2 := by
      simp
      have : b • ω = (b : K) * ω := by
        rw [←Rat.cast_smul_eq_qsmul K b ω]
        rfl
      grind
    _ = (b : K) ^ 2 * ω ^ 2 - (d : K) * (b : K) ^ 2 := by grind
    _ = (b : K) ^ 2 * d - (d : K) * (b : K) ^ 2 := by
      have : (ω : K) ^ 2 = d := by
        rw [pow_two]
        simp [omega_mul_omega_eq_mk]
        rfl
      grind
    _ = 0 := by ring
  · intro q qdeg_lt_2
    have : (X ^ 2 - C (2 * a) * X + C (a ^ 2 - (d : ℚ) * b ^ 2) : ℚ[X]).degree = 2 := by
      compute_degree!
    rw [this] at qdeg_lt_2
    match h : q.degree with
    | none => exact Or.inl (degree_eq_bot.mp h)
    | some 0 =>
      right
      intro q_root
      have : 0 < q.degree := by
        have q_ne_0 : q ≠ 0 := by aesop
        apply Polynomial.degree_pos_of_aeval_root («R» := ℚ) (S := K) («z» := z) q_ne_0
        · exact q_root
        · simp
      have : q.degree < q.degree := by
        calc q.degree
        _ = 0 := h
        _ < q.degree := this
      exact (lt_self_iff_false q.degree).mp this
    | some 1 =>
      right
      intro q_root
      have := Polynomial.eq_X_add_C_of_degree_eq_one h
      rw [this] at q_root
      simp at q_root
      have : z = -↑(q.coeff 0) / ↑q.leadingCoeff := by
        have leading_ne_0 : q.leadingCoeff ≠ 0 :=
          Polynomial.leadingCoeff_eq_zero_iff_deg_eq_bot (p := q) |>.not.mpr (by simp [h])
        have : q.leadingCoeff * z = -(q.coeff 0) := by grind
        have : (q.leadingCoeff * z) / (q.leadingCoeff) = -(q.coeff 0) / (q.leadingCoeff) := by
          grind
        simpa [leading_ne_0] using this
      norm_cast at this
      have : z ∈ range (algebraMap ℚ K) := by
        simp
        use -↑(q.coeff 0) / ↑q.leadingCoeff
        exact this.symm
      rw [rational_iff] at this
      contradiction
    | some (t + 2) =>
      have q_ne_bot : q.degree ≠ ⊥ := by aesop
      obtain ⟨n, hn⟩ : ∃n, q.degree = .some n := Option.ne_none_iff_exists'.mp q_ne_bot
      have qnatdeg_eq_2 := natDegree_eq_of_degree_eq_some hn
      have : n < 2 := by
        calc n
        _ = q.natDegree := by grind
        _ < 2 := by
          refine (natDegree_lt_iff_degree_lt ?_).mpr qdeg_lt_2
          exact degree_ne_bot.mp q_ne_bot
      simp [hn] at h
      have : n = t + 1 + 1 := ENat.coe_inj.mp h
      grind

open IntermediateField

omit [NeZero d] in

lemma adjoin_z_eq_top (h : b ≠ 0): ℚ⟮z⟯ = ⊤ := by
  apply (Field.primitive_element_iff_minpoly_natDegree_eq ℚ z).mpr
  have := finrank_eq_two (d : ℚ) 0
  rw [this, minpoly]
  compute_degree!
  assumption

omit [NeZero d] in
/--
We have that the trace of $z$ is $2a$.

PROVIDED SOLUTION:
If $b = 0$ then $z = a \in \Q$ and the trace is $2a$ since $[K : \Q] = 2$.
Otherwise this is clear by lemma `minpoly`.
This proof uses `minpoly` and `field`.
-/
lemma trace : trace ℚ K z = 2 * a := by
  by_cases h : b = 0
  · subst h
    have := trace_algebraMap (S := K) a
    simp at this ⊢
    rw [this]
    have : Module.finrank ℚ K = 2 := by
      exact finrank_eq_two (d : ℚ) 0
    simp [this]
  · rw [trace_eq_finrank_mul_minpoly_nextCoeff ℚ z,
       minpoly (a := a) (b := b) (d := d) h]

    set p := X ^ 2 - C (2 * a) * X + C (a ^ 2 - ↑d * b ^ 2) with p_def
    have p_deg_2 : p.natDegree = 2 := by
      rw [p_def]
      compute_degree!

    have := Polynomial.nextCoeff_of_natDegree_pos (p := p) (by simp [p_deg_2])
    simp [this]
    have p_coeff_eq_2a: p.coeff 1 = -(2 * a) := by
      rw [p_def, coeff_add, coeff_C]
      simp
    simp [p_deg_2, p_coeff_eq_2a]

    have : ℚ⟮z⟯ = ⊤ := by
      apply (Field.primitive_element_iff_minpoly_natDegree_eq ℚ z).mpr
      have := finrank_eq_two (d : ℚ) 0
      rw [this, minpoly]
      compute_degree!
      assumption
    rw [this]
    simp

/--
We have that the norm of $z$ is $a^2-db^2$.

PROVIDED SOLUTION:
If $b = 0$ then $z = a \in \Q$ and the norm is $a^2$ since $[K : \Q] = 2$.
Otherwise this is clear by lemma `minpoly`.
This proof uses `minpoly` and `field`.
-/
lemma norm : norm ℚ z = a ^ 2 - d * b ^ 2 := by
    by_cases h : b = 0
    · have  hzeq : z = algebraMap ℚ K a := by simp [h]
      have hnorma : (Algebra.norm ℚ) (algebraMap ℚ K a) = a ^ 2 := by
        rw [Algebra.norm_algebraMap, finrank_eq_two]
      rw [hzeq, hnorma, h]
      ring
    · have fact₁ : ℚ⟮z⟯ = ⊤ := adjoin_z_eq_top h
      let pb : PowerBasis ℚ K := by
        apply PowerBasis.ofAdjoinEqTop' (IsIntegral.isIntegral z)
        apply_fun IntermediateField.toSubalgebra at fact₁
        simp at fact₁
        rw [← fact₁]
        refine Eq.symm (adjoin_simple_toSubalgebra_of_integral (IsIntegral.isIntegral z))
      have h_z_eq_gen : z = pb.gen := by simp_all only [PowerBasis.ofAdjoinEqTop'_gen, pb]
      rw [h_z_eq_gen, PowerBasis.norm_gen_eq_coeff_zero_minpoly pb, ← h_z_eq_gen, minpoly h,
        ← PowerBasis.finrank, finrank_eq_two (d : ℚ) 0, coeff_zero_eq_eval_zero]
      simp

      /-PowerBasis.norm_gen_eq_coeff_zero_minpoly
        (pb : PowerBasis R S) :
        norm R pb.gen = (-1) ^ pb.dim * coeff (minpoly R pb.gen) 0 -/


section integrality

omit [NeZero d] in
/--
We have that $2a \in \Z$.

PROVIDED SOLUTION:
Since the trace of an algebraic integer is an integers, this follows by lemma `trace`.
This proof uses `trace`.
-/
lemma trace_int (hz : IsIntegral ℤ z) : ∃ (t : ℤ), t = 2 * a := by
  have : IsIntegral ℤ (Algebra.trace ℚ K z) := Algebra.isIntegral_trace hz
  rw [trace, IsIntegrallyClosed.isIntegral_iff] at this
  obtain ⟨y, hy⟩ := this
  simp at hy
  use y

def t (hz : IsIntegral ℤ z) := (trace_int hz).choose

omit [NeZero d] in
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
  have : IsIntegral ℤ (Algebra.norm ℚ z) := Algebra.isIntegral_norm ℚ hz
  rw [norm, IsIntegrallyClosed.isIntegral_iff] at this
  obtain ⟨y, hy⟩ := this
  simp at hy
  use y

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
  simp [n_spec]
  ring


/--
Let $n$ be a squarefree integer and let $r$ be a rational such that $b r^2$ is an integer.
Then $r$ is itself an integer.

PROVIDED SOLUTION:
Easy.
-/
lemma squarefree_mul {n : ℤ} {r : ℚ} (hn : Squarefree n) (hnr : ∃ (m : ℤ), n * r ^ 2 = m) :
    ∃ (t : ℤ), t = r := by
  rcases hnr with ⟨m,hm⟩
  have h₁: (n * r^ 2 ).den = (m : ℚ).den := congrArg Rat.den hm
  dsimp at h₁
  have h := Rat.mul_num_den' n (r ^ 2)
  simp [h₁] at h
  have h₂ : (r.den ^ 2 : ℤ) ∣ ((n : ℤ) * r ^ 2).num * r.den ^ 2 := by
   exact Int.dvd_mul_left ((n : ℤ) * r ^ 2).num (↑r.den ^ 2)
  rw [h] at h₂

  -- have h₃ : (r.den ^ 2 : ℤ).natAbs ∣ (((n : ℤ) * r ^ 2).num * r.den ^ 2).natAbs := by apply?

  have red := r.reduced
  have red₂ : r.den.Coprime r.num.natAbs := Nat.coprime_comm.mp red
  clear red
  have red₂ : (r.den ^ 2).Coprime (r.num.natAbs ^ 2) := Nat.pow_gcd_pow_of_gcd_eq_one red₂
  rw [Eq.symm (Int.natAbs_pow r.num 2)] at red₂
  have red₃ : IsCoprime (r.den ^2 : ℤ) (r.num ^2) :=
    Int.isCoprime_iff_gcd_eq_one.mpr red₂
  have H : (r.den ^2 : ℤ) ∣ n :=
   Int.dvd_of_dvd_mul_left_of_gcd_one h₂ red₂
  rw [pow_two] at H
  apply hn at H
  rw [Int.isUnit_iff] at H
  rcases H with H | H

  rw [←Rat.coe_int_num_of_den_eq_one (q := r)]
  tauto
  exact_mod_cast H

  linarith

/--
We have that $2b \in \Z$.

PROVIDED SOLUTION:
By lemma `four_n`, $(2a)^2 - d(2b)^2$ is an integer and so, by lemma `trace_int`,
we know that $d(2b)^2 \in \Z$. Since $d$ is squarefree, we conclude that $2b \in \Z$ by
lemma `squarefree_mul`.
-/
lemma two_b_int (hz : IsIntegral ℤ z) : ∃ (B₂ : ℤ), B₂ = 2 * b := by
  have := four_n hz
  obtain ⟨y, hy⟩ := trace_int hz
  apply squarefree_mul sf.out
  use y ^ 2 - (4 * n hz)
  grind

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
  have := four_n hz
  obtain ⟨A, hA⟩ := ha
  apply squarefree_mul sf.out
  use A ^ 2 - (n hz)
  grind

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
  constructor
  · sorry
  · sorry

end d_2_3

section d_1

variable [h : Fact (d ≡ 1 [ZMOD 4])]

local notation3 "e" => (d - 1) / 4

/--
We have that $e$ is an integer and $4e = d - 1$.

PROVIDED SOLUTION:
It's obvious.
-/
lemma e_spec : 4 * e = d - 1 := by
  refine Int.mul_ediv_cancel_of_emod_eq_zero ?_
  cases h
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
  assumption

local notation3 "S" => QuadraticAlgebra ℤ e 1

/--
We have that $$\left(2 \left( \frac{1+\sqrt{d}}{2} \right) - 1 \right)^2 = d$$
so that $S$ is an $R$-algebra.

PROVIDED SOLUTION:
Obvious by Lemma `e_spec`.
-/
lemma algebra_R_S : (2 * (ω : S) - 1) * (2 * ω - 1) = d • 1 + 0 • ((2 * ω - 1)) := by
  rcases Int.modEq_iff_dvd.mp h.out with ⟨w,hw⟩
  have s := omega_mul_omega_eq_add (a:=e) (b:=1)
  ring_nf
  rw [pow_two, s]
  ring_nf
  norm_cast
  grind

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
