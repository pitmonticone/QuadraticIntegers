import Mathlib.Algebra.Squarefree.Basic

--check if this is already in mathlib in some form
-- anyway generalize it

/--
Let $n$ be a squarefree integer and let $r$ be a rational such that $b r^2$ is an integer.
Then $r$ is itself an integer.
-/
lemma squarefree_mul {n : ℤ} {r : ℚ} (hn : Squarefree n) (hnr : ∃ (m : ℤ), n * r ^ 2 = m) :
    ∃ (t : ℤ), t = r := by
  sorry
