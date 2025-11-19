import Mathlib.Algebra.Squarefree.Basic

--check if this is already in mathlib in some form
-- anyway generalize it

lemma squarefree_mul {n : ℤ} {r : ℚ} (hn : Squarefree n) (hnr : ∃ (m : ℤ), n * r ^ 2 = m) :
    ∃ (t : ℤ), t = r := by
  sorry
