import QuadraticIntegers.Mathlib.Algebra.QuadraticAlgebra.Basic

namespace QuadraticAlgebra

variable {R S : Type*} [CommSemiring R] [CommRing S] [Algebra R S]

instance (a b : R) : Algebra (QuadraticAlgebra R a b)
    (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) :=
  (lift ⟨ω, by simpa using
    omega_mul_omega_eq_add (a := algebraMap R S a) (b := algebraMap R S b)⟩).toRingHom.toAlgebra

@[simp] lemma algebraMap_omega (a b : R) : algebraMap (QuadraticAlgebra R a b)
    (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) ω = ω := by
  convert lift_symm_apply_coe _
  simp

instance (a b : ℤ) : Algebra (QuadraticAlgebra ℤ a b) (QuadraticAlgebra S a b) :=
  (lift ⟨ω, by simpa [Int.cast_smul_eq_zsmul] using
    omega_mul_omega_eq_add (R := S) (a := a) (b := b)⟩).toRingHom.toAlgebra

@[simp] lemma algebraMap_omega' (a b : ℤ) : algebraMap (QuadraticAlgebra ℤ a b)
    (QuadraticAlgebra S a b) ω = ω := by
  simpa using algebraMap_omega (S := S) a b

instance (a : ℤ) : Algebra (QuadraticAlgebra ℤ a 0) (QuadraticAlgebra S a 0) :=
  (lift ⟨ω, by simpa [Int.cast_smul_eq_zsmul] using
    omega_mul_omega_eq_add (R := S) (a := a) (b := 0)⟩).toRingHom.toAlgebra

@[simp] lemma algebraMap_omega'' (a : ℤ) : algebraMap (QuadraticAlgebra ℤ a 0)
    (QuadraticAlgebra S a 0) ω = ω := by
  convert lift_symm_apply_coe _
  simp

end QuadraticAlgebra
