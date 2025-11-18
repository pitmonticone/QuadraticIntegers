import Mathlib.Algebra.QuadraticAlgebra.Basic

namespace QuadraticAlgebra

variable {R S : Type*} [CommSemiring R] [CommRing S] [Algebra R S]

instance (a b : R) : Algebra (QuadraticAlgebra R a b)
    (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) :=
  (lift ⟨ω, by simpa using
    omega_mul_omega_eq_add (a := algebraMap R S a) (b := algebraMap R S b)⟩).toRingHom.toAlgebra

instance (a b : ℤ) : Algebra (QuadraticAlgebra ℤ a b) (QuadraticAlgebra S a b) :=
  (lift ⟨ω, by simpa [Int.cast_smul_eq_zsmul] using
    omega_mul_omega_eq_add (R := S) (a := a) (b := b)⟩).toRingHom.toAlgebra

end QuadraticAlgebra
