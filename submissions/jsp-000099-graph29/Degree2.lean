import Degree2Part1
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Erdos82Finite
open RegularCertificate

@[irreducible] def cert2 : FastCert := (.checkpoint 0 536870911 c2_110)
theorem cert2_ok : fcheck 7 2 0 536870911 cert2 = true := by
  unfold cert2
  exact (accept_checkpoint (by decide +kernel) c2_110_ok)

theorem checked2 : fcheck 7 2 0 full cert2 = true := cert2_ok

theorem no_regular_2 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 2 :=
  fcheck_sound 2 cert2 checked2 T h

#print axioms no_regular_2
end Erdos82Finite
