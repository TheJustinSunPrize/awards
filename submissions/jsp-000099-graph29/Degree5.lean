import Degree5Part4
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Erdos82Finite
open RegularCertificate

@[irreducible] def cert5 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.split 1 (.split 12 c5_1 (.fill 1 (.checkpoint 437780482 536866814 (.empty 20 (.empty 25 (.bad 19)))))) c5_388)))
theorem cert5_ok : fcheck 7 5 0 536870911 cert5 = true := by
  unfold cert5
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_split (accept_split c5_1_ok (accept_fill (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_empty (by decide +kernel) (accept_empty (by decide +kernel) (by decide +kernel)))))) c5_388_ok)))

theorem checked5 : fcheck 7 5 0 full cert5 = true := cert5_ok

theorem no_regular_5 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 5 :=
  fcheck_sound 5 cert5 checked5 T h

#print axioms no_regular_5
end Erdos82Finite
