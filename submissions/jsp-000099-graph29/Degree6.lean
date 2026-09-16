import Degree6Part3
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Erdos82Finite
open RegularCertificate

@[irreducible] def cert6 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.split 1 (.fill 1 (.empty 25 (.checkpoint 437784578 454563022 (.drop 2 (.drop 3 (.drop 7 (.drop 10 (.checkpoint 437784578 454561858 (.fill 27 (.bad 12)))))))))) (.split 2 (.fill 2 (.checkpoint 73565188 536870908 (.split 7 (.empty 7 (.empty 10 (.empty 15 (.checkpoint 73565316 73832428 (.empty 17 (.empty 21 (.empty 22 (.drop 3 (.checkpoint 73565316 73565412 (.fill 26 (.bad 5))))))))))) c6_0))) c6_282))))
theorem cert6_ok : fcheck 7 6 0 536870911 cert6 = true := by
  unfold cert6
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_split (accept_fill (by decide +kernel) (accept_empty (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_fill (by decide +kernel) (by decide +kernel)))))))))) (accept_split (accept_fill (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_split (accept_empty (by decide +kernel) (accept_empty (by decide +kernel) (accept_empty (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_empty (by decide +kernel) (accept_empty (by decide +kernel) (accept_empty (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_fill (by decide +kernel) (by decide +kernel))))))))))) c6_0_ok))) c6_282_ok))))

theorem checked6 : fcheck 7 6 0 full cert6 = true := cert6_ok

theorem no_regular_6 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 6 :=
  fcheck_sound 6 cert6 checked6 T h

#print axioms no_regular_6
end Erdos82Finite
