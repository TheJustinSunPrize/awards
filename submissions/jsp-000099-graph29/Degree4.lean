import Degree4Part4
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Erdos82Finite
open RegularCertificate

@[irreducible] def cert4 : FastCert := (.checkpoint 0 536870911 (.split 0 (.fill 0 (.empty 14 (.drop 1 (.checkpoint 67192833 214531573 (.drop 2 (.split 19 (.empty 16 (.empty 26 (.checkpoint 67717121 67718145 (.fill 11 (.bad 10))))) (.split 27 (.empty 16 (.checkpoint 201410561 209800433 (.empty 26 (.fill 11 (.bad 10))))) (.fill 11 (.checkpoint 75582465 79789553 (.fill 10 (.bad 16))))))))))) (.split 1 c4_4 (.split 2 c4_12 (.split 3 (.checkpoint 8 536870904 c4_25) (.checkpoint 0 536870896 c4_344))))))
theorem cert4_ok : fcheck 7 4 0 536870911 cert4 = true := by
  unfold cert4
  exact (accept_checkpoint (by decide +kernel) (accept_split (accept_fill (by decide +kernel) (accept_empty (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_split (accept_empty (by decide +kernel) (accept_empty (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_fill (by decide +kernel) (by decide +kernel))))) (accept_split (accept_empty (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_empty (by decide +kernel) (accept_fill (by decide +kernel) (by decide +kernel))))) (accept_fill (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_fill (by decide +kernel) (by decide +kernel))))))))))) (accept_split c4_4_ok (accept_split c4_12_ok (accept_split (accept_checkpoint (by decide +kernel) c4_25_ok) (accept_checkpoint (by decide +kernel) c4_344_ok))))))

theorem checked4 : fcheck 7 4 0 full cert4 = true := cert4_ok

theorem no_regular_4 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 4 :=
  fcheck_sound 4 cert4 checked4 T h

#print axioms no_regular_4
end Erdos82Finite
