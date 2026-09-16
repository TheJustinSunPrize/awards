import Degree7Part1
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Erdos82Finite
open RegularCertificate

@[irreducible] def cert7 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.split 3 (.checkpoint 8 536870904 (.fill 3 (.split 18 (.empty 18 (.fill 8 (.checkpoint 348474120 350080920 (.bad 26)))) (.split 24 (.empty 24 (.checkpoint 360729352 394349464 (.fill 8 (.bad 9)))) (.split 25 (.checkpoint 377506568 519831544 (.empty 25 (.bad 8))) (.checkpoint 343952136 486277112 (.fill 8 (.bad 26)))))))) (.checkpoint 0 536870896 c7_138))))))
theorem cert7_ok : fcheck 7 7 0 536870911 cert7 = true := by
  unfold cert7
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_split (accept_checkpoint (by decide +kernel) (accept_fill (by decide +kernel) (accept_split (accept_empty (by decide +kernel) (accept_fill (by decide +kernel) (accept_checkpoint (by decide +kernel) (by decide +kernel)))) (accept_split (accept_empty (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_fill (by decide +kernel) (by decide +kernel)))) (accept_split (accept_checkpoint (by decide +kernel) (accept_empty (by decide +kernel) (by decide +kernel))) (accept_checkpoint (by decide +kernel) (accept_fill (by decide +kernel) (by decide +kernel)))))))) (accept_checkpoint (by decide +kernel) c7_138_ok))))))

theorem checked7 : fcheck 7 7 0 full cert7 = true := cert7_ok

theorem no_regular_7 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 7 :=
  fcheck_sound 7 cert7 checked7 T h

#print axioms no_regular_7
end Erdos82Finite
