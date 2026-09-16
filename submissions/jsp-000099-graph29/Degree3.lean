import Degree3Part2
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Erdos82Finite
open RegularCertificate

@[irreducible] def cert3 : FastCert := (.checkpoint 0 536870911 (.split 0 (.split 11 (.split 14 (.split 3 (.checkpoint 18441 536870911 (.empty 11 (.empty 14 (.bad 0)))) (.checkpoint 18433 536870903 (.split 9 (.empty 11 (.empty 14 (.bad 0))) c3_0))) (.fill 0 (.checkpoint 67176449 536854527 (.split 9 (.empty 9 (.empty 16 (.empty 26 (.checkpoint 67176961 67177987 (.fill 11 (.bad 10)))))) (.split 19 (.empty 16 (.empty 19 (.checkpoint 67700737 70060221 (.empty 26 .small)))) (.split 25 (.empty 16 (.checkpoint 100730881 128257279 (.empty 25 (.empty 26 .small)))) (.split 27 (.checkpoint 201394177 502775295 (.empty 16 (.empty 26 (.fill 11 (.bad 10))))) (.checkpoint 67176449 368557567 c3_1)))))))) (.fill 0 (.empty 14 (.checkpoint 67190785 214529527 (.empty 16 (.empty 26 .small)))))) c3_205))
theorem cert3_ok : fcheck 7 3 0 536870911 cert3 = true := by
  unfold cert3
  exact (accept_checkpoint (by decide +kernel) (accept_split (accept_split (accept_split (accept_split (accept_checkpoint (by decide +kernel) (accept_empty (by decide +kernel) (accept_empty (by decide +kernel) (by decide +kernel)))) (accept_checkpoint (by decide +kernel) (accept_split (accept_empty (by decide +kernel) (accept_empty (by decide +kernel) (by decide +kernel))) c3_0_ok))) (accept_fill (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_split (accept_empty (by decide +kernel) (accept_empty (by decide +kernel) (accept_empty (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_fill (by decide +kernel) (by decide +kernel)))))) (accept_split (accept_empty (by decide +kernel) (accept_empty (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_empty (by decide +kernel) (by decide +kernel))))) (accept_split (accept_empty (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_empty (by decide +kernel) (accept_empty (by decide +kernel) (by decide +kernel))))) (accept_split (accept_checkpoint (by decide +kernel) (accept_empty (by decide +kernel) (accept_empty (by decide +kernel) (accept_fill (by decide +kernel) (by decide +kernel))))) (accept_checkpoint (by decide +kernel) c3_1_ok)))))))) (accept_fill (by decide +kernel) (accept_empty (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_empty (by decide +kernel) (accept_empty (by decide +kernel) (by decide +kernel))))))) c3_205_ok))

theorem checked3 : fcheck 7 3 0 full cert3 = true := cert3_ok

theorem no_regular_3 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 3 :=
  fcheck_sound 3 cert3 checked3 T h

#print axioms no_regular_3
end Erdos82Finite
