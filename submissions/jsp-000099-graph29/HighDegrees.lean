import CertificateSteps
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Erdos82Finite
open RegularCertificate
open RegularCertificate

@[irreducible] def cert11 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 11 (.drop 10 (.checkpoint 0 536866816 (.drop 14 (.drop 18 (.drop 12 (.drop 13 (.checkpoint 0 536576000 (.drop 16 (.drop 15 (.drop 17 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert11_ok : fcheck 7 11 0 536870911 cert11 = true := by
  unfold cert11
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked11 : fcheck 7 11 0 full cert11 = true := cert11_ok

theorem no_regular_11 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 11 :=
  fcheck_sound 11 cert11 checked11 T h

#print axioms no_regular_11

open RegularCertificate

@[irreducible] def cert12 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert12_ok : fcheck 7 12 0 536870911 cert12 = true := by
  unfold cert12
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked12 : fcheck 7 12 0 full cert12 = true := cert12_ok

theorem no_regular_12 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 12 :=
  fcheck_sound 12 cert12 checked12 T h

#print axioms no_regular_12

open RegularCertificate

@[irreducible] def cert13 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert13_ok : fcheck 7 13 0 536870911 cert13 = true := by
  unfold cert13
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked13 : fcheck 7 13 0 full cert13 = true := cert13_ok

theorem no_regular_13 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 13 :=
  fcheck_sound 13 cert13 checked13 T h

#print axioms no_regular_13

open RegularCertificate

@[irreducible] def cert14 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert14_ok : fcheck 7 14 0 536870911 cert14 = true := by
  unfold cert14
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked14 : fcheck 7 14 0 full cert14 = true := cert14_ok

theorem no_regular_14 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 14 :=
  fcheck_sound 14 cert14 checked14 T h

#print axioms no_regular_14

open RegularCertificate

@[irreducible] def cert15 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert15_ok : fcheck 7 15 0 536870911 cert15 = true := by
  unfold cert15
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked15 : fcheck 7 15 0 full cert15 = true := cert15_ok

theorem no_regular_15 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 15 :=
  fcheck_sound 15 cert15 checked15 T h

#print axioms no_regular_15

open RegularCertificate

@[irreducible] def cert16 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert16_ok : fcheck 7 16 0 536870911 cert16 = true := by
  unfold cert16
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked16 : fcheck 7 16 0 full cert16 = true := cert16_ok

theorem no_regular_16 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 16 :=
  fcheck_sound 16 cert16 checked16 T h

#print axioms no_regular_16

open RegularCertificate

@[irreducible] def cert17 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert17_ok : fcheck 7 17 0 536870911 cert17 = true := by
  unfold cert17
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked17 : fcheck 7 17 0 full cert17 = true := cert17_ok

theorem no_regular_17 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 17 :=
  fcheck_sound 17 cert17 checked17 T h

#print axioms no_regular_17

open RegularCertificate

@[irreducible] def cert18 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert18_ok : fcheck 7 18 0 536870911 cert18 = true := by
  unfold cert18
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked18 : fcheck 7 18 0 full cert18 = true := cert18_ok

theorem no_regular_18 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 18 :=
  fcheck_sound 18 cert18 checked18 T h

#print axioms no_regular_18

open RegularCertificate

@[irreducible] def cert19 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert19_ok : fcheck 7 19 0 536870911 cert19 = true := by
  unfold cert19
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked19 : fcheck 7 19 0 full cert19 = true := cert19_ok

theorem no_regular_19 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 19 :=
  fcheck_sound 19 cert19 checked19 T h

#print axioms no_regular_19

open RegularCertificate

@[irreducible] def cert20 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert20_ok : fcheck 7 20 0 536870911 cert20 = true := by
  unfold cert20
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked20 : fcheck 7 20 0 full cert20 = true := cert20_ok

theorem no_regular_20 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 20 :=
  fcheck_sound 20 cert20 checked20 T h

#print axioms no_regular_20

open RegularCertificate

@[irreducible] def cert21 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert21_ok : fcheck 7 21 0 536870911 cert21 = true := by
  unfold cert21
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked21 : fcheck 7 21 0 full cert21 = true := cert21_ok

theorem no_regular_21 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 21 :=
  fcheck_sound 21 cert21 checked21 T h

#print axioms no_regular_21

open RegularCertificate

@[irreducible] def cert22 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert22_ok : fcheck 7 22 0 536870911 cert22 = true := by
  unfold cert22
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked22 : fcheck 7 22 0 full cert22 = true := cert22_ok

theorem no_regular_22 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 22 :=
  fcheck_sound 22 cert22 checked22 T h

#print axioms no_regular_22

open RegularCertificate

@[irreducible] def cert23 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert23_ok : fcheck 7 23 0 536870911 cert23 = true := by
  unfold cert23
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked23 : fcheck 7 23 0 full cert23 = true := cert23_ok

theorem no_regular_23 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 23 :=
  fcheck_sound 23 cert23 checked23 T h

#print axioms no_regular_23

open RegularCertificate

@[irreducible] def cert24 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert24_ok : fcheck 7 24 0 536870911 cert24 = true := by
  unfold cert24
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked24 : fcheck 7 24 0 full cert24 = true := cert24_ok

theorem no_regular_24 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 24 :=
  fcheck_sound 24 cert24 checked24 T h

#print axioms no_regular_24

open RegularCertificate

@[irreducible] def cert25 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert25_ok : fcheck 7 25 0 536870911 cert25 = true := by
  unfold cert25
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked25 : fcheck 7 25 0 full cert25 = true := cert25_ok

theorem no_regular_25 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 25 :=
  fcheck_sound 25 cert25 checked25 T h

#print axioms no_regular_25

open RegularCertificate

@[irreducible] def cert26 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert26_ok : fcheck 7 26 0 536870911 cert26 = true := by
  unfold cert26
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked26 : fcheck 7 26 0 full cert26 = true := cert26_ok

theorem no_regular_26 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 26 :=
  fcheck_sound 26 cert26 checked26 T h

#print axioms no_regular_26

open RegularCertificate

@[irreducible] def cert27 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert27_ok : fcheck 7 27 0 536870911 cert27 = true := by
  unfold cert27
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked27 : fcheck 7 27 0 full cert27 = true := cert27_ok

theorem no_regular_27 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 27 :=
  fcheck_sound 27 cert27 checked27 T h

#print axioms no_regular_27

open RegularCertificate

@[irreducible] def cert28 : FastCert := (.checkpoint 0 536870911 (.drop 0 (.drop 1 (.drop 2 (.drop 3 (.checkpoint 0 536870896 (.drop 4 (.drop 5 (.drop 6 (.drop 7 (.checkpoint 0 536870656 (.drop 8 (.drop 9 (.drop 10 (.drop 11 (.checkpoint 0 536866816 (.drop 12 (.drop 13 (.drop 14 (.drop 15 (.checkpoint 0 536805376 (.drop 16 (.drop 17 (.drop 18 (.drop 19 (.checkpoint 0 535822336 (.drop 20 (.drop 21 (.drop 22 .small)))))))))))))))))))))))))))))
theorem cert28_ok : fcheck 7 28 0 536870911 cert28 = true := by
  unfold cert28
  exact (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_checkpoint (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (accept_drop (by decide +kernel) (by decide +kernel))))))))))))))))))))))))))))))

theorem checked28 : fcheck 7 28 0 full cert28 = true := cert28_ok

theorem no_regular_28 (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T 28 :=
  fcheck_sound 28 cert28 checked28 T h

#print axioms no_regular_28

end Erdos82Finite
