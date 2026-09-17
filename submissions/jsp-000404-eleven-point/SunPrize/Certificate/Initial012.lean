import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory004
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule8328 (p3045 p4982 : Prop) (h : (p3045 ↔ p4982)) : (¬ p3045) ∨ (p4982) := by
  classical
  tauto

theorem initial8328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3045)) ∨ (meaning t m 4982) := by
  have source := ElevenTheory.theory1214 t (m.theta 0 5) (m.theta 0 7) (m.theta 5 7)
  exact rule8328 (meaning t m 3045) (meaning t m 4982) source

theorem rule8330 (p2651 p2657 : Prop) (h : (¬ p2657) ∨ (¬ p2651)) : (¬ p2651) ∨ (¬ p2657) := by
  classical
  tauto

theorem initial8330 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2657)) := by
  have source := ElevenTheory.theory1215 (m.theta 0 3) (m.theta 3 4)
  exact rule8330 (meaning t m 2651) (meaning t m 2657) source

theorem rule8331 (p2027 p2230 p2440 p2663 p2963 p4972 : Prop) (h : (¬ p2440) ∨ (¬ p2230) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p4972) ∨ (¬ p2663)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p2963) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial8331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory1216 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5)
  exact rule8331 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2663) (meaning t m 2963) (meaning t m 4972) source

theorem rule8332 (p3923 p4371 p4993 p4994 p4995 : Prop) : (p4371) ∨ (¬ (p4371 ∧ p4993 ∧ p3923 ∧ p4994 ∧ p4995)) := by
  classical
  tauto

theorem initial8332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4371) ∨ (¬ (meaning t m 4992)) := by
  exact rule8332 (meaning t m 3923) (meaning t m 4371) (meaning t m 4993) (meaning t m 4994) (meaning t m 4995)

theorem rule8333 (p3923 p4371 p4993 p4994 p4995 : Prop) : (¬ (p4371 ∧ p4993 ∧ p3923 ∧ p4994 ∧ p4995)) ∨ (p4993) := by
  classical
  tauto

theorem initial8333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4992)) ∨ (meaning t m 4993) := by
  exact rule8333 (meaning t m 3923) (meaning t m 4371) (meaning t m 4993) (meaning t m 4994) (meaning t m 4995)

theorem rule8334 (p3923 p4371 p4993 p4994 p4995 : Prop) : (p3923) ∨ (¬ (p4371 ∧ p4993 ∧ p3923 ∧ p4994 ∧ p4995)) := by
  classical
  tauto

theorem initial8334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3923) ∨ (¬ (meaning t m 4992)) := by
  exact rule8334 (meaning t m 3923) (meaning t m 4371) (meaning t m 4993) (meaning t m 4994) (meaning t m 4995)

theorem rule8335 (p3923 p4371 p4993 p4994 p4995 : Prop) : (¬ (p4371 ∧ p4993 ∧ p3923 ∧ p4994 ∧ p4995)) ∨ (p4994) := by
  classical
  tauto

theorem initial8335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4992)) ∨ (meaning t m 4994) := by
  exact rule8335 (meaning t m 3923) (meaning t m 4371) (meaning t m 4993) (meaning t m 4994) (meaning t m 4995)

theorem rule8336 (p3923 p4371 p4993 p4994 p4995 : Prop) : (¬ (p4371 ∧ p4993 ∧ p3923 ∧ p4994 ∧ p4995)) ∨ (p4995) := by
  classical
  tauto

theorem initial8336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4992)) ∨ (meaning t m 4995) := by
  exact rule8336 (meaning t m 3923) (meaning t m 4371) (meaning t m 4993) (meaning t m 4994) (meaning t m 4995)

theorem rule8338 (p3063 p4317 p4318 p4997 p4998 : Prop) : (p4318) ∨ (¬ (p4318 ∧ p4317 ∧ p3063 ∧ p4997 ∧ p4998)) := by
  classical
  tauto

theorem initial8338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4318) ∨ (¬ (meaning t m 4996)) := by
  exact rule8338 (meaning t m 3063) (meaning t m 4317) (meaning t m 4318) (meaning t m 4997) (meaning t m 4998)

theorem rule8339 (p3063 p4317 p4318 p4997 p4998 : Prop) : (p4317) ∨ (¬ (p4318 ∧ p4317 ∧ p3063 ∧ p4997 ∧ p4998)) := by
  classical
  tauto

theorem initial8339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4317) ∨ (¬ (meaning t m 4996)) := by
  exact rule8339 (meaning t m 3063) (meaning t m 4317) (meaning t m 4318) (meaning t m 4997) (meaning t m 4998)

theorem rule8340 (p3063 p4317 p4318 p4997 p4998 : Prop) : (p3063) ∨ (¬ (p4318 ∧ p4317 ∧ p3063 ∧ p4997 ∧ p4998)) := by
  classical
  tauto

theorem initial8340 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3063) ∨ (¬ (meaning t m 4996)) := by
  exact rule8340 (meaning t m 3063) (meaning t m 4317) (meaning t m 4318) (meaning t m 4997) (meaning t m 4998)

theorem rule8342 (p3063 p4317 p4318 p4997 p4998 : Prop) : (¬ (p4318 ∧ p4317 ∧ p3063 ∧ p4997 ∧ p4998)) ∨ (p4998) := by
  classical
  tauto

theorem initial8342 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4996)) ∨ (meaning t m 4998) := by
  exact rule8342 (meaning t m 3063) (meaning t m 4317) (meaning t m 4318) (meaning t m 4997) (meaning t m 4998)

theorem rule8346 (p4992 p4996 : Prop) : (¬ (p4992 ∨ p4996)) ∨ (p4992) ∨ (p4996) := by
  classical
  tauto

theorem initial8346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4991)) ∨ (meaning t m 4992) ∨ (meaning t m 4996) := by
  exact rule8346 (meaning t m 4992) (meaning t m 4996)

theorem rule8347 (p3057 p4991 : Prop) (h : (p3057 ↔ p4991)) : (¬ p3057) ∨ (p4991) := by
  classical
  tauto

theorem initial8347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3057)) ∨ (meaning t m 4991) := by
  have source := ElevenTheory.theory1217 t (m.theta 1 6) (m.theta 1 8) (m.theta 6 8)
  exact rule8347 (meaning t m 3057) (meaning t m 4991) source

theorem rule8349 (p3438 p3440 p4261 p5001 p5002 : Prop) : (p3440) ∨ (¬ (p3440 ∧ p3438 ∧ p4261 ∧ p5001 ∧ p5002)) := by
  classical
  tauto

theorem initial8349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3440) ∨ (¬ (meaning t m 5000)) := by
  exact rule8349 (meaning t m 3438) (meaning t m 3440) (meaning t m 4261) (meaning t m 5001) (meaning t m 5002)

theorem rule8350 (p3438 p3440 p4261 p5001 p5002 : Prop) : (p3438) ∨ (¬ (p3440 ∧ p3438 ∧ p4261 ∧ p5001 ∧ p5002)) := by
  classical
  tauto

theorem initial8350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3438) ∨ (¬ (meaning t m 5000)) := by
  exact rule8350 (meaning t m 3438) (meaning t m 3440) (meaning t m 4261) (meaning t m 5001) (meaning t m 5002)

theorem rule8351 (p3438 p3440 p4261 p5001 p5002 : Prop) : (p4261) ∨ (¬ (p3440 ∧ p3438 ∧ p4261 ∧ p5001 ∧ p5002)) := by
  classical
  tauto

theorem initial8351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4261) ∨ (¬ (meaning t m 5000)) := by
  exact rule8351 (meaning t m 3438) (meaning t m 3440) (meaning t m 4261) (meaning t m 5001) (meaning t m 5002)

theorem rule8353 (p3438 p3440 p4261 p5001 p5002 : Prop) : (¬ (p3440 ∧ p3438 ∧ p4261 ∧ p5001 ∧ p5002)) ∨ (p5002) := by
  classical
  tauto

theorem initial8353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5000)) ∨ (meaning t m 5002) := by
  exact rule8353 (meaning t m 3438) (meaning t m 3440) (meaning t m 4261) (meaning t m 5001) (meaning t m 5002)

theorem rule8355 (p3073 p4351 p4352 p5004 p5005 : Prop) : (p4352) ∨ (¬ (p4352 ∧ p4351 ∧ p3073 ∧ p5004 ∧ p5005)) := by
  classical
  tauto

theorem initial8355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4352) ∨ (¬ (meaning t m 5003)) := by
  exact rule8355 (meaning t m 3073) (meaning t m 4351) (meaning t m 4352) (meaning t m 5004) (meaning t m 5005)

theorem rule8356 (p3073 p4351 p4352 p5004 p5005 : Prop) : (p4351) ∨ (¬ (p4352 ∧ p4351 ∧ p3073 ∧ p5004 ∧ p5005)) := by
  classical
  tauto

theorem initial8356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4351) ∨ (¬ (meaning t m 5003)) := by
  exact rule8356 (meaning t m 3073) (meaning t m 4351) (meaning t m 4352) (meaning t m 5004) (meaning t m 5005)

theorem rule8357 (p3073 p4351 p4352 p5004 p5005 : Prop) : (p3073) ∨ (¬ (p4352 ∧ p4351 ∧ p3073 ∧ p5004 ∧ p5005)) := by
  classical
  tauto

theorem initial8357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3073) ∨ (¬ (meaning t m 5003)) := by
  exact rule8357 (meaning t m 3073) (meaning t m 4351) (meaning t m 4352) (meaning t m 5004) (meaning t m 5005)

theorem rule8363 (p5000 p5003 : Prop) : (¬ (p5000 ∨ p5003)) ∨ (p5000) ∨ (p5003) := by
  classical
  tauto

theorem initial8363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4999)) ∨ (meaning t m 5000) ∨ (meaning t m 5003) := by
  exact rule8363 (meaning t m 5000) (meaning t m 5003)

theorem rule8364 (p3067 p4999 : Prop) (h : (p3067 ↔ p4999)) : (¬ p3067) ∨ (p4999) := by
  classical
  tauto

theorem initial8364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3067)) ∨ (meaning t m 4999) := by
  have source := ElevenTheory.theory1218 t (m.theta 1 8) (m.theta 1 9) (m.theta 8 9)
  exact rule8364 (meaning t m 3067) (meaning t m 4999) source

theorem rule8366 (p2027 p2459 p2881 p3544 p4261 p4911 : Prop) (h : p2027 ∨ (¬ p4911) ∨ (¬ p4261) ∨ (¬ p2881) ∨ (¬ p2459) ∨ (¬ p3544)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3544) ∨ (¬ p4261) ∨ (¬ p4911) := by
  classical
  tauto

theorem initial8366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4911)) := by
  have source := ElevenTheory.theory1219 t (m.theta 1 7) (m.theta 1 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule8366 (meaning t m 2027) (meaning t m 2459) (meaning t m 2881) (meaning t m 3544) (meaning t m 4261) (meaning t m 4911) source

theorem rule8367 (p3878 p4256 p4437 p5008 p5009 : Prop) : (p3878) ∨ (¬ (p3878 ∧ p4437 ∧ p4256 ∧ p5008 ∧ p5009)) := by
  classical
  tauto

theorem initial8367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3878) ∨ (¬ (meaning t m 5007)) := by
  exact rule8367 (meaning t m 3878) (meaning t m 4256) (meaning t m 4437) (meaning t m 5008) (meaning t m 5009)

theorem rule8368 (p3878 p4256 p4437 p5008 p5009 : Prop) : (p4437) ∨ (¬ (p3878 ∧ p4437 ∧ p4256 ∧ p5008 ∧ p5009)) := by
  classical
  tauto

theorem initial8368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4437) ∨ (¬ (meaning t m 5007)) := by
  exact rule8368 (meaning t m 3878) (meaning t m 4256) (meaning t m 4437) (meaning t m 5008) (meaning t m 5009)

theorem rule8369 (p3878 p4256 p4437 p5008 p5009 : Prop) : (p4256) ∨ (¬ (p3878 ∧ p4437 ∧ p4256 ∧ p5008 ∧ p5009)) := by
  classical
  tauto

theorem initial8369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4256) ∨ (¬ (meaning t m 5007)) := by
  exact rule8369 (meaning t m 3878) (meaning t m 4256) (meaning t m 4437) (meaning t m 5008) (meaning t m 5009)

theorem rule8370 (p3878 p4256 p4437 p5008 p5009 : Prop) : (¬ (p3878 ∧ p4437 ∧ p4256 ∧ p5008 ∧ p5009)) ∨ (p5008) := by
  classical
  tauto

theorem initial8370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5007)) ∨ (meaning t m 5008) := by
  exact rule8370 (meaning t m 3878) (meaning t m 4256) (meaning t m 4437) (meaning t m 5008) (meaning t m 5009)

theorem rule8371 (p3878 p4256 p4437 p5008 p5009 : Prop) : (¬ (p3878 ∧ p4437 ∧ p4256 ∧ p5008 ∧ p5009)) ∨ (p5009) := by
  classical
  tauto

theorem initial8371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5007)) ∨ (meaning t m 5009) := by
  exact rule8371 (meaning t m 3878) (meaning t m 4256) (meaning t m 4437) (meaning t m 5008) (meaning t m 5009)

theorem rule8373 (p3083 p4121 p4346 p5011 p5012 : Prop) : (p4346) ∨ (¬ (p4346 ∧ p4121 ∧ p3083 ∧ p5011 ∧ p5012)) := by
  classical
  tauto

theorem initial8373 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4346) ∨ (¬ (meaning t m 5010)) := by
  exact rule8373 (meaning t m 3083) (meaning t m 4121) (meaning t m 4346) (meaning t m 5011) (meaning t m 5012)

theorem rule8374 (p3083 p4121 p4346 p5011 p5012 : Prop) : (p4121) ∨ (¬ (p4346 ∧ p4121 ∧ p3083 ∧ p5011 ∧ p5012)) := by
  classical
  tauto

theorem initial8374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4121) ∨ (¬ (meaning t m 5010)) := by
  exact rule8374 (meaning t m 3083) (meaning t m 4121) (meaning t m 4346) (meaning t m 5011) (meaning t m 5012)

theorem rule8375 (p3083 p4121 p4346 p5011 p5012 : Prop) : (p3083) ∨ (¬ (p4346 ∧ p4121 ∧ p3083 ∧ p5011 ∧ p5012)) := by
  classical
  tauto

theorem initial8375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3083) ∨ (¬ (meaning t m 5010)) := by
  exact rule8375 (meaning t m 3083) (meaning t m 4121) (meaning t m 4346) (meaning t m 5011) (meaning t m 5012)

theorem rule8376 (p3083 p4121 p4346 p5011 p5012 : Prop) : (¬ (p4346 ∧ p4121 ∧ p3083 ∧ p5011 ∧ p5012)) ∨ (p5011) := by
  classical
  tauto

theorem initial8376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5010)) ∨ (meaning t m 5011) := by
  exact rule8376 (meaning t m 3083) (meaning t m 4121) (meaning t m 4346) (meaning t m 5011) (meaning t m 5012)

theorem rule8381 (p5007 p5010 : Prop) : (¬ (p5007 ∨ p5010)) ∨ (p5007) ∨ (p5010) := by
  classical
  tauto

theorem initial8381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5006)) ∨ (meaning t m 5007) ∨ (meaning t m 5010) := by
  exact rule8381 (meaning t m 5007) (meaning t m 5010)

theorem rule8382 (p3077 p5006 : Prop) (h : (p3077 ↔ p5006)) : (¬ p3077) ∨ (p5006) := by
  classical
  tauto

theorem initial8382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3077)) ∨ (meaning t m 5006) := by
  have source := ElevenTheory.theory1220 t (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule8382 (meaning t m 3077) (meaning t m 5006) source

theorem rule8384 (p3591 p5015 p5016 p5017 p5018 : Prop) : (¬ (p5015 ∧ p5016 ∧ p3591 ∧ p5017 ∧ p5018)) ∨ (p5015) := by
  classical
  tauto

theorem initial8384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5014)) ∨ (meaning t m 5015) := by
  exact rule8384 (meaning t m 3591) (meaning t m 5015) (meaning t m 5016) (meaning t m 5017) (meaning t m 5018)

theorem rule8385 (p3591 p5015 p5016 p5017 p5018 : Prop) : (¬ (p5015 ∧ p5016 ∧ p3591 ∧ p5017 ∧ p5018)) ∨ (p5016) := by
  classical
  tauto

theorem initial8385 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5014)) ∨ (meaning t m 5016) := by
  exact rule8385 (meaning t m 3591) (meaning t m 5015) (meaning t m 5016) (meaning t m 5017) (meaning t m 5018)

theorem rule8386 (p3591 p5015 p5016 p5017 p5018 : Prop) : (p3591) ∨ (¬ (p5015 ∧ p5016 ∧ p3591 ∧ p5017 ∧ p5018)) := by
  classical
  tauto

theorem initial8386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3591) ∨ (¬ (meaning t m 5014)) := by
  exact rule8386 (meaning t m 3591) (meaning t m 5015) (meaning t m 5016) (meaning t m 5017) (meaning t m 5018)

theorem rule8387 (p3591 p5015 p5016 p5017 p5018 : Prop) : (¬ (p5015 ∧ p5016 ∧ p3591 ∧ p5017 ∧ p5018)) ∨ (p5017) := by
  classical
  tauto

theorem initial8387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5014)) ∨ (meaning t m 5017) := by
  exact rule8387 (meaning t m 3591) (meaning t m 5015) (meaning t m 5016) (meaning t m 5017) (meaning t m 5018)

theorem rule8390 (p3093 p3204 p5020 p5021 p5022 : Prop) : (p3204) ∨ (¬ (p3204 ∧ p5020 ∧ p3093 ∧ p5021 ∧ p5022)) := by
  classical
  tauto

theorem initial8390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3204) ∨ (¬ (meaning t m 5019)) := by
  exact rule8390 (meaning t m 3093) (meaning t m 3204) (meaning t m 5020) (meaning t m 5021) (meaning t m 5022)

theorem rule8391 (p3093 p3204 p5020 p5021 p5022 : Prop) : (¬ (p3204 ∧ p5020 ∧ p3093 ∧ p5021 ∧ p5022)) ∨ (p5020) := by
  classical
  tauto

theorem initial8391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5019)) ∨ (meaning t m 5020) := by
  exact rule8391 (meaning t m 3093) (meaning t m 3204) (meaning t m 5020) (meaning t m 5021) (meaning t m 5022)

theorem rule8392 (p3093 p3204 p5020 p5021 p5022 : Prop) : (p3093) ∨ (¬ (p3204 ∧ p5020 ∧ p3093 ∧ p5021 ∧ p5022)) := by
  classical
  tauto

theorem initial8392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3093) ∨ (¬ (meaning t m 5019)) := by
  exact rule8392 (meaning t m 3093) (meaning t m 3204) (meaning t m 5020) (meaning t m 5021) (meaning t m 5022)

theorem rule8393 (p3093 p3204 p5020 p5021 p5022 : Prop) : (¬ (p3204 ∧ p5020 ∧ p3093 ∧ p5021 ∧ p5022)) ∨ (p5021) := by
  classical
  tauto

theorem initial8393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5019)) ∨ (meaning t m 5021) := by
  exact rule8393 (meaning t m 3093) (meaning t m 3204) (meaning t m 5020) (meaning t m 5021) (meaning t m 5022)

theorem rule8394 (p3093 p3204 p5020 p5021 p5022 : Prop) : (¬ (p3204 ∧ p5020 ∧ p3093 ∧ p5021 ∧ p5022)) ∨ (p5022) := by
  classical
  tauto

theorem initial8394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5019)) ∨ (meaning t m 5022) := by
  exact rule8394 (meaning t m 3093) (meaning t m 3204) (meaning t m 5020) (meaning t m 5021) (meaning t m 5022)

theorem rule8398 (p5014 p5019 : Prop) : (¬ (p5014 ∨ p5019)) ∨ (p5014) ∨ (p5019) := by
  classical
  tauto

theorem initial8398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5013)) ∨ (meaning t m 5014) ∨ (meaning t m 5019) := by
  exact rule8398 (meaning t m 5014) (meaning t m 5019)

theorem rule8399 (p3087 p5013 : Prop) (h : (p3087 ↔ p5013)) : (¬ p3087) ∨ (p5013) := by
  classical
  tauto

theorem initial8399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3087)) ∨ (meaning t m 5013) := by
  have source := ElevenTheory.theory1221 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 6)
  exact rule8399 (meaning t m 3087) (meaning t m 5013) source

theorem rule8401 (p3093 p3591 : Prop) (h : (¬ p3591) ∨ (¬ p3093)) : (¬ p3093) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial8401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory1222 (m.theta 0 1) (m.theta 1 6)
  exact rule8401 (meaning t m 3093) (meaning t m 3591) source

theorem rule8402 (p2027 p2598 p2745 p3365 p3683 p4111 : Prop) (h : (¬ p4111) ∨ (¬ p3365) ∨ (¬ p3683) ∨ p2027 ∨ (¬ p2745) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2745) ∨ (¬ p3365) ∨ (¬ p3683) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial8402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory1223 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4)
  exact rule8402 (meaning t m 2027) (meaning t m 2598) (meaning t m 2745) (meaning t m 3365) (meaning t m 3683) (meaning t m 4111) source

theorem rule8403 (p4385 p5025 p5026 p5027 p5028 : Prop) : (¬ (p5025 ∧ p5026 ∧ p4385 ∧ p5027 ∧ p5028)) ∨ (p5025) := by
  classical
  tauto

theorem initial8403 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5024)) ∨ (meaning t m 5025) := by
  exact rule8403 (meaning t m 4385) (meaning t m 5025) (meaning t m 5026) (meaning t m 5027) (meaning t m 5028)

theorem rule8405 (p4385 p5025 p5026 p5027 p5028 : Prop) : (p4385) ∨ (¬ (p5025 ∧ p5026 ∧ p4385 ∧ p5027 ∧ p5028)) := by
  classical
  tauto

theorem initial8405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4385) ∨ (¬ (meaning t m 5024)) := by
  exact rule8405 (meaning t m 4385) (meaning t m 5025) (meaning t m 5026) (meaning t m 5027) (meaning t m 5028)

theorem rule8409 (p3105 p5030 p5031 p5032 p5033 : Prop) : (¬ (p5030 ∧ p5031 ∧ p3105 ∧ p5032 ∧ p5033)) ∨ (p5030) := by
  classical
  tauto

theorem initial8409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5029)) ∨ (meaning t m 5030) := by
  exact rule8409 (meaning t m 3105) (meaning t m 5030) (meaning t m 5031) (meaning t m 5032) (meaning t m 5033)

theorem rule8410 (p3105 p5030 p5031 p5032 p5033 : Prop) : (¬ (p5030 ∧ p5031 ∧ p3105 ∧ p5032 ∧ p5033)) ∨ (p5031) := by
  classical
  tauto

theorem initial8410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5029)) ∨ (meaning t m 5031) := by
  exact rule8410 (meaning t m 3105) (meaning t m 5030) (meaning t m 5031) (meaning t m 5032) (meaning t m 5033)

theorem rule8411 (p3105 p5030 p5031 p5032 p5033 : Prop) : (p3105) ∨ (¬ (p5030 ∧ p5031 ∧ p3105 ∧ p5032 ∧ p5033)) := by
  classical
  tauto

theorem initial8411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3105) ∨ (¬ (meaning t m 5029)) := by
  exact rule8411 (meaning t m 3105) (meaning t m 5030) (meaning t m 5031) (meaning t m 5032) (meaning t m 5033)

theorem rule8417 (p5024 p5029 : Prop) : (¬ (p5024 ∨ p5029)) ∨ (p5024) ∨ (p5029) := by
  classical
  tauto

theorem initial8417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5023)) ∨ (meaning t m 5024) ∨ (meaning t m 5029) := by
  exact rule8417 (meaning t m 5024) (meaning t m 5029)

theorem rule8418 (p3099 p5023 : Prop) (h : (p3099 ↔ p5023)) : (¬ p3099) ∨ (p5023) := by
  classical
  tauto

theorem initial8418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3099)) ∨ (meaning t m 5023) := by
  have source := ElevenTheory.theory1224 t (m.theta 2 5) (m.theta 2 9) (m.theta 5 9)
  exact rule8418 (meaning t m 3099) (meaning t m 5023) source

theorem rule8420 (p4040 p4208 p4314 p4369 p5036 : Prop) : (p4314) ∨ (¬ (p4314 ∧ p4040 ∧ p4208 ∧ p5036 ∧ p4369)) := by
  classical
  tauto

theorem initial8420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4314) ∨ (¬ (meaning t m 5035)) := by
  exact rule8420 (meaning t m 4040) (meaning t m 4208) (meaning t m 4314) (meaning t m 4369) (meaning t m 5036)

theorem rule8421 (p4040 p4208 p4314 p4369 p5036 : Prop) : (p4040) ∨ (¬ (p4314 ∧ p4040 ∧ p4208 ∧ p5036 ∧ p4369)) := by
  classical
  tauto

theorem initial8421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4040) ∨ (¬ (meaning t m 5035)) := by
  exact rule8421 (meaning t m 4040) (meaning t m 4208) (meaning t m 4314) (meaning t m 4369) (meaning t m 5036)

theorem rule8422 (p4040 p4208 p4314 p4369 p5036 : Prop) : (p4208) ∨ (¬ (p4314 ∧ p4040 ∧ p4208 ∧ p5036 ∧ p4369)) := by
  classical
  tauto

theorem initial8422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4208) ∨ (¬ (meaning t m 5035)) := by
  exact rule8422 (meaning t m 4040) (meaning t m 4208) (meaning t m 4314) (meaning t m 4369) (meaning t m 5036)

theorem rule8426 (p3115 p4039 p5038 p5039 p5040 : Prop) : (p4039) ∨ (¬ (p4039 ∧ p5038 ∧ p3115 ∧ p5039 ∧ p5040)) := by
  classical
  tauto

theorem initial8426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4039) ∨ (¬ (meaning t m 5037)) := by
  exact rule8426 (meaning t m 3115) (meaning t m 4039) (meaning t m 5038) (meaning t m 5039) (meaning t m 5040)

theorem rule8427 (p3115 p4039 p5038 p5039 p5040 : Prop) : (¬ (p4039 ∧ p5038 ∧ p3115 ∧ p5039 ∧ p5040)) ∨ (p5038) := by
  classical
  tauto

theorem initial8427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5037)) ∨ (meaning t m 5038) := by
  exact rule8427 (meaning t m 3115) (meaning t m 4039) (meaning t m 5038) (meaning t m 5039) (meaning t m 5040)

theorem rule8428 (p3115 p4039 p5038 p5039 p5040 : Prop) : (p3115) ∨ (¬ (p4039 ∧ p5038 ∧ p3115 ∧ p5039 ∧ p5040)) := by
  classical
  tauto

theorem initial8428 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3115) ∨ (¬ (meaning t m 5037)) := by
  exact rule8428 (meaning t m 3115) (meaning t m 4039) (meaning t m 5038) (meaning t m 5039) (meaning t m 5040)

theorem rule8434 (p5035 p5037 : Prop) : (¬ (p5035 ∨ p5037)) ∨ (p5035) ∨ (p5037) := by
  classical
  tauto

theorem initial8434 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5034)) ∨ (meaning t m 5035) ∨ (meaning t m 5037) := by
  exact rule8434 (meaning t m 5035) (meaning t m 5037)

theorem rule8435 (p3109 p5034 : Prop) (h : (p3109 ↔ p5034)) : (¬ p3109) ∨ (p5034) := by
  classical
  tauto

theorem initial8435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3109)) ∨ (meaning t m 5034) := by
  have source := ElevenTheory.theory1225 t (m.theta 3 5) (m.theta 3 9) (m.theta 5 9)
  exact rule8435 (meaning t m 3109) (meaning t m 5034) source

theorem rule8437 (p3744 p4033 p4205 p4397 p5043 : Prop) : (p4205) ∨ (¬ (p4205 ∧ p4033 ∧ p3744 ∧ p5043 ∧ p4397)) := by
  classical
  tauto

theorem initial8437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4205) ∨ (¬ (meaning t m 5042)) := by
  exact rule8437 (meaning t m 3744) (meaning t m 4033) (meaning t m 4205) (meaning t m 4397) (meaning t m 5043)

theorem rule8438 (p3744 p4033 p4205 p4397 p5043 : Prop) : (p4033) ∨ (¬ (p4205 ∧ p4033 ∧ p3744 ∧ p5043 ∧ p4397)) := by
  classical
  tauto

theorem initial8438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4033) ∨ (¬ (meaning t m 5042)) := by
  exact rule8438 (meaning t m 3744) (meaning t m 4033) (meaning t m 4205) (meaning t m 4397) (meaning t m 5043)

theorem rule8439 (p3744 p4033 p4205 p4397 p5043 : Prop) : (p3744) ∨ (¬ (p4205 ∧ p4033 ∧ p3744 ∧ p5043 ∧ p4397)) := by
  classical
  tauto

theorem initial8439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3744) ∨ (¬ (meaning t m 5042)) := by
  exact rule8439 (meaning t m 3744) (meaning t m 4033) (meaning t m 4205) (meaning t m 4397) (meaning t m 5043)

theorem rule8440 (p3744 p4033 p4205 p4397 p5043 : Prop) : (¬ (p4205 ∧ p4033 ∧ p3744 ∧ p5043 ∧ p4397)) ∨ (p5043) := by
  classical
  tauto

theorem initial8440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5042)) ∨ (meaning t m 5043) := by
  exact rule8440 (meaning t m 3744) (meaning t m 4033) (meaning t m 4205) (meaning t m 4397) (meaning t m 5043)

theorem rule8441 (p3744 p4033 p4205 p4397 p5043 : Prop) : (p4397) ∨ (¬ (p4205 ∧ p4033 ∧ p3744 ∧ p5043 ∧ p4397)) := by
  classical
  tauto

theorem initial8441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4397) ∨ (¬ (meaning t m 5042)) := by
  exact rule8441 (meaning t m 3744) (meaning t m 4033) (meaning t m 4205) (meaning t m 4397) (meaning t m 5043)

theorem rule8443 (p3125 p4334 p4368 p5045 p5046 : Prop) : (¬ (p5045 ∧ p4334 ∧ p3125 ∧ p5046 ∧ p4368)) ∨ (p5045) := by
  classical
  tauto

theorem initial8443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5044)) ∨ (meaning t m 5045) := by
  exact rule8443 (meaning t m 3125) (meaning t m 4334) (meaning t m 4368) (meaning t m 5045) (meaning t m 5046)

theorem rule8444 (p3125 p4334 p4368 p5045 p5046 : Prop) : (p4334) ∨ (¬ (p5045 ∧ p4334 ∧ p3125 ∧ p5046 ∧ p4368)) := by
  classical
  tauto

theorem initial8444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4334) ∨ (¬ (meaning t m 5044)) := by
  exact rule8444 (meaning t m 3125) (meaning t m 4334) (meaning t m 4368) (meaning t m 5045) (meaning t m 5046)

theorem rule8445 (p3125 p4334 p4368 p5045 p5046 : Prop) : (p3125) ∨ (¬ (p5045 ∧ p4334 ∧ p3125 ∧ p5046 ∧ p4368)) := by
  classical
  tauto

theorem initial8445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3125) ∨ (¬ (meaning t m 5044)) := by
  exact rule8445 (meaning t m 3125) (meaning t m 4334) (meaning t m 4368) (meaning t m 5045) (meaning t m 5046)

theorem rule8446 (p3125 p4334 p4368 p5045 p5046 : Prop) : (¬ (p5045 ∧ p4334 ∧ p3125 ∧ p5046 ∧ p4368)) ∨ (p5046) := by
  classical
  tauto

theorem initial8446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5044)) ∨ (meaning t m 5046) := by
  exact rule8446 (meaning t m 3125) (meaning t m 4334) (meaning t m 4368) (meaning t m 5045) (meaning t m 5046)

theorem rule8447 (p3125 p4334 p4368 p5045 p5046 : Prop) : (p4368) ∨ (¬ (p5045 ∧ p4334 ∧ p3125 ∧ p5046 ∧ p4368)) := by
  classical
  tauto

theorem initial8447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4368) ∨ (¬ (meaning t m 5044)) := by
  exact rule8447 (meaning t m 3125) (meaning t m 4334) (meaning t m 4368) (meaning t m 5045) (meaning t m 5046)

theorem rule8451 (p5042 p5044 : Prop) : (¬ (p5042 ∨ p5044)) ∨ (p5042) ∨ (p5044) := by
  classical
  tauto

theorem initial8451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5041)) ∨ (meaning t m 5042) ∨ (meaning t m 5044) := by
  exact rule8451 (meaning t m 5042) (meaning t m 5044)

theorem rule8452 (p3119 p5041 : Prop) (h : (p3119 ↔ p5041)) : (¬ p3119) ∨ (p5041) := by
  classical
  tauto

theorem initial8452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3119)) ∨ (meaning t m 5041) := by
  have source := ElevenTheory.theory1226 t (m.theta 5 6) (m.theta 5 9) (m.theta 6 9)
  exact rule8452 (meaning t m 3119) (meaning t m 5041) source

theorem rule8454 (p4315 p4316 p4392 p4906 p5049 : Prop) : (p4392) ∨ (¬ (p4392 ∧ p4316 ∧ p4315 ∧ p5049 ∧ p4906)) := by
  classical
  tauto

theorem initial8454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4392) ∨ (¬ (meaning t m 5048)) := by
  exact rule8454 (meaning t m 4315) (meaning t m 4316) (meaning t m 4392) (meaning t m 4906) (meaning t m 5049)

theorem rule8455 (p4315 p4316 p4392 p4906 p5049 : Prop) : (p4316) ∨ (¬ (p4392 ∧ p4316 ∧ p4315 ∧ p5049 ∧ p4906)) := by
  classical
  tauto

theorem initial8455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4316) ∨ (¬ (meaning t m 5048)) := by
  exact rule8455 (meaning t m 4315) (meaning t m 4316) (meaning t m 4392) (meaning t m 4906) (meaning t m 5049)

theorem rule8456 (p4315 p4316 p4392 p4906 p5049 : Prop) : (p4315) ∨ (¬ (p4392 ∧ p4316 ∧ p4315 ∧ p5049 ∧ p4906)) := by
  classical
  tauto

theorem initial8456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4315) ∨ (¬ (meaning t m 5048)) := by
  exact rule8456 (meaning t m 4315) (meaning t m 4316) (meaning t m 4392) (meaning t m 4906) (meaning t m 5049)

theorem rule8457 (p4315 p4316 p4392 p4906 p5049 : Prop) : (¬ (p4392 ∧ p4316 ∧ p4315 ∧ p5049 ∧ p4906)) ∨ (p5049) := by
  classical
  tauto

theorem initial8457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5048)) ∨ (meaning t m 5049) := by
  exact rule8457 (meaning t m 4315) (meaning t m 4316) (meaning t m 4392) (meaning t m 4906) (meaning t m 5049)

theorem rule8458 (p4315 p4316 p4392 p4906 p5049 : Prop) : (p4906) ∨ (¬ (p4392 ∧ p4316 ∧ p4315 ∧ p5049 ∧ p4906)) := by
  classical
  tauto

theorem initial8458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4906) ∨ (¬ (meaning t m 5048)) := by
  exact rule8458 (meaning t m 4315) (meaning t m 4316) (meaning t m 4392) (meaning t m 4906) (meaning t m 5049)

theorem rule8460 (p3136 p4313 p5051 p5052 p5053 : Prop) : (¬ (p5051 ∧ p4313 ∧ p3136 ∧ p5052 ∧ p5053)) ∨ (p5051) := by
  classical
  tauto

theorem initial8460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5050)) ∨ (meaning t m 5051) := by
  exact rule8460 (meaning t m 3136) (meaning t m 4313) (meaning t m 5051) (meaning t m 5052) (meaning t m 5053)

theorem rule8461 (p3136 p4313 p5051 p5052 p5053 : Prop) : (p4313) ∨ (¬ (p5051 ∧ p4313 ∧ p3136 ∧ p5052 ∧ p5053)) := by
  classical
  tauto

theorem initial8461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4313) ∨ (¬ (meaning t m 5050)) := by
  exact rule8461 (meaning t m 3136) (meaning t m 4313) (meaning t m 5051) (meaning t m 5052) (meaning t m 5053)

theorem rule8462 (p3136 p4313 p5051 p5052 p5053 : Prop) : (p3136) ∨ (¬ (p5051 ∧ p4313 ∧ p3136 ∧ p5052 ∧ p5053)) := by
  classical
  tauto

theorem initial8462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3136) ∨ (¬ (meaning t m 5050)) := by
  exact rule8462 (meaning t m 3136) (meaning t m 4313) (meaning t m 5051) (meaning t m 5052) (meaning t m 5053)

theorem rule8463 (p3136 p4313 p5051 p5052 p5053 : Prop) : (¬ (p5051 ∧ p4313 ∧ p3136 ∧ p5052 ∧ p5053)) ∨ (p5052) := by
  classical
  tauto

theorem initial8463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5050)) ∨ (meaning t m 5052) := by
  exact rule8463 (meaning t m 3136) (meaning t m 4313) (meaning t m 5051) (meaning t m 5052) (meaning t m 5053)

theorem rule8464 (p3136 p4313 p5051 p5052 p5053 : Prop) : (¬ (p5051 ∧ p4313 ∧ p3136 ∧ p5052 ∧ p5053)) ∨ (p5053) := by
  classical
  tauto

theorem initial8464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5050)) ∨ (meaning t m 5053) := by
  exact rule8464 (meaning t m 3136) (meaning t m 4313) (meaning t m 5051) (meaning t m 5052) (meaning t m 5053)

theorem rule8468 (p5048 p5050 : Prop) : (¬ (p5048 ∨ p5050)) ∨ (p5048) ∨ (p5050) := by
  classical
  tauto

theorem initial8468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5047)) ∨ (meaning t m 5048) ∨ (meaning t m 5050) := by
  exact rule8468 (meaning t m 5048) (meaning t m 5050)

theorem rule8469 (p3130 p5047 : Prop) (h : (p3130 ↔ p5047)) : (¬ p3130) ∨ (p5047) := by
  classical
  tauto

theorem initial8469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3130)) ∨ (meaning t m 5047) := by
  have source := ElevenTheory.theory1227 t (m.theta 2 3) (m.theta 2 5) (m.theta 3 5)
  exact rule8469 (meaning t m 3130) (meaning t m 5047) source

theorem rule8471 (p3692 p3949 p4335 p4450 p5056 : Prop) : (p4335) ∨ (¬ (p4335 ∧ p3949 ∧ p3692 ∧ p5056 ∧ p4450)) := by
  classical
  tauto

theorem initial8471 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4335) ∨ (¬ (meaning t m 5055)) := by
  exact rule8471 (meaning t m 3692) (meaning t m 3949) (meaning t m 4335) (meaning t m 4450) (meaning t m 5056)

theorem rule8472 (p3692 p3949 p4335 p4450 p5056 : Prop) : (p3949) ∨ (¬ (p4335 ∧ p3949 ∧ p3692 ∧ p5056 ∧ p4450)) := by
  classical
  tauto

theorem initial8472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3949) ∨ (¬ (meaning t m 5055)) := by
  exact rule8472 (meaning t m 3692) (meaning t m 3949) (meaning t m 4335) (meaning t m 4450) (meaning t m 5056)

theorem rule8473 (p3692 p3949 p4335 p4450 p5056 : Prop) : (p3692) ∨ (¬ (p4335 ∧ p3949 ∧ p3692 ∧ p5056 ∧ p4450)) := by
  classical
  tauto

theorem initial8473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3692) ∨ (¬ (meaning t m 5055)) := by
  exact rule8473 (meaning t m 3692) (meaning t m 3949) (meaning t m 4335) (meaning t m 4450) (meaning t m 5056)

theorem rule8475 (p3692 p3949 p4335 p4450 p5056 : Prop) : (p4450) ∨ (¬ (p4335 ∧ p3949 ∧ p3692 ∧ p5056 ∧ p4450)) := by
  classical
  tauto

theorem initial8475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4450) ∨ (¬ (meaning t m 5055)) := by
  exact rule8475 (meaning t m 3692) (meaning t m 3949) (meaning t m 4335) (meaning t m 4450) (meaning t m 5056)

theorem rule8477 (p2532 p2533 p3146 p5058 p5059 : Prop) : (p2532) ∨ (¬ (p2532 ∧ p2533 ∧ p3146 ∧ p5058 ∧ p5059)) := by
  classical
  tauto

theorem initial8477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2532) ∨ (¬ (meaning t m 5057)) := by
  exact rule8477 (meaning t m 2532) (meaning t m 2533) (meaning t m 3146) (meaning t m 5058) (meaning t m 5059)

theorem rule8478 (p2532 p2533 p3146 p5058 p5059 : Prop) : (p2533) ∨ (¬ (p2532 ∧ p2533 ∧ p3146 ∧ p5058 ∧ p5059)) := by
  classical
  tauto

theorem initial8478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2533) ∨ (¬ (meaning t m 5057)) := by
  exact rule8478 (meaning t m 2532) (meaning t m 2533) (meaning t m 3146) (meaning t m 5058) (meaning t m 5059)

theorem rule8479 (p2532 p2533 p3146 p5058 p5059 : Prop) : (p3146) ∨ (¬ (p2532 ∧ p2533 ∧ p3146 ∧ p5058 ∧ p5059)) := by
  classical
  tauto

theorem initial8479 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3146) ∨ (¬ (meaning t m 5057)) := by
  exact rule8479 (meaning t m 2532) (meaning t m 2533) (meaning t m 3146) (meaning t m 5058) (meaning t m 5059)

theorem rule8481 (p2532 p2533 p3146 p5058 p5059 : Prop) : (¬ (p2532 ∧ p2533 ∧ p3146 ∧ p5058 ∧ p5059)) ∨ (p5059) := by
  classical
  tauto

theorem initial8481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5057)) ∨ (meaning t m 5059) := by
  exact rule8481 (meaning t m 2532) (meaning t m 2533) (meaning t m 3146) (meaning t m 5058) (meaning t m 5059)

theorem rule8485 (p5055 p5057 : Prop) : (¬ (p5055 ∨ p5057)) ∨ (p5055) ∨ (p5057) := by
  classical
  tauto

theorem initial8485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5054)) ∨ (meaning t m 5055) ∨ (meaning t m 5057) := by
  exact rule8485 (meaning t m 5055) (meaning t m 5057)

theorem rule8486 (p3140 p5054 : Prop) (h : (p3140 ↔ p5054)) : (¬ p3140) ∨ (p5054) := by
  classical
  tauto

theorem initial8486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3140)) ∨ (meaning t m 5054) := by
  have source := ElevenTheory.theory1228 t (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule8486 (meaning t m 3140) (meaning t m 5054) source

theorem rule8488 (p3497 p3661 p4312 p5062 p5063 : Prop) : (p3661) ∨ (¬ (p3661 ∧ p4312 ∧ p3497 ∧ p5062 ∧ p5063)) := by
  classical
  tauto

theorem initial8488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3661) ∨ (¬ (meaning t m 5061)) := by
  exact rule8488 (meaning t m 3497) (meaning t m 3661) (meaning t m 4312) (meaning t m 5062) (meaning t m 5063)

theorem rule8489 (p3497 p3661 p4312 p5062 p5063 : Prop) : (p4312) ∨ (¬ (p3661 ∧ p4312 ∧ p3497 ∧ p5062 ∧ p5063)) := by
  classical
  tauto

theorem initial8489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4312) ∨ (¬ (meaning t m 5061)) := by
  exact rule8489 (meaning t m 3497) (meaning t m 3661) (meaning t m 4312) (meaning t m 5062) (meaning t m 5063)

theorem rule8490 (p3497 p3661 p4312 p5062 p5063 : Prop) : (p3497) ∨ (¬ (p3661 ∧ p4312 ∧ p3497 ∧ p5062 ∧ p5063)) := by
  classical
  tauto

theorem initial8490 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3497) ∨ (¬ (meaning t m 5061)) := by
  exact rule8490 (meaning t m 3497) (meaning t m 3661) (meaning t m 4312) (meaning t m 5062) (meaning t m 5063)

theorem rule8491 (p3497 p3661 p4312 p5062 p5063 : Prop) : (¬ (p3661 ∧ p4312 ∧ p3497 ∧ p5062 ∧ p5063)) ∨ (p5062) := by
  classical
  tauto

theorem initial8491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5061)) ∨ (meaning t m 5062) := by
  exact rule8491 (meaning t m 3497) (meaning t m 3661) (meaning t m 4312) (meaning t m 5062) (meaning t m 5063)

theorem rule8492 (p3497 p3661 p4312 p5062 p5063 : Prop) : (¬ (p3661 ∧ p4312 ∧ p3497 ∧ p5062 ∧ p5063)) ∨ (p5063) := by
  classical
  tauto

theorem initial8492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5061)) ∨ (meaning t m 5063) := by
  exact rule8492 (meaning t m 3497) (meaning t m 3661) (meaning t m 4312) (meaning t m 5062) (meaning t m 5063)

theorem rule8494 (p3156 p4043 p4237 p4311 p5065 : Prop) : (p4311) ∨ (¬ (p4311 ∧ p4237 ∧ p3156 ∧ p5065 ∧ p4043)) := by
  classical
  tauto

theorem initial8494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4311) ∨ (¬ (meaning t m 5064)) := by
  exact rule8494 (meaning t m 3156) (meaning t m 4043) (meaning t m 4237) (meaning t m 4311) (meaning t m 5065)

theorem rule8495 (p3156 p4043 p4237 p4311 p5065 : Prop) : (p4237) ∨ (¬ (p4311 ∧ p4237 ∧ p3156 ∧ p5065 ∧ p4043)) := by
  classical
  tauto

theorem initial8495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4237) ∨ (¬ (meaning t m 5064)) := by
  exact rule8495 (meaning t m 3156) (meaning t m 4043) (meaning t m 4237) (meaning t m 4311) (meaning t m 5065)

theorem rule8496 (p3156 p4043 p4237 p4311 p5065 : Prop) : (p3156) ∨ (¬ (p4311 ∧ p4237 ∧ p3156 ∧ p5065 ∧ p4043)) := by
  classical
  tauto

theorem initial8496 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3156) ∨ (¬ (meaning t m 5064)) := by
  exact rule8496 (meaning t m 3156) (meaning t m 4043) (meaning t m 4237) (meaning t m 4311) (meaning t m 5065)

theorem rule8497 (p3156 p4043 p4237 p4311 p5065 : Prop) : (¬ (p4311 ∧ p4237 ∧ p3156 ∧ p5065 ∧ p4043)) ∨ (p5065) := by
  classical
  tauto

theorem initial8497 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5064)) ∨ (meaning t m 5065) := by
  exact rule8497 (meaning t m 3156) (meaning t m 4043) (meaning t m 4237) (meaning t m 4311) (meaning t m 5065)

theorem rule8502 (p5061 p5064 : Prop) : (¬ (p5061 ∨ p5064)) ∨ (p5061) ∨ (p5064) := by
  classical
  tauto

theorem initial8502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5060)) ∨ (meaning t m 5061) ∨ (meaning t m 5064) := by
  exact rule8502 (meaning t m 5061) (meaning t m 5064)

theorem rule8503 (p3150 p5060 : Prop) (h : (p3150 ↔ p5060)) : (¬ p3150) ∨ (p5060) := by
  classical
  tauto

theorem initial8503 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3150)) ∨ (meaning t m 5060) := by
  have source := ElevenTheory.theory1229 t (m.theta 3 5) (m.theta 3 8) (m.theta 5 8)
  exact rule8503 (meaning t m 3150) (meaning t m 5060) source

theorem rule8507 (p3169 p3176 : Prop) : (p3169) ∨ (p3176) ∨ (¬ (p3169 ∨ p3176)) := by
  classical
  tauto

theorem initial8507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3169) ∨ (meaning t m 3176) ∨ (¬ (meaning t m 5066)) := by
  exact rule8507 (meaning t m 3169) (meaning t m 3176)

theorem rule8508 (p3160 p5066 : Prop) (h : (p3160 ↔ p5066)) : (¬ p3160) ∨ (p5066) := by
  classical
  tauto

theorem initial8508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3160)) ∨ (meaning t m 5066) := by
  have source := ElevenTheory.theory1230 t (m.theta 0 3) (m.theta 0 8) (m.theta 3 8)
  exact rule8508 (meaning t m 3160) (meaning t m 5066) source

theorem rule8531 (p2027 p2963 p3166 p3923 p4417 p4757 : Prop) (h : (¬ p3166) ∨ (¬ p2963) ∨ (¬ p4417) ∨ (¬ p4757) ∨ p2027 ∨ (¬ p3923)) : (p2027) ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3923) ∨ (¬ p4417) ∨ (¬ p4757) := by
  classical
  tauto

theorem initial8531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4417)) ∨ (¬ (meaning t m 4757)) := by
  have source := ElevenTheory.theory1233 t (m.theta 0 3) (m.theta 1 6) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8)
  exact rule8531 (meaning t m 2027) (meaning t m 2963) (meaning t m 3166) (meaning t m 3923) (meaning t m 4417) (meaning t m 4757) source

theorem rule8532 (p4262 p4360 p5074 p5075 p5076 : Prop) : (p4262) ∨ (¬ (p4262 ∧ p5074 ∧ p4360 ∧ p5075 ∧ p5076)) := by
  classical
  tauto

theorem initial8532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4262) ∨ (¬ (meaning t m 5073)) := by
  exact rule8532 (meaning t m 4262) (meaning t m 4360) (meaning t m 5074) (meaning t m 5075) (meaning t m 5076)

theorem rule8533 (p4262 p4360 p5074 p5075 p5076 : Prop) : (¬ (p4262 ∧ p5074 ∧ p4360 ∧ p5075 ∧ p5076)) ∨ (p5074) := by
  classical
  tauto

theorem initial8533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5073)) ∨ (meaning t m 5074) := by
  exact rule8533 (meaning t m 4262) (meaning t m 4360) (meaning t m 5074) (meaning t m 5075) (meaning t m 5076)

theorem rule8534 (p4262 p4360 p5074 p5075 p5076 : Prop) : (p4360) ∨ (¬ (p4262 ∧ p5074 ∧ p4360 ∧ p5075 ∧ p5076)) := by
  classical
  tauto

theorem initial8534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4360) ∨ (¬ (meaning t m 5073)) := by
  exact rule8534 (meaning t m 4262) (meaning t m 4360) (meaning t m 5074) (meaning t m 5075) (meaning t m 5076)

theorem rule8538 (p3189 p3859 p4288 p5078 p5079 : Prop) : (p4288) ∨ (¬ (p4288 ∧ p3859 ∧ p3189 ∧ p5078 ∧ p5079)) := by
  classical
  tauto

theorem initial8538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4288) ∨ (¬ (meaning t m 5077)) := by
  exact rule8538 (meaning t m 3189) (meaning t m 3859) (meaning t m 4288) (meaning t m 5078) (meaning t m 5079)

theorem rule8539 (p3189 p3859 p4288 p5078 p5079 : Prop) : (p3859) ∨ (¬ (p4288 ∧ p3859 ∧ p3189 ∧ p5078 ∧ p5079)) := by
  classical
  tauto

theorem initial8539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3859) ∨ (¬ (meaning t m 5077)) := by
  exact rule8539 (meaning t m 3189) (meaning t m 3859) (meaning t m 4288) (meaning t m 5078) (meaning t m 5079)

theorem rule8540 (p3189 p3859 p4288 p5078 p5079 : Prop) : (p3189) ∨ (¬ (p4288 ∧ p3859 ∧ p3189 ∧ p5078 ∧ p5079)) := by
  classical
  tauto

theorem initial8540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3189) ∨ (¬ (meaning t m 5077)) := by
  exact rule8540 (meaning t m 3189) (meaning t m 3859) (meaning t m 4288) (meaning t m 5078) (meaning t m 5079)

theorem rule8542 (p3189 p3859 p4288 p5078 p5079 : Prop) : (¬ (p4288 ∧ p3859 ∧ p3189 ∧ p5078 ∧ p5079)) ∨ (p5079) := by
  classical
  tauto

theorem initial8542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5077)) ∨ (meaning t m 5079) := by
  exact rule8542 (meaning t m 3189) (meaning t m 3859) (meaning t m 4288) (meaning t m 5078) (meaning t m 5079)

theorem rule8546 (p5073 p5077 : Prop) : (¬ (p5073 ∨ p5077)) ∨ (p5073) ∨ (p5077) := by
  classical
  tauto

theorem initial8546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5072)) ∨ (meaning t m 5073) ∨ (meaning t m 5077) := by
  exact rule8546 (meaning t m 5073) (meaning t m 5077)

theorem rule8547 (p3183 p5072 : Prop) (h : (p3183 ↔ p5072)) : (¬ p3183) ∨ (p5072) := by
  classical
  tauto

theorem initial8547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3183)) ∨ (meaning t m 5072) := by
  have source := ElevenTheory.theory1234 t (m.theta 1 3) (m.theta 1 8) (m.theta 3 8)
  exact rule8547 (meaning t m 3183) (meaning t m 5072) source

theorem rule8549 (p2027 p2449 p2922 p3193 p4636 p4653 : Prop) (h : (¬ p4636) ∨ p2027 ∨ (¬ p3193) ∨ (¬ p2922) ∨ (¬ p4653) ∨ (¬ p2449)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2922) ∨ (¬ p3193) ∨ (¬ p4636) ∨ (¬ p4653) := by
  classical
  tauto

theorem initial8549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 4636)) ∨ (¬ (meaning t m 4653)) := by
  have source := ElevenTheory.theory1235 t (m.theta 1 4) (m.theta 3 7) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9)
  exact rule8549 (meaning t m 2027) (meaning t m 2449) (meaning t m 2922) (meaning t m 3193) (meaning t m 4636) (meaning t m 4653) source

theorem rule8550 (p3686 p3876 p4106 p5082 p5083 : Prop) : (p3686) ∨ (¬ (p3686 ∧ p4106 ∧ p3876 ∧ p5082 ∧ p5083)) := by
  classical
  tauto

theorem initial8550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3686) ∨ (¬ (meaning t m 5081)) := by
  exact rule8550 (meaning t m 3686) (meaning t m 3876) (meaning t m 4106) (meaning t m 5082) (meaning t m 5083)

theorem rule8551 (p3686 p3876 p4106 p5082 p5083 : Prop) : (p4106) ∨ (¬ (p3686 ∧ p4106 ∧ p3876 ∧ p5082 ∧ p5083)) := by
  classical
  tauto

theorem initial8551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4106) ∨ (¬ (meaning t m 5081)) := by
  exact rule8551 (meaning t m 3686) (meaning t m 3876) (meaning t m 4106) (meaning t m 5082) (meaning t m 5083)

theorem rule8552 (p3686 p3876 p4106 p5082 p5083 : Prop) : (p3876) ∨ (¬ (p3686 ∧ p4106 ∧ p3876 ∧ p5082 ∧ p5083)) := by
  classical
  tauto

theorem initial8552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3876) ∨ (¬ (meaning t m 5081)) := by
  exact rule8552 (meaning t m 3686) (meaning t m 3876) (meaning t m 4106) (meaning t m 5082) (meaning t m 5083)

theorem rule8553 (p3686 p3876 p4106 p5082 p5083 : Prop) : (¬ (p3686 ∧ p4106 ∧ p3876 ∧ p5082 ∧ p5083)) ∨ (p5082) := by
  classical
  tauto

theorem initial8553 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5081)) ∨ (meaning t m 5082) := by
  exact rule8553 (meaning t m 3686) (meaning t m 3876) (meaning t m 4106) (meaning t m 5082) (meaning t m 5083)

theorem rule8554 (p3686 p3876 p4106 p5082 p5083 : Prop) : (¬ (p3686 ∧ p4106 ∧ p3876 ∧ p5082 ∧ p5083)) ∨ (p5083) := by
  classical
  tauto

theorem initial8554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5081)) ∨ (meaning t m 5083) := by
  exact rule8554 (meaning t m 3686) (meaning t m 3876) (meaning t m 4106) (meaning t m 5082) (meaning t m 5083)

theorem rule8556 (p3201 p3658 p5085 p5086 p5087 : Prop) : (p3658) ∨ (¬ (p3658 ∧ p5085 ∧ p3201 ∧ p5086 ∧ p5087)) := by
  classical
  tauto

theorem initial8556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3658) ∨ (¬ (meaning t m 5084)) := by
  exact rule8556 (meaning t m 3201) (meaning t m 3658) (meaning t m 5085) (meaning t m 5086) (meaning t m 5087)

theorem rule8557 (p3201 p3658 p5085 p5086 p5087 : Prop) : (¬ (p3658 ∧ p5085 ∧ p3201 ∧ p5086 ∧ p5087)) ∨ (p5085) := by
  classical
  tauto

theorem initial8557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5084)) ∨ (meaning t m 5085) := by
  exact rule8557 (meaning t m 3201) (meaning t m 3658) (meaning t m 5085) (meaning t m 5086) (meaning t m 5087)

theorem rule8558 (p3201 p3658 p5085 p5086 p5087 : Prop) : (p3201) ∨ (¬ (p3658 ∧ p5085 ∧ p3201 ∧ p5086 ∧ p5087)) := by
  classical
  tauto

theorem initial8558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3201) ∨ (¬ (meaning t m 5084)) := by
  exact rule8558 (meaning t m 3201) (meaning t m 3658) (meaning t m 5085) (meaning t m 5086) (meaning t m 5087)

theorem rule8559 (p3201 p3658 p5085 p5086 p5087 : Prop) : (¬ (p3658 ∧ p5085 ∧ p3201 ∧ p5086 ∧ p5087)) ∨ (p5086) := by
  classical
  tauto

theorem initial8559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5084)) ∨ (meaning t m 5086) := by
  exact rule8559 (meaning t m 3201) (meaning t m 3658) (meaning t m 5085) (meaning t m 5086) (meaning t m 5087)

theorem rule8560 (p3201 p3658 p5085 p5086 p5087 : Prop) : (¬ (p3658 ∧ p5085 ∧ p3201 ∧ p5086 ∧ p5087)) ∨ (p5087) := by
  classical
  tauto

theorem initial8560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5084)) ∨ (meaning t m 5087) := by
  exact rule8560 (meaning t m 3201) (meaning t m 3658) (meaning t m 5085) (meaning t m 5086) (meaning t m 5087)

theorem rule8564 (p5081 p5084 : Prop) : (¬ (p5081 ∨ p5084)) ∨ (p5081) ∨ (p5084) := by
  classical
  tauto

theorem initial8564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5080)) ∨ (meaning t m 5081) ∨ (meaning t m 5084) := by
  exact rule8564 (meaning t m 5081) (meaning t m 5084)

theorem rule8565 (p3195 p5080 : Prop) (h : (p3195 ↔ p5080)) : (¬ p3195) ∨ (p5080) := by
  classical
  tauto

theorem initial8565 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3195)) ∨ (meaning t m 5080) := by
  have source := ElevenTheory.theory1236 t (m.theta 2 4) (m.theta 2 7) (m.theta 4 7)
  exact rule8565 (meaning t m 3195) (meaning t m 5080) source

theorem rule8567 (p2027 p2459 p2619 p3949 p4133 p4385 p4441 : Prop) (h : (¬ p2459) ∨ (¬ p3949) ∨ p2027 ∨ (¬ p4441) ∨ (¬ p4133) ∨ (¬ p4385) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2619) ∨ (¬ p3949) ∨ (¬ p4133) ∨ (¬ p4385) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial8567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory1237 t (m.theta 2 5) (m.theta 5 8) (m.theta 5 9) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule8567 (meaning t m 2027) (meaning t m 2459) (meaning t m 2619) (meaning t m 3949) (meaning t m 4133) (meaning t m 4385) (meaning t m 4441) source

theorem rule8568 (p2383 p2578 p3956 : Prop) (h : (¬ p2383) ∨ (¬ p3956) ∨ (¬ p2578)) : (¬ p2383) ∨ (¬ p2578) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial8568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory1238 (m.theta 0 6) (m.theta 4 6) (m.theta 6 8)
  exact rule8568 (meaning t m 2383) (meaning t m 2578) (meaning t m 3956) source

theorem rule8569 (p4032 p4323 p4380 p5090 p5091 : Prop) : (p4380) ∨ (¬ (p4380 ∧ p4323 ∧ p4032 ∧ p5090 ∧ p5091)) := by
  classical
  tauto

theorem initial8569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4380) ∨ (¬ (meaning t m 5089)) := by
  exact rule8569 (meaning t m 4032) (meaning t m 4323) (meaning t m 4380) (meaning t m 5090) (meaning t m 5091)

theorem rule8570 (p4032 p4323 p4380 p5090 p5091 : Prop) : (p4323) ∨ (¬ (p4380 ∧ p4323 ∧ p4032 ∧ p5090 ∧ p5091)) := by
  classical
  tauto

theorem initial8570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4323) ∨ (¬ (meaning t m 5089)) := by
  exact rule8570 (meaning t m 4032) (meaning t m 4323) (meaning t m 4380) (meaning t m 5090) (meaning t m 5091)

theorem rule8571 (p4032 p4323 p4380 p5090 p5091 : Prop) : (p4032) ∨ (¬ (p4380 ∧ p4323 ∧ p4032 ∧ p5090 ∧ p5091)) := by
  classical
  tauto

theorem initial8571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4032) ∨ (¬ (meaning t m 5089)) := by
  exact rule8571 (meaning t m 4032) (meaning t m 4323) (meaning t m 4380) (meaning t m 5090) (meaning t m 5091)

theorem rule8575 (p3212 p4207 p4209 p5093 p5094 : Prop) : (p4209) ∨ (¬ (p4209 ∧ p4207 ∧ p3212 ∧ p5093 ∧ p5094)) := by
  classical
  tauto

theorem initial8575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4209) ∨ (¬ (meaning t m 5092)) := by
  exact rule8575 (meaning t m 3212) (meaning t m 4207) (meaning t m 4209) (meaning t m 5093) (meaning t m 5094)

theorem rule8576 (p3212 p4207 p4209 p5093 p5094 : Prop) : (p4207) ∨ (¬ (p4209 ∧ p4207 ∧ p3212 ∧ p5093 ∧ p5094)) := by
  classical
  tauto

theorem initial8576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4207) ∨ (¬ (meaning t m 5092)) := by
  exact rule8576 (meaning t m 3212) (meaning t m 4207) (meaning t m 4209) (meaning t m 5093) (meaning t m 5094)

theorem rule8577 (p3212 p4207 p4209 p5093 p5094 : Prop) : (p3212) ∨ (¬ (p4209 ∧ p4207 ∧ p3212 ∧ p5093 ∧ p5094)) := by
  classical
  tauto

theorem initial8577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3212) ∨ (¬ (meaning t m 5092)) := by
  exact rule8577 (meaning t m 3212) (meaning t m 4207) (meaning t m 4209) (meaning t m 5093) (meaning t m 5094)

theorem rule8578 (p3212 p4207 p4209 p5093 p5094 : Prop) : (¬ (p4209 ∧ p4207 ∧ p3212 ∧ p5093 ∧ p5094)) ∨ (p5093) := by
  classical
  tauto

theorem initial8578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5092)) ∨ (meaning t m 5093) := by
  exact rule8578 (meaning t m 3212) (meaning t m 4207) (meaning t m 4209) (meaning t m 5093) (meaning t m 5094)

theorem rule8579 (p3212 p4207 p4209 p5093 p5094 : Prop) : (¬ (p4209 ∧ p4207 ∧ p3212 ∧ p5093 ∧ p5094)) ∨ (p5094) := by
  classical
  tauto

theorem initial8579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5092)) ∨ (meaning t m 5094) := by
  exact rule8579 (meaning t m 3212) (meaning t m 4207) (meaning t m 4209) (meaning t m 5093) (meaning t m 5094)

theorem rule8580 (p3212 p4207 p4209 p5093 p5094 : Prop) : (¬ p3212) ∨ (¬ p4207) ∨ (¬ p4209) ∨ ((p4209 ∧ p4207 ∧ p3212 ∧ p5093 ∧ p5094)) ∨ (¬ p5093) ∨ (¬ p5094) := by
  classical
  tauto

theorem initial8580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4207)) ∨ (¬ (meaning t m 4209)) ∨ (meaning t m 5092) ∨ (¬ (meaning t m 5093)) ∨ (¬ (meaning t m 5094)) := by
  exact rule8580 (meaning t m 3212) (meaning t m 4207) (meaning t m 4209) (meaning t m 5093) (meaning t m 5094)

theorem rule8583 (p5089 p5092 : Prop) : (¬ (p5089 ∨ p5092)) ∨ (p5089) ∨ (p5092) := by
  classical
  tauto

theorem initial8583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5088)) ∨ (meaning t m 5089) ∨ (meaning t m 5092) := by
  exact rule8583 (meaning t m 5089) (meaning t m 5092)

theorem rule8584 (p3206 p5088 : Prop) (h : (p3206 ↔ p5088)) : (¬ p3206) ∨ (p5088) := by
  classical
  tauto

theorem initial8584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3206)) ∨ (meaning t m 5088) := by
  have source := ElevenTheory.theory1239 t (m.theta 0 5) (m.theta 0 9) (m.theta 5 9)
  exact rule8584 (meaning t m 3206) (meaning t m 5088) source

theorem rule8588 (p3225 p3231 : Prop) : (p3225) ∨ (p3231) ∨ (¬ (p3225 ∨ p3231)) := by
  classical
  tauto

theorem initial8588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3225) ∨ (meaning t m 3231) ∨ (¬ (meaning t m 5095)) := by
  exact rule8588 (meaning t m 3225) (meaning t m 3231)

theorem rule8589 (p3216 p5095 : Prop) (h : (p3216 ↔ p5095)) : (¬ p3216) ∨ (p5095) := by
  classical
  tauto

theorem initial8589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3216)) ∨ (meaning t m 5095) := by
  have source := ElevenTheory.theory1240 t (m.theta 1 4) (m.theta 1 9) (m.theta 4 9)
  exact rule8589 (meaning t m 3216) (meaning t m 5095) source

theorem rule8607 (p3690 p4382 p4395 p4402 p5102 : Prop) : (p4402) ∨ (¬ (p4402 ∧ p4382 ∧ p3690 ∧ p5102 ∧ p4395)) := by
  classical
  tauto

theorem initial8607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4402) ∨ (¬ (meaning t m 5101)) := by
  exact rule8607 (meaning t m 3690) (meaning t m 4382) (meaning t m 4395) (meaning t m 4402) (meaning t m 5102)

theorem rule8608 (p3690 p4382 p4395 p4402 p5102 : Prop) : (p4382) ∨ (¬ (p4402 ∧ p4382 ∧ p3690 ∧ p5102 ∧ p4395)) := by
  classical
  tauto

theorem initial8608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4382) ∨ (¬ (meaning t m 5101)) := by
  exact rule8608 (meaning t m 3690) (meaning t m 4382) (meaning t m 4395) (meaning t m 4402) (meaning t m 5102)

theorem rule8609 (p3690 p4382 p4395 p4402 p5102 : Prop) : (p3690) ∨ (¬ (p4402 ∧ p4382 ∧ p3690 ∧ p5102 ∧ p4395)) := by
  classical
  tauto

theorem initial8609 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3690) ∨ (¬ (meaning t m 5101)) := by
  exact rule8609 (meaning t m 3690) (meaning t m 4382) (meaning t m 4395) (meaning t m 4402) (meaning t m 5102)

theorem rule8610 (p3690 p4382 p4395 p4402 p5102 : Prop) : (¬ (p4402 ∧ p4382 ∧ p3690 ∧ p5102 ∧ p4395)) ∨ (p5102) := by
  classical
  tauto

theorem initial8610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5101)) ∨ (meaning t m 5102) := by
  exact rule8610 (meaning t m 3690) (meaning t m 4382) (meaning t m 4395) (meaning t m 4402) (meaning t m 5102)

theorem rule8611 (p3690 p4382 p4395 p4402 p5102 : Prop) : (p4395) ∨ (¬ (p4402 ∧ p4382 ∧ p3690 ∧ p5102 ∧ p4395)) := by
  classical
  tauto

theorem initial8611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4395) ∨ (¬ (meaning t m 5101)) := by
  exact rule8611 (meaning t m 3690) (meaning t m 4382) (meaning t m 4395) (meaning t m 4402) (meaning t m 5102)

theorem rule8613 (p3246 p3951 p4135 p4192 p5104 : Prop) : (p4135) ∨ (¬ (p4135 ∧ p4192 ∧ p3246 ∧ p5104 ∧ p3951)) := by
  classical
  tauto

theorem initial8613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4135) ∨ (¬ (meaning t m 5103)) := by
  exact rule8613 (meaning t m 3246) (meaning t m 3951) (meaning t m 4135) (meaning t m 4192) (meaning t m 5104)

theorem rule8614 (p3246 p3951 p4135 p4192 p5104 : Prop) : (p4192) ∨ (¬ (p4135 ∧ p4192 ∧ p3246 ∧ p5104 ∧ p3951)) := by
  classical
  tauto

theorem initial8614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4192) ∨ (¬ (meaning t m 5103)) := by
  exact rule8614 (meaning t m 3246) (meaning t m 3951) (meaning t m 4135) (meaning t m 4192) (meaning t m 5104)

theorem rule8615 (p3246 p3951 p4135 p4192 p5104 : Prop) : (p3246) ∨ (¬ (p4135 ∧ p4192 ∧ p3246 ∧ p5104 ∧ p3951)) := by
  classical
  tauto

theorem initial8615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3246) ∨ (¬ (meaning t m 5103)) := by
  exact rule8615 (meaning t m 3246) (meaning t m 3951) (meaning t m 4135) (meaning t m 4192) (meaning t m 5104)

theorem rule8616 (p3246 p3951 p4135 p4192 p5104 : Prop) : (¬ (p4135 ∧ p4192 ∧ p3246 ∧ p5104 ∧ p3951)) ∨ (p5104) := by
  classical
  tauto

theorem initial8616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5103)) ∨ (meaning t m 5104) := by
  exact rule8616 (meaning t m 3246) (meaning t m 3951) (meaning t m 4135) (meaning t m 4192) (meaning t m 5104)

theorem rule8617 (p3246 p3951 p4135 p4192 p5104 : Prop) : (p3951) ∨ (¬ (p4135 ∧ p4192 ∧ p3246 ∧ p5104 ∧ p3951)) := by
  classical
  tauto

theorem initial8617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3951) ∨ (¬ (meaning t m 5103)) := by
  exact rule8617 (meaning t m 3246) (meaning t m 3951) (meaning t m 4135) (meaning t m 4192) (meaning t m 5104)

theorem rule8621 (p5101 p5103 : Prop) : (¬ (p5101 ∨ p5103)) ∨ (p5101) ∨ (p5103) := by
  classical
  tauto

theorem initial8621 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5100)) ∨ (meaning t m 5101) ∨ (meaning t m 5103) := by
  exact rule8621 (meaning t m 5101) (meaning t m 5103)

theorem rule8622 (p3240 p5100 : Prop) (h : (p3240 ↔ p5100)) : (¬ p3240) ∨ (p5100) := by
  classical
  tauto

theorem initial8622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3240)) ∨ (meaning t m 5100) := by
  have source := ElevenTheory.theory1243 t (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule8622 (meaning t m 3240) (meaning t m 5100) source

theorem rule8624 (p2027 p2528 p3570 p3875 p4348 p4647 : Prop) (h : p2027 ∨ (¬ p3875) ∨ (¬ p2528) ∨ (¬ p4348) ∨ (¬ p4647) ∨ (¬ p3570)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3570) ∨ (¬ p3875) ∨ (¬ p4348) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial8624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory1244 t (m.theta 4 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule8624 (meaning t m 2027) (meaning t m 2528) (meaning t m 3570) (meaning t m 3875) (meaning t m 4348) (meaning t m 4647) source

theorem rule8626 (p4118 p4349 p5107 p5108 p5109 : Prop) : (p4349) ∨ (¬ (p4349 ∧ p5107 ∧ p4118 ∧ p5108 ∧ p5109)) := by
  classical
  tauto

theorem initial8626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4349) ∨ (¬ (meaning t m 5106)) := by
  exact rule8626 (meaning t m 4118) (meaning t m 4349) (meaning t m 5107) (meaning t m 5108) (meaning t m 5109)

theorem rule8627 (p4118 p4349 p5107 p5108 p5109 : Prop) : (¬ (p4349 ∧ p5107 ∧ p4118 ∧ p5108 ∧ p5109)) ∨ (p5107) := by
  classical
  tauto

theorem initial8627 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5106)) ∨ (meaning t m 5107) := by
  exact rule8627 (meaning t m 4118) (meaning t m 4349) (meaning t m 5107) (meaning t m 5108) (meaning t m 5109)

theorem rule8628 (p4118 p4349 p5107 p5108 p5109 : Prop) : (p4118) ∨ (¬ (p4349 ∧ p5107 ∧ p4118 ∧ p5108 ∧ p5109)) := by
  classical
  tauto

theorem initial8628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4118) ∨ (¬ (meaning t m 5106)) := by
  exact rule8628 (meaning t m 4118) (meaning t m 4349) (meaning t m 5107) (meaning t m 5108) (meaning t m 5109)

theorem rule8630 (p4118 p4349 p5107 p5108 p5109 : Prop) : (¬ (p4349 ∧ p5107 ∧ p4118 ∧ p5108 ∧ p5109)) ∨ (p5109) := by
  classical
  tauto

theorem initial8630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5106)) ∨ (meaning t m 5109) := by
  exact rule8630 (meaning t m 4118) (meaning t m 4349) (meaning t m 5107) (meaning t m 5108) (meaning t m 5109)

theorem rule8632 (p3256 p4350 p5111 p5112 p5113 : Prop) : (p4350) ∨ (¬ (p4350 ∧ p5111 ∧ p3256 ∧ p5112 ∧ p5113)) := by
  classical
  tauto

theorem initial8632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4350) ∨ (¬ (meaning t m 5110)) := by
  exact rule8632 (meaning t m 3256) (meaning t m 4350) (meaning t m 5111) (meaning t m 5112) (meaning t m 5113)

theorem rule8633 (p3256 p4350 p5111 p5112 p5113 : Prop) : (¬ (p4350 ∧ p5111 ∧ p3256 ∧ p5112 ∧ p5113)) ∨ (p5111) := by
  classical
  tauto

theorem initial8633 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5110)) ∨ (meaning t m 5111) := by
  exact rule8633 (meaning t m 3256) (meaning t m 4350) (meaning t m 5111) (meaning t m 5112) (meaning t m 5113)

theorem rule8634 (p3256 p4350 p5111 p5112 p5113 : Prop) : (p3256) ∨ (¬ (p4350 ∧ p5111 ∧ p3256 ∧ p5112 ∧ p5113)) := by
  classical
  tauto

theorem initial8634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3256) ∨ (¬ (meaning t m 5110)) := by
  exact rule8634 (meaning t m 3256) (meaning t m 4350) (meaning t m 5111) (meaning t m 5112) (meaning t m 5113)

theorem rule8636 (p3256 p4350 p5111 p5112 p5113 : Prop) : (¬ (p4350 ∧ p5111 ∧ p3256 ∧ p5112 ∧ p5113)) ∨ (p5113) := by
  classical
  tauto

theorem initial8636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5110)) ∨ (meaning t m 5113) := by
  exact rule8636 (meaning t m 3256) (meaning t m 4350) (meaning t m 5111) (meaning t m 5112) (meaning t m 5113)

theorem rule8640 (p5106 p5110 : Prop) : (¬ (p5106 ∨ p5110)) ∨ (p5106) ∨ (p5110) := by
  classical
  tauto

theorem initial8640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5105)) ∨ (meaning t m 5106) ∨ (meaning t m 5110) := by
  exact rule8640 (meaning t m 5106) (meaning t m 5110)

theorem rule8641 (p3250 p5105 : Prop) (h : (p3250 ↔ p5105)) : (¬ p3250) ∨ (p5105) := by
  classical
  tauto

theorem initial8641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3250)) ∨ (meaning t m 5105) := by
  have source := ElevenTheory.theory1246 t (m.theta 3 8) (m.theta 3 9) (m.theta 8 9)
  exact rule8641 (meaning t m 3250) (meaning t m 5105) source

theorem rule8643 (p2027 p2088 p3266 p3657 p4381 p4592 : Prop) (h : (¬ p4592) ∨ (¬ p4381) ∨ (¬ p2088) ∨ (¬ p3657) ∨ p2027 ∨ (¬ p3266)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4381) ∨ (¬ p4592) := by
  classical
  tauto

theorem initial8643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4592)) := by
  have source := ElevenTheory.theory1247 t (m.theta 0 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule8643 (meaning t m 2027) (meaning t m 2088) (meaning t m 3266) (meaning t m 3657) (meaning t m 4381) (meaning t m 4592) source

theorem rule8644 (p4444 p5116 p5117 p5118 p5119 : Prop) : (¬ (p5116 ∧ p5117 ∧ p4444 ∧ p5118 ∧ p5119)) ∨ (p5116) := by
  classical
  tauto

theorem initial8644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5115)) ∨ (meaning t m 5116) := by
  exact rule8644 (meaning t m 4444) (meaning t m 5116) (meaning t m 5117) (meaning t m 5118) (meaning t m 5119)

theorem rule8645 (p4444 p5116 p5117 p5118 p5119 : Prop) : (¬ (p5116 ∧ p5117 ∧ p4444 ∧ p5118 ∧ p5119)) ∨ (p5117) := by
  classical
  tauto

theorem initial8645 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5115)) ∨ (meaning t m 5117) := by
  exact rule8645 (meaning t m 4444) (meaning t m 5116) (meaning t m 5117) (meaning t m 5118) (meaning t m 5119)

theorem rule8646 (p4444 p5116 p5117 p5118 p5119 : Prop) : (p4444) ∨ (¬ (p5116 ∧ p5117 ∧ p4444 ∧ p5118 ∧ p5119)) := by
  classical
  tauto

theorem initial8646 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4444) ∨ (¬ (meaning t m 5115)) := by
  exact rule8646 (meaning t m 4444) (meaning t m 5116) (meaning t m 5117) (meaning t m 5118) (meaning t m 5119)

theorem rule8647 (p4444 p5116 p5117 p5118 p5119 : Prop) : (¬ (p5116 ∧ p5117 ∧ p4444 ∧ p5118 ∧ p5119)) ∨ (p5118) := by
  classical
  tauto

theorem initial8647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5115)) ∨ (meaning t m 5118) := by
  exact rule8647 (meaning t m 4444) (meaning t m 5116) (meaning t m 5117) (meaning t m 5118) (meaning t m 5119)

theorem rule8648 (p4444 p5116 p5117 p5118 p5119 : Prop) : (¬ (p5116 ∧ p5117 ∧ p4444 ∧ p5118 ∧ p5119)) ∨ (p5119) := by
  classical
  tauto

theorem initial8648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5115)) ∨ (meaning t m 5119) := by
  exact rule8648 (meaning t m 4444) (meaning t m 5116) (meaning t m 5117) (meaning t m 5118) (meaning t m 5119)

theorem rule8650 (p3266 p4200 p5121 p5122 p5123 : Prop) : (¬ (p5121 ∧ p4200 ∧ p3266 ∧ p5122 ∧ p5123)) ∨ (p5121) := by
  classical
  tauto

theorem initial8650 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5120)) ∨ (meaning t m 5121) := by
  exact rule8650 (meaning t m 3266) (meaning t m 4200) (meaning t m 5121) (meaning t m 5122) (meaning t m 5123)

theorem rule8651 (p3266 p4200 p5121 p5122 p5123 : Prop) : (p4200) ∨ (¬ (p5121 ∧ p4200 ∧ p3266 ∧ p5122 ∧ p5123)) := by
  classical
  tauto

theorem initial8651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4200) ∨ (¬ (meaning t m 5120)) := by
  exact rule8651 (meaning t m 3266) (meaning t m 4200) (meaning t m 5121) (meaning t m 5122) (meaning t m 5123)

theorem rule8652 (p3266 p4200 p5121 p5122 p5123 : Prop) : (p3266) ∨ (¬ (p5121 ∧ p4200 ∧ p3266 ∧ p5122 ∧ p5123)) := by
  classical
  tauto

theorem initial8652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3266) ∨ (¬ (meaning t m 5120)) := by
  exact rule8652 (meaning t m 3266) (meaning t m 4200) (meaning t m 5121) (meaning t m 5122) (meaning t m 5123)

theorem rule8653 (p3266 p4200 p5121 p5122 p5123 : Prop) : (¬ (p5121 ∧ p4200 ∧ p3266 ∧ p5122 ∧ p5123)) ∨ (p5122) := by
  classical
  tauto

theorem initial8653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5120)) ∨ (meaning t m 5122) := by
  exact rule8653 (meaning t m 3266) (meaning t m 4200) (meaning t m 5121) (meaning t m 5122) (meaning t m 5123)

theorem rule8654 (p3266 p4200 p5121 p5122 p5123 : Prop) : (¬ (p5121 ∧ p4200 ∧ p3266 ∧ p5122 ∧ p5123)) ∨ (p5123) := by
  classical
  tauto

theorem initial8654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5120)) ∨ (meaning t m 5123) := by
  exact rule8654 (meaning t m 3266) (meaning t m 4200) (meaning t m 5121) (meaning t m 5122) (meaning t m 5123)

theorem rule8658 (p5115 p5120 : Prop) : (¬ (p5115 ∨ p5120)) ∨ (p5115) ∨ (p5120) := by
  classical
  tauto

theorem initial8658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5114)) ∨ (meaning t m 5115) ∨ (meaning t m 5120) := by
  exact rule8658 (meaning t m 5115) (meaning t m 5120)

theorem rule8659 (p3260 p5114 : Prop) (h : (p3260 ↔ p5114)) : (¬ p3260) ∨ (p5114) := by
  classical
  tauto

theorem initial8659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3260)) ∨ (meaning t m 5114) := by
  have source := ElevenTheory.theory1248 t (m.theta 8 10) (m.theta 8 9) (m.theta 9 10)
  exact rule8659 (meaning t m 3260) (meaning t m 5114) source

theorem rule8661 (p2027 p3276 p3358 p4348 p4438 p4444 : Prop) (h : (¬ p3358) ∨ (¬ p4444) ∨ p2027 ∨ (¬ p4438) ∨ (¬ p3276) ∨ (¬ p4348)) : (p2027) ∨ (¬ p3276) ∨ (¬ p3358) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial8661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3358)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory1249 t (m.theta 4 8) (m.theta 4 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule8661 (meaning t m 2027) (meaning t m 3276) (meaning t m 3358) (meaning t m 4348) (meaning t m 4438) (meaning t m 4444) source

theorem rule8662 (p4425 p5126 p5127 p5128 p5129 : Prop) : (¬ (p5126 ∧ p5127 ∧ p4425 ∧ p5128 ∧ p5129)) ∨ (p5126) := by
  classical
  tauto

theorem initial8662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5125)) ∨ (meaning t m 5126) := by
  exact rule8662 (meaning t m 4425) (meaning t m 5126) (meaning t m 5127) (meaning t m 5128) (meaning t m 5129)

theorem rule8663 (p4425 p5126 p5127 p5128 p5129 : Prop) : (¬ (p5126 ∧ p5127 ∧ p4425 ∧ p5128 ∧ p5129)) ∨ (p5127) := by
  classical
  tauto

theorem initial8663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5125)) ∨ (meaning t m 5127) := by
  exact rule8663 (meaning t m 4425) (meaning t m 5126) (meaning t m 5127) (meaning t m 5128) (meaning t m 5129)

theorem rule8664 (p4425 p5126 p5127 p5128 p5129 : Prop) : (p4425) ∨ (¬ (p5126 ∧ p5127 ∧ p4425 ∧ p5128 ∧ p5129)) := by
  classical
  tauto

theorem initial8664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4425) ∨ (¬ (meaning t m 5125)) := by
  exact rule8664 (meaning t m 4425) (meaning t m 5126) (meaning t m 5127) (meaning t m 5128) (meaning t m 5129)

theorem rule8670 (p3276 p4184 p5131 p5132 p5133 : Prop) : (p3276) ∨ (¬ (p5131 ∧ p4184 ∧ p3276 ∧ p5132 ∧ p5133)) := by
  classical
  tauto

theorem initial8670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3276) ∨ (¬ (meaning t m 5130)) := by
  exact rule8670 (meaning t m 3276) (meaning t m 4184) (meaning t m 5131) (meaning t m 5132) (meaning t m 5133)

theorem rule8676 (p5125 p5130 : Prop) : (¬ (p5125 ∨ p5130)) ∨ (p5125) ∨ (p5130) := by
  classical
  tauto

theorem initial8676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5124)) ∨ (meaning t m 5125) ∨ (meaning t m 5130) := by
  exact rule8676 (meaning t m 5125) (meaning t m 5130)

theorem rule8677 (p3270 p5124 : Prop) (h : (p3270 ↔ p5124)) : (¬ p3270) ∨ (p5124) := by
  classical
  tauto

theorem initial8677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3270)) ∨ (meaning t m 5124) := by
  have source := ElevenTheory.theory1250 t (m.theta 4 10) (m.theta 4 9) (m.theta 9 10)
  exact rule8677 (meaning t m 3270) (meaning t m 5124) source

theorem rule8681 (p3289 p3296 : Prop) : (p3289) ∨ (p3296) ∨ (¬ (p3289 ∨ p3296)) := by
  classical
  tauto

theorem initial8681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3289) ∨ (meaning t m 3296) ∨ (¬ (meaning t m 5134)) := by
  exact rule8681 (meaning t m 3289) (meaning t m 3296)

theorem rule8682 (p3280 p5134 : Prop) (h : (p3280 ↔ p5134)) : (¬ p3280) ∨ (p5134) := by
  classical
  tauto

theorem initial8682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3280)) ∨ (meaning t m 5134) := by
  have source := ElevenTheory.theory1251 t (m.theta 0 3) (m.theta 0 9) (m.theta 3 9)
  exact rule8682 (meaning t m 3280) (meaning t m 5134) source

theorem rule8700 (p2027 p3172 p3286 p4347 p4350 p4774 : Prop) (h : p2027 ∨ (¬ p4774) ∨ (¬ p3286) ∨ (¬ p3172) ∨ (¬ p4347) ∨ (¬ p4350)) : (p2027) ∨ (¬ p3172) ∨ (¬ p3286) ∨ (¬ p4347) ∨ (¬ p4350) ∨ (¬ p4774) := by
  classical
  tauto

theorem initial8700 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4350)) ∨ (¬ (meaning t m 4774)) := by
  have source := ElevenTheory.theory1254 t (m.theta 0 3) (m.theta 3 8) (m.theta 3 9) (m.theta 6 8) (m.theta 8 9)
  exact rule8700 (meaning t m 2027) (meaning t m 3172) (meaning t m 3286) (meaning t m 4347) (meaning t m 4350) (meaning t m 4774) source

theorem rule8701 (p2528 p2534 : Prop) (h : (¬ p2534) ∨ (¬ p2528)) : (¬ p2528) ∨ (¬ p2534) := by
  classical
  tauto

theorem initial8701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2534)) := by
  have source := ElevenTheory.theory1255 (m.theta 4 8) (m.theta 8 9)
  exact rule8701 (meaning t m 2528) (meaning t m 2534) source

theorem rule8702 (p3166 p3172 : Prop) (h : (¬ p3172) ∨ (¬ p3166)) : (¬ p3166) ∨ (¬ p3172) := by
  classical
  tauto

theorem initial8702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3172)) := by
  have source := ElevenTheory.theory1256 (m.theta 0 3) (m.theta 3 8)
  exact rule8702 (meaning t m 3166) (meaning t m 3172) source

theorem rule8703 (p3549 p4105 p4427 p5141 p5142 : Prop) : (p4105) ∨ (¬ (p4105 ∧ p4427 ∧ p3549 ∧ p5141 ∧ p5142)) := by
  classical
  tauto

theorem initial8703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4105) ∨ (¬ (meaning t m 5140)) := by
  exact rule8703 (meaning t m 3549) (meaning t m 4105) (meaning t m 4427) (meaning t m 5141) (meaning t m 5142)

theorem rule8704 (p3549 p4105 p4427 p5141 p5142 : Prop) : (p4427) ∨ (¬ (p4105 ∧ p4427 ∧ p3549 ∧ p5141 ∧ p5142)) := by
  classical
  tauto

theorem initial8704 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4427) ∨ (¬ (meaning t m 5140)) := by
  exact rule8704 (meaning t m 3549) (meaning t m 4105) (meaning t m 4427) (meaning t m 5141) (meaning t m 5142)

theorem rule8705 (p3549 p4105 p4427 p5141 p5142 : Prop) : (p3549) ∨ (¬ (p4105 ∧ p4427 ∧ p3549 ∧ p5141 ∧ p5142)) := by
  classical
  tauto

theorem initial8705 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3549) ∨ (¬ (meaning t m 5140)) := by
  exact rule8705 (meaning t m 3549) (meaning t m 4105) (meaning t m 4427) (meaning t m 5141) (meaning t m 5142)

theorem rule8707 (p3549 p4105 p4427 p5141 p5142 : Prop) : (¬ (p4105 ∧ p4427 ∧ p3549 ∧ p5141 ∧ p5142)) ∨ (p5142) := by
  classical
  tauto

theorem initial8707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5140)) ∨ (meaning t m 5142) := by
  exact rule8707 (meaning t m 3549) (meaning t m 4105) (meaning t m 4427) (meaning t m 5141) (meaning t m 5142)

end SunPrize.SMT
