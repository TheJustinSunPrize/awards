import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory005
import SunPrize.Certificate.Theory006
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule9391 (p4393 p5440 p5443 p5444 p5445 : Prop) : (¬ (p5443 ∧ p5444 ∧ p4393 ∧ p5440 ∧ p5445)) ∨ (p5444) := by
  classical
  tauto

theorem initial9391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5442)) ∨ (meaning t m 5444) := by
  exact rule9391 (meaning t m 4393) (meaning t m 5440) (meaning t m 5443) (meaning t m 5444) (meaning t m 5445)

theorem rule9392 (p4393 p5440 p5443 p5444 p5445 : Prop) : (p4393) ∨ (¬ (p5443 ∧ p5444 ∧ p4393 ∧ p5440 ∧ p5445)) := by
  classical
  tauto

theorem initial9392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4393) ∨ (¬ (meaning t m 5442)) := by
  exact rule9392 (meaning t m 4393) (meaning t m 5440) (meaning t m 5443) (meaning t m 5444) (meaning t m 5445)

theorem rule9393 (p4393 p5440 p5443 p5444 p5445 : Prop) : (p5440) ∨ (¬ (p5443 ∧ p5444 ∧ p4393 ∧ p5440 ∧ p5445)) := by
  classical
  tauto

theorem initial9393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5440) ∨ (¬ (meaning t m 5442)) := by
  exact rule9393 (meaning t m 4393) (meaning t m 5440) (meaning t m 5443) (meaning t m 5444) (meaning t m 5445)

theorem rule9394 (p4393 p5440 p5443 p5444 p5445 : Prop) : (¬ (p5443 ∧ p5444 ∧ p4393 ∧ p5440 ∧ p5445)) ∨ (p5445) := by
  classical
  tauto

theorem initial9394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5442)) ∨ (meaning t m 5445) := by
  exact rule9394 (meaning t m 4393) (meaning t m 5440) (meaning t m 5443) (meaning t m 5444) (meaning t m 5445)

theorem rule9395 (p4393 p5440 p5443 p5444 p5445 : Prop) : (¬ p4393) ∨ (¬ p5440) ∨ ((p5443 ∧ p5444 ∧ p4393 ∧ p5440 ∧ p5445)) ∨ (¬ p5443) ∨ (¬ p5444) ∨ (¬ p5445) := by
  classical
  tauto

theorem initial9395 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 5440)) ∨ (meaning t m 5442) ∨ (¬ (meaning t m 5443)) ∨ (¬ (meaning t m 5444)) ∨ (¬ (meaning t m 5445)) := by
  exact rule9395 (meaning t m 4393) (meaning t m 5440) (meaning t m 5443) (meaning t m 5444) (meaning t m 5445)

theorem rule9397 (p3737 p5447 p5448 p5449 p5450 : Prop) : (¬ (p5447 ∧ p5448 ∧ p3737 ∧ p5449 ∧ p5450)) ∨ (p5448) := by
  classical
  tauto

theorem initial9397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5446)) ∨ (meaning t m 5448) := by
  exact rule9397 (meaning t m 3737) (meaning t m 5447) (meaning t m 5448) (meaning t m 5449) (meaning t m 5450)

theorem rule9398 (p3737 p5447 p5448 p5449 p5450 : Prop) : (p3737) ∨ (¬ (p5447 ∧ p5448 ∧ p3737 ∧ p5449 ∧ p5450)) := by
  classical
  tauto

theorem initial9398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3737) ∨ (¬ (meaning t m 5446)) := by
  exact rule9398 (meaning t m 3737) (meaning t m 5447) (meaning t m 5448) (meaning t m 5449) (meaning t m 5450)

theorem rule9399 (p3737 p5447 p5448 p5449 p5450 : Prop) : (¬ (p5447 ∧ p5448 ∧ p3737 ∧ p5449 ∧ p5450)) ∨ (p5449) := by
  classical
  tauto

theorem initial9399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5446)) ∨ (meaning t m 5449) := by
  exact rule9399 (meaning t m 3737) (meaning t m 5447) (meaning t m 5448) (meaning t m 5449) (meaning t m 5450)

theorem rule9404 (p5442 p5446 : Prop) : (¬ (p5442 ∨ p5446)) ∨ (p5442) ∨ (p5446) := by
  classical
  tauto

theorem initial9404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5441)) ∨ (meaning t m 5442) ∨ (meaning t m 5446) := by
  exact rule9404 (meaning t m 5442) (meaning t m 5446)

theorem rule9405 (p3731 p5441 : Prop) (h : (p3731 ↔ p5441)) : (¬ p3731) ∨ (p5441) := by
  classical
  tauto

theorem initial9405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3731)) ∨ (meaning t m 5441) := by
  have source := ElevenTheory.theory1432 t (m.theta 5 10) (m.theta 5 6) (m.theta 6 10)
  exact rule9405 (meaning t m 3731) (meaning t m 5441) source

theorem rule9407 (p2027 p2922 p3238 p3569 p4948 p5102 : Prop) (h : p2027 ∨ (¬ p3238) ∨ (¬ p4948) ∨ (¬ p5102) ∨ (¬ p3569) ∨ (¬ p2922)) : (p2027) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3569) ∨ (¬ p4948) ∨ (¬ p5102) := by
  classical
  tauto

theorem initial9407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5102)) := by
  have source := ElevenTheory.theory1433 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 9)
  exact rule9407 (meaning t m 2027) (meaning t m 2922) (meaning t m 3238) (meaning t m 3569) (meaning t m 4948) (meaning t m 5102) source

theorem rule9408 (p2027 p2230 p2982 p3054 p4385 p4730 : Prop) (h : (¬ p4730) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3054) ∨ (¬ p4385) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3054) ∨ (¬ p4385) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial9408 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory1434 t (m.theta 0 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 9)
  exact rule9408 (meaning t m 2027) (meaning t m 2230) (meaning t m 2982) (meaning t m 3054) (meaning t m 4385) (meaning t m 4730) source

theorem rule9409 (p2027 p2138 p3471 p3486 p4344 p4875 : Prop) (h : (¬ p4875) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p2138) ∨ (¬ p3486) ∨ (¬ p4344)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3471) ∨ (¬ p3486) ∨ (¬ p4344) ∨ (¬ p4875) := by
  classical
  tauto

theorem initial9409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4344)) ∨ (¬ (meaning t m 4875)) := by
  have source := ElevenTheory.theory1435 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7)
  exact rule9409 (meaning t m 2027) (meaning t m 2138) (meaning t m 3471) (meaning t m 3486) (meaning t m 4344) (meaning t m 4875) source

theorem rule9410 (p2027 p2807 p2952 p4235 p4333 p4705 : Prop) (h : (¬ p4705) ∨ (¬ p2807) ∨ (¬ p4333) ∨ (¬ p4235) ∨ (¬ p2952) ∨ p2027) : (p2027) ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p4235) ∨ (¬ p4333) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial9410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory1436 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7)
  exact rule9410 (meaning t m 2027) (meaning t m 2807) (meaning t m 2952) (meaning t m 4235) (meaning t m 4333) (meaning t m 4705) source

theorem rule9411 (p2027 p3367 p3422 p3583 p3698 p4717 : Prop) (h : (¬ p3583) ∨ (¬ p3422) ∨ (¬ p4717) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p3698)) : (p2027) ∨ (¬ p3367) ∨ (¬ p3422) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial9411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory1437 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6)
  exact rule9411 (meaning t m 2027) (meaning t m 3367) (meaning t m 3422) (meaning t m 3583) (meaning t m 3698) (meaning t m 4717) source

theorem rule9413 (p2027 p2427 p2573 p3556 p3904 p4717 : Prop) (h : (¬ p3904) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p4717) ∨ (¬ p3556) ∨ (¬ p2427)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2573) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial9413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory1439 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule9413 (meaning t m 2027) (meaning t m 2427) (meaning t m 2573) (meaning t m 3556) (meaning t m 3904) (meaning t m 4717) source

theorem rule9414 (p2027 p3212 p3684 p4399 p4730 p4948 : Prop) (h : (¬ p4730) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p4399) ∨ (¬ p4948) ∨ (¬ p3212)) : (p2027) ∨ (¬ p3212) ∨ (¬ p3684) ∨ (¬ p4399) ∨ (¬ p4730) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial9414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4730)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory1440 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9)
  exact rule9414 (meaning t m 2027) (meaning t m 3212) (meaning t m 3684) (meaning t m 4399) (meaning t m 4730) (meaning t m 4948) source

theorem rule9415 (p2850 p3684 : Prop) (h : (¬ p3684) ∨ (¬ p2850)) : (¬ p2850) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial9415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory1441 (m.theta 2 4) (m.theta 4 5)
  exact rule9415 (meaning t m 2850) (meaning t m 3684) source

theorem rule9416 (p2427 p4235 : Prop) (h : (¬ p4235) ∨ (¬ p2427)) : (¬ p2427) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial9416 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory1442 (m.theta 4 5) (m.theta 5 7)
  exact rule9416 (meaning t m 2427) (meaning t m 4235) source

theorem rule9417 (p2027 p2156 p3684 p4110 p4399 p4730 : Prop) (h : (¬ p4399) ∨ (¬ p4730) ∨ (¬ p3684) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3684) ∨ (¬ p4110) ∨ (¬ p4399) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial9417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory1443 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6)
  exact rule9417 (meaning t m 2027) (meaning t m 2156) (meaning t m 3684) (meaning t m 4110) (meaning t m 4399) (meaning t m 4730) source

theorem rule9418 (p2027 p2341 p2509 p2922 p3577 p4383 p5087 : Prop) (h : (¬ p5087) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p3577) ∨ (¬ p2509) ∨ (¬ p2341) ∨ (¬ p4383)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2509) ∨ (¬ p2922) ∨ (¬ p3577) ∨ (¬ p4383) ∨ (¬ p5087) := by
  classical
  tauto

theorem initial9418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 5087)) := by
  have source := ElevenTheory.theory1444 t (m.theta 0 7) (m.theta 1 4) (m.theta 2 7) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule9418 (meaning t m 2027) (meaning t m 2341) (meaning t m 2509) (meaning t m 2922) (meaning t m 3577) (meaning t m 4383) (meaning t m 5087) source

theorem rule9419 (p2027 p2274 p2588 p2590 p2860 p4885 : Prop) (h : (¬ p2588) ∨ (¬ p2590) ∨ (¬ p4885) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2860)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p2860) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial9419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory1445 t (m.theta 2 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule9419 (meaning t m 2027) (meaning t m 2274) (meaning t m 2588) (meaning t m 2590) (meaning t m 2860) (meaning t m 4885) source

theorem rule9420 (p2027 p2341 p2870 p3548 p3554 p3691 p4875 : Prop) (h : (¬ p3548) ∨ (¬ p2870) ∨ (¬ p3691) ∨ (¬ p3554) ∨ p2027 ∨ (¬ p4875) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2870) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p3691) ∨ (¬ p4875) := by
  classical
  tauto

theorem initial9420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3554)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 4875)) := by
  have source := ElevenTheory.theory1446 t (m.theta 0 7) (m.theta 1 5) (m.theta 1 7) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule9420 (meaning t m 2027) (meaning t m 2341) (meaning t m 2870) (meaning t m 3548) (meaning t m 3554) (meaning t m 3691) (meaning t m 4875) source

theorem rule9422 (p4035 p5453 p5454 p5455 p5456 : Prop) : (¬ (p5453 ∧ p5454 ∧ p4035 ∧ p5455 ∧ p5456)) ∨ (p5453) := by
  classical
  tauto

theorem initial9422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5452)) ∨ (meaning t m 5453) := by
  exact rule9422 (meaning t m 4035) (meaning t m 5453) (meaning t m 5454) (meaning t m 5455) (meaning t m 5456)

theorem rule9423 (p4035 p5453 p5454 p5455 p5456 : Prop) : (¬ (p5453 ∧ p5454 ∧ p4035 ∧ p5455 ∧ p5456)) ∨ (p5454) := by
  classical
  tauto

theorem initial9423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5452)) ∨ (meaning t m 5454) := by
  exact rule9423 (meaning t m 4035) (meaning t m 5453) (meaning t m 5454) (meaning t m 5455) (meaning t m 5456)

theorem rule9424 (p4035 p5453 p5454 p5455 p5456 : Prop) : (p4035) ∨ (¬ (p5453 ∧ p5454 ∧ p4035 ∧ p5455 ∧ p5456)) := by
  classical
  tauto

theorem initial9424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4035) ∨ (¬ (meaning t m 5452)) := by
  exact rule9424 (meaning t m 4035) (meaning t m 5453) (meaning t m 5454) (meaning t m 5455) (meaning t m 5456)

theorem rule9429 (p3755 p5458 p5459 p5460 p5461 : Prop) : (¬ (p5458 ∧ p5459 ∧ p3755 ∧ p5460 ∧ p5461)) ∨ (p5459) := by
  classical
  tauto

theorem initial9429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5457)) ∨ (meaning t m 5459) := by
  exact rule9429 (meaning t m 3755) (meaning t m 5458) (meaning t m 5459) (meaning t m 5460) (meaning t m 5461)

theorem rule9430 (p3755 p5458 p5459 p5460 p5461 : Prop) : (p3755) ∨ (¬ (p5458 ∧ p5459 ∧ p3755 ∧ p5460 ∧ p5461)) := by
  classical
  tauto

theorem initial9430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3755) ∨ (¬ (meaning t m 5457)) := by
  exact rule9430 (meaning t m 3755) (meaning t m 5458) (meaning t m 5459) (meaning t m 5460) (meaning t m 5461)

theorem rule9436 (p5452 p5457 : Prop) : (¬ (p5452 ∨ p5457)) ∨ (p5452) ∨ (p5457) := by
  classical
  tauto

theorem initial9436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5451)) ∨ (meaning t m 5452) ∨ (meaning t m 5457) := by
  exact rule9436 (meaning t m 5452) (meaning t m 5457)

theorem rule9437 (p3749 p5451 : Prop) (h : (p3749 ↔ p5451)) : (¬ p3749) ∨ (p5451) := by
  classical
  tauto

theorem initial9437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3749)) ∨ (meaning t m 5451) := by
  have source := ElevenTheory.theory1448 t (m.theta 2 3) (m.theta 2 9) (m.theta 3 9)
  exact rule9437 (meaning t m 3749) (meaning t m 5451) source

theorem rule9439 (p3156 p3497 : Prop) (h : (¬ p3497) ∨ (¬ p3156)) : (¬ p3156) ∨ (¬ p3497) := by
  classical
  tauto

theorem initial9439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3497)) := by
  have source := ElevenTheory.theory1449 (m.theta 3 5) (m.theta 5 8)
  exact rule9439 (meaning t m 3156) (meaning t m 3497) source

theorem rule9440 (p2563 p4110 : Prop) (h : (¬ p4110) ∨ (¬ p2563)) : (¬ p2563) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial9440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory1450 (m.theta 4 5) (m.theta 5 6)
  exact rule9440 (meaning t m 2563) (meaning t m 4110) source

theorem rule9442 (p2027 p2542 p2563 p3742 p4001 p4555 : Prop) (h : (¬ p2563) ∨ (¬ p4001) ∨ (¬ p2542) ∨ p2027 ∨ (¬ p4555) ∨ (¬ p3742)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p3742) ∨ (¬ p4001) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial9442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory1452 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7)
  exact rule9442 (meaning t m 2027) (meaning t m 2542) (meaning t m 2563) (meaning t m 3742) (meaning t m 4001) (meaning t m 4555) source

theorem rule9443 (p2027 p2930 p3083 p3548 p3742 p4404 : Prop) (h : p2027 ∨ (¬ p2930) ∨ (¬ p3548) ∨ (¬ p3742) ∨ (¬ p4404) ∨ (¬ p3083)) : (p2027) ∨ (¬ p2930) ∨ (¬ p3083) ∨ (¬ p3548) ∨ (¬ p3742) ∨ (¬ p4404) := by
  classical
  tauto

theorem initial9443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2930)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4404)) := by
  have source := ElevenTheory.theory1453 t (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule9443 (meaning t m 2027) (meaning t m 2930) (meaning t m 3083) (meaning t m 3548) (meaning t m 3742) (meaning t m 4404) source

theorem rule9444 (p2027 p2230 p2417 p3821 p4644 p5197 : Prop) (h : (¬ p4644) ∨ p2027 ∨ (¬ p5197) ∨ (¬ p2230) ∨ (¬ p2417) ∨ (¬ p3821)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2417) ∨ (¬ p3821) ∨ (¬ p4644) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial9444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4644)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory1454 t (m.theta 0 4) (m.theta 0 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule9444 (meaning t m 2027) (meaning t m 2230) (meaning t m 2417) (meaning t m 3821) (meaning t m 4644) (meaning t m 5197) source

theorem rule9445 (p3422 p3584 : Prop) (h : (¬ p3584) ∨ (¬ p3422)) : (¬ p3422) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial9445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory1455 (m.theta 2 4) (m.theta 4 6)
  exact rule9445 (meaning t m 3422) (meaning t m 3584) source

theorem rule9447 (p2027 p2313 p2417 p2581 p3920 p4107 : Prop) (h : p2027 ∨ (¬ p2581) ∨ (¬ p2313) ∨ (¬ p3920) ∨ (¬ p2417) ∨ (¬ p4107)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2417) ∨ (¬ p2581) ∨ (¬ p3920) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial9447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2581)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory1457 t (m.theta 0 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule9447 (meaning t m 2027) (meaning t m 2313) (meaning t m 2417) (meaning t m 2581) (meaning t m 3920) (meaning t m 4107) source

theorem rule9448 (p2027 p2341 p3027 p4360 p4548 p4854 : Prop) (h : (¬ p4854) ∨ (¬ p4360) ∨ (¬ p3027) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p4548)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3027) ∨ (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4854) := by
  classical
  tauto

theorem initial9448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4548)) ∨ (¬ (meaning t m 4854)) := by
  have source := ElevenTheory.theory1458 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8)
  exact rule9448 (meaning t m 2027) (meaning t m 2341) (meaning t m 3027) (meaning t m 4360) (meaning t m 4548) (meaning t m 4854) source

theorem rule9449 (p2027 p2341 p2493 p2926 p3548 p3575 p3741 p4717 : Prop) (h : (¬ p3575) ∨ p2027 ∨ (¬ p3548) ∨ (¬ p3741) ∨ (¬ p2926) ∨ (¬ p4717) ∨ (¬ p2341) ∨ (¬ p2493)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2493) ∨ (¬ p2926) ∨ (¬ p3548) ∨ (¬ p3575) ∨ (¬ p3741) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial9449 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory1459 t (m.theta 0 7) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule9449 (meaning t m 2027) (meaning t m 2341) (meaning t m 2493) (meaning t m 2926) (meaning t m 3548) (meaning t m 3575) (meaning t m 3741) (meaning t m 4717) source

theorem rule9450 (p2027 p2657 p2946 p3238 p4241 p4811 : Prop) (h : (¬ p4811) ∨ (¬ p3238) ∨ (¬ p2946) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p4241)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3238) ∨ (¬ p4241) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial9450 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory1460 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule9450 (meaning t m 2027) (meaning t m 2657) (meaning t m 2946) (meaning t m 3238) (meaning t m 4241) (meaning t m 4811) source

theorem rule9451 (p2440 p2542 : Prop) (h : (¬ p2440) ∨ (¬ p2542)) : (¬ p2440) ∨ (¬ p2542) := by
  classical
  tauto

theorem initial9451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2542)) := by
  have source := ElevenTheory.theory1461 (m.theta 3 4) (m.theta 4 5)
  exact rule9451 (meaning t m 2440) (meaning t m 2542) source

theorem rule9454 (p3770 p3777 : Prop) : (p3770) ∨ (p3777) ∨ (¬ (p3770 ∨ p3777)) := by
  classical
  tauto

theorem initial9454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3770) ∨ (meaning t m 3777) ∨ (¬ (meaning t m 5462)) := by
  exact rule9454 (meaning t m 3770) (meaning t m 3777)

theorem rule9455 (p3761 p5462 : Prop) (h : (p3761 ↔ p5462)) : (¬ p3761) ∨ (p5462) := by
  classical
  tauto

theorem initial9455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3761)) ∨ (meaning t m 5462) := by
  have source := ElevenTheory.theory1462 t (m.theta 0 10) (m.theta 0 9) (m.theta 9 10)
  exact rule9455 (meaning t m 3761) (meaning t m 5462) source

theorem rule9478 (p2027 p2396 p2761 p3579 p4276 p4429 p5284 : Prop) (h : (¬ p4276) ∨ (¬ p3579) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p5284) ∨ (¬ p4429) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p3579) ∨ (¬ p4276) ∨ (¬ p4429) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial9478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4429)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory1465 t (m.theta 3 7) (m.theta 3 9) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule9478 (meaning t m 2027) (meaning t m 2396) (meaning t m 2761) (meaning t m 3579) (meaning t m 4276) (meaning t m 4429) (meaning t m 5284) source

theorem rule9481 (p4260 p5470 p5471 p5472 p5473 : Prop) : (p4260) ∨ (¬ (p5470 ∧ p5471 ∧ p4260 ∧ p5472 ∧ p5473)) := by
  classical
  tauto

theorem initial9481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4260) ∨ (¬ (meaning t m 5469)) := by
  exact rule9481 (meaning t m 4260) (meaning t m 5470) (meaning t m 5471) (meaning t m 5472) (meaning t m 5473)

theorem rule9482 (p4260 p5470 p5471 p5472 p5473 : Prop) : (¬ (p5470 ∧ p5471 ∧ p4260 ∧ p5472 ∧ p5473)) ∨ (p5472) := by
  classical
  tauto

theorem initial9482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5469)) ∨ (meaning t m 5472) := by
  exact rule9482 (meaning t m 4260) (meaning t m 5470) (meaning t m 5471) (meaning t m 5472) (meaning t m 5473)

theorem rule9485 (p3791 p5475 p5476 p5477 p5478 : Prop) : (¬ (p5475 ∧ p5476 ∧ p3791 ∧ p5477 ∧ p5478)) ∨ (p5475) := by
  classical
  tauto

theorem initial9485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5474)) ∨ (meaning t m 5475) := by
  exact rule9485 (meaning t m 3791) (meaning t m 5475) (meaning t m 5476) (meaning t m 5477) (meaning t m 5478)

theorem rule9487 (p3791 p5475 p5476 p5477 p5478 : Prop) : (p3791) ∨ (¬ (p5475 ∧ p5476 ∧ p3791 ∧ p5477 ∧ p5478)) := by
  classical
  tauto

theorem initial9487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3791) ∨ (¬ (meaning t m 5474)) := by
  exact rule9487 (meaning t m 3791) (meaning t m 5475) (meaning t m 5476) (meaning t m 5477) (meaning t m 5478)

theorem rule9488 (p3791 p5475 p5476 p5477 p5478 : Prop) : (¬ (p5475 ∧ p5476 ∧ p3791 ∧ p5477 ∧ p5478)) ∨ (p5477) := by
  classical
  tauto

theorem initial9488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5474)) ∨ (meaning t m 5477) := by
  exact rule9488 (meaning t m 3791) (meaning t m 5475) (meaning t m 5476) (meaning t m 5477) (meaning t m 5478)

theorem rule9493 (p5469 p5474 : Prop) : (¬ (p5469 ∨ p5474)) ∨ (p5469) ∨ (p5474) := by
  classical
  tauto

theorem initial9493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5468)) ∨ (meaning t m 5469) ∨ (meaning t m 5474) := by
  exact rule9493 (meaning t m 5469) (meaning t m 5474)

theorem rule9494 (p3785 p5468 : Prop) (h : (p3785 ↔ p5468)) : (¬ p3785) ∨ (p5468) := by
  classical
  tauto

theorem initial9494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3785)) ∨ (meaning t m 5468) := by
  have source := ElevenTheory.theory1466 t (m.theta 6 10) (m.theta 6 7) (m.theta 7 10)
  exact rule9494 (meaning t m 3785) (meaning t m 5468) source

theorem rule9499 (p3795 p5479 : Prop) (h : (p3795 ↔ p5479)) : (¬ p3795) ∨ (p5479) := by
  classical
  tauto

theorem initial9499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3795)) ∨ (meaning t m 5479) := by
  have source := ElevenTheory.theory1467 t (m.theta 1 10) (m.theta 1 4) (m.theta 4 10)
  exact rule9499 (meaning t m 3795) (meaning t m 5479) source

theorem rule9503 (p3804 p3810 : Prop) : (p3804) ∨ (¬ p3810) ∨ ((p3804 ↔ (¬ p3810))) := by
  classical
  tauto

theorem initial9503 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3804) ∨ (¬ (meaning t m 3810)) ∨ (meaning t m 5480) := by
  exact rule9503 (meaning t m 3804) (meaning t m 3810)

theorem rule9504 (p3804 p3810 : Prop) : (¬ p3804) ∨ (p3810) ∨ ((p3804 ↔ (¬ p3810))) := by
  classical
  tauto

theorem initial9504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3804)) ∨ (meaning t m 3810) ∨ (meaning t m 5480) := by
  exact rule9504 (meaning t m 3804) (meaning t m 3810)

theorem rule9507 (p3811 p3816 : Prop) : (p3811) ∨ (¬ p3816) ∨ ((p3811 ↔ (¬ p3816))) := by
  classical
  tauto

theorem initial9507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3811) ∨ (¬ (meaning t m 3816)) ∨ (meaning t m 5481) := by
  exact rule9507 (meaning t m 3811) (meaning t m 3816)

theorem rule9508 (p3811 p3816 : Prop) : (¬ p3811) ∨ (p3816) ∨ ((p3811 ↔ (¬ p3816))) := by
  classical
  tauto

theorem initial9508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3811)) ∨ (meaning t m 3816) ∨ (meaning t m 5481) := by
  exact rule9508 (meaning t m 3811) (meaning t m 3816)

theorem rule9511 (p3810 p3816 : Prop) : (¬ p3810) ∨ (¬ p3816) ∨ (¬ ((¬ p3810) ∨ (¬ p3816))) := by
  classical
  tauto

theorem initial9511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3810)) ∨ (¬ (meaning t m 3816)) ∨ (¬ (meaning t m 5483)) := by
  exact rule9511 (meaning t m 3810) (meaning t m 3816)

theorem rule9512 (p5479 p5483 : Prop) : (¬ p5479) ∨ (¬ (p5479 ↔ p5483)) ∨ (p5483) := by
  classical
  tauto

theorem initial9512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5479)) ∨ (¬ (meaning t m 5482)) ∨ (meaning t m 5483) := by
  exact rule9512 (meaning t m 5479) (meaning t m 5483)

theorem rule9516 (p5480 p5481 p5482 : Prop) (h : ((¬ p5480) ∨ (¬ p5481) ∨ p5482)) : (¬ p5480) ∨ (¬ p5481) ∨ (p5482) := by
  classical
  tauto

theorem initial9516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5480)) ∨ (¬ (meaning t m 5481)) ∨ (meaning t m 5482) := by
  have source := ElevenTheory.theory1468 t (m.theta 1 10) (m.theta 1 4) (m.theta 4 10)
  exact rule9516 (meaning t m 5480) (meaning t m 5481) (meaning t m 5482) source

theorem rule9518 (p2027 p2230 p3362 p3365 p3684 p4752 : Prop) (h : (¬ p3365) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p3362) ∨ (¬ p4752)) : (p2027) ∨ (¬ p2230) ∨ (¬ p3362) ∨ (¬ p3365) ∨ (¬ p3684) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial9518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory1471 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5)
  exact rule9518 (meaning t m 2027) (meaning t m 2230) (meaning t m 3362) (meaning t m 3365) (meaning t m 3684) (meaning t m 4752) source

theorem rule9519 (p2027 p2230 p2247 p3238 p4079 p4813 : Prop) (h : (¬ p2230) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p4079) ∨ (¬ p2247) ∨ (¬ p4813)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p3238) ∨ (¬ p4079) ∨ (¬ p4813) := by
  classical
  tauto

theorem initial9519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4813)) := by
  have source := ElevenTheory.theory1472 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 4 5)
  exact rule9519 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 3238) (meaning t m 4079) (meaning t m 4813) source

theorem rule9521 (p2027 p2588 p2807 p2963 p3552 p4976 : Prop) (h : (¬ p2588) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3552) ∨ (¬ p4976) ∨ p2027) : (p2027) ∨ (¬ p2588) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3552) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial9521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory1474 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7)
  exact rule9521 (meaning t m 2027) (meaning t m 2588) (meaning t m 2807) (meaning t m 2963) (meaning t m 3552) (meaning t m 4976) source

theorem rule9522 (p2027 p2761 p3246 p4025 p4191 p4559 : Prop) (h : (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4559) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2761) ∨ (¬ p3246) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial9522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4025)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory1475 t (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule9522 (meaning t m 2027) (meaning t m 2761) (meaning t m 3246) (meaning t m 4025) (meaning t m 4191) (meaning t m 4559) source

theorem rule9523 (p2027 p3680 p3947 p4192 p4280 p4381 : Prop) (h : (¬ p3947) ∨ (¬ p4280) ∨ (¬ p4381) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p4192)) : (p2027) ∨ (¬ p3680) ∨ (¬ p3947) ∨ (¬ p4192) ∨ (¬ p4280) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial9523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4192)) ∨ (¬ (meaning t m 4280)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory1476 t (m.theta 3 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule9523 (meaning t m 2027) (meaning t m 3680) (meaning t m 3947) (meaning t m 4192) (meaning t m 4280) (meaning t m 4381) source

theorem rule9524 (p2027 p2470 p2930 p3540 p3548 p4404 : Prop) (h : (¬ p3548) ∨ (¬ p4404) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p2930) ∨ (¬ p2470)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2930) ∨ (¬ p3540) ∨ (¬ p3548) ∨ (¬ p4404) := by
  classical
  tauto

theorem initial9524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2930)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4404)) := by
  have source := ElevenTheory.theory1477 t (m.theta 0 4) (m.theta 1 7) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule9524 (meaning t m 2027) (meaning t m 2470) (meaning t m 2930) (meaning t m 3540) (meaning t m 3548) (meaning t m 4404) source

theorem rule9525 (p2027 p2696 p3434 p3820 p3821 p4778 : Prop) (h : (¬ p3434) ∨ (¬ p3820) ∨ (¬ p3821) ∨ p2027 ∨ (¬ p4778) ∨ (¬ p2696)) : (p2027) ∨ (¬ p2696) ∨ (¬ p3434) ∨ (¬ p3820) ∨ (¬ p3821) ∨ (¬ p4778) := by
  classical
  tauto

theorem initial9525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4778)) := by
  have source := ElevenTheory.theory1478 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 3) (m.theta 2 7) (m.theta 7 9)
  exact rule9525 (meaning t m 2027) (meaning t m 2696) (meaning t m 3434) (meaning t m 3820) (meaning t m 3821) (meaning t m 4778) source

theorem rule9526 (p2027 p2383 p2493 p2509 p2586 p4432 : Prop) (h : (¬ p2383) ∨ (¬ p2586) ∨ (¬ p2493) ∨ (¬ p4432) ∨ p2027 ∨ (¬ p2509)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2586) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial9526 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2586)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory1479 t (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule9526 (meaning t m 2027) (meaning t m 2383) (meaning t m 2493) (meaning t m 2509) (meaning t m 2586) (meaning t m 4432) source

theorem rule9527 (p2027 p2911 p3201 p3553 p4112 p4753 : Prop) (h : (¬ p4112) ∨ (¬ p3553) ∨ (¬ p3201) ∨ (¬ p2911) ∨ (¬ p4753) ∨ p2027) : (p2027) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3553) ∨ (¬ p4112) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial9527 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory1480 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule9527 (meaning t m 2027) (meaning t m 2911) (meaning t m 3201) (meaning t m 3553) (meaning t m 4112) (meaning t m 4753) source

theorem rule9528 (p2027 p3362 p3365 p3389 p3876 p4752 : Prop) (h : (¬ p3365) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p4752) ∨ p2027 ∨ (¬ p3876)) : (p2027) ∨ (¬ p3362) ∨ (¬ p3365) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial9528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory1481 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 7)
  exact rule9528 (meaning t m 2027) (meaning t m 3362) (meaning t m 3365) (meaning t m 3389) (meaning t m 3876) (meaning t m 4752) source

theorem rule9529 (p2122 p3822 : Prop) (h : (¬ p3822) ∨ (¬ p2122)) : (¬ p2122) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial9529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory1482 (m.theta 2 6) (m.theta 6 7)
  exact rule9529 (meaning t m 2122) (meaning t m 3822) source

theorem rule9532 (p3834 p5486 p5487 p5488 p5489 : Prop) : (¬ (p5486 ∧ p5487 ∧ p3834 ∧ p5488 ∧ p5489)) ∨ (p5487) := by
  classical
  tauto

theorem initial9532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5485)) ∨ (meaning t m 5487) := by
  exact rule9532 (meaning t m 3834) (meaning t m 5486) (meaning t m 5487) (meaning t m 5488) (meaning t m 5489)

theorem rule9533 (p3834 p5486 p5487 p5488 p5489 : Prop) : (p3834) ∨ (¬ (p5486 ∧ p5487 ∧ p3834 ∧ p5488 ∧ p5489)) := by
  classical
  tauto

theorem initial9533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3834) ∨ (¬ (meaning t m 5485)) := by
  exact rule9533 (meaning t m 3834) (meaning t m 5486) (meaning t m 5487) (meaning t m 5488) (meaning t m 5489)

theorem rule9537 (p3830 p4374 p4439 p5491 p5492 : Prop) : (p4374) ∨ (¬ (p4374 ∧ p4439 ∧ p3830 ∧ p5491 ∧ p5492)) := by
  classical
  tauto

theorem initial9537 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4374) ∨ (¬ (meaning t m 5490)) := by
  exact rule9537 (meaning t m 3830) (meaning t m 4374) (meaning t m 4439) (meaning t m 5491) (meaning t m 5492)

theorem rule9538 (p3830 p4374 p4439 p5491 p5492 : Prop) : (p4439) ∨ (¬ (p4374 ∧ p4439 ∧ p3830 ∧ p5491 ∧ p5492)) := by
  classical
  tauto

theorem initial9538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4439) ∨ (¬ (meaning t m 5490)) := by
  exact rule9538 (meaning t m 3830) (meaning t m 4374) (meaning t m 4439) (meaning t m 5491) (meaning t m 5492)

theorem rule9539 (p3830 p4374 p4439 p5491 p5492 : Prop) : (p3830) ∨ (¬ (p4374 ∧ p4439 ∧ p3830 ∧ p5491 ∧ p5492)) := by
  classical
  tauto

theorem initial9539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3830) ∨ (¬ (meaning t m 5490)) := by
  exact rule9539 (meaning t m 3830) (meaning t m 4374) (meaning t m 4439) (meaning t m 5491) (meaning t m 5492)

theorem rule9545 (p5485 p5490 : Prop) : (¬ (p5485 ∨ p5490)) ∨ (p5485) ∨ (p5490) := by
  classical
  tauto

theorem initial9545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5484)) ∨ (meaning t m 5485) ∨ (meaning t m 5490) := by
  exact rule9545 (meaning t m 5485) (meaning t m 5490)

theorem rule9546 (p3824 p5484 : Prop) (h : (p3824 ↔ p5484)) : (¬ p3824) ∨ (p5484) := by
  classical
  tauto

theorem initial9546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3824)) ∨ (meaning t m 5484) := by
  have source := ElevenTheory.theory1484 t (m.theta 0 1) (m.theta 0 9) (m.theta 1 9)
  exact rule9546 (meaning t m 3824) (meaning t m 5484) source

theorem rule9550 (p3845 p3852 : Prop) : (p3845) ∨ (p3852) ∨ (¬ (p3845 ∨ p3852)) := by
  classical
  tauto

theorem initial9550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3845) ∨ (meaning t m 3852) ∨ (¬ (meaning t m 5493)) := by
  exact rule9550 (meaning t m 3845) (meaning t m 3852)

theorem rule9551 (p3836 p5493 : Prop) (h : (p3836 ↔ p5493)) : (¬ p3836) ∨ (p5493) := by
  classical
  tauto

theorem initial9551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3836)) ∨ (meaning t m 5493) := by
  have source := ElevenTheory.theory1485 t (m.theta 1 3) (m.theta 1 9) (m.theta 3 9)
  exact rule9551 (meaning t m 3836) (meaning t m 5493) source

theorem rule9574 (p3707 p4321 : Prop) (h : (¬ p4321) ∨ (¬ p3707)) : (¬ p3707) ∨ (¬ p4321) := by
  classical
  tauto

theorem initial9574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4321)) := by
  have source := ElevenTheory.theory1488 (m.theta 1 9) (m.theta 9 10)
  exact rule9574 (meaning t m 3707) (meaning t m 4321) source

theorem rule9575 (p2027 p2475 p2930 p3548 p3641 p3876 p4403 : Prop) (h : (¬ p4403) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3548) ∨ (¬ p2475) ∨ (¬ p2930) ∨ p2027) : (p2027) ∨ (¬ p2475) ∨ (¬ p2930) ∨ (¬ p3548) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4403) := by
  classical
  tauto

theorem initial9575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 2930)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4403)) := by
  have source := ElevenTheory.theory1489 t (m.theta 0 8) (m.theta 1 7) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule9575 (meaning t m 2027) (meaning t m 2475) (meaning t m 2930) (meaning t m 3548) (meaning t m 3641) (meaning t m 3876) (meaning t m 4403) source

theorem rule9576 (p2542 p3574 p3660 : Prop) (h : (¬ p2542) ∨ (¬ p3574) ∨ (¬ p3660)) : (¬ p2542) ∨ (¬ p3574) ∨ (¬ p3660) := by
  classical
  tauto

theorem initial9576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3660)) := by
  have source := ElevenTheory.theory1490 (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule9576 (meaning t m 2542) (meaning t m 3574) (meaning t m 3660) source

theorem rule9577 (p2881 p3548 p3571 : Prop) (h : (¬ p3548) ∨ (¬ p2881) ∨ (¬ p3571)) : (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3571) := by
  classical
  tauto

theorem initial9577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3571)) := by
  have source := ElevenTheory.theory1491 (m.theta 1 7) (m.theta 5 7) (m.theta 7 8)
  exact rule9577 (meaning t m 2881) (meaning t m 3548) (meaning t m 3571) source

theorem rule9578 (p2027 p2230 p2780 p3362 p3684 p5221 : Prop) (h : (¬ p2780) ∨ p2027 ∨ (¬ p5221) ∨ (¬ p3684) ∨ (¬ p2230) ∨ (¬ p3362)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2780) ∨ (¬ p3362) ∨ (¬ p3684) ∨ (¬ p5221) := by
  classical
  tauto

theorem initial9578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 5221)) := by
  have source := ElevenTheory.theory1492 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5)
  exact rule9578 (meaning t m 2027) (meaning t m 2230) (meaning t m 2780) (meaning t m 3362) (meaning t m 3684) (meaning t m 5221) source

theorem rule9579 (p2027 p2930 p3355 p3540 p3817 p4451 : Prop) (h : (¬ p2930) ∨ (¬ p3817) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p3355) ∨ (¬ p4451)) : (p2027) ∨ (¬ p2930) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p3817) ∨ (¬ p4451) := by
  classical
  tauto

theorem initial9579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2930)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4451)) := by
  have source := ElevenTheory.theory1493 t (m.theta 0 4) (m.theta 1 7) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9)
  exact rule9579 (meaning t m 2027) (meaning t m 2930) (meaning t m 3355) (meaning t m 3540) (meaning t m 3817) (meaning t m 4451) source

theorem rule9581 (p5501 p5502 p5503 p5504 p5505 : Prop) : (¬ (p5501 ∧ p5502 ∧ p5503 ∧ p5504 ∧ p5505)) ∨ (p5501) := by
  classical
  tauto

theorem initial9581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5500)) ∨ (meaning t m 5501) := by
  exact rule9581 (meaning t m 5501) (meaning t m 5502) (meaning t m 5503) (meaning t m 5504) (meaning t m 5505)

theorem rule9582 (p5501 p5502 p5503 p5504 p5505 : Prop) : (¬ (p5501 ∧ p5502 ∧ p5503 ∧ p5504 ∧ p5505)) ∨ (p5502) := by
  classical
  tauto

theorem initial9582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5500)) ∨ (meaning t m 5502) := by
  exact rule9582 (meaning t m 5501) (meaning t m 5502) (meaning t m 5503) (meaning t m 5504) (meaning t m 5505)

theorem rule9583 (p5501 p5502 p5503 p5504 p5505 : Prop) : (¬ (p5501 ∧ p5502 ∧ p5503 ∧ p5504 ∧ p5505)) ∨ (p5503) := by
  classical
  tauto

theorem initial9583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5500)) ∨ (meaning t m 5503) := by
  exact rule9583 (meaning t m 5501) (meaning t m 5502) (meaning t m 5503) (meaning t m 5504) (meaning t m 5505)

theorem rule9584 (p5501 p5502 p5503 p5504 p5505 : Prop) : (¬ (p5501 ∧ p5502 ∧ p5503 ∧ p5504 ∧ p5505)) ∨ (p5504) := by
  classical
  tauto

theorem initial9584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5500)) ∨ (meaning t m 5504) := by
  exact rule9584 (meaning t m 5501) (meaning t m 5502) (meaning t m 5503) (meaning t m 5504) (meaning t m 5505)

theorem rule9585 (p5501 p5502 p5503 p5504 p5505 : Prop) : (¬ (p5501 ∧ p5502 ∧ p5503 ∧ p5504 ∧ p5505)) ∨ (p5505) := by
  classical
  tauto

theorem initial9585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5500)) ∨ (meaning t m 5505) := by
  exact rule9585 (meaning t m 5501) (meaning t m 5502) (meaning t m 5503) (meaning t m 5504) (meaning t m 5505)

theorem rule9586 (p5501 p5502 p5503 p5504 p5505 : Prop) : ((p5501 ∧ p5502 ∧ p5503 ∧ p5504 ∧ p5505)) ∨ (¬ p5501) ∨ (¬ p5502) ∨ (¬ p5503) ∨ (¬ p5504) ∨ (¬ p5505) := by
  classical
  tauto

theorem initial9586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5500) ∨ (¬ (meaning t m 5501)) ∨ (¬ (meaning t m 5502)) ∨ (¬ (meaning t m 5503)) ∨ (¬ (meaning t m 5504)) ∨ (¬ (meaning t m 5505)) := by
  exact rule9586 (meaning t m 5501) (meaning t m 5502) (meaning t m 5503) (meaning t m 5504) (meaning t m 5505)

theorem rule9587 (p3868 p5507 p5508 p5509 p5510 : Prop) : (¬ (p5507 ∧ p5508 ∧ p3868 ∧ p5509 ∧ p5510)) ∨ (p5507) := by
  classical
  tauto

theorem initial9587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5506)) ∨ (meaning t m 5507) := by
  exact rule9587 (meaning t m 3868) (meaning t m 5507) (meaning t m 5508) (meaning t m 5509) (meaning t m 5510)

theorem rule9588 (p3868 p5507 p5508 p5509 p5510 : Prop) : (¬ (p5507 ∧ p5508 ∧ p3868 ∧ p5509 ∧ p5510)) ∨ (p5508) := by
  classical
  tauto

theorem initial9588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5506)) ∨ (meaning t m 5508) := by
  exact rule9588 (meaning t m 3868) (meaning t m 5507) (meaning t m 5508) (meaning t m 5509) (meaning t m 5510)

theorem rule9589 (p3868 p5507 p5508 p5509 p5510 : Prop) : (p3868) ∨ (¬ (p5507 ∧ p5508 ∧ p3868 ∧ p5509 ∧ p5510)) := by
  classical
  tauto

theorem initial9589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3868) ∨ (¬ (meaning t m 5506)) := by
  exact rule9589 (meaning t m 3868) (meaning t m 5507) (meaning t m 5508) (meaning t m 5509) (meaning t m 5510)

theorem rule9590 (p3868 p5507 p5508 p5509 p5510 : Prop) : (¬ (p5507 ∧ p5508 ∧ p3868 ∧ p5509 ∧ p5510)) ∨ (p5509) := by
  classical
  tauto

theorem initial9590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5506)) ∨ (meaning t m 5509) := by
  exact rule9590 (meaning t m 3868) (meaning t m 5507) (meaning t m 5508) (meaning t m 5509) (meaning t m 5510)

theorem rule9591 (p3868 p5507 p5508 p5509 p5510 : Prop) : (¬ (p5507 ∧ p5508 ∧ p3868 ∧ p5509 ∧ p5510)) ∨ (p5510) := by
  classical
  tauto

theorem initial9591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5506)) ∨ (meaning t m 5510) := by
  exact rule9591 (meaning t m 3868) (meaning t m 5507) (meaning t m 5508) (meaning t m 5509) (meaning t m 5510)

theorem rule9592 (p3868 p5507 p5508 p5509 p5510 : Prop) : (¬ p3868) ∨ ((p5507 ∧ p5508 ∧ p3868 ∧ p5509 ∧ p5510)) ∨ (¬ p5507) ∨ (¬ p5508) ∨ (¬ p5509) ∨ (¬ p5510) := by
  classical
  tauto

theorem initial9592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3868)) ∨ (meaning t m 5506) ∨ (¬ (meaning t m 5507)) ∨ (¬ (meaning t m 5508)) ∨ (¬ (meaning t m 5509)) ∨ (¬ (meaning t m 5510)) := by
  exact rule9592 (meaning t m 3868) (meaning t m 5507) (meaning t m 5508) (meaning t m 5509) (meaning t m 5510)

theorem rule9595 (p5500 p5506 : Prop) : (¬ (p5500 ∨ p5506)) ∨ (p5500) ∨ (p5506) := by
  classical
  tauto

theorem initial9595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5499)) ∨ (meaning t m 5500) ∨ (meaning t m 5506) := by
  exact rule9595 (meaning t m 5500) (meaning t m 5506)

theorem rule9596 (p3862 p5499 : Prop) (h : (p3862 ↔ p5499)) : (¬ p3862) ∨ (p5499) := by
  classical
  tauto

theorem initial9596 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3862)) ∨ (meaning t m 5499) := by
  have source := ElevenTheory.theory1495 t (m.theta 4 10) (m.theta 4 7) (m.theta 7 10)
  exact rule9596 (meaning t m 3862) (meaning t m 5499) source

theorem rule9600 (p2027 p3192 p3276 p3947 p4327 p4381 : Prop) (h : (¬ p3276) ∨ (¬ p3192) ∨ (¬ p4327) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p3947)) : (p2027) ∨ (¬ p3192) ∨ (¬ p3276) ∨ (¬ p3947) ∨ (¬ p4327) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial9600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3192)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4327)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory1498 t (m.theta 3 7) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule9600 (meaning t m 2027) (meaning t m 3192) (meaning t m 3276) (meaning t m 3947) (meaning t m 4327) (meaning t m 4381) source

theorem rule9603 (p2027 p2383 p2952 p3324 p3987 p4566 : Prop) (h : p2027 ∨ (¬ p4566) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p2952) ∨ (¬ p2383)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2952) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4566) := by
  classical
  tauto

theorem initial9603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4566)) := by
  have source := ElevenTheory.theory1501 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 5) (m.theta 3 6) (m.theta 6 8)
  exact rule9603 (meaning t m 2027) (meaning t m 2383) (meaning t m 2952) (meaning t m 3324) (meaning t m 3987) (meaning t m 4566) source

theorem rule9604 (p2027 p2499 p2573 p2630 p2656 p2745 p3402 : Prop) (h : (¬ p2573) ∨ (¬ p2499) ∨ (¬ p3402) ∨ (¬ p2656) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p2745)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p3402) := by
  classical
  tauto

theorem initial9604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3402)) := by
  have source := ElevenTheory.theory1502 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6)
  exact rule9604 (meaning t m 2027) (meaning t m 2499) (meaning t m 2573) (meaning t m 2630) (meaning t m 2656) (meaning t m 2745) (meaning t m 3402) source

theorem rule9605 (p2027 p2589 p2662 p2850 p3475 p3572 p4650 : Prop) (h : (¬ p2589) ∨ (¬ p2850) ∨ p2027 ∨ (¬ p2662) ∨ (¬ p3475) ∨ (¬ p4650) ∨ (¬ p3572)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2850) ∨ (¬ p3475) ∨ (¬ p3572) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial9605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory1503 t (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule9605 (meaning t m 2027) (meaning t m 2589) (meaning t m 2662) (meaning t m 2850) (meaning t m 3475) (meaning t m 3572) (meaning t m 4650) source

theorem rule9606 (p2630 p2810 : Prop) (h : (¬ p2810) ∨ (¬ p2630)) : (¬ p2630) ∨ (¬ p2810) := by
  classical
  tauto

theorem initial9606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2810)) := by
  have source := ElevenTheory.theory1504 (m.theta 2 3) (m.theta 3 4)
  exact rule9606 (meaning t m 2630) (meaning t m 2810) source

theorem rule9607 (p2027 p3422 p3684 p4203 p4235 p4555 : Prop) (h : (¬ p3684) ∨ (¬ p4203) ∨ (¬ p4555) ∨ p2027 ∨ (¬ p3422) ∨ (¬ p4235)) : (p2027) ∨ (¬ p3422) ∨ (¬ p3684) ∨ (¬ p4203) ∨ (¬ p4235) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial9607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory1505 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7)
  exact rule9607 (meaning t m 2027) (meaning t m 3422) (meaning t m 3684) (meaning t m 4203) (meaning t m 4235) (meaning t m 4555) source

theorem rule9608 (p2027 p2696 p3136 p3425 p4777 p4917 : Prop) (h : (¬ p4777) ∨ (¬ p4917) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p3425) ∨ (¬ p2696)) : (p2027) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3425) ∨ (¬ p4777) ∨ (¬ p4917) := by
  classical
  tauto

theorem initial9608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4777)) ∨ (¬ (meaning t m 4917)) := by
  have source := ElevenTheory.theory1506 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 5) (m.theta 3 7)
  exact rule9608 (meaning t m 2027) (meaning t m 2696) (meaning t m 3136) (meaning t m 3425) (meaning t m 4777) (meaning t m 4917) source

theorem rule9609 (p2027 p2696 p2743 p3555 p3589 p4377 : Prop) (h : (¬ p2743) ∨ (¬ p2696) ∨ (¬ p4377) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p3589)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3555) ∨ (¬ p3589) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial9609 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory1507 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3)
  exact rule9609 (meaning t m 2027) (meaning t m 2696) (meaning t m 2743) (meaning t m 3555) (meaning t m 3589) (meaning t m 4377) source

theorem rule9610 (p2027 p2696 p2727 p2742 p3425 p4650 p4777 : Prop) (h : (¬ p4650) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p4777) ∨ (¬ p2727) ∨ (¬ p2742) ∨ (¬ p2696)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2727) ∨ (¬ p2742) ∨ (¬ p3425) ∨ (¬ p4650) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial9610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4650)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory1508 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7)
  exact rule9610 (meaning t m 2027) (meaning t m 2696) (meaning t m 2727) (meaning t m 2742) (meaning t m 3425) (meaning t m 4650) (meaning t m 4777) source

theorem rule9611 (p2027 p2132 p2860 p3425 p4169 p4555 : Prop) (h : (¬ p4169) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p4555) ∨ (¬ p2860)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3425) ∨ (¬ p4169) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial9611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4169)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory1509 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 6) (m.theta 5 7)
  exact rule9611 (meaning t m 2027) (meaning t m 2132) (meaning t m 2860) (meaning t m 3425) (meaning t m 4169) (meaning t m 4555) source

theorem rule9612 (p2437 p3742 : Prop) (h : (¬ p3742) ∨ (¬ p2437)) : (¬ p2437) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial9612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory1510 (m.theta 3 4) (m.theta 4 7)
  exact rule9612 (meaning t m 2437) (meaning t m 3742) source

theorem rule9613 (p3425 p3471 : Prop) (h : (¬ p3425) ∨ (¬ p3471)) : (¬ p3425) ∨ (¬ p3471) := by
  classical
  tauto

theorem initial9613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3471)) := by
  have source := ElevenTheory.theory1511 (m.theta 0 2) (m.theta 2 7)
  exact rule9613 (meaning t m 3425) (meaning t m 3471) source

theorem rule9614 (p2027 p2341 p2926 p2963 p3487 p3548 p4104 p4972 : Prop) (h : (¬ p4972) ∨ (¬ p2926) ∨ (¬ p3548) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p4104) ∨ (¬ p2963) ∨ (¬ p3487)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2926) ∨ (¬ p2963) ∨ (¬ p3487) ∨ (¬ p3548) ∨ (¬ p4104) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial9614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory1512 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 4) (m.theta 1 7) (m.theta 3 4) (m.theta 3 6) (m.theta 7 8)
  exact rule9614 (meaning t m 2027) (meaning t m 2341) (meaning t m 2926) (meaning t m 2963) (meaning t m 3487) (meaning t m 3548) (meaning t m 4104) (meaning t m 4972) source

theorem rule9615 (p2027 p2930 p3343 p3742 p3817 p4451 : Prop) (h : (¬ p3343) ∨ p2027 ∨ (¬ p4451) ∨ (¬ p3817) ∨ (¬ p2930) ∨ (¬ p3742)) : (p2027) ∨ (¬ p2930) ∨ (¬ p3343) ∨ (¬ p3742) ∨ (¬ p3817) ∨ (¬ p4451) := by
  classical
  tauto

theorem initial9615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2930)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4451)) := by
  have source := ElevenTheory.theory1513 t (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9)
  exact rule9615 (meaning t m 2027) (meaning t m 2930) (meaning t m 3343) (meaning t m 3742) (meaning t m 3817) (meaning t m 4451) source

theorem rule9617 (p2027 p3564 p3660 p3744 p4235 p4555 : Prop) (h : (¬ p3744) ∨ p2027 ∨ (¬ p4555) ∨ (¬ p3564) ∨ (¬ p3660) ∨ (¬ p4235)) : (p2027) ∨ (¬ p3564) ∨ (¬ p3660) ∨ (¬ p3744) ∨ (¬ p4235) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial9617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory1515 t (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule9617 (meaning t m 2027) (meaning t m 3564) (meaning t m 3660) (meaning t m 3744) (meaning t m 4235) (meaning t m 4555) source

theorem rule9618 (p2027 p2563 p3125 p4026 p4512 p4629 : Prop) (h : (¬ p4512) ∨ (¬ p2563) ∨ (¬ p4026) ∨ (¬ p4629) ∨ p2027 ∨ (¬ p3125)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p4026) ∨ (¬ p4512) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial9618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory1516 t (m.theta 1 5) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9)
  exact rule9618 (meaning t m 2027) (meaning t m 2563) (meaning t m 3125) (meaning t m 4026) (meaning t m 4512) (meaning t m 4629) source

theorem rule9622 (p4240 p5513 p5514 p5515 p5516 : Prop) : (¬ (p4240 ∧ p5513 ∧ p5514 ∧ p5515 ∧ p5516)) ∨ (p5514) := by
  classical
  tauto

theorem initial9622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5512)) ∨ (meaning t m 5514) := by
  exact rule9622 (meaning t m 4240) (meaning t m 5513) (meaning t m 5514) (meaning t m 5515) (meaning t m 5516)

theorem rule9626 (p3888 p3893 p5518 p5519 p5520 : Prop) : (¬ (p5518 ∧ p3893 ∧ p3888 ∧ p5519 ∧ p5520)) ∨ (p5518) := by
  classical
  tauto

theorem initial9626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5517)) ∨ (meaning t m 5518) := by
  exact rule9626 (meaning t m 3888) (meaning t m 3893) (meaning t m 5518) (meaning t m 5519) (meaning t m 5520)

theorem rule9627 (p3888 p3893 p5518 p5519 p5520 : Prop) : (p3893) ∨ (¬ (p5518 ∧ p3893 ∧ p3888 ∧ p5519 ∧ p5520)) := by
  classical
  tauto

theorem initial9627 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3893) ∨ (¬ (meaning t m 5517)) := by
  exact rule9627 (meaning t m 3888) (meaning t m 3893) (meaning t m 5518) (meaning t m 5519) (meaning t m 5520)

theorem rule9628 (p3888 p3893 p5518 p5519 p5520 : Prop) : (p3888) ∨ (¬ (p5518 ∧ p3893 ∧ p3888 ∧ p5519 ∧ p5520)) := by
  classical
  tauto

theorem initial9628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3888) ∨ (¬ (meaning t m 5517)) := by
  exact rule9628 (meaning t m 3888) (meaning t m 3893) (meaning t m 5518) (meaning t m 5519) (meaning t m 5520)

theorem rule9629 (p3888 p3893 p5518 p5519 p5520 : Prop) : (¬ (p5518 ∧ p3893 ∧ p3888 ∧ p5519 ∧ p5520)) ∨ (p5519) := by
  classical
  tauto

theorem initial9629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5517)) ∨ (meaning t m 5519) := by
  exact rule9629 (meaning t m 3888) (meaning t m 3893) (meaning t m 5518) (meaning t m 5519) (meaning t m 5520)

theorem rule9630 (p3888 p3893 p5518 p5519 p5520 : Prop) : (¬ (p5518 ∧ p3893 ∧ p3888 ∧ p5519 ∧ p5520)) ∨ (p5520) := by
  classical
  tauto

theorem initial9630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5517)) ∨ (meaning t m 5520) := by
  exact rule9630 (meaning t m 3888) (meaning t m 3893) (meaning t m 5518) (meaning t m 5519) (meaning t m 5520)

theorem rule9631 (p3888 p3893 p5518 p5519 p5520 : Prop) : (¬ p3888) ∨ (¬ p3893) ∨ ((p5518 ∧ p3893 ∧ p3888 ∧ p5519 ∧ p5520)) ∨ (¬ p5518) ∨ (¬ p5519) ∨ (¬ p5520) := by
  classical
  tauto

theorem initial9631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 3893)) ∨ (meaning t m 5517) ∨ (¬ (meaning t m 5518)) ∨ (¬ (meaning t m 5519)) ∨ (¬ (meaning t m 5520)) := by
  exact rule9631 (meaning t m 3888) (meaning t m 3893) (meaning t m 5518) (meaning t m 5519) (meaning t m 5520)

theorem rule9634 (p5512 p5517 : Prop) : (¬ (p5512 ∨ p5517)) ∨ (p5512) ∨ (p5517) := by
  classical
  tauto

theorem initial9634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5511)) ∨ (meaning t m 5512) ∨ (meaning t m 5517) := by
  exact rule9634 (meaning t m 5512) (meaning t m 5517)

theorem rule9635 (p3882 p5511 : Prop) (h : (p3882 ↔ p5511)) : (¬ p3882) ∨ (p5511) := by
  classical
  tauto

theorem initial9635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3882)) ∨ (meaning t m 5511) := by
  have source := ElevenTheory.theory1518 t (m.theta 4 10) (m.theta 4 6) (m.theta 6 10)
  exact rule9635 (meaning t m 3882) (meaning t m 5511) source

theorem rule9652 (p3895 p5521 : Prop) (h : (p3895 ↔ p5521)) : (¬ p3895) ∨ (p5521) := by
  classical
  tauto

theorem initial9652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3895)) ∨ (meaning t m 5521) := by
  have source := ElevenTheory.theory1519 t (m.theta 3 10) (m.theta 3 4) (m.theta 4 10)
  exact rule9652 (meaning t m 3895) (meaning t m 5521) source

theorem rule9654 (p2027 p2850 p3051 p3486 p4109 p4202 p5214 : Prop) (h : p2027 ∨ (¬ p4109) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p5214) ∨ (¬ p2850) ∨ (¬ p4202)) : (p2027) ∨ (¬ p2850) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial9654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory1520 t (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7)
  exact rule9654 (meaning t m 2027) (meaning t m 2850) (meaning t m 3051) (meaning t m 3486) (meaning t m 4109) (meaning t m 4202) (meaning t m 5214) source

theorem rule9655 (p2027 p2331 p2952 p3986 p4173 p4957 : Prop) (h : (¬ p2952) ∨ (¬ p3986) ∨ (¬ p4173) ∨ p2027 ∨ (¬ p4957) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3986) ∨ (¬ p4173) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial9655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory1521 t (m.theta 0 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule9655 (meaning t m 2027) (meaning t m 2331) (meaning t m 2952) (meaning t m 3986) (meaning t m 4173) (meaning t m 4957) source

theorem rule9657 (p2027 p2982 p3690 p4235 p4395 : Prop) (h : (¬ p4395) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2982) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4395) := by
  classical
  tauto

theorem initial9657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4395)) := by
  have source := ElevenTheory.theory1523 t (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule9657 (meaning t m 2027) (meaning t m 2982) (meaning t m 3690) (meaning t m 4235) (meaning t m 4395) source

theorem rule9658 (p2027 p2138 p2341 p2748 p3031 p3548 p3819 p5049 : Prop) (h : (¬ p5049) ∨ (¬ p3031) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2748) ∨ (¬ p3548) ∨ (¬ p3819) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2341) ∨ (¬ p2748) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p3819) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial9658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory1524 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 3) (m.theta 1 7) (m.theta 2 3) (m.theta 2 5) (m.theta 7 8)
  exact rule9658 (meaning t m 2027) (meaning t m 2138) (meaning t m 2341) (meaning t m 2748) (meaning t m 3031) (meaning t m 3548) (meaning t m 3819) (meaning t m 5049) source

theorem rule9661 (p4329 p5534 p5535 p5536 p5537 : Prop) : (p4329) ∨ (¬ (p5534 ∧ p5535 ∧ p4329 ∧ p5536 ∧ p5537)) := by
  classical
  tauto

theorem initial9661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4329) ∨ (¬ (meaning t m 5533)) := by
  exact rule9661 (meaning t m 4329) (meaning t m 5534) (meaning t m 5535) (meaning t m 5536) (meaning t m 5537)

theorem rule9665 (p3914 p5539 p5540 p5541 p5542 : Prop) : (¬ (p5539 ∧ p5540 ∧ p3914 ∧ p5541 ∧ p5542)) ∨ (p5539) := by
  classical
  tauto

theorem initial9665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5538)) ∨ (meaning t m 5539) := by
  exact rule9665 (meaning t m 3914) (meaning t m 5539) (meaning t m 5540) (meaning t m 5541) (meaning t m 5542)

theorem rule9666 (p3914 p5539 p5540 p5541 p5542 : Prop) : (¬ (p5539 ∧ p5540 ∧ p3914 ∧ p5541 ∧ p5542)) ∨ (p5540) := by
  classical
  tauto

theorem initial9666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5538)) ∨ (meaning t m 5540) := by
  exact rule9666 (meaning t m 3914) (meaning t m 5539) (meaning t m 5540) (meaning t m 5541) (meaning t m 5542)

theorem rule9667 (p3914 p5539 p5540 p5541 p5542 : Prop) : (p3914) ∨ (¬ (p5539 ∧ p5540 ∧ p3914 ∧ p5541 ∧ p5542)) := by
  classical
  tauto

theorem initial9667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3914) ∨ (¬ (meaning t m 5538)) := by
  exact rule9667 (meaning t m 3914) (meaning t m 5539) (meaning t m 5540) (meaning t m 5541) (meaning t m 5542)

theorem rule9673 (p5533 p5538 : Prop) : (¬ (p5533 ∨ p5538)) ∨ (p5533) ∨ (p5538) := by
  classical
  tauto

theorem initial9673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5532)) ∨ (meaning t m 5533) ∨ (meaning t m 5538) := by
  exact rule9673 (meaning t m 5533) (meaning t m 5538)

theorem rule9674 (p3908 p5532 : Prop) (h : (p3908 ↔ p5532)) : (¬ p3908) ∨ (p5532) := by
  classical
  tauto

theorem initial9674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3908)) ∨ (meaning t m 5532) := by
  have source := ElevenTheory.theory1525 t (m.theta 2 10) (m.theta 2 6) (m.theta 6 10)
  exact rule9674 (meaning t m 3908) (meaning t m 5532) source

theorem rule9676 (p2027 p2264 p3570 p4037 p4140 p4156 p4620 : Prop) (h : (¬ p4140) ∨ (¬ p3570) ∨ (¬ p4037) ∨ (¬ p4620) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p4156)) : (p2027) ∨ (¬ p2264) ∨ (¬ p3570) ∨ (¬ p4037) ∨ (¬ p4140) ∨ (¬ p4156) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial9676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory1526 t (m.theta 3 6) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule9676 (meaning t m 2027) (meaning t m 2264) (meaning t m 3570) (meaning t m 4037) (meaning t m 4140) (meaning t m 4156) (meaning t m 4620) source

theorem rule9678 (p2027 p2191 p2341 p2891 p4132 p4990 : Prop) (h : p2027 ∨ (¬ p4990) ∨ (¬ p2191) ∨ (¬ p2341) ∨ (¬ p4132) ∨ (¬ p2891)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2341) ∨ (¬ p2891) ∨ (¬ p4132) ∨ (¬ p4990) := by
  classical
  tauto

theorem initial9678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4990)) := by
  have source := ElevenTheory.theory1528 t (m.theta 0 7) (m.theta 1 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule9678 (meaning t m 2027) (meaning t m 2191) (meaning t m 2341) (meaning t m 2891) (meaning t m 4132) (meaning t m 4990) source

theorem rule9679 (p2027 p2662 p2922 p3540 p3662 p4281 p4701 : Prop) (h : (¬ p4701) ∨ (¬ p3662) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p2662) ∨ (¬ p3540) ∨ (¬ p4281)) : (p2027) ∨ (¬ p2662) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p3662) ∨ (¬ p4281) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial9679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory1529 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7)
  exact rule9679 (meaning t m 2027) (meaning t m 2662) (meaning t m 2922) (meaning t m 3540) (meaning t m 3662) (meaning t m 4281) (meaning t m 4701) source

theorem rule9680 (p2027 p2284 p3238 p3413 p3646 p4031 p4811 : Prop) (h : (¬ p3413) ∨ (¬ p4811) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p4031) ∨ (¬ p3238)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3238) ∨ (¬ p3413) ∨ (¬ p3646) ∨ (¬ p4031) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial9680 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory1530 t (m.theta 0 5) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule9680 (meaning t m 2027) (meaning t m 2284) (meaning t m 3238) (meaning t m 3413) (meaning t m 3646) (meaning t m 4031) (meaning t m 4811) source

theorem rule9681 (p2027 p2481 p2509 p3256 p3580 p3857 p4044 p4811 : Prop) (h : (¬ p4811) ∨ (¬ p3256) ∨ (¬ p4044) ∨ (¬ p3580) ∨ (¬ p2481) ∨ (¬ p2509) ∨ (¬ p3857) ∨ p2027) : (p2027) ∨ (¬ p2481) ∨ (¬ p2509) ∨ (¬ p3256) ∨ (¬ p3580) ∨ (¬ p3857) ∨ (¬ p4044) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial9681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory1531 t (m.theta 0 8) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule9681 (meaning t m 2027) (meaning t m 2481) (meaning t m 2509) (meaning t m 3256) (meaning t m 3580) (meaning t m 3857) (meaning t m 4044) (meaning t m 4811) source

theorem rule9682 (p2027 p2518 p2928 p4278 p4404 p4666 : Prop) (h : (¬ p2928) ∨ (¬ p4278) ∨ (¬ p2518) ∨ (¬ p4404) ∨ p2027 ∨ (¬ p4666)) : (p2027) ∨ (¬ p2518) ∨ (¬ p2928) ∨ (¬ p4278) ∨ (¬ p4404) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial9682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4404)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory1532 t (m.theta 1 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 7 9)
  exact rule9682 (meaning t m 2027) (meaning t m 2518) (meaning t m 2928) (meaning t m 4278) (meaning t m 4404) (meaning t m 4666) source

theorem rule9683 (p2027 p2088 p2177 p4107 p4445 p4592 : Prop) (h : (¬ p4592) ∨ (¬ p2088) ∨ (¬ p4445) ∨ (¬ p2177) ∨ (¬ p4107) ∨ p2027) : (p2027) ∨ (¬ p2088) ∨ (¬ p2177) ∨ (¬ p4107) ∨ (¬ p4445) ∨ (¬ p4592) := by
  classical
  tauto

theorem initial9683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 4592)) := by
  have source := ElevenTheory.theory1533 t (m.theta 0 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule9683 (meaning t m 2027) (meaning t m 2088) (meaning t m 2177) (meaning t m 4107) (meaning t m 4445) (meaning t m 4592) source

theorem rule9684 (p2027 p2481 p2509 p2810 p3005 p3171 p4811 : Prop) (h : (¬ p2481) ∨ (¬ p4811) ∨ (¬ p3171) ∨ (¬ p2810) ∨ (¬ p2509) ∨ p2027 ∨ (¬ p3005)) : (p2027) ∨ (¬ p2481) ∨ (¬ p2509) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial9684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3171)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory1534 t (m.theta 0 8) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule9684 (meaning t m 2027) (meaning t m 2481) (meaning t m 2509) (meaning t m 2810) (meaning t m 3005) (meaning t m 3171) (meaning t m 4811) source

theorem rule9685 (p2027 p2509 p2657 p3166 p4346 p4811 : Prop) (h : (¬ p3166) ∨ (¬ p4811) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p2509) ∨ (¬ p4346)) : (p2027) ∨ (¬ p2509) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p4346) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial9685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4346)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory1535 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule9685 (meaning t m 2027) (meaning t m 2509) (meaning t m 2657) (meaning t m 3166) (meaning t m 4346) (meaning t m 4811) source

theorem rule9686 (p2027 p2532 p3212 p4120 p4348 p4905 : Prop) (h : (¬ p4905) ∨ (¬ p3212) ∨ p2027 ∨ (¬ p2532) ∨ (¬ p4348) ∨ (¬ p4120)) : (p2027) ∨ (¬ p2532) ∨ (¬ p3212) ∨ (¬ p4120) ∨ (¬ p4348) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial9686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory1536 t (m.theta 0 5) (m.theta 5 8) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule9686 (meaning t m 2027) (meaning t m 2532) (meaning t m 3212) (meaning t m 4120) (meaning t m 4348) (meaning t m 4905) source

theorem rule9687 (p2027 p2810 p2951 p3136 p3238 p4031 p4811 : Prop) (h : p2027 ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4811) ∨ (¬ p2951) ∨ (¬ p4031) ∨ (¬ p3238)) : (p2027) ∨ (¬ p2810) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3238) ∨ (¬ p4031) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial9687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory1537 t (m.theta 0 5) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule9687 (meaning t m 2027) (meaning t m 2810) (meaning t m 2951) (meaning t m 3136) (meaning t m 3238) (meaning t m 4031) (meaning t m 4811) source

theorem rule9689 (p2027 p2449 p2928 p3580 p3821 p4279 p4811 : Prop) (h : (¬ p4279) ∨ p2027 ∨ (¬ p2449) ∨ (¬ p3821) ∨ (¬ p4811) ∨ (¬ p2928) ∨ (¬ p3580)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2928) ∨ (¬ p3580) ∨ (¬ p3821) ∨ (¬ p4279) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial9689 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory1539 t (m.theta 0 7) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule9689 (meaning t m 2027) (meaning t m 2449) (meaning t m 2928) (meaning t m 3580) (meaning t m 3821) (meaning t m 4279) (meaning t m 4811) source

theorem rule9691 (p2027 p2132 p3055 p3238 p3695 p5214 : Prop) (h : (¬ p2132) ∨ (¬ p3695) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p5214) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2132) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p3695) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial9691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory1541 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule9691 (meaning t m 2027) (meaning t m 2132) (meaning t m 3055) (meaning t m 3238) (meaning t m 3695) (meaning t m 5214) source

theorem rule9692 (p2027 p2307 p3189 p3549 p3567 p4245 p4773 : Prop) (h : (¬ p4245) ∨ (¬ p2307) ∨ (¬ p3189) ∨ (¬ p3567) ∨ (¬ p4773) ∨ p2027 ∨ (¬ p3549)) : (p2027) ∨ (¬ p2307) ∨ (¬ p3189) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p4245) ∨ (¬ p4773) := by
  classical
  tauto

theorem initial9692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4245)) ∨ (¬ (meaning t m 4773)) := by
  have source := ElevenTheory.theory1542 t (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7)
  exact rule9692 (meaning t m 2027) (meaning t m 2307) (meaning t m 3189) (meaning t m 3549) (meaning t m 3567) (meaning t m 4245) (meaning t m 4773) source

theorem rule9693 (p2027 p2363 p2383 p2781 p2810 p3365 p3693 p4256 p4348 p4905 : Prop) (h : (¬ p4256) ∨ (¬ p4348) ∨ (¬ p3693) ∨ (¬ p4905) ∨ (¬ p2363) ∨ (¬ p2781) ∨ p2027 ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p2383)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3693) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial9693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory1543 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule9693 (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 2781) (meaning t m 2810) (meaning t m 3365) (meaning t m 3693) (meaning t m 4256) (meaning t m 4348) (meaning t m 4905) source

theorem rule9695 (p2996 p3027 : Prop) (h : (¬ p2996) ∨ (¬ p3027)) : (¬ p2996) ∨ (¬ p3027) := by
  classical
  tauto

theorem initial9695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3027)) := by
  have source := ElevenTheory.theory1545 (m.theta 1 3) (m.theta 3 7)
  exact rule9695 (meaning t m 2996) (meaning t m 3027) source

theorem rule9696 (p3461 p4171 p4444 : Prop) (h : (¬ p4444) ∨ (¬ p3461) ∨ (¬ p4171)) : (¬ p3461) ∨ (¬ p4171) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial9696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4171)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory1546 (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule9696 (meaning t m 3461) (meaning t m 4171) (meaning t m 4444) source

theorem rule9697 (p2027 p2363 p3266 p3657 p4381 p4503 : Prop) (h : (¬ p4503) ∨ (¬ p4381) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4381) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial9697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory1547 t (m.theta 6 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule9697 (meaning t m 2027) (meaning t m 2363) (meaning t m 3266) (meaning t m 3657) (meaning t m 4381) (meaning t m 4503) source

theorem rule9698 (p2027 p3125 p3461 p4564 p5274 p5284 : Prop) (h : (¬ p4564) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p5284) ∨ (¬ p3461) ∨ (¬ p5274)) : (p2027) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p4564) ∨ (¬ p5274) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial9698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4564)) ∨ (¬ (meaning t m 5274)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory1548 t (m.theta 3 6) (m.theta 3 9) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule9698 (meaning t m 2027) (meaning t m 3125) (meaning t m 3461) (meaning t m 4564) (meaning t m 5274) (meaning t m 5284) source

theorem rule9699 (p3323 p4037 : Prop) (h : (¬ p4037) ∨ (¬ p3323)) : (¬ p3323) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial9699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory1549 (m.theta 3 6) (m.theta 6 9)
  exact rule9699 (meaning t m 3323) (meaning t m 4037) source

theorem rule9703 (p4391 p5545 p5546 p5547 p5548 : Prop) : (p4391) ∨ (¬ (p5545 ∧ p5546 ∧ p4391 ∧ p5547 ∧ p5548)) := by
  classical
  tauto

theorem initial9703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4391) ∨ (¬ (meaning t m 5544)) := by
  exact rule9703 (meaning t m 4391) (meaning t m 5545) (meaning t m 5546) (meaning t m 5547) (meaning t m 5548)

theorem rule9707 (p3931 p5550 p5551 p5552 p5553 : Prop) : (¬ (p5550 ∧ p5551 ∧ p3931 ∧ p5552 ∧ p5553)) ∨ (p5550) := by
  classical
  tauto

theorem initial9707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5549)) ∨ (meaning t m 5550) := by
  exact rule9707 (meaning t m 3931) (meaning t m 5550) (meaning t m 5551) (meaning t m 5552) (meaning t m 5553)

theorem rule9708 (p3931 p5550 p5551 p5552 p5553 : Prop) : (¬ (p5550 ∧ p5551 ∧ p3931 ∧ p5552 ∧ p5553)) ∨ (p5551) := by
  classical
  tauto

theorem initial9708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5549)) ∨ (meaning t m 5551) := by
  exact rule9708 (meaning t m 3931) (meaning t m 5550) (meaning t m 5551) (meaning t m 5552) (meaning t m 5553)

theorem rule9709 (p3931 p5550 p5551 p5552 p5553 : Prop) : (p3931) ∨ (¬ (p5550 ∧ p5551 ∧ p3931 ∧ p5552 ∧ p5553)) := by
  classical
  tauto

theorem initial9709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3931) ∨ (¬ (meaning t m 5549)) := by
  exact rule9709 (meaning t m 3931) (meaning t m 5550) (meaning t m 5551) (meaning t m 5552) (meaning t m 5553)

theorem rule9710 (p3931 p5550 p5551 p5552 p5553 : Prop) : (¬ (p5550 ∧ p5551 ∧ p3931 ∧ p5552 ∧ p5553)) ∨ (p5552) := by
  classical
  tauto

theorem initial9710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5549)) ∨ (meaning t m 5552) := by
  exact rule9710 (meaning t m 3931) (meaning t m 5550) (meaning t m 5551) (meaning t m 5552) (meaning t m 5553)

theorem rule9711 (p3931 p5550 p5551 p5552 p5553 : Prop) : (¬ (p5550 ∧ p5551 ∧ p3931 ∧ p5552 ∧ p5553)) ∨ (p5553) := by
  classical
  tauto

theorem initial9711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5549)) ∨ (meaning t m 5553) := by
  exact rule9711 (meaning t m 3931) (meaning t m 5550) (meaning t m 5551) (meaning t m 5552) (meaning t m 5553)

theorem rule9712 (p3931 p5550 p5551 p5552 p5553 : Prop) : (¬ p3931) ∨ ((p5550 ∧ p5551 ∧ p3931 ∧ p5552 ∧ p5553)) ∨ (¬ p5550) ∨ (¬ p5551) ∨ (¬ p5552) ∨ (¬ p5553) := by
  classical
  tauto

theorem initial9712 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3931)) ∨ (meaning t m 5549) ∨ (¬ (meaning t m 5550)) ∨ (¬ (meaning t m 5551)) ∨ (¬ (meaning t m 5552)) ∨ (¬ (meaning t m 5553)) := by
  exact rule9712 (meaning t m 3931) (meaning t m 5550) (meaning t m 5551) (meaning t m 5552) (meaning t m 5553)

theorem rule9715 (p5544 p5549 : Prop) : (¬ (p5544 ∨ p5549)) ∨ (p5544) ∨ (p5549) := by
  classical
  tauto

theorem initial9715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5543)) ∨ (meaning t m 5544) ∨ (meaning t m 5549) := by
  exact rule9715 (meaning t m 5544) (meaning t m 5549)

theorem rule9716 (p3925 p5543 : Prop) (h : (p3925 ↔ p5543)) : (¬ p3925) ∨ (p5543) := by
  classical
  tauto

theorem initial9716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3925)) ∨ (meaning t m 5543) := by
  have source := ElevenTheory.theory1551 t (m.theta 3 10) (m.theta 3 7) (m.theta 7 10)
  exact rule9716 (meaning t m 3925) (meaning t m 5543) source

theorem rule9718 (p2027 p2274 p3791 p4067 p4391 p4564 : Prop) (h : (¬ p4564) ∨ (¬ p4391) ∨ (¬ p3791) ∨ (¬ p2274) ∨ (¬ p4067) ∨ p2027) : (p2027) ∨ (¬ p2274) ∨ (¬ p3791) ∨ (¬ p4067) ∨ (¬ p4391) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial9718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory1552 t (m.theta 3 6) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 10)
  exact rule9718 (meaning t m 2027) (meaning t m 2274) (meaning t m 3791) (meaning t m 4067) (meaning t m 4391) (meaning t m 4564) source

theorem rule9719 (p5556 p5557 p5558 p5559 p5560 : Prop) : (¬ (p5556 ∧ p5557 ∧ p5558 ∧ p5559 ∧ p5560)) ∨ (p5556) := by
  classical
  tauto

theorem initial9719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5555)) ∨ (meaning t m 5556) := by
  exact rule9719 (meaning t m 5556) (meaning t m 5557) (meaning t m 5558) (meaning t m 5559) (meaning t m 5560)

theorem rule9720 (p5556 p5557 p5558 p5559 p5560 : Prop) : (¬ (p5556 ∧ p5557 ∧ p5558 ∧ p5559 ∧ p5560)) ∨ (p5557) := by
  classical
  tauto

theorem initial9720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5555)) ∨ (meaning t m 5557) := by
  exact rule9720 (meaning t m 5556) (meaning t m 5557) (meaning t m 5558) (meaning t m 5559) (meaning t m 5560)

theorem rule9721 (p5556 p5557 p5558 p5559 p5560 : Prop) : (¬ (p5556 ∧ p5557 ∧ p5558 ∧ p5559 ∧ p5560)) ∨ (p5558) := by
  classical
  tauto

theorem initial9721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5555)) ∨ (meaning t m 5558) := by
  exact rule9721 (meaning t m 5556) (meaning t m 5557) (meaning t m 5558) (meaning t m 5559) (meaning t m 5560)

theorem rule9722 (p5556 p5557 p5558 p5559 p5560 : Prop) : (¬ (p5556 ∧ p5557 ∧ p5558 ∧ p5559 ∧ p5560)) ∨ (p5559) := by
  classical
  tauto

theorem initial9722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5555)) ∨ (meaning t m 5559) := by
  exact rule9722 (meaning t m 5556) (meaning t m 5557) (meaning t m 5558) (meaning t m 5559) (meaning t m 5560)

theorem rule9725 (p3941 p5562 p5563 p5564 p5565 : Prop) : (¬ (p5562 ∧ p5563 ∧ p3941 ∧ p5564 ∧ p5565)) ∨ (p5562) := by
  classical
  tauto

theorem initial9725 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5561)) ∨ (meaning t m 5562) := by
  exact rule9725 (meaning t m 3941) (meaning t m 5562) (meaning t m 5563) (meaning t m 5564) (meaning t m 5565)

theorem rule9726 (p3941 p5562 p5563 p5564 p5565 : Prop) : (¬ (p5562 ∧ p5563 ∧ p3941 ∧ p5564 ∧ p5565)) ∨ (p5563) := by
  classical
  tauto

theorem initial9726 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5561)) ∨ (meaning t m 5563) := by
  exact rule9726 (meaning t m 3941) (meaning t m 5562) (meaning t m 5563) (meaning t m 5564) (meaning t m 5565)

theorem rule9727 (p3941 p5562 p5563 p5564 p5565 : Prop) : (p3941) ∨ (¬ (p5562 ∧ p5563 ∧ p3941 ∧ p5564 ∧ p5565)) := by
  classical
  tauto

theorem initial9727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3941) ∨ (¬ (meaning t m 5561)) := by
  exact rule9727 (meaning t m 3941) (meaning t m 5562) (meaning t m 5563) (meaning t m 5564) (meaning t m 5565)

theorem rule9728 (p3941 p5562 p5563 p5564 p5565 : Prop) : (¬ (p5562 ∧ p5563 ∧ p3941 ∧ p5564 ∧ p5565)) ∨ (p5564) := by
  classical
  tauto

theorem initial9728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5561)) ∨ (meaning t m 5564) := by
  exact rule9728 (meaning t m 3941) (meaning t m 5562) (meaning t m 5563) (meaning t m 5564) (meaning t m 5565)

theorem rule9729 (p3941 p5562 p5563 p5564 p5565 : Prop) : (¬ (p5562 ∧ p5563 ∧ p3941 ∧ p5564 ∧ p5565)) ∨ (p5565) := by
  classical
  tauto

theorem initial9729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5561)) ∨ (meaning t m 5565) := by
  exact rule9729 (meaning t m 3941) (meaning t m 5562) (meaning t m 5563) (meaning t m 5564) (meaning t m 5565)

theorem rule9733 (p5555 p5561 : Prop) : (¬ (p5555 ∨ p5561)) ∨ (p5555) ∨ (p5561) := by
  classical
  tauto

theorem initial9733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5554)) ∨ (meaning t m 5555) ∨ (meaning t m 5561) := by
  exact rule9733 (meaning t m 5555) (meaning t m 5561)

theorem rule9734 (p3935 p5554 : Prop) (h : (p3935 ↔ p5554)) : (¬ p3935) ∨ (p5554) := by
  classical
  tauto

theorem initial9734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3935)) ∨ (meaning t m 5554) := by
  have source := ElevenTheory.theory1553 t (m.theta 7 10) (m.theta 7 8) (m.theta 8 10)
  exact rule9734 (meaning t m 3935) (meaning t m 5554) source

theorem rule9737 (p3654 p3946 : Prop) (h : (¬ p3946) ∨ (¬ p3654)) : (¬ p3654) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial9737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory1555 (m.theta 0 6) (m.theta 6 9)
  exact rule9737 (meaning t m 3654) (meaning t m 3946) source

theorem rule9738 (p2027 p2579 p3389 p3568 p4710 p4973 : Prop) (h : (¬ p2579) ∨ (¬ p4710) ∨ p2027 ∨ (¬ p4973) ∨ (¬ p3389) ∨ (¬ p3568)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3568) ∨ (¬ p4710) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial9738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory1556 t (m.theta 0 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule9738 (meaning t m 2027) (meaning t m 2579) (meaning t m 3389) (meaning t m 3568) (meaning t m 4710) (meaning t m 4973) source

theorem rule9739 (p2027 p2501 p2579 p3389 p3549 p4710 : Prop) (h : p2027 ∨ (¬ p2501) ∨ (¬ p3549) ∨ (¬ p3389) ∨ (¬ p2579) ∨ (¬ p4710)) : (p2027) ∨ (¬ p2501) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3549) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial9739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2501)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory1557 t (m.theta 0 4) (m.theta 1 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule9739 (meaning t m 2027) (meaning t m 2501) (meaning t m 2579) (meaning t m 3389) (meaning t m 3549) (meaning t m 4710) source

theorem rule9740 (p3399 p4366 : Prop) (h : (¬ p4366) ∨ (¬ p3399)) : (¬ p3399) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial9740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory1558 (m.theta 0 1) (m.theta 1 7)
  exact rule9740 (meaning t m 3399) (meaning t m 4366) source

theorem rule9741 (p2027 p2741 p2807 p2811 p2996 p3367 p4752 : Prop) (h : (¬ p2996) ∨ (¬ p2741) ∨ p2027 ∨ (¬ p2811) ∨ (¬ p3367) ∨ (¬ p2807) ∨ (¬ p4752)) : (p2027) ∨ (¬ p2741) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p2996) ∨ (¬ p3367) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial9741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory1559 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7)
  exact rule9741 (meaning t m 2027) (meaning t m 2741) (meaning t m 2807) (meaning t m 2811) (meaning t m 2996) (meaning t m 3367) (meaning t m 4752) source

theorem rule9742 (p2027 p2761 p3040 p3631 p4429 p5284 : Prop) (h : (¬ p3040) ∨ p2027 ∨ (¬ p5284) ∨ (¬ p2761) ∨ (¬ p4429) ∨ (¬ p3631)) : (p2027) ∨ (¬ p2761) ∨ (¬ p3040) ∨ (¬ p3631) ∨ (¬ p4429) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial9742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3040)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4429)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory1560 t (m.theta 1 7) (m.theta 3 7) (m.theta 3 9) (m.theta 7 9) (m.theta 9 10)
  exact rule9742 (meaning t m 2027) (meaning t m 2761) (meaning t m 3040) (meaning t m 3631) (meaning t m 4429) (meaning t m 5284) source

theorem rule9743 (p2027 p2819 p3367 p3923 p3953 p5221 : Prop) (h : (¬ p5221) ∨ (¬ p3923) ∨ (¬ p2819) ∨ (¬ p3367) ∨ p2027 ∨ (¬ p3953)) : (p2027) ∨ (¬ p2819) ∨ (¬ p3367) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p5221) := by
  classical
  tauto

theorem initial9743 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 5221)) := by
  have source := ElevenTheory.theory1561 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 2 6) (m.theta 6 8)
  exact rule9743 (meaning t m 2027) (meaning t m 2819) (meaning t m 3367) (meaning t m 3923) (meaning t m 3953) (meaning t m 5221) source

theorem rule9744 (p2027 p2220 p3646 p3956 p3958 p4441 : Prop) (h : (¬ p3958) ∨ (¬ p3956) ∨ (¬ p4441) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p3646)) : (p2027) ∨ (¬ p2220) ∨ (¬ p3646) ∨ (¬ p3956) ∨ (¬ p3958) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial9744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory1562 t (m.theta 0 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule9744 (meaning t m 2027) (meaning t m 2220) (meaning t m 3646) (meaning t m 3956) (meaning t m 3958) (meaning t m 4441) source

theorem rule9745 (p2027 p2295 p2313 p2386 p2499 p3019 p4811 : Prop) (h : (¬ p2499) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p4811) ∨ (¬ p2295) ∨ (¬ p3019) ∨ p2027) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2499) ∨ (¬ p3019) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial9745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory1563 t (m.theta 0 6) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule9745 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2386) (meaning t m 2499) (meaning t m 3019) (meaning t m 4811) source

theorem rule9746 (p2027 p2230 p2284 p2579 p3096 p4705 : Prop) (h : (¬ p2230) ∨ (¬ p2284) ∨ (¬ p3096) ∨ (¬ p4705) ∨ (¬ p2579) ∨ p2027) : (p2027) ∨ (¬ p2230) ∨ (¬ p2284) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial9746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory1564 t (m.theta 0 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule9746 (meaning t m 2027) (meaning t m 2230) (meaning t m 2284) (meaning t m 2579) (meaning t m 3096) (meaning t m 4705) source

theorem rule9747 (p2027 p2499 p2774 p3055 p4390 p5214 : Prop) (h : (¬ p2499) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p5214) ∨ (¬ p4390) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2774) ∨ (¬ p3055) ∨ (¬ p4390) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial9747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory1565 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6)
  exact rule9747 (meaning t m 2027) (meaning t m 2499) (meaning t m 2774) (meaning t m 3055) (meaning t m 4390) (meaning t m 5214) source

theorem rule9748 (p2027 p2685 p2810 p2928 p3579 p4811 : Prop) (h : (¬ p3579) ∨ (¬ p2928) ∨ (¬ p2810) ∨ (¬ p4811) ∨ (¬ p2685) ∨ p2027) : (p2027) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p2928) ∨ (¬ p3579) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial9748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory1566 t (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule9748 (meaning t m 2027) (meaning t m 2685) (meaning t m 2810) (meaning t m 2928) (meaning t m 3579) (meaning t m 4811) source

theorem rule9750 (p2027 p2307 p2476 p2584 p2588 p4595 : Prop) (h : p2027 ∨ (¬ p2584) ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p4595) ∨ (¬ p2476)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2476) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p4595) := by
  classical
  tauto

theorem initial9750 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 4595)) := by
  have source := ElevenTheory.theory1568 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule9750 (meaning t m 2027) (meaning t m 2307) (meaning t m 2476) (meaning t m 2584) (meaning t m 2588) (meaning t m 4595) source

theorem rule9751 (p2027 p2190 p3146 p3956 p3958 p4347 : Prop) (h : (¬ p4347) ∨ (¬ p3958) ∨ (¬ p2190) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2190) ∨ (¬ p3146) ∨ (¬ p3956) ∨ (¬ p3958) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial9751 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory1569 t (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule9751 (meaning t m 2027) (meaning t m 2190) (meaning t m 3146) (meaning t m 3956) (meaning t m 3958) (meaning t m 4347) source

theorem rule9752 (p2027 p2307 p2493 p2586 p2928 p3921 : Prop) (h : (¬ p2493) ∨ p2027 ∨ (¬ p2586) ∨ (¬ p2307) ∨ (¬ p2928) ∨ (¬ p3921)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2493) ∨ (¬ p2586) ∨ (¬ p2928) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial9752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2586)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory1570 t (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule9752 (meaning t m 2027) (meaning t m 2307) (meaning t m 2493) (meaning t m 2586) (meaning t m 2928) (meaning t m 3921) source

theorem rule9753 (p2553 p2588 : Prop) (h : (¬ p2588) ∨ (¬ p2553)) : (¬ p2553) ∨ (¬ p2588) := by
  classical
  tauto

theorem initial9753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2588)) := by
  have source := ElevenTheory.theory1571 (m.theta 4 6) (m.theta 6 7)
  exact rule9753 (meaning t m 2553) (meaning t m 2588) source

theorem rule9755 (p2027 p2318 p2319 p2588 p3125 p3946 p3958 : Prop) (h : (¬ p2318) ∨ p2027 ∨ (¬ p2319) ∨ (¬ p3946) ∨ (¬ p2588) ∨ (¬ p3125) ∨ (¬ p3958)) : (p2027) ∨ (¬ p2318) ∨ (¬ p2319) ∨ (¬ p2588) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p3958) := by
  classical
  tauto

theorem initial9755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 3958)) := by
  have source := ElevenTheory.theory1573 t (m.theta 0 6) (m.theta 0 7) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule9755 (meaning t m 2027) (meaning t m 2318) (meaning t m 2319) (meaning t m 2588) (meaning t m 3125) (meaning t m 3946) (meaning t m 3958) source

theorem rule9756 (p2027 p2318 p2717 p3426 p3549 p3551 p4867 : Prop) (h : (¬ p3549) ∨ p2027 ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p2318) ∨ (¬ p4867) ∨ (¬ p3426)) : (p2027) ∨ (¬ p2318) ∨ (¬ p2717) ∨ (¬ p3426) ∨ (¬ p3549) ∨ (¬ p3551) ∨ (¬ p4867) := by
  classical
  tauto

theorem initial9756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4867)) := by
  have source := ElevenTheory.theory1574 t (m.theta 0 7) (m.theta 1 6) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule9756 (meaning t m 2027) (meaning t m 2318) (meaning t m 2717) (meaning t m 3426) (meaning t m 3549) (meaning t m 3551) (meaning t m 4867) source

theorem rule9759 (p2027 p2274 p2284 p2588 p2590 p4705 : Prop) (h : p2027 ∨ (¬ p2284) ∨ (¬ p2588) ∨ (¬ p2274) ∨ (¬ p2590) ∨ (¬ p4705)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial9759 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory1577 t (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule9759 (meaning t m 2027) (meaning t m 2274) (meaning t m 2284) (meaning t m 2588) (meaning t m 2590) (meaning t m 4705) source

theorem rule9760 (p2027 p2870 p3549 p3758 p4140 p4514 : Prop) (h : p2027 ∨ (¬ p4514) ∨ (¬ p3549) ∨ (¬ p4140) ∨ (¬ p3758) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3549) ∨ (¬ p3758) ∨ (¬ p4140) ∨ (¬ p4514) := by
  classical
  tauto

theorem initial9760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4514)) := by
  have source := ElevenTheory.theory1578 t (m.theta 1 6) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule9760 (meaning t m 2027) (meaning t m 2870) (meaning t m 3549) (meaning t m 3758) (meaning t m 4140) (meaning t m 4514) source

theorem rule9761 (p3051 p3646 p4204 : Prop) (h : (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4204)) : (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial9761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory1579 (m.theta 0 5) (m.theta 5 6) (m.theta 5 7)
  exact rule9761 (meaning t m 3051) (meaning t m 3646) (meaning t m 4204) source

theorem rule9762 (p2027 p2307 p3549 p3954 p4512 p4877 p5020 : Prop) (h : (¬ p4877) ∨ (¬ p2307) ∨ (¬ p3954) ∨ (¬ p3549) ∨ (¬ p4512) ∨ p2027 ∨ (¬ p5020)) : (p2027) ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3954) ∨ (¬ p4512) ∨ (¬ p4877) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial9762 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory1580 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 6 7)
  exact rule9762 (meaning t m 2027) (meaning t m 2307) (meaning t m 3549) (meaning t m 3954) (meaning t m 4512) (meaning t m 4877) (meaning t m 5020) source

theorem rule9763 (p2027 p2284 p2307 p2504 p2590 p3549 p3743 p4705 : Prop) (h : (¬ p2307) ∨ (¬ p3743) ∨ (¬ p2284) ∨ (¬ p2590) ∨ (¬ p3549) ∨ p2027 ∨ (¬ p2504) ∨ (¬ p4705)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2307) ∨ (¬ p2504) ∨ (¬ p2590) ∨ (¬ p3549) ∨ (¬ p3743) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial9763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory1581 t (m.theta 0 6) (m.theta 1 6) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule9763 (meaning t m 2027) (meaning t m 2284) (meaning t m 2307) (meaning t m 2504) (meaning t m 2590) (meaning t m 3549) (meaning t m 3743) (meaning t m 4705) source

theorem rule9765 (p2027 p2307 p2584 p2656 p2992 p3549 p4245 p4704 : Prop) (h : (¬ p4245) ∨ (¬ p2656) ∨ (¬ p4704) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p2584)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2656) ∨ (¬ p2992) ∨ (¬ p3549) ∨ (¬ p4245) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial9765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4245)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory1583 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 5) (m.theta 6 7)
  exact rule9765 (meaning t m 2027) (meaning t m 2307) (meaning t m 2584) (meaning t m 2656) (meaning t m 2992) (meaning t m 3549) (meaning t m 4245) (meaning t m 4704) source

end SunPrize.SMT
