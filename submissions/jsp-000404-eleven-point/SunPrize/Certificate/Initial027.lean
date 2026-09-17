import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory013
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule13325 (p5226 p6051 : Prop) (h : (p5226 ↔ p6051)) : (¬ p5226) ∨ (p6051) := by
  classical
  tauto

theorem initial13325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5226)) ∨ (meaning t m 6051) := by
  have source := ElevenTheory.theory3382 t (m.theta 2 7) (m.theta 2 9) (m.theta 7 9)
  exact rule13325 (meaning t m 5226) (meaning t m 6051) source

theorem rule13327 (p1984 p2027 p2928 p3434 p3437 p3452 p4278 : Prop) (h : p2027 ∨ p3437 ∨ (¬ p2928) ∨ (¬ p1984) ∨ (¬ p3434) ∨ (¬ p4278) ∨ (¬ p3452)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2928) ∨ (¬ p3434) ∨ (p3437) ∨ (¬ p3452) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial13327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3434)) ∨ (meaning t m 3437) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory3383 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 9)
  exact rule13327 (meaning t m 1984) (meaning t m 2027) (meaning t m 2928) (meaning t m 3434) (meaning t m 3437) (meaning t m 3452) (meaning t m 4278) source

theorem rule13329 (p1991 p2027 p2641 p2766 p2963 p4118 p4360 : Prop) (h : (¬ p1991) ∨ (¬ p4360) ∨ p2027 ∨ p2766 ∨ (¬ p2963) ∨ (¬ p2641) ∨ (¬ p4118)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2641) ∨ (p2766) ∨ (¬ p2963) ∨ (¬ p4118) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial13329 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory3385 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 8 9)
  exact rule13329 (meaning t m 1991) (meaning t m 2027) (meaning t m 2641) (meaning t m 2766) (meaning t m 2963) (meaning t m 4118) (meaning t m 4360) source

theorem rule13331 (p1982 p2027 p2156 p2187 p2363 p2688 p2951 p2992 : Prop) (h : (¬ p1982) ∨ p2688 ∨ (¬ p2951) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2992) ∨ (¬ p2156)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (p2688) ∨ (¬ p2951) ∨ (¬ p2992) := by
  classical
  tauto

theorem initial13331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) := by
  have source := ElevenTheory.theory3387 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule13331 (meaning t m 1982) (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 2688) (meaning t m 2951) (meaning t m 2992) source

theorem rule13333 (p3439 p3860 p4416 p5239 p5240 : Prop) : (p4416) ∨ (((¬ p5240) ∨ (¬ p4416) ∨ (¬ p5239) ∨ (¬ p3860) ∨ (¬ p3439))) := by
  classical
  tauto

theorem initial13333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4416) ∨ (meaning t m 6055) := by
  exact rule13333 (meaning t m 3439) (meaning t m 3860) (meaning t m 4416) (meaning t m 5239) (meaning t m 5240)

theorem rule13334 (p3439 p3860 p4416 p5239 p5240 : Prop) : (p5239) ∨ (((¬ p5240) ∨ (¬ p4416) ∨ (¬ p5239) ∨ (¬ p3860) ∨ (¬ p3439))) := by
  classical
  tauto

theorem initial13334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5239) ∨ (meaning t m 6055) := by
  exact rule13334 (meaning t m 3439) (meaning t m 3860) (meaning t m 4416) (meaning t m 5239) (meaning t m 5240)

theorem rule13335 (p3439 p3860 p4416 p5239 p5240 : Prop) : (p3860) ∨ (((¬ p5240) ∨ (¬ p4416) ∨ (¬ p5239) ∨ (¬ p3860) ∨ (¬ p3439))) := by
  classical
  tauto

theorem initial13335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3860) ∨ (meaning t m 6055) := by
  exact rule13335 (meaning t m 3439) (meaning t m 3860) (meaning t m 4416) (meaning t m 5239) (meaning t m 5240)

theorem rule13336 (p3439 p3860 p4416 p5239 p5240 : Prop) : (p3439) ∨ (((¬ p5240) ∨ (¬ p4416) ∨ (¬ p5239) ∨ (¬ p3860) ∨ (¬ p3439))) := by
  classical
  tauto

theorem initial13336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3439) ∨ (meaning t m 6055) := by
  exact rule13336 (meaning t m 3439) (meaning t m 3860) (meaning t m 4416) (meaning t m 5239) (meaning t m 5240)

theorem rule13339 (p3449 p3858 p5242 p5243 p5244 : Prop) : (p3449) ∨ (((¬ p5243) ∨ (¬ p3449) ∨ (¬ p3858) ∨ (¬ p5242) ∨ (¬ p5244))) := by
  classical
  tauto

theorem initial13339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3449) ∨ (meaning t m 6056) := by
  exact rule13339 (meaning t m 3449) (meaning t m 3858) (meaning t m 5242) (meaning t m 5243) (meaning t m 5244)

theorem rule13340 (p3449 p3858 p5242 p5243 p5244 : Prop) : (p3858) ∨ (((¬ p5243) ∨ (¬ p3449) ∨ (¬ p3858) ∨ (¬ p5242) ∨ (¬ p5244))) := by
  classical
  tauto

theorem initial13340 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3858) ∨ (meaning t m 6056) := by
  exact rule13340 (meaning t m 3449) (meaning t m 3858) (meaning t m 5242) (meaning t m 5243) (meaning t m 5244)

theorem rule13341 (p3449 p3858 p5242 p5243 p5244 : Prop) : (p5242) ∨ (((¬ p5243) ∨ (¬ p3449) ∨ (¬ p3858) ∨ (¬ p5242) ∨ (¬ p5244))) := by
  classical
  tauto

theorem initial13341 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5242) ∨ (meaning t m 6056) := by
  exact rule13341 (meaning t m 3449) (meaning t m 3858) (meaning t m 5242) (meaning t m 5243) (meaning t m 5244)

theorem rule13346 (p6055 p6056 : Prop) : (¬ ((¬ p6055) ∨ (¬ p6056))) ∨ (¬ p6055) ∨ (¬ p6056) := by
  classical
  tauto

theorem initial13346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6054)) ∨ (¬ (meaning t m 6055)) ∨ (¬ (meaning t m 6056)) := by
  exact rule13346 (meaning t m 6055) (meaning t m 6056)

theorem rule13347 (p5237 p6054 : Prop) (h : (p5237 ↔ p6054)) : (¬ p5237) ∨ (p6054) := by
  classical
  tauto

theorem initial13347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5237)) ∨ (meaning t m 6054) := by
  have source := ElevenTheory.theory3388 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 8)
  exact rule13347 (meaning t m 5237) (meaning t m 6054) source

theorem rule13349 (p2027 p2341 p3556 p3570 p4985 : Prop) (h : (¬ p4985) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4985) := by
  classical
  tauto

theorem initial13349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4985)) := by
  have source := ElevenTheory.theory3389 t (m.theta 0 5) (m.theta 0 7) (m.theta 5 7) (m.theta 7 8)
  exact rule13349 (meaning t m 2027) (meaning t m 2341) (meaning t m 3556) (meaning t m 3570) (meaning t m 4985) source

theorem rule13350 (p2000 p2148 p2589 p4539 : Prop) (h : p2148 ∨ (¬ p2589) ∨ (¬ p2000) ∨ p4539) : (¬ p2000) ∨ (p2148) ∨ (¬ p2589) ∨ (p4539) := by
  classical
  tauto

theorem initial13350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 4539) := by
  have source := ElevenTheory.theory3390 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5)
  exact rule13350 (meaning t m 2000) (meaning t m 2148) (meaning t m 2589) (meaning t m 4539) source

theorem rule13351 (p1975 p2027 p2299 p2688 p2881 p2951 p2992 p3051 : Prop) (h : (¬ p2951) ∨ (¬ p1975) ∨ (¬ p2299) ∨ p2027 ∨ p2688 ∨ (¬ p2881) ∨ (¬ p2992) ∨ (¬ p3051)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2688) ∨ (¬ p2881) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3051) := by
  classical
  tauto

theorem initial13351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3051)) := by
  have source := ElevenTheory.theory3391 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule13351 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2688) (meaning t m 2881) (meaning t m 2951) (meaning t m 2992) (meaning t m 3051) source

theorem rule13352 (p1984 p2027 p2509 p2534 p2764 p3452 p4444 : Prop) (h : (¬ p1984) ∨ (¬ p2509) ∨ (¬ p4444) ∨ p2027 ∨ p2764 ∨ (¬ p3452) ∨ (¬ p2534)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (p2764) ∨ (¬ p3452) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial13352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory3392 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 8) (m.theta 8 9) (m.theta 9 10)
  exact rule13352 (meaning t m 1984) (meaning t m 2027) (meaning t m 2509) (meaning t m 2534) (meaning t m 2764) (meaning t m 3452) (meaning t m 4444) source

theorem rule13353 (p4191 p5247 p5248 p5249 p5250 : Prop) : (p5248) ∨ (((¬ p5248) ∨ (¬ p4191) ∨ (¬ p5247) ∨ (¬ p5249) ∨ (¬ p5250))) := by
  classical
  tauto

theorem initial13353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5248) ∨ (meaning t m 6058) := by
  exact rule13353 (meaning t m 4191) (meaning t m 5247) (meaning t m 5248) (meaning t m 5249) (meaning t m 5250)

theorem rule13354 (p4191 p5247 p5248 p5249 p5250 : Prop) : (p4191) ∨ (((¬ p5248) ∨ (¬ p4191) ∨ (¬ p5247) ∨ (¬ p5249) ∨ (¬ p5250))) := by
  classical
  tauto

theorem initial13354 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4191) ∨ (meaning t m 6058) := by
  exact rule13354 (meaning t m 4191) (meaning t m 5247) (meaning t m 5248) (meaning t m 5249) (meaning t m 5250)

theorem rule13355 (p4191 p5247 p5248 p5249 p5250 : Prop) : (p5247) ∨ (((¬ p5248) ∨ (¬ p4191) ∨ (¬ p5247) ∨ (¬ p5249) ∨ (¬ p5250))) := by
  classical
  tauto

theorem initial13355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5247) ∨ (meaning t m 6058) := by
  exact rule13355 (meaning t m 4191) (meaning t m 5247) (meaning t m 5248) (meaning t m 5249) (meaning t m 5250)

theorem rule13357 (p4191 p5247 p5248 p5249 p5250 : Prop) : (p5250) ∨ (((¬ p5248) ∨ (¬ p4191) ∨ (¬ p5247) ∨ (¬ p5249) ∨ (¬ p5250))) := by
  classical
  tauto

theorem initial13357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5250) ∨ (meaning t m 6058) := by
  exact rule13357 (meaning t m 4191) (meaning t m 5247) (meaning t m 5248) (meaning t m 5249) (meaning t m 5250)

theorem rule13359 (p3461 p4394 p5252 p5253 p5254 : Prop) : (p5252) ∨ (((¬ p5252) ∨ (¬ p4394) ∨ (¬ p3461) ∨ (¬ p5253) ∨ (¬ p5254))) := by
  classical
  tauto

theorem initial13359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5252) ∨ (meaning t m 6059) := by
  exact rule13359 (meaning t m 3461) (meaning t m 4394) (meaning t m 5252) (meaning t m 5253) (meaning t m 5254)

theorem rule13360 (p3461 p4394 p5252 p5253 p5254 : Prop) : (p4394) ∨ (((¬ p5252) ∨ (¬ p4394) ∨ (¬ p3461) ∨ (¬ p5253) ∨ (¬ p5254))) := by
  classical
  tauto

theorem initial13360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4394) ∨ (meaning t m 6059) := by
  exact rule13360 (meaning t m 3461) (meaning t m 4394) (meaning t m 5252) (meaning t m 5253) (meaning t m 5254)

theorem rule13361 (p3461 p4394 p5252 p5253 p5254 : Prop) : (p3461) ∨ (((¬ p5252) ∨ (¬ p4394) ∨ (¬ p3461) ∨ (¬ p5253) ∨ (¬ p5254))) := by
  classical
  tauto

theorem initial13361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3461) ∨ (meaning t m 6059) := by
  exact rule13361 (meaning t m 3461) (meaning t m 4394) (meaning t m 5252) (meaning t m 5253) (meaning t m 5254)

theorem rule13362 (p3461 p4394 p5252 p5253 p5254 : Prop) : (p5253) ∨ (((¬ p5252) ∨ (¬ p4394) ∨ (¬ p3461) ∨ (¬ p5253) ∨ (¬ p5254))) := by
  classical
  tauto

theorem initial13362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5253) ∨ (meaning t m 6059) := by
  exact rule13362 (meaning t m 3461) (meaning t m 4394) (meaning t m 5252) (meaning t m 5253) (meaning t m 5254)

theorem rule13363 (p3461 p4394 p5252 p5253 p5254 : Prop) : (p5254) ∨ (((¬ p5252) ∨ (¬ p4394) ∨ (¬ p3461) ∨ (¬ p5253) ∨ (¬ p5254))) := by
  classical
  tauto

theorem initial13363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5254) ∨ (meaning t m 6059) := by
  exact rule13363 (meaning t m 3461) (meaning t m 4394) (meaning t m 5252) (meaning t m 5253) (meaning t m 5254)

theorem rule13367 (p6058 p6059 : Prop) : (¬ ((¬ p6058) ∨ (¬ p6059))) ∨ (¬ p6058) ∨ (¬ p6059) := by
  classical
  tauto

theorem initial13367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6057)) ∨ (¬ (meaning t m 6058)) ∨ (¬ (meaning t m 6059)) := by
  exact rule13367 (meaning t m 6058) (meaning t m 6059)

theorem rule13368 (p5245 p6057 : Prop) (h : (p5245 ↔ p6057)) : (¬ p5245) ∨ (p6057) := by
  classical
  tauto

theorem initial13368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5245)) ∨ (meaning t m 6057) := by
  have source := ElevenTheory.theory3393 t (m.theta 6 10) (m.theta 6 9) (m.theta 9 10)
  exact rule13368 (meaning t m 5245) (meaning t m 6057) source

theorem rule13370 (p1988 p2027 p2156 p2688 p2951 p2992 p3125 p3461 : Prop) (h : (¬ p1988) ∨ (¬ p2951) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p3125) ∨ (¬ p2156) ∨ p2688) : (¬ p1988) ∨ (p2027) ∨ (¬ p2156) ∨ (p2688) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3125) ∨ (¬ p3461) := by
  classical
  tauto

theorem initial13370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) := by
  have source := ElevenTheory.theory3394 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule13370 (meaning t m 1988) (meaning t m 2027) (meaning t m 2156) (meaning t m 2688) (meaning t m 2951) (meaning t m 2992) (meaning t m 3125) (meaning t m 3461) source

theorem rule13371 (p1975 p2027 p2264 p2287 p2299 p2807 p2963 : Prop) (h : (¬ p1975) ∨ (¬ p2807) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p2299) ∨ p2287 ∨ (¬ p2264)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2264) ∨ (p2287) ∨ (¬ p2299) ∨ (¬ p2807) ∨ (¬ p2963) := by
  classical
  tauto

theorem initial13371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) := by
  have source := ElevenTheory.theory3395 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule13371 (meaning t m 1975) (meaning t m 2027) (meaning t m 2264) (meaning t m 2287) (meaning t m 2299) (meaning t m 2807) (meaning t m 2963) source

theorem rule13372 (p2598 p3577 p3820 p5085 : Prop) (h : (¬ p2598) ∨ (¬ p3820) ∨ (¬ p5085) ∨ (¬ p3577)) : (¬ p2598) ∨ (¬ p3577) ∨ (¬ p3820) ∨ (¬ p5085) := by
  classical
  tauto

theorem initial13372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 5085)) := by
  have source := ElevenTheory.theory3396 (m.theta 0 2) (m.theta 0 7) (m.theta 2 4) (m.theta 2 7)
  exact rule13372 (meaning t m 2598) (meaning t m 3577) (meaning t m 3820) (meaning t m 5085) source

theorem rule13373 (p3425 p3577 p3820 p5257 p5258 : Prop) : (p3820) ∨ (((¬ p3820) ∨ (¬ p3577) ∨ (¬ p3425) ∨ (¬ p5257) ∨ (¬ p5258))) := by
  classical
  tauto

theorem initial13373 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3820) ∨ (meaning t m 6061) := by
  exact rule13373 (meaning t m 3425) (meaning t m 3577) (meaning t m 3820) (meaning t m 5257) (meaning t m 5258)

theorem rule13374 (p3425 p3577 p3820 p5257 p5258 : Prop) : (p3577) ∨ (((¬ p3820) ∨ (¬ p3577) ∨ (¬ p3425) ∨ (¬ p5257) ∨ (¬ p5258))) := by
  classical
  tauto

theorem initial13374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3577) ∨ (meaning t m 6061) := by
  exact rule13374 (meaning t m 3425) (meaning t m 3577) (meaning t m 3820) (meaning t m 5257) (meaning t m 5258)

theorem rule13375 (p3425 p3577 p3820 p5257 p5258 : Prop) : (p3425) ∨ (((¬ p3820) ∨ (¬ p3577) ∨ (¬ p3425) ∨ (¬ p5257) ∨ (¬ p5258))) := by
  classical
  tauto

theorem initial13375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3425) ∨ (meaning t m 6061) := by
  exact rule13375 (meaning t m 3425) (meaning t m 3577) (meaning t m 3820) (meaning t m 5257) (meaning t m 5258)

theorem rule13377 (p3425 p3577 p3820 p5257 p5258 : Prop) : (p5258) ∨ (((¬ p3820) ∨ (¬ p3577) ∨ (¬ p3425) ∨ (¬ p5257) ∨ (¬ p5258))) := by
  classical
  tauto

theorem initial13377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5258) ∨ (meaning t m 6061) := by
  exact rule13377 (meaning t m 3425) (meaning t m 3577) (meaning t m 3820) (meaning t m 5257) (meaning t m 5258)

theorem rule13379 (p3471 p3819 p3959 p5260 p5261 : Prop) : (p5260) ∨ (((¬ p5260) ∨ (¬ p3471) ∨ (¬ p3959) ∨ (¬ p3819) ∨ (¬ p5261))) := by
  classical
  tauto

theorem initial13379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5260) ∨ (meaning t m 6062) := by
  exact rule13379 (meaning t m 3471) (meaning t m 3819) (meaning t m 3959) (meaning t m 5260) (meaning t m 5261)

theorem rule13380 (p3471 p3819 p3959 p5260 p5261 : Prop) : (p3471) ∨ (((¬ p5260) ∨ (¬ p3471) ∨ (¬ p3959) ∨ (¬ p3819) ∨ (¬ p5261))) := by
  classical
  tauto

theorem initial13380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3471) ∨ (meaning t m 6062) := by
  exact rule13380 (meaning t m 3471) (meaning t m 3819) (meaning t m 3959) (meaning t m 5260) (meaning t m 5261)

theorem rule13381 (p3471 p3819 p3959 p5260 p5261 : Prop) : (p3959) ∨ (((¬ p5260) ∨ (¬ p3471) ∨ (¬ p3959) ∨ (¬ p3819) ∨ (¬ p5261))) := by
  classical
  tauto

theorem initial13381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3959) ∨ (meaning t m 6062) := by
  exact rule13381 (meaning t m 3471) (meaning t m 3819) (meaning t m 3959) (meaning t m 5260) (meaning t m 5261)

theorem rule13382 (p3471 p3819 p3959 p5260 p5261 : Prop) : (p3819) ∨ (((¬ p5260) ∨ (¬ p3471) ∨ (¬ p3959) ∨ (¬ p3819) ∨ (¬ p5261))) := by
  classical
  tauto

theorem initial13382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3819) ∨ (meaning t m 6062) := by
  exact rule13382 (meaning t m 3471) (meaning t m 3819) (meaning t m 3959) (meaning t m 5260) (meaning t m 5261)

theorem rule13383 (p3471 p3819 p3959 p5260 p5261 : Prop) : (p5261) ∨ (((¬ p5260) ∨ (¬ p3471) ∨ (¬ p3959) ∨ (¬ p3819) ∨ (¬ p5261))) := by
  classical
  tauto

theorem initial13383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5261) ∨ (meaning t m 6062) := by
  exact rule13383 (meaning t m 3471) (meaning t m 3819) (meaning t m 3959) (meaning t m 5260) (meaning t m 5261)

theorem rule13387 (p6061 p6062 : Prop) : (¬ ((¬ p6061) ∨ (¬ p6062))) ∨ (¬ p6061) ∨ (¬ p6062) := by
  classical
  tauto

theorem initial13387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6060)) ∨ (¬ (meaning t m 6061)) ∨ (¬ (meaning t m 6062)) := by
  exact rule13387 (meaning t m 6061) (meaning t m 6062)

theorem rule13388 (p5255 p6060 : Prop) (h : (p5255 ↔ p6060)) : (¬ p5255) ∨ (p6060) := by
  classical
  tauto

theorem initial13388 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5255)) ∨ (meaning t m 6060) := by
  have source := ElevenTheory.theory3397 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 7)
  exact rule13388 (meaning t m 5255) (meaning t m 6060) source

theorem rule13390 (p2753 p3588 p3819 p3959 : Prop) (h : (¬ p3819) ∨ (¬ p2753) ∨ (¬ p3588) ∨ (¬ p3959)) : (¬ p2753) ∨ (¬ p3588) ∨ (¬ p3819) ∨ (¬ p3959) := by
  classical
  tauto

theorem initial13390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 3959)) := by
  have source := ElevenTheory.theory3398 (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 2 7)
  exact rule13390 (meaning t m 2753) (meaning t m 3588) (meaning t m 3819) (meaning t m 3959) source

theorem rule13392 (p1977 p2027 p2534 p2630 p2766 p3877 p4111 p4437 : Prop) (h : (¬ p4437) ∨ (¬ p3877) ∨ (¬ p2534) ∨ p2766 ∨ (¬ p4111) ∨ (¬ p1977) ∨ (¬ p2630) ∨ p2027) : (¬ p1977) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2630) ∨ (p2766) ∨ (¬ p3877) ∨ (¬ p4111) ∨ (¬ p4437) := by
  classical
  tauto

theorem initial13392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4437)) := by
  have source := ElevenTheory.theory3400 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule13392 (meaning t m 1977) (meaning t m 2027) (meaning t m 2534) (meaning t m 2630) (meaning t m 2766) (meaning t m 3877) (meaning t m 4111) (meaning t m 4437) source

theorem rule13394 (p3917 p5264 p5265 p5266 p5267 : Prop) : (p3917) ∨ (((¬ p5265) ∨ (¬ p3917) ∨ (¬ p5264) ∨ (¬ p5266) ∨ (¬ p5267))) := by
  classical
  tauto

theorem initial13394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3917) ∨ (meaning t m 6064) := by
  exact rule13394 (meaning t m 3917) (meaning t m 5264) (meaning t m 5265) (meaning t m 5266) (meaning t m 5267)

theorem rule13401 (p3483 p4231 p5269 p5270 p5271 : Prop) : (p3483) ∨ (((¬ p5269) ∨ (¬ p4231) ∨ (¬ p3483) ∨ (¬ p5270) ∨ (¬ p5271))) := by
  classical
  tauto

theorem initial13401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3483) ∨ (meaning t m 6065) := by
  exact rule13401 (meaning t m 3483) (meaning t m 4231) (meaning t m 5269) (meaning t m 5270) (meaning t m 5271)

theorem rule13407 (p6064 p6065 : Prop) : (¬ ((¬ p6064) ∨ (¬ p6065))) ∨ (¬ p6064) ∨ (¬ p6065) := by
  classical
  tauto

theorem initial13407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6063)) ∨ (¬ (meaning t m 6064)) ∨ (¬ (meaning t m 6065)) := by
  exact rule13407 (meaning t m 6064) (meaning t m 6065)

theorem rule13408 (p5262 p6063 : Prop) (h : (p5262 ↔ p6063)) : (¬ p5262) ∨ (p6063) := by
  classical
  tauto

theorem initial13408 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5262)) ∨ (meaning t m 6063) := by
  have source := ElevenTheory.theory3401 t (m.theta 2 6) (m.theta 2 9) (m.theta 6 9)
  exact rule13408 (meaning t m 5262) (meaning t m 6063) source

theorem rule13410 (p1985 p2027 p2287 p2717 p3323 p3426 p3570 p3917 : Prop) (h : (¬ p1985) ∨ (¬ p2717) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p3426) ∨ p2287 ∨ (¬ p3917) ∨ (¬ p3323)) : (¬ p1985) ∨ (p2027) ∨ (p2287) ∨ (¬ p2717) ∨ (¬ p3323) ∨ (¬ p3426) ∨ (¬ p3570) ∨ (¬ p3917) := by
  classical
  tauto

theorem initial13410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3917)) := by
  have source := ElevenTheory.theory3402 t (m.theta 2 6) (m.theta 2 7) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8)
  exact rule13410 (meaning t m 1985) (meaning t m 2027) (meaning t m 2287) (meaning t m 2717) (meaning t m 3323) (meaning t m 3426) (meaning t m 3570) (meaning t m 3917) source

theorem rule13411 (p1975 p2027 p2132 p2299 p2611 p2860 p2881 p3872 : Prop) (h : (¬ p2132) ∨ p2611 ∨ (¬ p2860) ∨ (¬ p2881) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p3872) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2299) ∨ (p2611) ∨ (¬ p2860) ∨ (¬ p2881) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial13411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory3403 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule13411 (meaning t m 1975) (meaning t m 2027) (meaning t m 2132) (meaning t m 2299) (meaning t m 2611) (meaning t m 2860) (meaning t m 2881) (meaning t m 3872) source

theorem rule13412 (p2001 p2027 p2114 p2132 p2619 p2780 p2829 : Prop) (h : p2114 ∨ (¬ p2829) ∨ (¬ p2001) ∨ (¬ p2619) ∨ p2027 ∨ (¬ p2780) ∨ (¬ p2132)) : (¬ p2001) ∨ (p2027) ∨ (p2114) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2780) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial13412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory3404 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 8)
  exact rule13412 (meaning t m 2001) (meaning t m 2027) (meaning t m 2114) (meaning t m 2132) (meaning t m 2619) (meaning t m 2780) (meaning t m 2829) source

theorem rule13413 (p1975 p2027 p2274 p2388 p2860 p3156 p3694 : Prop) (h : (¬ p3694) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p1975) ∨ p2388 ∨ (¬ p2860) ∨ (¬ p2274)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2388) ∨ (¬ p2860) ∨ (¬ p3156) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial13413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory3405 t (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule13413 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2388) (meaning t m 2860) (meaning t m 3156) (meaning t m 3694) source

theorem rule13414 (p1975 p2027 p2114 p2264 p2299 p2737 p2797 p4156 : Prop) (h : p2114 ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p1975) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p4156) ∨ (¬ p2264)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial13414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory3406 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule13414 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2264) (meaning t m 2299) (meaning t m 2737) (meaning t m 2797) (meaning t m 4156) source

theorem rule13415 (p1994 p2027 p2388 p2651 p3172 p3189 p3662 : Prop) (h : p2388 ∨ (¬ p3172) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p3189) ∨ (¬ p2651) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (p2388) ∨ (¬ p2651) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial13415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory3407 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 8)
  exact rule13415 (meaning t m 1994) (meaning t m 2027) (meaning t m 2388) (meaning t m 2651) (meaning t m 3172) (meaning t m 3189) (meaning t m 3662) source

theorem rule13416 (p1994 p2027 p2202 p2563 p2651 p2952 p3952 : Prop) (h : (¬ p3952) ∨ (¬ p2952) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p2651) ∨ p2202 ∨ (¬ p2563)) : (¬ p1994) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial13416 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory3408 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule13416 (meaning t m 1994) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2651) (meaning t m 2952) (meaning t m 3952) source

theorem rule13417 (p1975 p2027 p2299 p2427 p2765 p2881 p4110 : Prop) (h : (¬ p4110) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p2299) ∨ (¬ p2881) ∨ p2765 ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2427) ∨ (p2765) ∨ (¬ p2881) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial13417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory3409 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule13417 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2427) (meaning t m 2765) (meaning t m 2881) (meaning t m 4110) source

theorem rule13418 (p1975 p2027 p2299 p2341 p2622 p2707 p2743 p3577 : Prop) (h : (¬ p3577) ∨ (¬ p1975) ∨ p2622 ∨ (¬ p2743) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p2707) ∨ (¬ p2299)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (p2622) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3577) := by
  classical
  tauto

theorem initial13418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3577)) := by
  have source := ElevenTheory.theory3410 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule13418 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2341) (meaning t m 2622) (meaning t m 2707) (meaning t m 2743) (meaning t m 3577) source

theorem rule13419 (p1985 p2027 p2138 p2717 p3471 p3474 p3570 : Prop) (h : (¬ p2138) ∨ p3474 ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p1985)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (p3474) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial13419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3471)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory3411 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule13419 (meaning t m 1985) (meaning t m 2027) (meaning t m 2138) (meaning t m 2717) (meaning t m 3471) (meaning t m 3474) (meaning t m 3570) source

theorem rule13422 (p1981 p2027 p2187 p2688 p2992 p3323 p3744 p4336 : Prop) (h : p2027 ∨ (¬ p2187) ∨ (¬ p2992) ∨ (¬ p1981) ∨ (¬ p3744) ∨ p2688 ∨ (¬ p3323) ∨ (¬ p4336)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (p2688) ∨ (¬ p2992) ∨ (¬ p3323) ∨ (¬ p3744) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial13422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory3414 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule13422 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2688) (meaning t m 2992) (meaning t m 3323) (meaning t m 3744) (meaning t m 4336) source

theorem rule13423 (p4037 p4190 p5274 p5275 p5276 : Prop) : (p4190) ∨ (((¬ p4190) ∨ (¬ p4037) ∨ (¬ p5274) ∨ (¬ p5275) ∨ (¬ p5276))) := by
  classical
  tauto

theorem initial13423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4190) ∨ (meaning t m 6067) := by
  exact rule13423 (meaning t m 4037) (meaning t m 4190) (meaning t m 5274) (meaning t m 5275) (meaning t m 5276)

theorem rule13424 (p4037 p4190 p5274 p5275 p5276 : Prop) : (p4037) ∨ (((¬ p4190) ∨ (¬ p4037) ∨ (¬ p5274) ∨ (¬ p5275) ∨ (¬ p5276))) := by
  classical
  tauto

theorem initial13424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4037) ∨ (meaning t m 6067) := by
  exact rule13424 (meaning t m 4037) (meaning t m 4190) (meaning t m 5274) (meaning t m 5275) (meaning t m 5276)

theorem rule13425 (p4037 p4190 p5274 p5275 p5276 : Prop) : (p5274) ∨ (((¬ p4190) ∨ (¬ p4037) ∨ (¬ p5274) ∨ (¬ p5275) ∨ (¬ p5276))) := by
  classical
  tauto

theorem initial13425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5274) ∨ (meaning t m 6067) := by
  exact rule13425 (meaning t m 4037) (meaning t m 4190) (meaning t m 5274) (meaning t m 5275) (meaning t m 5276)

theorem rule13427 (p4037 p4190 p5274 p5275 p5276 : Prop) : (p5276) ∨ (((¬ p4190) ∨ (¬ p4037) ∨ (¬ p5274) ∨ (¬ p5275) ∨ (¬ p5276))) := by
  classical
  tauto

theorem initial13427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5276) ∨ (meaning t m 6067) := by
  exact rule13427 (meaning t m 4037) (meaning t m 4190) (meaning t m 5274) (meaning t m 5275) (meaning t m 5276)

theorem rule13431 (p3323 p4367 p4421 p5278 p5279 : Prop) : (p3323) ∨ (((¬ p4367) ∨ (¬ p4421) ∨ (¬ p3323) ∨ (¬ p5278) ∨ (¬ p5279))) := by
  classical
  tauto

theorem initial13431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3323) ∨ (meaning t m 6068) := by
  exact rule13431 (meaning t m 3323) (meaning t m 4367) (meaning t m 4421) (meaning t m 5278) (meaning t m 5279)

theorem rule13437 (p6067 p6068 : Prop) : (¬ ((¬ p6067) ∨ (¬ p6068))) ∨ (¬ p6067) ∨ (¬ p6068) := by
  classical
  tauto

theorem initial13437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6066)) ∨ (¬ (meaning t m 6067)) ∨ (¬ (meaning t m 6068)) := by
  exact rule13437 (meaning t m 6067) (meaning t m 6068)

theorem rule13438 (p5272 p6066 : Prop) (h : (p5272 ↔ p6066)) : (¬ p5272) ∨ (p6066) := by
  classical
  tauto

theorem initial13438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5272)) ∨ (meaning t m 6066) := by
  have source := ElevenTheory.theory3415 t (m.theta 3 6) (m.theta 3 9) (m.theta 6 9)
  exact rule13438 (meaning t m 5272) (meaning t m 6066) source

theorem rule13441 (p1987 p2027 p2651 p2688 p2810 p3027 p3414 : Prop) (h : (¬ p2810) ∨ (¬ p2651) ∨ p2027 ∨ p2688 ∨ (¬ p1987) ∨ (¬ p3414) ∨ (¬ p3027)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2651) ∨ (p2688) ∨ (¬ p2810) ∨ (¬ p3027) ∨ (¬ p3414) := by
  classical
  tauto

theorem initial13441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) := by
  have source := ElevenTheory.theory3417 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule13441 (meaning t m 1987) (meaning t m 2027) (meaning t m 2651) (meaning t m 2688) (meaning t m 2810) (meaning t m 3027) (meaning t m 3414) source

theorem rule13442 (p1975 p2027 p2295 p2323 p2641 p2651 p4111 : Prop) (h : (¬ p2295) ∨ (¬ p2641) ∨ (¬ p4111) ∨ p2323 ∨ (¬ p1975) ∨ (¬ p2651) ∨ p2027) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2323) ∨ (¬ p2641) ∨ (¬ p2651) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial13442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory3418 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule13442 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2323) (meaning t m 2641) (meaning t m 2651) (meaning t m 4111) source

theorem rule13443 (p1975 p2027 p2274 p2563 p2598 p2611 p2850 : Prop) (h : (¬ p1975) ∨ p2611 ∨ (¬ p2850) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p2598)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2850) := by
  classical
  tauto

theorem initial13443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2850)) := by
  have source := ElevenTheory.theory3419 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule13443 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2563) (meaning t m 2598) (meaning t m 2611) (meaning t m 2850) source

theorem rule13444 (p1988 p2027 p2363 p2611 p2774 p2819 p3266 : Prop) (h : (¬ p1988) ∨ p2611 ∨ (¬ p2363) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p2774) ∨ (¬ p2819)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2363) ∨ (p2611) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial13444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory3420 t (m.theta 0 2) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule13444 (meaning t m 1988) (meaning t m 2027) (meaning t m 2363) (meaning t m 2611) (meaning t m 2774) (meaning t m 2819) (meaning t m 3266) source

theorem rule13445 (p1982 p2027 p2144 p2156 p2611 p3125 p3461 p4444 : Prop) (h : (¬ p1982) ∨ p2027 ∨ p2611 ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p4444) ∨ (¬ p3461) ∨ (¬ p3125)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (p2611) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial13445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory3421 t (m.theta 0 2) (m.theta 0 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule13445 (meaning t m 1982) (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 2611) (meaning t m 3125) (meaning t m 3461) (meaning t m 4444) source

theorem rule13446 (p1991 p2027 p2810 p2952 p3136 p3498 p4256 : Prop) (h : (¬ p2810) ∨ p3498 ∨ (¬ p1991) ∨ (¬ p2952) ∨ (¬ p3136) ∨ p2027 ∨ (¬ p4256)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2810) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (p3498) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial13446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory3422 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 8)
  exact rule13446 (meaning t m 1991) (meaning t m 2027) (meaning t m 2810) (meaning t m 2952) (meaning t m 3136) (meaning t m 3498) (meaning t m 4256) source

theorem rule13449 (p5282 p5283 p5284 p5285 p5286 : Prop) : (p5284) ∨ (((¬ p5283) ∨ (¬ p5284) ∨ (¬ p5282) ∨ (¬ p5285) ∨ (¬ p5286))) := by
  classical
  tauto

theorem initial13449 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5284) ∨ (meaning t m 6070) := by
  exact rule13449 (meaning t m 5282) (meaning t m 5283) (meaning t m 5284) (meaning t m 5285) (meaning t m 5286)

theorem rule13456 (p3506 p5288 p5289 p5290 p5291 : Prop) : (p3506) ∨ (((¬ p5288) ∨ (¬ p5289) ∨ (¬ p3506) ∨ (¬ p5290) ∨ (¬ p5291))) := by
  classical
  tauto

theorem initial13456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3506) ∨ (meaning t m 6071) := by
  exact rule13456 (meaning t m 3506) (meaning t m 5288) (meaning t m 5289) (meaning t m 5290) (meaning t m 5291)

theorem rule13462 (p6070 p6071 : Prop) : (¬ ((¬ p6070) ∨ (¬ p6071))) ∨ (¬ p6070) ∨ (¬ p6071) := by
  classical
  tauto

theorem initial13462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6069)) ∨ (¬ (meaning t m 6070)) ∨ (¬ (meaning t m 6071)) := by
  exact rule13462 (meaning t m 6070) (meaning t m 6071)

theorem rule13463 (p5280 p6069 : Prop) (h : (p5280 ↔ p6069)) : (¬ p5280) ∨ (p6069) := by
  classical
  tauto

theorem initial13463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5280)) ∨ (meaning t m 6069) := by
  have source := ElevenTheory.theory3424 t (m.theta 3 10) (m.theta 3 9) (m.theta 9 10)
  exact rule13463 (meaning t m 5280) (meaning t m 6069) source

theorem rule13466 (p3821 p5294 p5295 p5296 p5297 : Prop) : (p5294) ∨ (((¬ p5294) ∨ (¬ p3821) ∨ (¬ p5297) ∨ (¬ p5296) ∨ (¬ p5295))) := by
  classical
  tauto

theorem initial13466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5294) ∨ (meaning t m 6073) := by
  exact rule13466 (meaning t m 3821) (meaning t m 5294) (meaning t m 5295) (meaning t m 5296) (meaning t m 5297)

theorem rule13467 (p3821 p5294 p5295 p5296 p5297 : Prop) : (p3821) ∨ (((¬ p5294) ∨ (¬ p3821) ∨ (¬ p5297) ∨ (¬ p5296) ∨ (¬ p5295))) := by
  classical
  tauto

theorem initial13467 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3821) ∨ (meaning t m 6073) := by
  exact rule13467 (meaning t m 3821) (meaning t m 5294) (meaning t m 5295) (meaning t m 5296) (meaning t m 5297)

theorem rule13470 (p3821 p5294 p5295 p5296 p5297 : Prop) : (p5295) ∨ (((¬ p5294) ∨ (¬ p3821) ∨ (¬ p5297) ∨ (¬ p5296) ∨ (¬ p5295))) := by
  classical
  tauto

theorem initial13470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5295) ∨ (meaning t m 6073) := by
  exact rule13470 (meaning t m 3821) (meaning t m 5294) (meaning t m 5295) (meaning t m 5296) (meaning t m 5297)

theorem rule13472 (p3516 p5299 p5300 p5301 p5302 : Prop) : (p5299) ∨ (((¬ p5299) ∨ (¬ p5302) ∨ (¬ p5301) ∨ (¬ p5300) ∨ (¬ p3516))) := by
  classical
  tauto

theorem initial13472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5299) ∨ (meaning t m 6074) := by
  exact rule13472 (meaning t m 3516) (meaning t m 5299) (meaning t m 5300) (meaning t m 5301) (meaning t m 5302)

theorem rule13475 (p3516 p5299 p5300 p5301 p5302 : Prop) : (p5300) ∨ (((¬ p5299) ∨ (¬ p5302) ∨ (¬ p5301) ∨ (¬ p5300) ∨ (¬ p3516))) := by
  classical
  tauto

theorem initial13475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5300) ∨ (meaning t m 6074) := by
  exact rule13475 (meaning t m 3516) (meaning t m 5299) (meaning t m 5300) (meaning t m 5301) (meaning t m 5302)

theorem rule13476 (p3516 p5299 p5300 p5301 p5302 : Prop) : (p3516) ∨ (((¬ p5299) ∨ (¬ p5302) ∨ (¬ p5301) ∨ (¬ p5300) ∨ (¬ p3516))) := by
  classical
  tauto

theorem initial13476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3516) ∨ (meaning t m 6074) := by
  exact rule13476 (meaning t m 3516) (meaning t m 5299) (meaning t m 5300) (meaning t m 5301) (meaning t m 5302)

theorem rule13480 (p6073 p6074 : Prop) : (¬ ((¬ p6073) ∨ (¬ p6074))) ∨ (¬ p6073) ∨ (¬ p6074) := by
  classical
  tauto

theorem initial13480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6072)) ∨ (¬ (meaning t m 6073)) ∨ (¬ (meaning t m 6074)) := by
  exact rule13480 (meaning t m 6073) (meaning t m 6074)

theorem rule13481 (p5292 p6072 : Prop) (h : (p5292 ↔ p6072)) : (¬ p5292) ∨ (p6072) := by
  classical
  tauto

theorem initial13481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5292)) ∨ (meaning t m 6072) := by
  have source := ElevenTheory.theory3426 t (m.theta 0 7) (m.theta 0 9) (m.theta 7 9)
  exact rule13481 (meaning t m 5292) (meaning t m 6072) source

theorem rule13483 (p1975 p2027 p2299 p2341 p2355 p2449 p3821 : Prop) (h : p2355 ∨ (¬ p1975) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p2449) ∨ (¬ p3821) ∨ (¬ p2341)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (p2355) ∨ (¬ p2449) ∨ (¬ p3821) := by
  classical
  tauto

theorem initial13483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3821)) := by
  have source := ElevenTheory.theory3427 t (m.theta 0 7) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule13483 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2341) (meaning t m 2355) (meaning t m 2449) (meaning t m 3821) source

theorem rule13484 (p3542 p3544 p3548 p4832 p5305 : Prop) : (p3542) ∨ (((¬ p3542) ∨ (¬ p3548) ∨ (¬ p3544) ∨ (¬ p5305) ∨ (¬ p4832))) := by
  classical
  tauto

theorem initial13484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3542) ∨ (meaning t m 6076) := by
  exact rule13484 (meaning t m 3542) (meaning t m 3544) (meaning t m 3548) (meaning t m 4832) (meaning t m 5305)

theorem rule13485 (p3542 p3544 p3548 p4832 p5305 : Prop) : (p3548) ∨ (((¬ p3542) ∨ (¬ p3548) ∨ (¬ p3544) ∨ (¬ p5305) ∨ (¬ p4832))) := by
  classical
  tauto

theorem initial13485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3548) ∨ (meaning t m 6076) := by
  exact rule13485 (meaning t m 3542) (meaning t m 3544) (meaning t m 3548) (meaning t m 4832) (meaning t m 5305)

theorem rule13486 (p3542 p3544 p3548 p4832 p5305 : Prop) : (p3544) ∨ (((¬ p3542) ∨ (¬ p3548) ∨ (¬ p3544) ∨ (¬ p5305) ∨ (¬ p4832))) := by
  classical
  tauto

theorem initial13486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3544) ∨ (meaning t m 6076) := by
  exact rule13486 (meaning t m 3542) (meaning t m 3544) (meaning t m 3548) (meaning t m 4832) (meaning t m 5305)

theorem rule13488 (p3542 p3544 p3548 p4832 p5305 : Prop) : (p4832) ∨ (((¬ p3542) ∨ (¬ p3548) ∨ (¬ p3544) ∨ (¬ p5305) ∨ (¬ p4832))) := by
  classical
  tauto

theorem initial13488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4832) ∨ (meaning t m 6076) := by
  exact rule13488 (meaning t m 3542) (meaning t m 3544) (meaning t m 3548) (meaning t m 4832) (meaning t m 5305)

theorem rule13490 (p3527 p4189 p5307 p5308 p5309 : Prop) : (p5307) ∨ (((¬ p5307) ∨ (¬ p4189) ∨ (¬ p3527) ∨ (¬ p5308) ∨ (¬ p5309))) := by
  classical
  tauto

theorem initial13490 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5307) ∨ (meaning t m 6077) := by
  exact rule13490 (meaning t m 3527) (meaning t m 4189) (meaning t m 5307) (meaning t m 5308) (meaning t m 5309)

theorem rule13491 (p3527 p4189 p5307 p5308 p5309 : Prop) : (p4189) ∨ (((¬ p5307) ∨ (¬ p4189) ∨ (¬ p3527) ∨ (¬ p5308) ∨ (¬ p5309))) := by
  classical
  tauto

theorem initial13491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4189) ∨ (meaning t m 6077) := by
  exact rule13491 (meaning t m 3527) (meaning t m 4189) (meaning t m 5307) (meaning t m 5308) (meaning t m 5309)

theorem rule13492 (p3527 p4189 p5307 p5308 p5309 : Prop) : (p3527) ∨ (((¬ p5307) ∨ (¬ p4189) ∨ (¬ p3527) ∨ (¬ p5308) ∨ (¬ p5309))) := by
  classical
  tauto

theorem initial13492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3527) ∨ (meaning t m 6077) := by
  exact rule13492 (meaning t m 3527) (meaning t m 4189) (meaning t m 5307) (meaning t m 5308) (meaning t m 5309)

theorem rule13498 (p6076 p6077 : Prop) : (¬ ((¬ p6076) ∨ (¬ p6077))) ∨ (¬ p6076) ∨ (¬ p6077) := by
  classical
  tauto

theorem initial13498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6075)) ∨ (¬ (meaning t m 6076)) ∨ (¬ (meaning t m 6077)) := by
  exact rule13498 (meaning t m 6076) (meaning t m 6077)

theorem rule13499 (p5303 p6075 : Prop) (h : (p5303 ↔ p6075)) : (¬ p5303) ∨ (p6075) := by
  classical
  tauto

theorem initial13499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5303)) ∨ (meaning t m 6075) := by
  have source := ElevenTheory.theory3428 t (m.theta 1 7) (m.theta 1 8) (m.theta 7 8)
  exact rule13499 (meaning t m 5303) (meaning t m 6075) source

theorem rule13501 (p2000 p2344 p2579 p2586 : Prop) (h : p2586 ∨ p2344 ∨ (¬ p2000) ∨ (¬ p2579)) : (¬ p2000) ∨ (p2344) ∨ (¬ p2579) ∨ (p2586) := by
  classical
  tauto

theorem initial13501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2586) := by
  have source := ElevenTheory.theory3429 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 6)
  exact rule13501 (meaning t m 2000) (meaning t m 2344) (meaning t m 2579) (meaning t m 2586) source

theorem rule13502 (p2002 p2114 p3367 p3422 p5222 : Prop) (h : p2114 ∨ (¬ p3422) ∨ (¬ p2002) ∨ (¬ p3367) ∨ p5222) : (¬ p2002) ∨ (p2114) ∨ (¬ p3367) ∨ (¬ p3422) ∨ (p5222) := by
  classical
  tauto

theorem initial13502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3422)) ∨ (meaning t m 5222) := by
  have source := ElevenTheory.theory3430 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6)
  exact rule13502 (meaning t m 2002) (meaning t m 2114) (meaning t m 3367) (meaning t m 3422) (meaning t m 5222) source

theorem rule13504 (p4242 p4353 p4436 p5312 p5313 : Prop) : (p5312) ∨ (((¬ p5313) ∨ (¬ p5312) ∨ (¬ p4242) ∨ (¬ p4353) ∨ (¬ p4436))) := by
  classical
  tauto

theorem initial13504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5312) ∨ (meaning t m 6079) := by
  exact rule13504 (meaning t m 4242) (meaning t m 4353) (meaning t m 4436) (meaning t m 5312) (meaning t m 5313)

theorem rule13505 (p4242 p4353 p4436 p5312 p5313 : Prop) : (p4242) ∨ (((¬ p5313) ∨ (¬ p5312) ∨ (¬ p4242) ∨ (¬ p4353) ∨ (¬ p4436))) := by
  classical
  tauto

theorem initial13505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4242) ∨ (meaning t m 6079) := by
  exact rule13505 (meaning t m 4242) (meaning t m 4353) (meaning t m 4436) (meaning t m 5312) (meaning t m 5313)

theorem rule13506 (p4242 p4353 p4436 p5312 p5313 : Prop) : (p4353) ∨ (((¬ p5313) ∨ (¬ p5312) ∨ (¬ p4242) ∨ (¬ p4353) ∨ (¬ p4436))) := by
  classical
  tauto

theorem initial13506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4353) ∨ (meaning t m 6079) := by
  exact rule13506 (meaning t m 4242) (meaning t m 4353) (meaning t m 4436) (meaning t m 5312) (meaning t m 5313)

theorem rule13507 (p4242 p4353 p4436 p5312 p5313 : Prop) : (p4436) ∨ (((¬ p5313) ∨ (¬ p5312) ∨ (¬ p4242) ∨ (¬ p4353) ∨ (¬ p4436))) := by
  classical
  tauto

theorem initial13507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4436) ∨ (meaning t m 6079) := by
  exact rule13507 (meaning t m 4242) (meaning t m 4353) (meaning t m 4436) (meaning t m 5312) (meaning t m 5313)

theorem rule13509 (p3537 p5315 p5316 p5317 p5318 : Prop) : (p5317) ∨ (((¬ p5317) ∨ (¬ p5318) ∨ (¬ p5315) ∨ (¬ p5316) ∨ (¬ p3537))) := by
  classical
  tauto

theorem initial13509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5317) ∨ (meaning t m 6080) := by
  exact rule13509 (meaning t m 3537) (meaning t m 5315) (meaning t m 5316) (meaning t m 5317) (meaning t m 5318)

theorem rule13511 (p3537 p5315 p5316 p5317 p5318 : Prop) : (p5315) ∨ (((¬ p5317) ∨ (¬ p5318) ∨ (¬ p5315) ∨ (¬ p5316) ∨ (¬ p3537))) := by
  classical
  tauto

theorem initial13511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5315) ∨ (meaning t m 6080) := by
  exact rule13511 (meaning t m 3537) (meaning t m 5315) (meaning t m 5316) (meaning t m 5317) (meaning t m 5318)

theorem rule13512 (p3537 p5315 p5316 p5317 p5318 : Prop) : (p5316) ∨ (((¬ p5317) ∨ (¬ p5318) ∨ (¬ p5315) ∨ (¬ p5316) ∨ (¬ p3537))) := by
  classical
  tauto

theorem initial13512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5316) ∨ (meaning t m 6080) := by
  exact rule13512 (meaning t m 3537) (meaning t m 5315) (meaning t m 5316) (meaning t m 5317) (meaning t m 5318)

theorem rule13513 (p3537 p5315 p5316 p5317 p5318 : Prop) : (p3537) ∨ (((¬ p5317) ∨ (¬ p5318) ∨ (¬ p5315) ∨ (¬ p5316) ∨ (¬ p3537))) := by
  classical
  tauto

theorem initial13513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3537) ∨ (meaning t m 6080) := by
  exact rule13513 (meaning t m 3537) (meaning t m 5315) (meaning t m 5316) (meaning t m 5317) (meaning t m 5318)

theorem rule13517 (p6079 p6080 : Prop) : (¬ ((¬ p6079) ∨ (¬ p6080))) ∨ (¬ p6079) ∨ (¬ p6080) := by
  classical
  tauto

theorem initial13517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6078)) ∨ (¬ (meaning t m 6079)) ∨ (¬ (meaning t m 6080)) := by
  exact rule13517 (meaning t m 6079) (meaning t m 6080)

theorem rule13518 (p5310 p6078 : Prop) (h : (p5310 ↔ p6078)) : (¬ p5310) ∨ (p6078) := by
  classical
  tauto

theorem initial13518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5310)) ∨ (meaning t m 6078) := by
  have source := ElevenTheory.theory3431 t (m.theta 1 2) (m.theta 1 8) (m.theta 2 8)
  exact rule13518 (meaning t m 5310) (meaning t m 6078) source

theorem rule13521 (p1991 p2027 p2462 p2952 p3136 p3572 p3947 : Prop) (h : p2027 ∨ (¬ p1991) ∨ (¬ p3136) ∨ (¬ p2952) ∨ p2462 ∨ (¬ p3572) ∨ (¬ p3947)) : (¬ p1991) ∨ (p2027) ∨ (p2462) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3572) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial13521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory3433 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 9)
  exact rule13521 (meaning t m 1991) (meaning t m 2027) (meaning t m 2462) (meaning t m 2952) (meaning t m 3136) (meaning t m 3572) (meaning t m 3947) source

theorem rule13522 (p1984 p2027 p2462 p3055 p3367 p3588 p3873 p4324 : Prop) (h : (¬ p3588) ∨ p2462 ∨ (¬ p4324) ∨ (¬ p3367) ∨ (¬ p3055) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3873)) : (¬ p1984) ∨ (p2027) ∨ (p2462) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial13522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory3434 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 7 9)
  exact rule13522 (meaning t m 1984) (meaning t m 2027) (meaning t m 2462) (meaning t m 3055) (meaning t m 3367) (meaning t m 3588) (meaning t m 3873) (meaning t m 4324) source

theorem rule13523 (p1983 p2027 p2148 p2156 p2396 p2870 p3758 p4140 : Prop) (h : (¬ p4140) ∨ (¬ p1983) ∨ (¬ p2396) ∨ (¬ p2870) ∨ (¬ p2156) ∨ (¬ p3758) ∨ p2148 ∨ p2027) : (¬ p1983) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2396) ∨ (¬ p2870) ∨ (¬ p3758) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial13523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory3435 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule13523 (meaning t m 1983) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2396) (meaning t m 2870) (meaning t m 3758) (meaning t m 4140) source

theorem rule13524 (p1994 p2114 p3367 p4753 : Prop) (h : p2114 ∨ (¬ p1994) ∨ p4753 ∨ (¬ p3367)) : (¬ p1994) ∨ (p2114) ∨ (¬ p3367) ∨ (p4753) := by
  classical
  tauto

theorem initial13524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3367)) ∨ (meaning t m 4753) := by
  have source := ElevenTheory.theory3436 t (m.theta 1 2) (m.theta 2 4) (m.theta 3 4)
  exact rule13524 (meaning t m 1994) (meaning t m 2114) (meaning t m 3367) (meaning t m 4753) source

theorem rule13525 (p2707 p3366 p3577 p3820 : Prop) (h : (¬ p2707) ∨ (¬ p3366) ∨ (¬ p3820) ∨ (¬ p3577)) : (¬ p2707) ∨ (¬ p3366) ∨ (¬ p3577) ∨ (¬ p3820) := by
  classical
  tauto

theorem initial13525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 3820)) := by
  have source := ElevenTheory.theory3437 (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 2 7)
  exact rule13525 (meaning t m 2707) (meaning t m 3366) (meaning t m 3577) (meaning t m 3820) source

theorem rule13528 (p2000 p2027 p2589 p2766 p3989 p4110 p4347 : Prop) (h : (¬ p2589) ∨ (¬ p2000) ∨ (¬ p4110) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p4347) ∨ p2766) : (¬ p2000) ∨ (p2027) ∨ (¬ p2589) ∨ (p2766) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial13528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3440 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule13528 (meaning t m 2000) (meaning t m 2027) (meaning t m 2589) (meaning t m 2766) (meaning t m 3989) (meaning t m 4110) (meaning t m 4347) source

theorem rule13529 (p1983 p2027 p2241 p2295 p2396 p2641 p2699 : Prop) (h : (¬ p2396) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p1983) ∨ p2699 ∨ p2027 ∨ (¬ p2641)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2396) ∨ (¬ p2641) ∨ (p2699) := by
  classical
  tauto

theorem initial13529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2699) := by
  have source := ElevenTheory.theory3441 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9)
  exact rule13529 (meaning t m 1983) (meaning t m 2027) (meaning t m 2241) (meaning t m 2295) (meaning t m 2396) (meaning t m 2641) (meaning t m 2699) source

theorem rule13531 (p1994 p2027 p2233 p2440 p2573 p2850 p3584 : Prop) (h : p2027 ∨ (¬ p2573) ∨ (¬ p2440) ∨ p2233 ∨ (¬ p1994) ∨ (¬ p2850) ∨ (¬ p3584)) : (¬ p1994) ∨ (p2027) ∨ (p2233) ∨ (¬ p2440) ∨ (¬ p2573) ∨ (¬ p2850) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial13531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory3443 t (m.theta 0 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule13531 (meaning t m 1994) (meaning t m 2027) (meaning t m 2233) (meaning t m 2440) (meaning t m 2573) (meaning t m 2850) (meaning t m 3584) source

theorem rule13532 (p1995 p2027 p2230 p2274 p2765 p3238 p3540 p3921 : Prop) (h : p2027 ∨ p2765 ∨ (¬ p1995) ∨ (¬ p2274) ∨ (¬ p3238) ∨ (¬ p3921) ∨ (¬ p3540) ∨ (¬ p2230)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (p2765) ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial13532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory3444 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7)
  exact rule13532 (meaning t m 1995) (meaning t m 2027) (meaning t m 2230) (meaning t m 2274) (meaning t m 2765) (meaning t m 3238) (meaning t m 3540) (meaning t m 3921) source

theorem rule13534 (p1992 p2027 p2230 p2842 p3201 p3238 p3540 p4257 : Prop) (h : p2027 ∨ (¬ p3201) ∨ p2842 ∨ (¬ p1992) ∨ (¬ p3238) ∨ (¬ p4257) ∨ (¬ p2230) ∨ (¬ p3540)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2230) ∨ (p2842) ∨ (¬ p3201) ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p4257) := by
  classical
  tauto

theorem initial13534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4257)) := by
  have source := ElevenTheory.theory3446 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7)
  exact rule13534 (meaning t m 1992) (meaning t m 2027) (meaning t m 2230) (meaning t m 2842) (meaning t m 3201) (meaning t m 3238) (meaning t m 3540) (meaning t m 4257) source

theorem rule13536 (p1995 p2027 p2169 p2590 p3125 p3238 p3989 p4137 : Prop) (h : (¬ p3238) ∨ p2169 ∨ (¬ p2590) ∨ (¬ p1995) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p3989)) : (¬ p1995) ∨ (p2027) ∨ (p2169) ∨ (¬ p2590) ∨ (¬ p3125) ∨ (¬ p3238) ∨ (¬ p3989) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial13536 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory3448 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule13536 (meaning t m 1995) (meaning t m 2027) (meaning t m 2169) (meaning t m 2590) (meaning t m 3125) (meaning t m 3238) (meaning t m 3989) (meaning t m 4137) source

theorem rule13537 (p3556 p3571 p3645 p4431 : Prop) (h : (¬ p4431) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3571)) : (¬ p3556) ∨ (¬ p3571) ∨ (¬ p3645) ∨ (¬ p4431) := by
  classical
  tauto

theorem initial13537 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4431)) := by
  have source := ElevenTheory.theory3449 (m.theta 0 5) (m.theta 1 5) (m.theta 1 7) (m.theta 5 7)
  exact rule13537 (meaning t m 3556) (meaning t m 3571) (meaning t m 3645) (meaning t m 4431) source

theorem rule13540 (p1997 p2027 p2323 p2946 p3027 p3662 p4235 p4333 : Prop) (h : (¬ p2946) ∨ (¬ p3662) ∨ (¬ p1997) ∨ p2323 ∨ p2027 ∨ (¬ p3027) ∨ (¬ p4235) ∨ (¬ p4333)) : (¬ p1997) ∨ (p2027) ∨ (p2323) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3662) ∨ (¬ p4235) ∨ (¬ p4333) := by
  classical
  tauto

theorem initial13540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4333)) := by
  have source := ElevenTheory.theory3452 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7)
  exact rule13540 (meaning t m 1997) (meaning t m 2027) (meaning t m 2323) (meaning t m 2946) (meaning t m 3027) (meaning t m 3662) (meaning t m 4235) (meaning t m 4333) source

theorem rule13541 (p2663 p2958 p4399 : Prop) (h : (¬ p4399) ∨ (¬ p2663) ∨ p2958) : (¬ p2663) ∨ (p2958) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial13541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2663)) ∨ (meaning t m 2958) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory3453 (m.theta 0 3) (m.theta 0 4) (m.theta 0 5)
  exact rule13541 (meaning t m 2663) (meaning t m 2958) (meaning t m 4399) source

theorem rule13542 (p1975 p2027 p2233 p2274 p2573 p3564 p3744 : Prop) (h : (¬ p1975) ∨ p2233 ∨ (¬ p3744) ∨ (¬ p3564) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2573)) : (¬ p1975) ∨ (p2027) ∨ (p2233) ∨ (¬ p2274) ∨ (¬ p2573) ∨ (¬ p3564) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial13542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory3454 t (m.theta 0 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule13542 (meaning t m 1975) (meaning t m 2027) (meaning t m 2233) (meaning t m 2274) (meaning t m 2573) (meaning t m 3564) (meaning t m 3744) source

theorem rule13543 (p3746 p4022 p4137 p5321 p5322 : Prop) : (p4022) ∨ (((¬ p4022) ∨ (¬ p4137) ∨ (¬ p3746) ∨ (¬ p5321) ∨ (¬ p5322))) := by
  classical
  tauto

theorem initial13543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4022) ∨ (meaning t m 6082) := by
  exact rule13543 (meaning t m 3746) (meaning t m 4022) (meaning t m 4137) (meaning t m 5321) (meaning t m 5322)

theorem rule13544 (p3746 p4022 p4137 p5321 p5322 : Prop) : (p4137) ∨ (((¬ p4022) ∨ (¬ p4137) ∨ (¬ p3746) ∨ (¬ p5321) ∨ (¬ p5322))) := by
  classical
  tauto

theorem initial13544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4137) ∨ (meaning t m 6082) := by
  exact rule13544 (meaning t m 3746) (meaning t m 4022) (meaning t m 4137) (meaning t m 5321) (meaning t m 5322)

theorem rule13545 (p3746 p4022 p4137 p5321 p5322 : Prop) : (p3746) ∨ (((¬ p4022) ∨ (¬ p4137) ∨ (¬ p3746) ∨ (¬ p5321) ∨ (¬ p5322))) := by
  classical
  tauto

theorem initial13545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3746) ∨ (meaning t m 6082) := by
  exact rule13545 (meaning t m 3746) (meaning t m 4022) (meaning t m 4137) (meaning t m 5321) (meaning t m 5322)

theorem rule13546 (p3746 p4022 p4137 p5321 p5322 : Prop) : (p5321) ∨ (((¬ p4022) ∨ (¬ p4137) ∨ (¬ p3746) ∨ (¬ p5321) ∨ (¬ p5322))) := by
  classical
  tauto

theorem initial13546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5321) ∨ (meaning t m 6082) := by
  exact rule13546 (meaning t m 3746) (meaning t m 4022) (meaning t m 4137) (meaning t m 5321) (meaning t m 5322)

theorem rule13547 (p3746 p4022 p4137 p5321 p5322 : Prop) : (p5322) ∨ (((¬ p4022) ∨ (¬ p4137) ∨ (¬ p3746) ∨ (¬ p5321) ∨ (¬ p5322))) := by
  classical
  tauto

theorem initial13547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5322) ∨ (meaning t m 6082) := by
  exact rule13547 (meaning t m 3746) (meaning t m 4022) (meaning t m 4137) (meaning t m 5321) (meaning t m 5322)

theorem rule13549 (p3564 p4331 p4422 p5324 p5325 : Prop) : (p4331) ∨ (((¬ p4331) ∨ (¬ p4422) ∨ (¬ p3564) ∨ (¬ p5324) ∨ (¬ p5325))) := by
  classical
  tauto

theorem initial13549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4331) ∨ (meaning t m 6083) := by
  exact rule13549 (meaning t m 3564) (meaning t m 4331) (meaning t m 4422) (meaning t m 5324) (meaning t m 5325)

theorem rule13550 (p3564 p4331 p4422 p5324 p5325 : Prop) : (p4422) ∨ (((¬ p4331) ∨ (¬ p4422) ∨ (¬ p3564) ∨ (¬ p5324) ∨ (¬ p5325))) := by
  classical
  tauto

theorem initial13550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4422) ∨ (meaning t m 6083) := by
  exact rule13550 (meaning t m 3564) (meaning t m 4331) (meaning t m 4422) (meaning t m 5324) (meaning t m 5325)

theorem rule13551 (p3564 p4331 p4422 p5324 p5325 : Prop) : (p3564) ∨ (((¬ p4331) ∨ (¬ p4422) ∨ (¬ p3564) ∨ (¬ p5324) ∨ (¬ p5325))) := by
  classical
  tauto

theorem initial13551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3564) ∨ (meaning t m 6083) := by
  exact rule13551 (meaning t m 3564) (meaning t m 4331) (meaning t m 4422) (meaning t m 5324) (meaning t m 5325)

theorem rule13552 (p3564 p4331 p4422 p5324 p5325 : Prop) : (p5324) ∨ (((¬ p4331) ∨ (¬ p4422) ∨ (¬ p3564) ∨ (¬ p5324) ∨ (¬ p5325))) := by
  classical
  tauto

theorem initial13552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5324) ∨ (meaning t m 6083) := by
  exact rule13552 (meaning t m 3564) (meaning t m 4331) (meaning t m 4422) (meaning t m 5324) (meaning t m 5325)

theorem rule13553 (p3564 p4331 p4422 p5324 p5325 : Prop) : (p5325) ∨ (((¬ p4331) ∨ (¬ p4422) ∨ (¬ p3564) ∨ (¬ p5324) ∨ (¬ p5325))) := by
  classical
  tauto

theorem initial13553 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5325) ∨ (meaning t m 6083) := by
  exact rule13553 (meaning t m 3564) (meaning t m 4331) (meaning t m 4422) (meaning t m 5324) (meaning t m 5325)

theorem rule13557 (p6082 p6083 : Prop) : (¬ ((¬ p6082) ∨ (¬ p6083))) ∨ (¬ p6082) ∨ (¬ p6083) := by
  classical
  tauto

theorem initial13557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6081)) ∨ (¬ (meaning t m 6082)) ∨ (¬ (meaning t m 6083)) := by
  exact rule13557 (meaning t m 6082) (meaning t m 6083)

theorem rule13558 (p5319 p6081 : Prop) (h : (p5319 ↔ p6081)) : (¬ p5319) ∨ (p6081) := by
  classical
  tauto

theorem initial13558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5319)) ∨ (meaning t m 6081) := by
  have source := ElevenTheory.theory3455 t (m.theta 4 6) (m.theta 4 9) (m.theta 6 9)
  exact rule13558 (meaning t m 5319) (meaning t m 6081) source

theorem rule13561 (p1990 p2027 p2122 p2608 p2699 p2829 p3097 : Prop) (h : (¬ p2829) ∨ (¬ p1990) ∨ (¬ p2122) ∨ (¬ p3097) ∨ p2699 ∨ p2027 ∨ (¬ p2608)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2829) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial13561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory3457 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule13561 (meaning t m 1990) (meaning t m 2027) (meaning t m 2122) (meaning t m 2608) (meaning t m 2699) (meaning t m 2829) (meaning t m 3097) source

theorem rule13562 (p2005 p2027 p2295 p2331 p2545 p2588 p2657 : Prop) (h : p2545 ∨ (¬ p2657) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p2005) ∨ (¬ p2331) ∨ (¬ p2295)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (p2545) ∨ (¬ p2588) ∨ (¬ p2657) := by
  classical
  tauto

theorem initial13562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2657)) := by
  have source := ElevenTheory.theory3458 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule13562 (meaning t m 2005) (meaning t m 2027) (meaning t m 2295) (meaning t m 2331) (meaning t m 2545) (meaning t m 2588) (meaning t m 2657) source

theorem rule13563 (p1982 p2027 p2373 p2406 p2699 p3146 p3379 : Prop) (h : p2027 ∨ (¬ p3146) ∨ (¬ p1982) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p3379) ∨ p2699) : (¬ p1982) ∨ (p2027) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (p2699) ∨ (¬ p3146) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial13563 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory3459 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule13563 (meaning t m 1982) (meaning t m 2027) (meaning t m 2373) (meaning t m 2406) (meaning t m 2699) (meaning t m 3146) (meaning t m 3379) source

theorem rule13564 (p1982 p2027 p2230 p2233 p2518 p2531 p3146 p3238 : Prop) (h : (¬ p2518) ∨ (¬ p2531) ∨ (¬ p2230) ∨ (¬ p3146) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p1982) ∨ p2233) : (¬ p1982) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2518) ∨ (¬ p2531) ∨ (¬ p3146) ∨ (¬ p3238) := by
  classical
  tauto

theorem initial13564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3238)) := by
  have source := ElevenTheory.theory3460 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule13564 (meaning t m 1982) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2518) (meaning t m 2531) (meaning t m 3146) (meaning t m 3238) source

theorem rule13566 (p1981 p2187 p3578 p4507 : Prop) (h : (¬ p1981) ∨ p3578 ∨ (¬ p2187) ∨ p4507) : (¬ p1981) ∨ (¬ p2187) ∨ (p3578) ∨ (p4507) := by
  classical
  tauto

theorem initial13566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 3578) ∨ (meaning t m 4507) := by
  have source := ElevenTheory.theory3462 t (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule13566 (meaning t m 1981) (meaning t m 2187) (meaning t m 3578) (meaning t m 4507) source

theorem rule13567 (p1978 p2027 p2177 p2459 p2997 p3692 p4120 : Prop) (h : (¬ p1978) ∨ (¬ p4120) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p2459) ∨ p2997 ∨ (¬ p3692)) : (¬ p1978) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2459) ∨ (p2997) ∨ (¬ p3692) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial13567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory3463 t (m.theta 0 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule13567 (meaning t m 1978) (meaning t m 2027) (meaning t m 2177) (meaning t m 2459) (meaning t m 2997) (meaning t m 3692) (meaning t m 4120) source

theorem rule13568 (p1992 p2027 p2743 p2766 p2963 p3324 p3361 p4347 : Prop) (h : (¬ p1992) ∨ (¬ p4347) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p2963) ∨ p2766 ∨ (¬ p3361) ∨ (¬ p2743)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2743) ∨ (p2766) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3361) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial13568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3464 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule13568 (meaning t m 1992) (meaning t m 2027) (meaning t m 2743) (meaning t m 2766) (meaning t m 2963) (meaning t m 3324) (meaning t m 3361) (meaning t m 4347) source

theorem rule13569 (p1992 p2027 p2462 p2743 p2952 p3361 p3690 p4320 : Prop) (h : (¬ p3361) ∨ (¬ p1992) ∨ (¬ p2743) ∨ (¬ p3690) ∨ p2027 ∨ p2462 ∨ (¬ p2952) ∨ (¬ p4320)) : (¬ p1992) ∨ (p2027) ∨ (p2462) ∨ (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3690) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial13569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory3465 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9)
  exact rule13569 (meaning t m 1992) (meaning t m 2027) (meaning t m 2462) (meaning t m 2743) (meaning t m 2952) (meaning t m 3361) (meaning t m 3690) (meaning t m 4320) source

theorem rule13571 (p2006 p2202 p3684 p4884 : Prop) (h : (¬ p3684) ∨ (¬ p2006) ∨ p2202 ∨ p4884) : (¬ p2006) ∨ (p2202) ∨ (¬ p3684) ∨ (p4884) := by
  classical
  tauto

theorem initial13571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 3684)) ∨ (meaning t m 4884) := by
  have source := ElevenTheory.theory3467 t (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule13571 (meaning t m 2006) (meaning t m 2202) (meaning t m 3684) (meaning t m 4884) source

theorem rule13573 (p1979 p2027 p2427 p2850 p3008 p3584 p4320 : Prop) (h : p2027 ∨ (¬ p1979) ∨ (¬ p2850) ∨ (¬ p3584) ∨ (¬ p4320) ∨ (¬ p2427) ∨ p3008) : (¬ p1979) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2850) ∨ (p3008) ∨ (¬ p3584) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial13573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2850)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory3469 t (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule13573 (meaning t m 1979) (meaning t m 2027) (meaning t m 2427) (meaning t m 2850) (meaning t m 3008) (meaning t m 3584) (meaning t m 4320) source

theorem rule13576 (p1995 p2027 p2509 p2608 p2699 p3367 p3641 : Prop) (h : p2699 ∨ (¬ p3367) ∨ (¬ p3641) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p1995) ∨ (¬ p2509)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2509) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p3367) ∨ (¬ p3641) := by
  classical
  tauto

theorem initial13576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3641)) := by
  have source := ElevenTheory.theory3472 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 8)
  exact rule13576 (meaning t m 1995) (meaning t m 2027) (meaning t m 2509) (meaning t m 2608) (meaning t m 2699) (meaning t m 3367) (meaning t m 3641) source

theorem rule13579 (p2589 p3347 p3948 p4210 : Prop) (h : (¬ p4210) ∨ (¬ p2589) ∨ (¬ p3948) ∨ (¬ p3347)) : (¬ p2589) ∨ (¬ p3347) ∨ (¬ p3948) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial13579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory3475 (m.theta 0 4) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5)
  exact rule13579 (meaning t m 2589) (meaning t m 3347) (meaning t m 3948) (meaning t m 4210) source

theorem rule13580 (p2027 p2630 p2657 p2737 p4236 p4734 : Prop) (h : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p4236) ∨ p2027 ∨ (¬ p4734) ∨ (¬ p2737)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2737) ∨ (¬ p4236) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial13580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory3476 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4)
  exact rule13580 (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 2737) (meaning t m 4236) (meaning t m 4734) source

theorem rule13581 (p1992 p2027 p2138 p2598 p2765 p3585 p3758 : Prop) (h : (¬ p1992) ∨ (¬ p3585) ∨ p2027 ∨ p2765 ∨ (¬ p2138) ∨ (¬ p3758) ∨ (¬ p2598)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2598) ∨ (p2765) ∨ (¬ p3585) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial13581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory3477 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 6)
  exact rule13581 (meaning t m 1992) (meaning t m 2027) (meaning t m 2138) (meaning t m 2598) (meaning t m 2765) (meaning t m 3585) (meaning t m 3758) source

theorem rule13582 (p1985 p2027 p2427 p2598 p2699 p2860 p3582 p3589 p4110 : Prop) (h : (¬ p3589) ∨ p2027 ∨ (¬ p2598) ∨ p2699 ∨ (¬ p2860) ∨ (¬ p4110) ∨ (¬ p2427) ∨ (¬ p1985) ∨ (¬ p3582)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2598) ∨ (p2699) ∨ (¬ p2860) ∨ (¬ p3582) ∨ (¬ p3589) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial13582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory3478 t (m.theta 0 1) (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule13582 (meaning t m 1985) (meaning t m 2027) (meaning t m 2427) (meaning t m 2598) (meaning t m 2699) (meaning t m 2860) (meaning t m 3582) (meaning t m 3589) (meaning t m 4110) source

theorem rule13583 (p1975 p2027 p2274 p2406 p2563 p2699 p3379 : Prop) (h : p2699 ∨ (¬ p3379) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p1975) ∨ (¬ p2563)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2406) ∨ (¬ p2563) ∨ (p2699) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial13583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory3479 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule13583 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2406) (meaning t m 2563) (meaning t m 2699) (meaning t m 3379) source

theorem rule13584 (p1980 p2027 p2493 p2553 p2699 p3379 p3568 : Prop) (h : p2027 ∨ (¬ p2493) ∨ p2699 ∨ (¬ p3379) ∨ (¬ p3568) ∨ (¬ p2553) ∨ (¬ p1980)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (p2699) ∨ (¬ p3379) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial13584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory3480 t (m.theta 0 1) (m.theta 1 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule13584 (meaning t m 1980) (meaning t m 2027) (meaning t m 2493) (meaning t m 2553) (meaning t m 2699) (meaning t m 3379) (meaning t m 3568) source

theorem rule13585 (p1985 p2027 p2387 p2427 p2766 p4110 p4347 p4356 : Prop) (h : (¬ p4347) ∨ (¬ p1985) ∨ p2766 ∨ p2027 ∨ (¬ p4356) ∨ (¬ p2387) ∨ (¬ p4110) ∨ (¬ p2427)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2427) ∨ (p2766) ∨ (¬ p4110) ∨ (¬ p4347) ∨ (¬ p4356) := by
  classical
  tauto

theorem initial13585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4356)) := by
  have source := ElevenTheory.theory3481 t (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8) (m.theta 8 9)
  exact rule13585 (meaning t m 1985) (meaning t m 2027) (meaning t m 2387) (meaning t m 2427) (meaning t m 2766) (meaning t m 4110) (meaning t m 4347) (meaning t m 4356) source

theorem rule13586 (p2143 p2860 p3646 : Prop) (h : (¬ p3646) ∨ (¬ p2860) ∨ (¬ p2143)) : (¬ p2143) ∨ (¬ p2860) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial13586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory3482 (m.theta 0 5) (m.theta 2 5) (m.theta 5 6)
  exact rule13586 (meaning t m 2143) (meaning t m 2860) (meaning t m 3646) source

theorem rule13587 (p1987 p2027 p2737 p2766 p2785 p3324 p3567 p3688 p4347 : Prop) (h : (¬ p4347) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p2785) ∨ (¬ p3567) ∨ p2766 ∨ (¬ p1987) ∨ (¬ p2737) ∨ (¬ p3688)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (p2766) ∨ (¬ p2785) ∨ (¬ p3324) ∨ (¬ p3567) ∨ (¬ p3688) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial13587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3483 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule13587 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 2766) (meaning t m 2785) (meaning t m 3324) (meaning t m 3567) (meaning t m 3688) (meaning t m 4347) source

theorem rule13588 (p1987 p2027 p2598 p2737 p2780 p3585 p3586 : Prop) (h : (¬ p1987) ∨ (¬ p2737) ∨ (¬ p3585) ∨ (¬ p2598) ∨ (¬ p2780) ∨ p2027 ∨ p3586) : (¬ p1987) ∨ (p2027) ∨ (¬ p2598) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3585) ∨ (p3586) := by
  classical
  tauto

theorem initial13588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3585)) ∨ (meaning t m 3586) := by
  have source := ElevenTheory.theory3484 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6)
  exact rule13588 (meaning t m 1987) (meaning t m 2027) (meaning t m 2598) (meaning t m 2737) (meaning t m 2780) (meaning t m 3585) (meaning t m 3586) source

theorem rule13590 (p1975 p2027 p2132 p2274 p2699 p2829 p3583 p3589 p4185 : Prop) (h : (¬ p2829) ∨ (¬ p3583) ∨ p2699 ∨ (¬ p4185) ∨ (¬ p1975) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p3589)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2274) ∨ (p2699) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4185) := by
  classical
  tauto

theorem initial13590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4185)) := by
  have source := ElevenTheory.theory3486 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule13590 (meaning t m 1975) (meaning t m 2027) (meaning t m 2132) (meaning t m 2274) (meaning t m 2699) (meaning t m 2829) (meaning t m 3583) (meaning t m 3589) (meaning t m 4185) source

theorem rule13591 (p1992 p2409 p3585 p5217 : Prop) (h : (¬ p1992) ∨ p2409 ∨ (¬ p3585) ∨ p5217) : (¬ p1992) ∨ (p2409) ∨ (¬ p3585) ∨ (p5217) := by
  classical
  tauto

theorem initial13591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 3585)) ∨ (meaning t m 5217) := by
  have source := ElevenTheory.theory3487 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 4)
  exact rule13591 (meaning t m 1992) (meaning t m 2409) (meaning t m 3585) (meaning t m 5217) source

theorem rule13592 (p1987 p2027 p2138 p2598 p2737 p3474 p3585 : Prop) (h : (¬ p2598) ∨ (¬ p2737) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p1987) ∨ (¬ p2138) ∨ p3474) : (¬ p1987) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2598) ∨ (¬ p2737) ∨ (p3474) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial13592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory3488 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5)
  exact rule13592 (meaning t m 1987) (meaning t m 2027) (meaning t m 2138) (meaning t m 2598) (meaning t m 2737) (meaning t m 3474) (meaning t m 3585) source

theorem rule13597 (p1975 p2027 p2553 p2598 p2611 p2829 p3585 p4390 : Prop) (h : p2611 ∨ (¬ p2598) ∨ (¬ p4390) ∨ (¬ p3585) ∨ (¬ p2829) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p4390) := by
  classical
  tauto

theorem initial13597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4390)) := by
  have source := ElevenTheory.theory3493 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule13597 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2598) (meaning t m 2611) (meaning t m 2829) (meaning t m 3585) (meaning t m 4390) source

theorem rule13598 (p1979 p2027 p2766 p2946 p2963 p3324 p4347 : Prop) (h : (¬ p1979) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p3324) ∨ (¬ p2963) ∨ p2766 ∨ (¬ p4347)) : (¬ p1979) ∨ (p2027) ∨ (p2766) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial13598 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3494 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule13598 (meaning t m 1979) (meaning t m 2027) (meaning t m 2766) (meaning t m 2946) (meaning t m 2963) (meaning t m 3324) (meaning t m 4347) source

theorem rule13600 (p2003 p2027 p2295 p2313 p2766 p3324 p4347 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p4347) ∨ (¬ p2313) ∨ (¬ p2295) ∨ (¬ p3324) ∨ (¬ p2003)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (p2766) ∨ (¬ p3324) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial13600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3496 t (m.theta 0 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule13600 (meaning t m 2003) (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2766) (meaning t m 3324) (meaning t m 4347) source

theorem rule13601 (p1997 p2027 p2299 p2766 p3097 p4110 p4348 : Prop) (h : p2766 ∨ (¬ p2299) ∨ (¬ p1997) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p4348) ∨ (¬ p4110)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2299) ∨ (p2766) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial13601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory3497 t (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule13601 (meaning t m 1997) (meaning t m 2027) (meaning t m 2299) (meaning t m 2766) (meaning t m 3097) (meaning t m 4110) (meaning t m 4348) source

theorem rule13602 (p1991 p2027 p2459 p2633 p2963 p3324 p4347 : Prop) (h : (¬ p1991) ∨ (¬ p4347) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p2963) ∨ p2633 ∨ (¬ p2459)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial13602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3498 t (m.theta 0 3) (m.theta 3 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule13602 (meaning t m 1991) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 2963) (meaning t m 3324) (meaning t m 4347) source

theorem rule13606 (p1992 p2027 p2589 p2633 p3363 p3570 p3585 p4235 : Prop) (h : (¬ p3363) ∨ (¬ p1992) ∨ p2633 ∨ (¬ p3570) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2589)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2589) ∨ (p2633) ∨ (¬ p3363) ∨ (¬ p3570) ∨ (¬ p3585) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial13606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory3502 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule13606 (meaning t m 1992) (meaning t m 2027) (meaning t m 2589) (meaning t m 2633) (meaning t m 3363) (meaning t m 3570) (meaning t m 3585) (meaning t m 4235) source

theorem rule13607 (p2881 p3960 p3961 p4283 : Prop) (h : (¬ p4283) ∨ (¬ p3960) ∨ (¬ p2881) ∨ (¬ p3961)) : (¬ p2881) ∨ (¬ p3960) ∨ (¬ p3961) ∨ (¬ p4283) := by
  classical
  tauto

theorem initial13607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4283)) := by
  have source := ElevenTheory.theory3503 (m.theta 0 7) (m.theta 0 8) (m.theta 5 7) (m.theta 7 8)
  exact rule13607 (meaning t m 2881) (meaning t m 3960) (meaning t m 3961) (meaning t m 4283) source

theorem rule13608 (p1985 p2027 p2427 p2598 p2699 p2839 p3585 p3589 p3695 : Prop) (h : p2699 ∨ p2027 ∨ (¬ p1985) ∨ (¬ p2598) ∨ (¬ p2427) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3695) ∨ (¬ p2839)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2598) ∨ (p2699) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3695) := by
  classical
  tauto

theorem initial13608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3695)) := by
  have source := ElevenTheory.theory3504 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule13608 (meaning t m 1985) (meaning t m 2027) (meaning t m 2427) (meaning t m 2598) (meaning t m 2699) (meaning t m 2839) (meaning t m 3585) (meaning t m 3589) (meaning t m 3695) source

theorem rule13610 (p1994 p2027 p2651 p2766 p2963 p3324 p4347 : Prop) (h : p2027 ∨ (¬ p4347) ∨ (¬ p2651) ∨ (¬ p2963) ∨ p2766 ∨ (¬ p3324) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2651) ∨ (p2766) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial13610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3506 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule13610 (meaning t m 1994) (meaning t m 2027) (meaning t m 2651) (meaning t m 2766) (meaning t m 2963) (meaning t m 3324) (meaning t m 4347) source

theorem rule13614 (p1997 p2027 p2156 p2462 p3556 p3690 p4110 : Prop) (h : p2027 ∨ (¬ p2156) ∨ (¬ p1997) ∨ (¬ p3556) ∨ (¬ p4110) ∨ p2462 ∨ (¬ p3690)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2156) ∨ (p2462) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial13614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory3510 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule13614 (meaning t m 1997) (meaning t m 2027) (meaning t m 2156) (meaning t m 2462) (meaning t m 3556) (meaning t m 3690) (meaning t m 4110) source

theorem rule13616 (p4029 p4379 p5328 p5329 p5330 : Prop) : (p4379) ∨ (((¬ p5330) ∨ (¬ p4379) ∨ (¬ p5329) ∨ (¬ p4029) ∨ (¬ p5328))) := by
  classical
  tauto

theorem initial13616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4379) ∨ (meaning t m 6085) := by
  exact rule13616 (meaning t m 4029) (meaning t m 4379) (meaning t m 5328) (meaning t m 5329) (meaning t m 5330)

theorem rule13618 (p4029 p4379 p5328 p5329 p5330 : Prop) : (p4029) ∨ (((¬ p5330) ∨ (¬ p4379) ∨ (¬ p5329) ∨ (¬ p4029) ∨ (¬ p5328))) := by
  classical
  tauto

theorem initial13618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4029) ∨ (meaning t m 6085) := by
  exact rule13618 (meaning t m 4029) (meaning t m 4379) (meaning t m 5328) (meaning t m 5329) (meaning t m 5330)

theorem rule13623 (p3599 p5332 p5333 p5334 p5335 : Prop) : (p5332) ∨ (((¬ p5335) ∨ (¬ p5334) ∨ (¬ p5332) ∨ (¬ p3599) ∨ (¬ p5333))) := by
  classical
  tauto

theorem initial13623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5332) ∨ (meaning t m 6086) := by
  exact rule13623 (meaning t m 3599) (meaning t m 5332) (meaning t m 5333) (meaning t m 5334) (meaning t m 5335)

theorem rule13624 (p3599 p5332 p5333 p5334 p5335 : Prop) : (p3599) ∨ (((¬ p5335) ∨ (¬ p5334) ∨ (¬ p5332) ∨ (¬ p3599) ∨ (¬ p5333))) := by
  classical
  tauto

theorem initial13624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3599) ∨ (meaning t m 6086) := by
  exact rule13624 (meaning t m 3599) (meaning t m 5332) (meaning t m 5333) (meaning t m 5334) (meaning t m 5335)

theorem rule13625 (p3599 p5332 p5333 p5334 p5335 : Prop) : (p5333) ∨ (((¬ p5335) ∨ (¬ p5334) ∨ (¬ p5332) ∨ (¬ p3599) ∨ (¬ p5333))) := by
  classical
  tauto

theorem initial13625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5333) ∨ (meaning t m 6086) := by
  exact rule13625 (meaning t m 3599) (meaning t m 5332) (meaning t m 5333) (meaning t m 5334) (meaning t m 5335)

theorem rule13629 (p6085 p6086 : Prop) : (¬ ((¬ p6085) ∨ (¬ p6086))) ∨ (¬ p6085) ∨ (¬ p6086) := by
  classical
  tauto

theorem initial13629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6084)) ∨ (¬ (meaning t m 6085)) ∨ (¬ (meaning t m 6086)) := by
  exact rule13629 (meaning t m 6085) (meaning t m 6086)

theorem rule13630 (p5326 p6084 : Prop) (h : (p5326 ↔ p6084)) : (¬ p5326) ∨ (p6084) := by
  classical
  tauto

theorem initial13630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5326)) ∨ (meaning t m 6084) := by
  have source := ElevenTheory.theory3511 t (m.theta 1 2) (m.theta 1 9) (m.theta 2 9)
  exact rule13630 (meaning t m 5326) (meaning t m 6084) source

theorem rule13632 (p4340 p5338 p5339 p5340 p5341 : Prop) : (p5339) ∨ (((¬ p5339) ∨ (¬ p4340) ∨ (¬ p5338) ∨ (¬ p5340) ∨ (¬ p5341))) := by
  classical
  tauto

theorem initial13632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5339) ∨ (meaning t m 6088) := by
  exact rule13632 (meaning t m 4340) (meaning t m 5338) (meaning t m 5339) (meaning t m 5340) (meaning t m 5341)

theorem rule13633 (p4340 p5338 p5339 p5340 p5341 : Prop) : (p4340) ∨ (((¬ p5339) ∨ (¬ p4340) ∨ (¬ p5338) ∨ (¬ p5340) ∨ (¬ p5341))) := by
  classical
  tauto

theorem initial13633 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4340) ∨ (meaning t m 6088) := by
  exact rule13633 (meaning t m 4340) (meaning t m 5338) (meaning t m 5339) (meaning t m 5340) (meaning t m 5341)

theorem rule13634 (p4340 p5338 p5339 p5340 p5341 : Prop) : (p5338) ∨ (((¬ p5339) ∨ (¬ p4340) ∨ (¬ p5338) ∨ (¬ p5340) ∨ (¬ p5341))) := by
  classical
  tauto

theorem initial13634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5338) ∨ (meaning t m 6088) := by
  exact rule13634 (meaning t m 4340) (meaning t m 5338) (meaning t m 5339) (meaning t m 5340) (meaning t m 5341)

theorem rule13638 (p3609 p5343 p5344 p5345 p5346 : Prop) : (p5343) ∨ (((¬ p5343) ∨ (¬ p5344) ∨ (¬ p3609) ∨ (¬ p5345) ∨ (¬ p5346))) := by
  classical
  tauto

theorem initial13638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5343) ∨ (meaning t m 6089) := by
  exact rule13638 (meaning t m 3609) (meaning t m 5343) (meaning t m 5344) (meaning t m 5345) (meaning t m 5346)

theorem rule13639 (p3609 p5343 p5344 p5345 p5346 : Prop) : (p5344) ∨ (((¬ p5343) ∨ (¬ p5344) ∨ (¬ p3609) ∨ (¬ p5345) ∨ (¬ p5346))) := by
  classical
  tauto

theorem initial13639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5344) ∨ (meaning t m 6089) := by
  exact rule13639 (meaning t m 3609) (meaning t m 5343) (meaning t m 5344) (meaning t m 5345) (meaning t m 5346)

theorem rule13640 (p3609 p5343 p5344 p5345 p5346 : Prop) : (p3609) ∨ (((¬ p5343) ∨ (¬ p5344) ∨ (¬ p3609) ∨ (¬ p5345) ∨ (¬ p5346))) := by
  classical
  tauto

theorem initial13640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3609) ∨ (meaning t m 6089) := by
  exact rule13640 (meaning t m 3609) (meaning t m 5343) (meaning t m 5344) (meaning t m 5345) (meaning t m 5346)

theorem rule13646 (p6088 p6089 : Prop) : (¬ ((¬ p6088) ∨ (¬ p6089))) ∨ (¬ p6088) ∨ (¬ p6089) := by
  classical
  tauto

theorem initial13646 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6087)) ∨ (¬ (meaning t m 6088)) ∨ (¬ (meaning t m 6089)) := by
  exact rule13646 (meaning t m 6088) (meaning t m 6089)

theorem rule13647 (p5336 p6087 : Prop) (h : (p5336 ↔ p6087)) : (¬ p5336) ∨ (p6087) := by
  classical
  tauto

theorem initial13647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5336)) ∨ (meaning t m 6087) := by
  have source := ElevenTheory.theory3512 t (m.theta 2 8) (m.theta 2 9) (m.theta 8 9)
  exact rule13647 (meaning t m 5336) (meaning t m 6087) source

theorem rule13655 (p3619 p4233 p5352 p5353 p5354 : Prop) : (p4233) ∨ (((¬ p4233) ∨ (¬ p5353) ∨ (¬ p5354) ∨ (¬ p5352) ∨ (¬ p3619))) := by
  classical
  tauto

theorem initial13655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4233) ∨ (meaning t m 6092) := by
  exact rule13655 (meaning t m 3619) (meaning t m 4233) (meaning t m 5352) (meaning t m 5353) (meaning t m 5354)

theorem rule13656 (p3619 p4233 p5352 p5353 p5354 : Prop) : (p5353) ∨ (((¬ p4233) ∨ (¬ p5353) ∨ (¬ p5354) ∨ (¬ p5352) ∨ (¬ p3619))) := by
  classical
  tauto

theorem initial13656 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5353) ∨ (meaning t m 6092) := by
  exact rule13656 (meaning t m 3619) (meaning t m 4233) (meaning t m 5352) (meaning t m 5353) (meaning t m 5354)

theorem rule13657 (p3619 p4233 p5352 p5353 p5354 : Prop) : (p5354) ∨ (((¬ p4233) ∨ (¬ p5353) ∨ (¬ p5354) ∨ (¬ p5352) ∨ (¬ p3619))) := by
  classical
  tauto

theorem initial13657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5354) ∨ (meaning t m 6092) := by
  exact rule13657 (meaning t m 3619) (meaning t m 4233) (meaning t m 5352) (meaning t m 5353) (meaning t m 5354)

theorem rule13658 (p3619 p4233 p5352 p5353 p5354 : Prop) : (p5352) ∨ (((¬ p4233) ∨ (¬ p5353) ∨ (¬ p5354) ∨ (¬ p5352) ∨ (¬ p3619))) := by
  classical
  tauto

theorem initial13658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5352) ∨ (meaning t m 6092) := by
  exact rule13658 (meaning t m 3619) (meaning t m 4233) (meaning t m 5352) (meaning t m 5353) (meaning t m 5354)

theorem rule13659 (p3619 p4233 p5352 p5353 p5354 : Prop) : (p3619) ∨ (((¬ p4233) ∨ (¬ p5353) ∨ (¬ p5354) ∨ (¬ p5352) ∨ (¬ p3619))) := by
  classical
  tauto

theorem initial13659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3619) ∨ (meaning t m 6092) := by
  exact rule13659 (meaning t m 3619) (meaning t m 4233) (meaning t m 5352) (meaning t m 5353) (meaning t m 5354)

theorem rule13660 (p3619 p4233 p5352 p5353 p5354 : Prop) : (¬ p3619) ∨ (¬ p4233) ∨ (¬ p5352) ∨ (¬ p5353) ∨ (¬ p5354) ∨ (¬ ((¬ p4233) ∨ (¬ p5353) ∨ (¬ p5354) ∨ (¬ p5352) ∨ (¬ p3619))) := by
  classical
  tauto

theorem initial13660 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 4233)) ∨ (¬ (meaning t m 5352)) ∨ (¬ (meaning t m 5353)) ∨ (¬ (meaning t m 5354)) ∨ (¬ (meaning t m 6092)) := by
  exact rule13660 (meaning t m 3619) (meaning t m 4233) (meaning t m 5352) (meaning t m 5353) (meaning t m 5354)

theorem rule13667 (p3817 p5357 p5358 p5359 p5360 : Prop) : (p5358) ∨ (((¬ p5358) ∨ (¬ p3817) ∨ (¬ p5357) ∨ (¬ p5359) ∨ (¬ p5360))) := by
  classical
  tauto

theorem initial13667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5358) ∨ (meaning t m 6094) := by
  exact rule13667 (meaning t m 3817) (meaning t m 5357) (meaning t m 5358) (meaning t m 5359) (meaning t m 5360)

theorem rule13668 (p3817 p5357 p5358 p5359 p5360 : Prop) : (p3817) ∨ (((¬ p5358) ∨ (¬ p3817) ∨ (¬ p5357) ∨ (¬ p5359) ∨ (¬ p5360))) := by
  classical
  tauto

theorem initial13668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3817) ∨ (meaning t m 6094) := by
  exact rule13668 (meaning t m 3817) (meaning t m 5357) (meaning t m 5358) (meaning t m 5359) (meaning t m 5360)

theorem rule13669 (p3817 p5357 p5358 p5359 p5360 : Prop) : (p5357) ∨ (((¬ p5358) ∨ (¬ p3817) ∨ (¬ p5357) ∨ (¬ p5359) ∨ (¬ p5360))) := by
  classical
  tauto

theorem initial13669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5357) ∨ (meaning t m 6094) := by
  exact rule13669 (meaning t m 3817) (meaning t m 5357) (meaning t m 5358) (meaning t m 5359) (meaning t m 5360)

theorem rule13673 (p3631 p5362 p5363 p5364 p5365 : Prop) : (p5362) ∨ (((¬ p5362) ∨ (¬ p5363) ∨ (¬ p3631) ∨ (¬ p5364) ∨ (¬ p5365))) := by
  classical
  tauto

theorem initial13673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5362) ∨ (meaning t m 6095) := by
  exact rule13673 (meaning t m 3631) (meaning t m 5362) (meaning t m 5363) (meaning t m 5364) (meaning t m 5365)

theorem rule13674 (p3631 p5362 p5363 p5364 p5365 : Prop) : (p5363) ∨ (((¬ p5362) ∨ (¬ p5363) ∨ (¬ p3631) ∨ (¬ p5364) ∨ (¬ p5365))) := by
  classical
  tauto

theorem initial13674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5363) ∨ (meaning t m 6095) := by
  exact rule13674 (meaning t m 3631) (meaning t m 5362) (meaning t m 5363) (meaning t m 5364) (meaning t m 5365)

theorem rule13675 (p3631 p5362 p5363 p5364 p5365 : Prop) : (p3631) ∨ (((¬ p5362) ∨ (¬ p5363) ∨ (¬ p3631) ∨ (¬ p5364) ∨ (¬ p5365))) := by
  classical
  tauto

theorem initial13675 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3631) ∨ (meaning t m 6095) := by
  exact rule13675 (meaning t m 3631) (meaning t m 5362) (meaning t m 5363) (meaning t m 5364) (meaning t m 5365)

theorem rule13681 (p6094 p6095 : Prop) : (¬ ((¬ p6094) ∨ (¬ p6095))) ∨ (¬ p6094) ∨ (¬ p6095) := by
  classical
  tauto

theorem initial13681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6093)) ∨ (¬ (meaning t m 6094)) ∨ (¬ (meaning t m 6095)) := by
  exact rule13681 (meaning t m 6094) (meaning t m 6095)

theorem rule13682 (p5355 p6093 : Prop) (h : (p5355 ↔ p6093)) : (¬ p5355) ∨ (p6093) := by
  classical
  tauto

theorem initial13682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5355)) ∨ (meaning t m 6093) := by
  have source := ElevenTheory.theory3515 t (m.theta 1 7) (m.theta 1 9) (m.theta 7 9)
  exact rule13682 (meaning t m 5355) (meaning t m 6093) source

theorem rule13684 (p2004 p2766 p3817 p3950 : Prop) (h : (¬ p3817) ∨ (¬ p2004) ∨ p2766 ∨ p3950) : (¬ p2004) ∨ (p2766) ∨ (¬ p3817) ∨ (p3950) := by
  classical
  tauto

theorem initial13684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3817)) ∨ (meaning t m 3950) := by
  have source := ElevenTheory.theory3516 t (m.theta 1 7) (m.theta 7 9) (m.theta 8 9)
  exact rule13684 (meaning t m 2004) (meaning t m 2766) (meaning t m 3817) (meaning t m 3950) source

theorem rule13687 (p2002 p2027 p2829 p2938 p3246 p3588 p4324 : Prop) (h : (¬ p2002) ∨ p2938 ∨ (¬ p2829) ∨ (¬ p3246) ∨ (¬ p4324) ∨ p2027 ∨ (¬ p3588)) : (¬ p2002) ∨ (p2027) ∨ (¬ p2829) ∨ (p2938) ∨ (¬ p3246) ∨ (¬ p3588) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial13687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory3519 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 5 7) (m.theta 7 9)
  exact rule13687 (meaning t m 2002) (meaning t m 2027) (meaning t m 2829) (meaning t m 2938) (meaning t m 3246) (meaning t m 3588) (meaning t m 4324) source

theorem rule13690 (p1998 p2027 p2406 p2427 p2699 p2881 p3379 : Prop) (h : (¬ p2406) ∨ (¬ p1998) ∨ (¬ p2427) ∨ p2027 ∨ p2699 ∨ (¬ p3379) ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2427) ∨ (p2699) ∨ (¬ p2881) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial13690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory3522 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule13690 (meaning t m 1998) (meaning t m 2027) (meaning t m 2406) (meaning t m 2427) (meaning t m 2699) (meaning t m 2881) (meaning t m 3379) source

theorem rule13691 (p2006 p2027 p2598 p2839 p3425 p3437 p3585 : Prop) (h : (¬ p3585) ∨ p2027 ∨ (¬ p2006) ∨ (¬ p2598) ∨ (¬ p2839) ∨ (¬ p3425) ∨ p3437) : (¬ p2006) ∨ (p2027) ∨ (¬ p2598) ∨ (¬ p2839) ∨ (¬ p3425) ∨ (p3437) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial13691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3425)) ∨ (meaning t m 3437) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory3523 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 2 7)
  exact rule13691 (meaning t m 2006) (meaning t m 2027) (meaning t m 2598) (meaning t m 2839) (meaning t m 3425) (meaning t m 3437) (meaning t m 3585) source

end SunPrize.SMT
