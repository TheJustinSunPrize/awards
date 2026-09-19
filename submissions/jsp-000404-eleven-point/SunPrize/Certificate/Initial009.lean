import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory004
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule7204 (p3097 p4204 p4275 p4555 p4556 : Prop) : (¬ (p4204 ∧ p4275 ∧ p3097 ∧ p4555 ∧ p4556)) ∨ (p4556) := by
  classical
  tauto

theorem initial7204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4554)) ∨ (meaning t m 4556) := by
  exact rule7204 (meaning t m 3097) (meaning t m 4204) (meaning t m 4275) (meaning t m 4555) (meaning t m 4556)

theorem rule7206 (p2274 p3872 p4140 p4558 p4559 : Prop) : (p4140) ∨ (¬ (p4140 ∧ p3872 ∧ p2274 ∧ p4558 ∧ p4559)) := by
  classical
  tauto

theorem initial7206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4140) ∨ (¬ (meaning t m 4557)) := by
  exact rule7206 (meaning t m 2274) (meaning t m 3872) (meaning t m 4140) (meaning t m 4558) (meaning t m 4559)

theorem rule7207 (p2274 p3872 p4140 p4558 p4559 : Prop) : (p3872) ∨ (¬ (p4140 ∧ p3872 ∧ p2274 ∧ p4558 ∧ p4559)) := by
  classical
  tauto

theorem initial7207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3872) ∨ (¬ (meaning t m 4557)) := by
  exact rule7207 (meaning t m 2274) (meaning t m 3872) (meaning t m 4140) (meaning t m 4558) (meaning t m 4559)

theorem rule7208 (p2274 p3872 p4140 p4558 p4559 : Prop) : (p2274) ∨ (¬ (p4140 ∧ p3872 ∧ p2274 ∧ p4558 ∧ p4559)) := by
  classical
  tauto

theorem initial7208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2274) ∨ (¬ (meaning t m 4557)) := by
  exact rule7208 (meaning t m 2274) (meaning t m 3872) (meaning t m 4140) (meaning t m 4558) (meaning t m 4559)

theorem rule7209 (p2274 p3872 p4140 p4558 p4559 : Prop) : (¬ (p4140 ∧ p3872 ∧ p2274 ∧ p4558 ∧ p4559)) ∨ (p4558) := by
  classical
  tauto

theorem initial7209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4557)) ∨ (meaning t m 4558) := by
  exact rule7209 (meaning t m 2274) (meaning t m 3872) (meaning t m 4140) (meaning t m 4558) (meaning t m 4559)

theorem rule7210 (p2274 p3872 p4140 p4558 p4559 : Prop) : (¬ (p4140 ∧ p3872 ∧ p2274 ∧ p4558 ∧ p4559)) ∨ (p4559) := by
  classical
  tauto

theorem initial7210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4557)) ∨ (meaning t m 4559) := by
  exact rule7210 (meaning t m 2274) (meaning t m 3872) (meaning t m 4140) (meaning t m 4558) (meaning t m 4559)

theorem rule7214 (p4554 p4557 : Prop) : (¬ (p4554 ∨ p4557)) ∨ (p4554) ∨ (p4557) := by
  classical
  tauto

theorem initial7214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4553)) ∨ (meaning t m 4554) ∨ (meaning t m 4557) := by
  exact rule7214 (meaning t m 4554) (meaning t m 4557)

theorem rule7215 (p2268 p4553 : Prop) (h : (p2268 ↔ p4553)) : (¬ p2268) ∨ (p4553) := by
  classical
  tauto

theorem initial7215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2268)) ∨ (meaning t m 4553) := by
  have source := ElevenTheory.theory1111 t (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule7215 (meaning t m 2268) (meaning t m 4553) source

theorem rule7218 (p3745 p3952 p4153 p4563 p4564 : Prop) : (p4153) ∨ (¬ (p4153 ∧ p3745 ∧ p3952 ∧ p4563 ∧ p4564)) := by
  classical
  tauto

theorem initial7218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4153) ∨ (¬ (meaning t m 4562)) := by
  exact rule7218 (meaning t m 3745) (meaning t m 3952) (meaning t m 4153) (meaning t m 4563) (meaning t m 4564)

theorem rule7219 (p3745 p3952 p4153 p4563 p4564 : Prop) : (p3745) ∨ (¬ (p4153 ∧ p3745 ∧ p3952 ∧ p4563 ∧ p4564)) := by
  classical
  tauto

theorem initial7219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3745) ∨ (¬ (meaning t m 4562)) := by
  exact rule7219 (meaning t m 3745) (meaning t m 3952) (meaning t m 4153) (meaning t m 4563) (meaning t m 4564)

theorem rule7220 (p3745 p3952 p4153 p4563 p4564 : Prop) : (p3952) ∨ (¬ (p4153 ∧ p3745 ∧ p3952 ∧ p4563 ∧ p4564)) := by
  classical
  tauto

theorem initial7220 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3952) ∨ (¬ (meaning t m 4562)) := by
  exact rule7220 (meaning t m 3745) (meaning t m 3952) (meaning t m 4153) (meaning t m 4563) (meaning t m 4564)

theorem rule7221 (p3745 p3952 p4153 p4563 p4564 : Prop) : (¬ (p4153 ∧ p3745 ∧ p3952 ∧ p4563 ∧ p4564)) ∨ (p4563) := by
  classical
  tauto

theorem initial7221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4562)) ∨ (meaning t m 4563) := by
  exact rule7221 (meaning t m 3745) (meaning t m 3952) (meaning t m 4153) (meaning t m 4563) (meaning t m 4564)

theorem rule7222 (p3745 p3952 p4153 p4563 p4564 : Prop) : (¬ (p4153 ∧ p3745 ∧ p3952 ∧ p4563 ∧ p4564)) ∨ (p4564) := by
  classical
  tauto

theorem initial7222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4562)) ∨ (meaning t m 4564) := by
  exact rule7222 (meaning t m 3745) (meaning t m 3952) (meaning t m 4153) (meaning t m 4563) (meaning t m 4564)

theorem rule7224 (p2284 p3986 p4336 p4560 p4566 : Prop) : (p3986) ∨ (¬ (p3986 ∧ p4336 ∧ p2284 ∧ p4566 ∧ p4560)) := by
  classical
  tauto

theorem initial7224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3986) ∨ (¬ (meaning t m 4565)) := by
  exact rule7224 (meaning t m 2284) (meaning t m 3986) (meaning t m 4336) (meaning t m 4560) (meaning t m 4566)

theorem rule7225 (p2284 p3986 p4336 p4560 p4566 : Prop) : (p4336) ∨ (¬ (p3986 ∧ p4336 ∧ p2284 ∧ p4566 ∧ p4560)) := by
  classical
  tauto

theorem initial7225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4336) ∨ (¬ (meaning t m 4565)) := by
  exact rule7225 (meaning t m 2284) (meaning t m 3986) (meaning t m 4336) (meaning t m 4560) (meaning t m 4566)

theorem rule7226 (p2284 p3986 p4336 p4560 p4566 : Prop) : (p2284) ∨ (¬ (p3986 ∧ p4336 ∧ p2284 ∧ p4566 ∧ p4560)) := by
  classical
  tauto

theorem initial7226 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2284) ∨ (¬ (meaning t m 4565)) := by
  exact rule7226 (meaning t m 2284) (meaning t m 3986) (meaning t m 4336) (meaning t m 4560) (meaning t m 4566)

theorem rule7227 (p2284 p3986 p4336 p4560 p4566 : Prop) : (¬ (p3986 ∧ p4336 ∧ p2284 ∧ p4566 ∧ p4560)) ∨ (p4566) := by
  classical
  tauto

theorem initial7227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4565)) ∨ (meaning t m 4566) := by
  exact rule7227 (meaning t m 2284) (meaning t m 3986) (meaning t m 4336) (meaning t m 4560) (meaning t m 4566)

theorem rule7228 (p2284 p3986 p4336 p4560 p4566 : Prop) : (p4560) ∨ (¬ (p3986 ∧ p4336 ∧ p2284 ∧ p4566 ∧ p4560)) := by
  classical
  tauto

theorem initial7228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4560) ∨ (¬ (meaning t m 4565)) := by
  exact rule7228 (meaning t m 2284) (meaning t m 3986) (meaning t m 4336) (meaning t m 4560) (meaning t m 4566)

theorem rule7232 (p4562 p4565 : Prop) : (¬ (p4562 ∨ p4565)) ∨ (p4562) ∨ (p4565) := by
  classical
  tauto

theorem initial7232 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4561)) ∨ (meaning t m 4562) ∨ (meaning t m 4565) := by
  exact rule7232 (meaning t m 4562) (meaning t m 4565)

theorem rule7233 (p2278 p4561 : Prop) (h : (p2278 ↔ p4561)) : (¬ p2278) ∨ (p4561) := by
  classical
  tauto

theorem initial7233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2278)) ∨ (meaning t m 4561) := by
  have source := ElevenTheory.theory1113 t (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule7233 (meaning t m 2278) (meaning t m 4561) source

theorem rule7235 (p2298 p3568 p4067 p4569 p4570 : Prop) : (p4067) ∨ (¬ (p4067 ∧ p2298 ∧ p3568 ∧ p4569 ∧ p4570)) := by
  classical
  tauto

theorem initial7235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4067) ∨ (¬ (meaning t m 4568)) := by
  exact rule7235 (meaning t m 2298) (meaning t m 3568) (meaning t m 4067) (meaning t m 4569) (meaning t m 4570)

theorem rule7236 (p2298 p3568 p4067 p4569 p4570 : Prop) : (p2298) ∨ (¬ (p4067 ∧ p2298 ∧ p3568 ∧ p4569 ∧ p4570)) := by
  classical
  tauto

theorem initial7236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2298) ∨ (¬ (meaning t m 4568)) := by
  exact rule7236 (meaning t m 2298) (meaning t m 3568) (meaning t m 4067) (meaning t m 4569) (meaning t m 4570)

theorem rule7237 (p2298 p3568 p4067 p4569 p4570 : Prop) : (p3568) ∨ (¬ (p4067 ∧ p2298 ∧ p3568 ∧ p4569 ∧ p4570)) := by
  classical
  tauto

theorem initial7237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3568) ∨ (¬ (meaning t m 4568)) := by
  exact rule7237 (meaning t m 2298) (meaning t m 3568) (meaning t m 4067) (meaning t m 4569) (meaning t m 4570)

theorem rule7238 (p2298 p3568 p4067 p4569 p4570 : Prop) : (¬ (p4067 ∧ p2298 ∧ p3568 ∧ p4569 ∧ p4570)) ∨ (p4569) := by
  classical
  tauto

theorem initial7238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4568)) ∨ (meaning t m 4569) := by
  exact rule7238 (meaning t m 2298) (meaning t m 3568) (meaning t m 4067) (meaning t m 4569) (meaning t m 4570)

theorem rule7239 (p2298 p3568 p4067 p4569 p4570 : Prop) : (¬ (p4067 ∧ p2298 ∧ p3568 ∧ p4569 ∧ p4570)) ∨ (p4570) := by
  classical
  tauto

theorem initial7239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4568)) ∨ (meaning t m 4570) := by
  exact rule7239 (meaning t m 2298) (meaning t m 3568) (meaning t m 4067) (meaning t m 4569) (meaning t m 4570)

theorem rule7241 (p2295 p3552 p4156 p4361 p4572 : Prop) : (p3552) ∨ (¬ (p3552 ∧ p4156 ∧ p2295 ∧ p4572 ∧ p4361)) := by
  classical
  tauto

theorem initial7241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3552) ∨ (¬ (meaning t m 4571)) := by
  exact rule7241 (meaning t m 2295) (meaning t m 3552) (meaning t m 4156) (meaning t m 4361) (meaning t m 4572)

theorem rule7242 (p2295 p3552 p4156 p4361 p4572 : Prop) : (p4156) ∨ (¬ (p3552 ∧ p4156 ∧ p2295 ∧ p4572 ∧ p4361)) := by
  classical
  tauto

theorem initial7242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4156) ∨ (¬ (meaning t m 4571)) := by
  exact rule7242 (meaning t m 2295) (meaning t m 3552) (meaning t m 4156) (meaning t m 4361) (meaning t m 4572)

theorem rule7243 (p2295 p3552 p4156 p4361 p4572 : Prop) : (p2295) ∨ (¬ (p3552 ∧ p4156 ∧ p2295 ∧ p4572 ∧ p4361)) := by
  classical
  tauto

theorem initial7243 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2295) ∨ (¬ (meaning t m 4571)) := by
  exact rule7243 (meaning t m 2295) (meaning t m 3552) (meaning t m 4156) (meaning t m 4361) (meaning t m 4572)

theorem rule7245 (p2295 p3552 p4156 p4361 p4572 : Prop) : (p4361) ∨ (¬ (p3552 ∧ p4156 ∧ p2295 ∧ p4572 ∧ p4361)) := by
  classical
  tauto

theorem initial7245 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4361) ∨ (¬ (meaning t m 4571)) := by
  exact rule7245 (meaning t m 2295) (meaning t m 3552) (meaning t m 4156) (meaning t m 4361) (meaning t m 4572)

theorem rule7249 (p4568 p4571 : Prop) : (¬ (p4568 ∨ p4571)) ∨ (p4568) ∨ (p4571) := by
  classical
  tauto

theorem initial7249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4567)) ∨ (meaning t m 4568) ∨ (meaning t m 4571) := by
  exact rule7249 (meaning t m 4568) (meaning t m 4571)

theorem rule7250 (p2289 p4567 : Prop) (h : (p2289 ↔ p4567)) : (¬ p2289) ∨ (p4567) := by
  classical
  tauto

theorem initial7250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2289)) ∨ (meaning t m 4567) := by
  have source := ElevenTheory.theory1114 t (m.theta 3 6) (m.theta 3 7) (m.theta 6 7)
  exact rule7250 (meaning t m 2289) (meaning t m 4567) source

theorem rule7254 (p2310 p2317 : Prop) : (p2310) ∨ (p2317) ∨ (¬ (p2310 ∨ p2317)) := by
  classical
  tauto

theorem initial7254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2310) ∨ (meaning t m 2317) ∨ (¬ (meaning t m 4573)) := by
  exact rule7254 (meaning t m 2310) (meaning t m 2317)

theorem rule7255 (p2301 p4573 : Prop) (h : (p2301 ↔ p4573)) : (¬ p2301) ∨ (p4573) := by
  classical
  tauto

theorem initial7255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2301)) ∨ (meaning t m 4573) := by
  have source := ElevenTheory.theory1115 t (m.theta 0 6) (m.theta 0 7) (m.theta 6 7)
  exact rule7255 (meaning t m 2301) (meaning t m 4573) source

theorem rule7273 (p2963 p3567 p3983 p4580 p4581 : Prop) : (p3983) ∨ (¬ (p3983 ∧ p3567 ∧ p2963 ∧ p4580 ∧ p4581)) := by
  classical
  tauto

theorem initial7273 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3983) ∨ (¬ (meaning t m 4579)) := by
  exact rule7273 (meaning t m 2963) (meaning t m 3567) (meaning t m 3983) (meaning t m 4580) (meaning t m 4581)

theorem rule7274 (p2963 p3567 p3983 p4580 p4581 : Prop) : (p3567) ∨ (¬ (p3983 ∧ p3567 ∧ p2963 ∧ p4580 ∧ p4581)) := by
  classical
  tauto

theorem initial7274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3567) ∨ (¬ (meaning t m 4579)) := by
  exact rule7274 (meaning t m 2963) (meaning t m 3567) (meaning t m 3983) (meaning t m 4580) (meaning t m 4581)

theorem rule7275 (p2963 p3567 p3983 p4580 p4581 : Prop) : (p2963) ∨ (¬ (p3983 ∧ p3567 ∧ p2963 ∧ p4580 ∧ p4581)) := by
  classical
  tauto

theorem initial7275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2963) ∨ (¬ (meaning t m 4579)) := by
  exact rule7275 (meaning t m 2963) (meaning t m 3567) (meaning t m 3983) (meaning t m 4580) (meaning t m 4581)

theorem rule7277 (p2963 p3567 p3983 p4580 p4581 : Prop) : (¬ (p3983 ∧ p3567 ∧ p2963 ∧ p4580 ∧ p4581)) ∨ (p4581) := by
  classical
  tauto

theorem initial7277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4579)) ∨ (meaning t m 4581) := by
  exact rule7277 (meaning t m 2963) (meaning t m 3567) (meaning t m 3983) (meaning t m 4580) (meaning t m 4581)

theorem rule7279 (p2331 p2667 p3987 p4583 p4584 : Prop) : (p2667) ∨ (¬ (p2667 ∧ p3987 ∧ p2331 ∧ p4583 ∧ p4584)) := by
  classical
  tauto

theorem initial7279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2667) ∨ (¬ (meaning t m 4582)) := by
  exact rule7279 (meaning t m 2331) (meaning t m 2667) (meaning t m 3987) (meaning t m 4583) (meaning t m 4584)

theorem rule7280 (p2331 p2667 p3987 p4583 p4584 : Prop) : (p3987) ∨ (¬ (p2667 ∧ p3987 ∧ p2331 ∧ p4583 ∧ p4584)) := by
  classical
  tauto

theorem initial7280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3987) ∨ (¬ (meaning t m 4582)) := by
  exact rule7280 (meaning t m 2331) (meaning t m 2667) (meaning t m 3987) (meaning t m 4583) (meaning t m 4584)

theorem rule7281 (p2331 p2667 p3987 p4583 p4584 : Prop) : (p2331) ∨ (¬ (p2667 ∧ p3987 ∧ p2331 ∧ p4583 ∧ p4584)) := by
  classical
  tauto

theorem initial7281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2331) ∨ (¬ (meaning t m 4582)) := by
  exact rule7281 (meaning t m 2331) (meaning t m 2667) (meaning t m 3987) (meaning t m 4583) (meaning t m 4584)

theorem rule7283 (p2331 p2667 p3987 p4583 p4584 : Prop) : (¬ (p2667 ∧ p3987 ∧ p2331 ∧ p4583 ∧ p4584)) ∨ (p4584) := by
  classical
  tauto

theorem initial7283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4582)) ∨ (meaning t m 4584) := by
  exact rule7283 (meaning t m 2331) (meaning t m 2667) (meaning t m 3987) (meaning t m 4583) (meaning t m 4584)

theorem rule7287 (p4579 p4582 : Prop) : (¬ (p4579 ∨ p4582)) ∨ (p4579) ∨ (p4582) := by
  classical
  tauto

theorem initial7287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4578)) ∨ (meaning t m 4579) ∨ (meaning t m 4582) := by
  exact rule7287 (meaning t m 4579) (meaning t m 4582)

theorem rule7288 (p2325 p4578 : Prop) (h : (p2325 ↔ p4578)) : (¬ p2325) ∨ (p4578) := by
  classical
  tauto

theorem initial7288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2325)) ∨ (meaning t m 4578) := by
  have source := ElevenTheory.theory1118 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 6)
  exact rule7288 (meaning t m 2325) (meaning t m 4578) source

theorem rule7290 (p3551 p3960 p3961 p4587 p4588 : Prop) : (p3961) ∨ (¬ (p3961 ∧ p3960 ∧ p3551 ∧ p4587 ∧ p4588)) := by
  classical
  tauto

theorem initial7290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3961) ∨ (¬ (meaning t m 4586)) := by
  exact rule7290 (meaning t m 3551) (meaning t m 3960) (meaning t m 3961) (meaning t m 4587) (meaning t m 4588)

theorem rule7291 (p3551 p3960 p3961 p4587 p4588 : Prop) : (p3960) ∨ (¬ (p3961 ∧ p3960 ∧ p3551 ∧ p4587 ∧ p4588)) := by
  classical
  tauto

theorem initial7291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3960) ∨ (¬ (meaning t m 4586)) := by
  exact rule7291 (meaning t m 3551) (meaning t m 3960) (meaning t m 3961) (meaning t m 4587) (meaning t m 4588)

theorem rule7292 (p3551 p3960 p3961 p4587 p4588 : Prop) : (p3551) ∨ (¬ (p3961 ∧ p3960 ∧ p3551 ∧ p4587 ∧ p4588)) := by
  classical
  tauto

theorem initial7292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3551) ∨ (¬ (meaning t m 4586)) := by
  exact rule7292 (meaning t m 3551) (meaning t m 3960) (meaning t m 3961) (meaning t m 4587) (meaning t m 4588)

theorem rule7296 (p2341 p4403 p4590 p4591 p4592 : Prop) : (p4403) ∨ (¬ (p4403 ∧ p4590 ∧ p2341 ∧ p4591 ∧ p4592)) := by
  classical
  tauto

theorem initial7296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4403) ∨ (¬ (meaning t m 4589)) := by
  exact rule7296 (meaning t m 2341) (meaning t m 4403) (meaning t m 4590) (meaning t m 4591) (meaning t m 4592)

theorem rule7297 (p2341 p4403 p4590 p4591 p4592 : Prop) : (¬ (p4403 ∧ p4590 ∧ p2341 ∧ p4591 ∧ p4592)) ∨ (p4590) := by
  classical
  tauto

theorem initial7297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4589)) ∨ (meaning t m 4590) := by
  exact rule7297 (meaning t m 2341) (meaning t m 4403) (meaning t m 4590) (meaning t m 4591) (meaning t m 4592)

theorem rule7298 (p2341 p4403 p4590 p4591 p4592 : Prop) : (p2341) ∨ (¬ (p4403 ∧ p4590 ∧ p2341 ∧ p4591 ∧ p4592)) := by
  classical
  tauto

theorem initial7298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2341) ∨ (¬ (meaning t m 4589)) := by
  exact rule7298 (meaning t m 2341) (meaning t m 4403) (meaning t m 4590) (meaning t m 4591) (meaning t m 4592)

theorem rule7300 (p2341 p4403 p4590 p4591 p4592 : Prop) : (¬ (p4403 ∧ p4590 ∧ p2341 ∧ p4591 ∧ p4592)) ∨ (p4592) := by
  classical
  tauto

theorem initial7300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4589)) ∨ (meaning t m 4592) := by
  exact rule7300 (meaning t m 2341) (meaning t m 4403) (meaning t m 4590) (meaning t m 4591) (meaning t m 4592)

theorem rule7304 (p4586 p4589 : Prop) : (¬ (p4586 ∨ p4589)) ∨ (p4586) ∨ (p4589) := by
  classical
  tauto

theorem initial7304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4585)) ∨ (meaning t m 4586) ∨ (meaning t m 4589) := by
  exact rule7304 (meaning t m 4586) (meaning t m 4589)

theorem rule7305 (p2335 p4585 : Prop) (h : (p2335 ↔ p4585)) : (¬ p2335) ∨ (p4585) := by
  classical
  tauto

theorem initial7305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2335)) ∨ (meaning t m 4585) := by
  have source := ElevenTheory.theory1119 t (m.theta 0 7) (m.theta 0 8) (m.theta 7 8)
  exact rule7305 (meaning t m 2335) (meaning t m 4585) source

theorem rule7307 (p3573 p3956 p4432 p4595 p4596 : Prop) : (p3573) ∨ (¬ (p3573 ∧ p4432 ∧ p3956 ∧ p4595 ∧ p4596)) := by
  classical
  tauto

theorem initial7307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3573) ∨ (¬ (meaning t m 4594)) := by
  exact rule7307 (meaning t m 3573) (meaning t m 3956) (meaning t m 4432) (meaning t m 4595) (meaning t m 4596)

theorem rule7308 (p3573 p3956 p4432 p4595 p4596 : Prop) : (p4432) ∨ (¬ (p3573 ∧ p4432 ∧ p3956 ∧ p4595 ∧ p4596)) := by
  classical
  tauto

theorem initial7308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4432) ∨ (¬ (meaning t m 4594)) := by
  exact rule7308 (meaning t m 3573) (meaning t m 3956) (meaning t m 4432) (meaning t m 4595) (meaning t m 4596)

theorem rule7309 (p3573 p3956 p4432 p4595 p4596 : Prop) : (p3956) ∨ (¬ (p3573 ∧ p4432 ∧ p3956 ∧ p4595 ∧ p4596)) := by
  classical
  tauto

theorem initial7309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3956) ∨ (¬ (meaning t m 4594)) := by
  exact rule7309 (meaning t m 3573) (meaning t m 3956) (meaning t m 4432) (meaning t m 4595) (meaning t m 4596)

theorem rule7310 (p3573 p3956 p4432 p4595 p4596 : Prop) : (¬ (p3573 ∧ p4432 ∧ p3956 ∧ p4595 ∧ p4596)) ∨ (p4595) := by
  classical
  tauto

theorem initial7310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4594)) ∨ (meaning t m 4595) := by
  exact rule7310 (meaning t m 3573) (meaning t m 3956) (meaning t m 4432) (meaning t m 4595) (meaning t m 4596)

theorem rule7311 (p3573 p3956 p4432 p4595 p4596 : Prop) : (¬ (p3573 ∧ p4432 ∧ p3956 ∧ p4595 ∧ p4596)) ∨ (p4596) := by
  classical
  tauto

theorem initial7311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4594)) ∨ (meaning t m 4596) := by
  exact rule7311 (meaning t m 3573) (meaning t m 3956) (meaning t m 4432) (meaning t m 4595) (meaning t m 4596)

theorem rule7313 (p2352 p2510 p4157 p4384 p4598 : Prop) : (p4157) ∨ (¬ (p4157 ∧ p2510 ∧ p2352 ∧ p4598 ∧ p4384)) := by
  classical
  tauto

theorem initial7313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4157) ∨ (¬ (meaning t m 4597)) := by
  exact rule7313 (meaning t m 2352) (meaning t m 2510) (meaning t m 4157) (meaning t m 4384) (meaning t m 4598)

theorem rule7314 (p2352 p2510 p4157 p4384 p4598 : Prop) : (p2510) ∨ (¬ (p4157 ∧ p2510 ∧ p2352 ∧ p4598 ∧ p4384)) := by
  classical
  tauto

theorem initial7314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2510) ∨ (¬ (meaning t m 4597)) := by
  exact rule7314 (meaning t m 2352) (meaning t m 2510) (meaning t m 4157) (meaning t m 4384) (meaning t m 4598)

theorem rule7315 (p2352 p2510 p4157 p4384 p4598 : Prop) : (p2352) ∨ (¬ (p4157 ∧ p2510 ∧ p2352 ∧ p4598 ∧ p4384)) := by
  classical
  tauto

theorem initial7315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2352) ∨ (¬ (meaning t m 4597)) := by
  exact rule7315 (meaning t m 2352) (meaning t m 2510) (meaning t m 4157) (meaning t m 4384) (meaning t m 4598)

theorem rule7316 (p2352 p2510 p4157 p4384 p4598 : Prop) : (¬ (p4157 ∧ p2510 ∧ p2352 ∧ p4598 ∧ p4384)) ∨ (p4598) := by
  classical
  tauto

theorem initial7316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4597)) ∨ (meaning t m 4598) := by
  exact rule7316 (meaning t m 2352) (meaning t m 2510) (meaning t m 4157) (meaning t m 4384) (meaning t m 4598)

theorem rule7317 (p2352 p2510 p4157 p4384 p4598 : Prop) : (p4384) ∨ (¬ (p4157 ∧ p2510 ∧ p2352 ∧ p4598 ∧ p4384)) := by
  classical
  tauto

theorem initial7317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4384) ∨ (¬ (meaning t m 4597)) := by
  exact rule7317 (meaning t m 2352) (meaning t m 2510) (meaning t m 4157) (meaning t m 4384) (meaning t m 4598)

theorem rule7321 (p4594 p4597 : Prop) : (¬ (p4594 ∨ p4597)) ∨ (p4594) ∨ (p4597) := by
  classical
  tauto

theorem initial7321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4593)) ∨ (meaning t m 4594) ∨ (meaning t m 4597) := by
  exact rule7321 (meaning t m 4594) (meaning t m 4597)

theorem rule7322 (p2346 p4593 : Prop) (h : (p2346 ↔ p4593)) : (¬ p2346) ∨ (p4593) := by
  classical
  tauto

theorem initial7322 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2346)) ∨ (meaning t m 4593) := by
  have source := ElevenTheory.theory1120 t (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule7322 (meaning t m 2346) (meaning t m 4593) source

theorem rule7324 (p3322 p4171 p4330 p4347 p4601 : Prop) : (p3322) ∨ (¬ (p3322 ∧ p4171 ∧ p4347 ∧ p4601 ∧ p4330)) := by
  classical
  tauto

theorem initial7324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3322) ∨ (¬ (meaning t m 4600)) := by
  exact rule7324 (meaning t m 3322) (meaning t m 4171) (meaning t m 4330) (meaning t m 4347) (meaning t m 4601)

theorem rule7325 (p3322 p4171 p4330 p4347 p4601 : Prop) : (p4171) ∨ (¬ (p3322 ∧ p4171 ∧ p4347 ∧ p4601 ∧ p4330)) := by
  classical
  tauto

theorem initial7325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4171) ∨ (¬ (meaning t m 4600)) := by
  exact rule7325 (meaning t m 3322) (meaning t m 4171) (meaning t m 4330) (meaning t m 4347) (meaning t m 4601)

theorem rule7326 (p3322 p4171 p4330 p4347 p4601 : Prop) : (p4347) ∨ (¬ (p3322 ∧ p4171 ∧ p4347 ∧ p4601 ∧ p4330)) := by
  classical
  tauto

theorem initial7326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4347) ∨ (¬ (meaning t m 4600)) := by
  exact rule7326 (meaning t m 3322) (meaning t m 4171) (meaning t m 4330) (meaning t m 4347) (meaning t m 4601)

theorem rule7327 (p3322 p4171 p4330 p4347 p4601 : Prop) : (¬ (p3322 ∧ p4171 ∧ p4347 ∧ p4601 ∧ p4330)) ∨ (p4601) := by
  classical
  tauto

theorem initial7327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4600)) ∨ (meaning t m 4601) := by
  exact rule7327 (meaning t m 3322) (meaning t m 4171) (meaning t m 4330) (meaning t m 4347) (meaning t m 4601)

theorem rule7328 (p3322 p4171 p4330 p4347 p4601 : Prop) : (p4330) ∨ (¬ (p3322 ∧ p4171 ∧ p4347 ∧ p4601 ∧ p4330)) := by
  classical
  tauto

theorem initial7328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4330) ∨ (¬ (meaning t m 4600)) := by
  exact rule7328 (meaning t m 3322) (meaning t m 4171) (meaning t m 4330) (meaning t m 4347) (meaning t m 4601)

theorem rule7330 (p2363 p3990 p4345 p4603 p4604 : Prop) : (p4345) ∨ (¬ (p4345 ∧ p3990 ∧ p2363 ∧ p4603 ∧ p4604)) := by
  classical
  tauto

theorem initial7330 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4345) ∨ (¬ (meaning t m 4602)) := by
  exact rule7330 (meaning t m 2363) (meaning t m 3990) (meaning t m 4345) (meaning t m 4603) (meaning t m 4604)

theorem rule7331 (p2363 p3990 p4345 p4603 p4604 : Prop) : (p3990) ∨ (¬ (p4345 ∧ p3990 ∧ p2363 ∧ p4603 ∧ p4604)) := by
  classical
  tauto

theorem initial7331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3990) ∨ (¬ (meaning t m 4602)) := by
  exact rule7331 (meaning t m 2363) (meaning t m 3990) (meaning t m 4345) (meaning t m 4603) (meaning t m 4604)

theorem rule7332 (p2363 p3990 p4345 p4603 p4604 : Prop) : (p2363) ∨ (¬ (p4345 ∧ p3990 ∧ p2363 ∧ p4603 ∧ p4604)) := by
  classical
  tauto

theorem initial7332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2363) ∨ (¬ (meaning t m 4602)) := by
  exact rule7332 (meaning t m 2363) (meaning t m 3990) (meaning t m 4345) (meaning t m 4603) (meaning t m 4604)

theorem rule7333 (p2363 p3990 p4345 p4603 p4604 : Prop) : (¬ (p4345 ∧ p3990 ∧ p2363 ∧ p4603 ∧ p4604)) ∨ (p4603) := by
  classical
  tauto

theorem initial7333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4602)) ∨ (meaning t m 4603) := by
  exact rule7333 (meaning t m 2363) (meaning t m 3990) (meaning t m 4345) (meaning t m 4603) (meaning t m 4604)

theorem rule7334 (p2363 p3990 p4345 p4603 p4604 : Prop) : (¬ (p4345 ∧ p3990 ∧ p2363 ∧ p4603 ∧ p4604)) ∨ (p4604) := by
  classical
  tauto

theorem initial7334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4602)) ∨ (meaning t m 4604) := by
  exact rule7334 (meaning t m 2363) (meaning t m 3990) (meaning t m 4345) (meaning t m 4603) (meaning t m 4604)

theorem rule7338 (p4600 p4602 : Prop) : (¬ (p4600 ∨ p4602)) ∨ (p4600) ∨ (p4602) := by
  classical
  tauto

theorem initial7338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4599)) ∨ (meaning t m 4600) ∨ (meaning t m 4602) := by
  exact rule7338 (meaning t m 4600) (meaning t m 4602)

theorem rule7339 (p2357 p4599 : Prop) (h : (p2357 ↔ p4599)) : (¬ p2357) ∨ (p4599) := by
  classical
  tauto

theorem initial7339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2357)) ∨ (meaning t m 4599) := by
  have source := ElevenTheory.theory1121 t (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule7339 (meaning t m 2357) (meaning t m 4599) source

theorem rule7341 (p3693 p3880 p4158 p4607 p4608 : Prop) : (¬ (p4607 ∧ p3693 ∧ p3880 ∧ p4608 ∧ p4158)) ∨ (p4607) := by
  classical
  tauto

theorem initial7341 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4606)) ∨ (meaning t m 4607) := by
  exact rule7341 (meaning t m 3693) (meaning t m 3880) (meaning t m 4158) (meaning t m 4607) (meaning t m 4608)

theorem rule7342 (p3693 p3880 p4158 p4607 p4608 : Prop) : (p3693) ∨ (¬ (p4607 ∧ p3693 ∧ p3880 ∧ p4608 ∧ p4158)) := by
  classical
  tauto

theorem initial7342 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3693) ∨ (¬ (meaning t m 4606)) := by
  exact rule7342 (meaning t m 3693) (meaning t m 3880) (meaning t m 4158) (meaning t m 4607) (meaning t m 4608)

theorem rule7343 (p3693 p3880 p4158 p4607 p4608 : Prop) : (p3880) ∨ (¬ (p4607 ∧ p3693 ∧ p3880 ∧ p4608 ∧ p4158)) := by
  classical
  tauto

theorem initial7343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3880) ∨ (¬ (meaning t m 4606)) := by
  exact rule7343 (meaning t m 3693) (meaning t m 3880) (meaning t m 4158) (meaning t m 4607) (meaning t m 4608)

theorem rule7344 (p3693 p3880 p4158 p4607 p4608 : Prop) : (¬ (p4607 ∧ p3693 ∧ p3880 ∧ p4608 ∧ p4158)) ∨ (p4608) := by
  classical
  tauto

theorem initial7344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4606)) ∨ (meaning t m 4608) := by
  exact rule7344 (meaning t m 3693) (meaning t m 3880) (meaning t m 4158) (meaning t m 4607) (meaning t m 4608)

theorem rule7345 (p3693 p3880 p4158 p4607 p4608 : Prop) : (p4158) ∨ (¬ (p4607 ∧ p3693 ∧ p3880 ∧ p4608 ∧ p4158)) := by
  classical
  tauto

theorem initial7345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4158) ∨ (¬ (meaning t m 4606)) := by
  exact rule7345 (meaning t m 3693) (meaning t m 3880) (meaning t m 4158) (meaning t m 4607) (meaning t m 4608)

theorem rule7347 (p2373 p2531 p4355 p4434 p4610 : Prop) : (p2531) ∨ (¬ (p2531 ∧ p4355 ∧ p2373 ∧ p4610 ∧ p4434)) := by
  classical
  tauto

theorem initial7347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2531) ∨ (¬ (meaning t m 4609)) := by
  exact rule7347 (meaning t m 2373) (meaning t m 2531) (meaning t m 4355) (meaning t m 4434) (meaning t m 4610)

theorem rule7348 (p2373 p2531 p4355 p4434 p4610 : Prop) : (p4355) ∨ (¬ (p2531 ∧ p4355 ∧ p2373 ∧ p4610 ∧ p4434)) := by
  classical
  tauto

theorem initial7348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4355) ∨ (¬ (meaning t m 4609)) := by
  exact rule7348 (meaning t m 2373) (meaning t m 2531) (meaning t m 4355) (meaning t m 4434) (meaning t m 4610)

theorem rule7349 (p2373 p2531 p4355 p4434 p4610 : Prop) : (p2373) ∨ (¬ (p2531 ∧ p4355 ∧ p2373 ∧ p4610 ∧ p4434)) := by
  classical
  tauto

theorem initial7349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2373) ∨ (¬ (meaning t m 4609)) := by
  exact rule7349 (meaning t m 2373) (meaning t m 2531) (meaning t m 4355) (meaning t m 4434) (meaning t m 4610)

theorem rule7350 (p2373 p2531 p4355 p4434 p4610 : Prop) : (¬ (p2531 ∧ p4355 ∧ p2373 ∧ p4610 ∧ p4434)) ∨ (p4610) := by
  classical
  tauto

theorem initial7350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4609)) ∨ (meaning t m 4610) := by
  exact rule7350 (meaning t m 2373) (meaning t m 2531) (meaning t m 4355) (meaning t m 4434) (meaning t m 4610)

theorem rule7351 (p2373 p2531 p4355 p4434 p4610 : Prop) : (p4434) ∨ (¬ (p2531 ∧ p4355 ∧ p2373 ∧ p4610 ∧ p4434)) := by
  classical
  tauto

theorem initial7351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4434) ∨ (¬ (meaning t m 4609)) := by
  exact rule7351 (meaning t m 2373) (meaning t m 2531) (meaning t m 4355) (meaning t m 4434) (meaning t m 4610)

theorem rule7355 (p4606 p4609 : Prop) : (¬ (p4606 ∨ p4609)) ∨ (p4606) ∨ (p4609) := by
  classical
  tauto

theorem initial7355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4605)) ∨ (meaning t m 4606) ∨ (meaning t m 4609) := by
  exact rule7355 (meaning t m 4606) (meaning t m 4609)

theorem rule7356 (p2367 p4605 : Prop) (h : (p2367 ↔ p4605)) : (¬ p2367) ∨ (p4605) := by
  classical
  tauto

theorem initial7356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2367)) ∨ (meaning t m 4605) := by
  have source := ElevenTheory.theory1122 t (m.theta 4 5) (m.theta 4 8) (m.theta 5 8)
  exact rule7356 (meaning t m 2367) (meaning t m 4605) source

theorem rule7358 (p2190 p2563 p3880 : Prop) (h : (¬ p2563) ∨ (¬ p3880) ∨ (¬ p2190)) : (¬ p2190) ∨ (¬ p2563) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial7358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory1123 (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule7358 (meaning t m 2190) (meaning t m 2563) (meaning t m 3880) source

theorem rule7359 (p2387 p4170 p4197 p4613 p4614 : Prop) : (p4197) ∨ (¬ (p4197 ∧ p4170 ∧ p2387 ∧ p4613 ∧ p4614)) := by
  classical
  tauto

theorem initial7359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4197) ∨ (¬ (meaning t m 4612)) := by
  exact rule7359 (meaning t m 2387) (meaning t m 4170) (meaning t m 4197) (meaning t m 4613) (meaning t m 4614)

theorem rule7360 (p2387 p4170 p4197 p4613 p4614 : Prop) : (p4170) ∨ (¬ (p4197 ∧ p4170 ∧ p2387 ∧ p4613 ∧ p4614)) := by
  classical
  tauto

theorem initial7360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4170) ∨ (¬ (meaning t m 4612)) := by
  exact rule7360 (meaning t m 2387) (meaning t m 4170) (meaning t m 4197) (meaning t m 4613) (meaning t m 4614)

theorem rule7361 (p2387 p4170 p4197 p4613 p4614 : Prop) : (p2387) ∨ (¬ (p4197 ∧ p4170 ∧ p2387 ∧ p4613 ∧ p4614)) := by
  classical
  tauto

theorem initial7361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2387) ∨ (¬ (meaning t m 4612)) := by
  exact rule7361 (meaning t m 2387) (meaning t m 4170) (meaning t m 4197) (meaning t m 4613) (meaning t m 4614)

theorem rule7363 (p2387 p4170 p4197 p4613 p4614 : Prop) : (¬ (p4197 ∧ p4170 ∧ p2387 ∧ p4613 ∧ p4614)) ∨ (p4614) := by
  classical
  tauto

theorem initial7363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4612)) ∨ (meaning t m 4614) := by
  exact rule7363 (meaning t m 2387) (meaning t m 4170) (meaning t m 4197) (meaning t m 4613) (meaning t m 4614)

theorem rule7365 (p2383 p4113 p4114 p4616 p4617 : Prop) : (p4113) ∨ (¬ (p4113 ∧ p4114 ∧ p2383 ∧ p4616 ∧ p4617)) := by
  classical
  tauto

theorem initial7365 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4113) ∨ (¬ (meaning t m 4615)) := by
  exact rule7365 (meaning t m 2383) (meaning t m 4113) (meaning t m 4114) (meaning t m 4616) (meaning t m 4617)

theorem rule7366 (p2383 p4113 p4114 p4616 p4617 : Prop) : (p4114) ∨ (¬ (p4113 ∧ p4114 ∧ p2383 ∧ p4616 ∧ p4617)) := by
  classical
  tauto

theorem initial7366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4114) ∨ (¬ (meaning t m 4615)) := by
  exact rule7366 (meaning t m 2383) (meaning t m 4113) (meaning t m 4114) (meaning t m 4616) (meaning t m 4617)

theorem rule7367 (p2383 p4113 p4114 p4616 p4617 : Prop) : (p2383) ∨ (¬ (p4113 ∧ p4114 ∧ p2383 ∧ p4616 ∧ p4617)) := by
  classical
  tauto

theorem initial7367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2383) ∨ (¬ (meaning t m 4615)) := by
  exact rule7367 (meaning t m 2383) (meaning t m 4113) (meaning t m 4114) (meaning t m 4616) (meaning t m 4617)

theorem rule7369 (p2383 p4113 p4114 p4616 p4617 : Prop) : (¬ (p4113 ∧ p4114 ∧ p2383 ∧ p4616 ∧ p4617)) ∨ (p4617) := by
  classical
  tauto

theorem initial7369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4615)) ∨ (meaning t m 4617) := by
  exact rule7369 (meaning t m 2383) (meaning t m 4113) (meaning t m 4114) (meaning t m 4616) (meaning t m 4617)

theorem rule7373 (p4612 p4615 : Prop) : (¬ (p4612 ∨ p4615)) ∨ (p4612) ∨ (p4615) := by
  classical
  tauto

theorem initial7373 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4611)) ∨ (meaning t m 4612) ∨ (meaning t m 4615) := by
  exact rule7373 (meaning t m 4612) (meaning t m 4615)

theorem rule7374 (p2377 p4611 : Prop) (h : (p2377 ↔ p4611)) : (¬ p2377) ∨ (p4611) := by
  classical
  tauto

theorem initial7374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2377)) ∨ (meaning t m 4611) := by
  have source := ElevenTheory.theory1124 t (m.theta 0 6) (m.theta 0 8) (m.theta 6 8)
  exact rule7374 (meaning t m 2377) (meaning t m 4611) source

theorem rule7376 (p4025 p4107 p4396 p4620 p4621 : Prop) : (p4025) ∨ (¬ (p4025 ∧ p4396 ∧ p4107 ∧ p4620 ∧ p4621)) := by
  classical
  tauto

theorem initial7376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4025) ∨ (¬ (meaning t m 4619)) := by
  exact rule7376 (meaning t m 4025) (meaning t m 4107) (meaning t m 4396) (meaning t m 4620) (meaning t m 4621)

theorem rule7377 (p4025 p4107 p4396 p4620 p4621 : Prop) : (p4396) ∨ (¬ (p4025 ∧ p4396 ∧ p4107 ∧ p4620 ∧ p4621)) := by
  classical
  tauto

theorem initial7377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4396) ∨ (¬ (meaning t m 4619)) := by
  exact rule7377 (meaning t m 4025) (meaning t m 4107) (meaning t m 4396) (meaning t m 4620) (meaning t m 4621)

theorem rule7378 (p4025 p4107 p4396 p4620 p4621 : Prop) : (p4107) ∨ (¬ (p4025 ∧ p4396 ∧ p4107 ∧ p4620 ∧ p4621)) := by
  classical
  tauto

theorem initial7378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4107) ∨ (¬ (meaning t m 4619)) := by
  exact rule7378 (meaning t m 4025) (meaning t m 4107) (meaning t m 4396) (meaning t m 4620) (meaning t m 4621)

theorem rule7379 (p4025 p4107 p4396 p4620 p4621 : Prop) : (¬ (p4025 ∧ p4396 ∧ p4107 ∧ p4620 ∧ p4621)) ∨ (p4620) := by
  classical
  tauto

theorem initial7379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4619)) ∨ (meaning t m 4620) := by
  exact rule7379 (meaning t m 4025) (meaning t m 4107) (meaning t m 4396) (meaning t m 4620) (meaning t m 4621)

theorem rule7380 (p4025 p4107 p4396 p4620 p4621 : Prop) : (¬ (p4025 ∧ p4396 ∧ p4107 ∧ p4620 ∧ p4621)) ∨ (p4621) := by
  classical
  tauto

theorem initial7380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4619)) ∨ (meaning t m 4621) := by
  exact rule7380 (meaning t m 4025) (meaning t m 4107) (meaning t m 4396) (meaning t m 4620) (meaning t m 4621)

theorem rule7382 (p2396 p4187 p4623 p4624 p4625 : Prop) : (¬ (p4623 ∧ p4187 ∧ p2396 ∧ p4624 ∧ p4625)) ∨ (p4623) := by
  classical
  tauto

theorem initial7382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4622)) ∨ (meaning t m 4623) := by
  exact rule7382 (meaning t m 2396) (meaning t m 4187) (meaning t m 4623) (meaning t m 4624) (meaning t m 4625)

theorem rule7383 (p2396 p4187 p4623 p4624 p4625 : Prop) : (p4187) ∨ (¬ (p4623 ∧ p4187 ∧ p2396 ∧ p4624 ∧ p4625)) := by
  classical
  tauto

theorem initial7383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4187) ∨ (¬ (meaning t m 4622)) := by
  exact rule7383 (meaning t m 2396) (meaning t m 4187) (meaning t m 4623) (meaning t m 4624) (meaning t m 4625)

theorem rule7384 (p2396 p4187 p4623 p4624 p4625 : Prop) : (p2396) ∨ (¬ (p4623 ∧ p4187 ∧ p2396 ∧ p4624 ∧ p4625)) := by
  classical
  tauto

theorem initial7384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2396) ∨ (¬ (meaning t m 4622)) := by
  exact rule7384 (meaning t m 2396) (meaning t m 4187) (meaning t m 4623) (meaning t m 4624) (meaning t m 4625)

theorem rule7385 (p2396 p4187 p4623 p4624 p4625 : Prop) : (¬ (p4623 ∧ p4187 ∧ p2396 ∧ p4624 ∧ p4625)) ∨ (p4624) := by
  classical
  tauto

theorem initial7385 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4622)) ∨ (meaning t m 4624) := by
  exact rule7385 (meaning t m 2396) (meaning t m 4187) (meaning t m 4623) (meaning t m 4624) (meaning t m 4625)

theorem rule7386 (p2396 p4187 p4623 p4624 p4625 : Prop) : (¬ (p4623 ∧ p4187 ∧ p2396 ∧ p4624 ∧ p4625)) ∨ (p4625) := by
  classical
  tauto

theorem initial7386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4622)) ∨ (meaning t m 4625) := by
  exact rule7386 (meaning t m 2396) (meaning t m 4187) (meaning t m 4623) (meaning t m 4624) (meaning t m 4625)

theorem rule7390 (p4619 p4622 : Prop) : (¬ (p4619 ∨ p4622)) ∨ (p4619) ∨ (p4622) := by
  classical
  tauto

theorem initial7390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4618)) ∨ (meaning t m 4619) ∨ (meaning t m 4622) := by
  exact rule7390 (meaning t m 4619) (meaning t m 4622)

theorem rule7391 (p2390 p4618 : Prop) (h : (p2390 ↔ p4618)) : (¬ p2390) ∨ (p4618) := by
  classical
  tauto

theorem initial7391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2390)) ∨ (meaning t m 4618) := by
  have source := ElevenTheory.theory1125 t (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule7391 (meaning t m 2390) (meaning t m 4618) source

theorem rule7393 (p3238 p4034 p4202 p4628 p4629 : Prop) : (p4202) ∨ (¬ (p4202 ∧ p4034 ∧ p3238 ∧ p4628 ∧ p4629)) := by
  classical
  tauto

theorem initial7393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4202) ∨ (¬ (meaning t m 4627)) := by
  exact rule7393 (meaning t m 3238) (meaning t m 4034) (meaning t m 4202) (meaning t m 4628) (meaning t m 4629)

theorem rule7394 (p3238 p4034 p4202 p4628 p4629 : Prop) : (p4034) ∨ (¬ (p4202 ∧ p4034 ∧ p3238 ∧ p4628 ∧ p4629)) := by
  classical
  tauto

theorem initial7394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4034) ∨ (¬ (meaning t m 4627)) := by
  exact rule7394 (meaning t m 3238) (meaning t m 4034) (meaning t m 4202) (meaning t m 4628) (meaning t m 4629)

theorem rule7395 (p3238 p4034 p4202 p4628 p4629 : Prop) : (p3238) ∨ (¬ (p4202 ∧ p4034 ∧ p3238 ∧ p4628 ∧ p4629)) := by
  classical
  tauto

theorem initial7395 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3238) ∨ (¬ (meaning t m 4627)) := by
  exact rule7395 (meaning t m 3238) (meaning t m 4034) (meaning t m 4202) (meaning t m 4628) (meaning t m 4629)

theorem rule7397 (p3238 p4034 p4202 p4628 p4629 : Prop) : (¬ (p4202 ∧ p4034 ∧ p3238 ∧ p4628 ∧ p4629)) ∨ (p4629) := by
  classical
  tauto

theorem initial7397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4627)) ∨ (meaning t m 4629) := by
  exact rule7397 (meaning t m 3238) (meaning t m 4034) (meaning t m 4202) (meaning t m 4628) (meaning t m 4629)

theorem rule7399 (p2406 p3948 p4210 p4631 p4632 : Prop) : (p4210) ∨ (¬ (p4210 ∧ p3948 ∧ p2406 ∧ p4631 ∧ p4632)) := by
  classical
  tauto

theorem initial7399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4210) ∨ (¬ (meaning t m 4630)) := by
  exact rule7399 (meaning t m 2406) (meaning t m 3948) (meaning t m 4210) (meaning t m 4631) (meaning t m 4632)

theorem rule7400 (p2406 p3948 p4210 p4631 p4632 : Prop) : (p3948) ∨ (¬ (p4210 ∧ p3948 ∧ p2406 ∧ p4631 ∧ p4632)) := by
  classical
  tauto

theorem initial7400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3948) ∨ (¬ (meaning t m 4630)) := by
  exact rule7400 (meaning t m 2406) (meaning t m 3948) (meaning t m 4210) (meaning t m 4631) (meaning t m 4632)

theorem rule7401 (p2406 p3948 p4210 p4631 p4632 : Prop) : (p2406) ∨ (¬ (p4210 ∧ p3948 ∧ p2406 ∧ p4631 ∧ p4632)) := by
  classical
  tauto

theorem initial7401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2406) ∨ (¬ (meaning t m 4630)) := by
  exact rule7401 (meaning t m 2406) (meaning t m 3948) (meaning t m 4210) (meaning t m 4631) (meaning t m 4632)

theorem rule7403 (p2406 p3948 p4210 p4631 p4632 : Prop) : (¬ (p4210 ∧ p3948 ∧ p2406 ∧ p4631 ∧ p4632)) ∨ (p4632) := by
  classical
  tauto

theorem initial7403 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4630)) ∨ (meaning t m 4632) := by
  exact rule7403 (meaning t m 2406) (meaning t m 3948) (meaning t m 4210) (meaning t m 4631) (meaning t m 4632)

theorem rule7407 (p4627 p4630 : Prop) : (¬ (p4627 ∨ p4630)) ∨ (p4627) ∨ (p4630) := by
  classical
  tauto

theorem initial7407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4626)) ∨ (meaning t m 4627) ∨ (meaning t m 4630) := by
  exact rule7407 (meaning t m 4627) (meaning t m 4630)

theorem rule7408 (p2400 p4626 : Prop) (h : (p2400 ↔ p4626)) : (¬ p2400) ∨ (p4626) := by
  classical
  tauto

theorem initial7408 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2400)) ∨ (meaning t m 4626) := by
  have source := ElevenTheory.theory1126 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 5)
  exact rule7408 (meaning t m 2400) (meaning t m 4626) source

theorem rule7410 (p4278 p4635 p4636 p4637 p4638 : Prop) : (¬ (p4635 ∧ p4636 ∧ p4278 ∧ p4637 ∧ p4638)) ∨ (p4635) := by
  classical
  tauto

theorem initial7410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4634)) ∨ (meaning t m 4635) := by
  exact rule7410 (meaning t m 4278) (meaning t m 4635) (meaning t m 4636) (meaning t m 4637) (meaning t m 4638)

theorem rule7411 (p4278 p4635 p4636 p4637 p4638 : Prop) : (¬ (p4635 ∧ p4636 ∧ p4278 ∧ p4637 ∧ p4638)) ∨ (p4636) := by
  classical
  tauto

theorem initial7411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4634)) ∨ (meaning t m 4636) := by
  exact rule7411 (meaning t m 4278) (meaning t m 4635) (meaning t m 4636) (meaning t m 4637) (meaning t m 4638)

theorem rule7412 (p4278 p4635 p4636 p4637 p4638 : Prop) : (p4278) ∨ (¬ (p4635 ∧ p4636 ∧ p4278 ∧ p4637 ∧ p4638)) := by
  classical
  tauto

theorem initial7412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4278) ∨ (¬ (meaning t m 4634)) := by
  exact rule7412 (meaning t m 4278) (meaning t m 4635) (meaning t m 4636) (meaning t m 4637) (meaning t m 4638)

theorem rule7413 (p4278 p4635 p4636 p4637 p4638 : Prop) : (¬ (p4635 ∧ p4636 ∧ p4278 ∧ p4637 ∧ p4638)) ∨ (p4637) := by
  classical
  tauto

theorem initial7413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4634)) ∨ (meaning t m 4637) := by
  exact rule7413 (meaning t m 4278) (meaning t m 4635) (meaning t m 4636) (meaning t m 4637) (meaning t m 4638)

theorem rule7414 (p4278 p4635 p4636 p4637 p4638 : Prop) : (¬ (p4635 ∧ p4636 ∧ p4278 ∧ p4637 ∧ p4638)) ∨ (p4638) := by
  classical
  tauto

theorem initial7414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4634)) ∨ (meaning t m 4638) := by
  exact rule7414 (meaning t m 4278) (meaning t m 4635) (meaning t m 4636) (meaning t m 4637) (meaning t m 4638)

theorem rule7416 (p2417 p3192 p4451 p4640 p4641 : Prop) : (p4451) ∨ (¬ (p4451 ∧ p3192 ∧ p2417 ∧ p4640 ∧ p4641)) := by
  classical
  tauto

theorem initial7416 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4451) ∨ (¬ (meaning t m 4639)) := by
  exact rule7416 (meaning t m 2417) (meaning t m 3192) (meaning t m 4451) (meaning t m 4640) (meaning t m 4641)

theorem rule7417 (p2417 p3192 p4451 p4640 p4641 : Prop) : (p3192) ∨ (¬ (p4451 ∧ p3192 ∧ p2417 ∧ p4640 ∧ p4641)) := by
  classical
  tauto

theorem initial7417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3192) ∨ (¬ (meaning t m 4639)) := by
  exact rule7417 (meaning t m 2417) (meaning t m 3192) (meaning t m 4451) (meaning t m 4640) (meaning t m 4641)

theorem rule7418 (p2417 p3192 p4451 p4640 p4641 : Prop) : (p2417) ∨ (¬ (p4451 ∧ p3192 ∧ p2417 ∧ p4640 ∧ p4641)) := by
  classical
  tauto

theorem initial7418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2417) ∨ (¬ (meaning t m 4639)) := by
  exact rule7418 (meaning t m 2417) (meaning t m 3192) (meaning t m 4451) (meaning t m 4640) (meaning t m 4641)

theorem rule7419 (p2417 p3192 p4451 p4640 p4641 : Prop) : (¬ (p4451 ∧ p3192 ∧ p2417 ∧ p4640 ∧ p4641)) ∨ (p4640) := by
  classical
  tauto

theorem initial7419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4639)) ∨ (meaning t m 4640) := by
  exact rule7419 (meaning t m 2417) (meaning t m 3192) (meaning t m 4451) (meaning t m 4640) (meaning t m 4641)

theorem rule7420 (p2417 p3192 p4451 p4640 p4641 : Prop) : (¬ (p4451 ∧ p3192 ∧ p2417 ∧ p4640 ∧ p4641)) ∨ (p4641) := by
  classical
  tauto

theorem initial7420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4639)) ∨ (meaning t m 4641) := by
  exact rule7420 (meaning t m 2417) (meaning t m 3192) (meaning t m 4451) (meaning t m 4640) (meaning t m 4641)

theorem rule7424 (p4634 p4639 : Prop) : (¬ (p4634 ∨ p4639)) ∨ (p4634) ∨ (p4639) := by
  classical
  tauto

theorem initial7424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4633)) ∨ (meaning t m 4634) ∨ (meaning t m 4639) := by
  exact rule7424 (meaning t m 4634) (meaning t m 4639)

theorem rule7425 (p2411 p4633 : Prop) (h : (p2411 ↔ p4633)) : (¬ p2411) ∨ (p4633) := by
  classical
  tauto

theorem initial7425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2411)) ∨ (meaning t m 4633) := by
  have source := ElevenTheory.theory1127 t (m.theta 4 7) (m.theta 4 9) (m.theta 7 9)
  exact rule7425 (meaning t m 2411) (meaning t m 4633) source

theorem rule7427 (p2441 p4001 p4235 p4277 p4644 : Prop) : (p2441) ∨ (¬ (p2441 ∧ p4001 ∧ p4235 ∧ p4644 ∧ p4277)) := by
  classical
  tauto

theorem initial7427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2441) ∨ (¬ (meaning t m 4643)) := by
  exact rule7427 (meaning t m 2441) (meaning t m 4001) (meaning t m 4235) (meaning t m 4277) (meaning t m 4644)

theorem rule7428 (p2441 p4001 p4235 p4277 p4644 : Prop) : (p4001) ∨ (¬ (p2441 ∧ p4001 ∧ p4235 ∧ p4644 ∧ p4277)) := by
  classical
  tauto

theorem initial7428 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4001) ∨ (¬ (meaning t m 4643)) := by
  exact rule7428 (meaning t m 2441) (meaning t m 4001) (meaning t m 4235) (meaning t m 4277) (meaning t m 4644)

theorem rule7429 (p2441 p4001 p4235 p4277 p4644 : Prop) : (p4235) ∨ (¬ (p2441 ∧ p4001 ∧ p4235 ∧ p4644 ∧ p4277)) := by
  classical
  tauto

theorem initial7429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4235) ∨ (¬ (meaning t m 4643)) := by
  exact rule7429 (meaning t m 2441) (meaning t m 4001) (meaning t m 4235) (meaning t m 4277) (meaning t m 4644)

theorem rule7430 (p2441 p4001 p4235 p4277 p4644 : Prop) : (¬ (p2441 ∧ p4001 ∧ p4235 ∧ p4644 ∧ p4277)) ∨ (p4644) := by
  classical
  tauto

theorem initial7430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4643)) ∨ (meaning t m 4644) := by
  exact rule7430 (meaning t m 2441) (meaning t m 4001) (meaning t m 4235) (meaning t m 4277) (meaning t m 4644)

theorem rule7431 (p2441 p4001 p4235 p4277 p4644 : Prop) : (p4277) ∨ (¬ (p2441 ∧ p4001 ∧ p4235 ∧ p4644 ∧ p4277)) := by
  classical
  tauto

theorem initial7431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4277) ∨ (¬ (meaning t m 4643)) := by
  exact rule7431 (meaning t m 2441) (meaning t m 4001) (meaning t m 4235) (meaning t m 4277) (meaning t m 4644)

theorem rule7433 (p2427 p3569 p3741 p4646 p4647 : Prop) : (p3569) ∨ (¬ (p3569 ∧ p3741 ∧ p2427 ∧ p4646 ∧ p4647)) := by
  classical
  tauto

theorem initial7433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3569) ∨ (¬ (meaning t m 4645)) := by
  exact rule7433 (meaning t m 2427) (meaning t m 3569) (meaning t m 3741) (meaning t m 4646) (meaning t m 4647)

theorem rule7434 (p2427 p3569 p3741 p4646 p4647 : Prop) : (p3741) ∨ (¬ (p3569 ∧ p3741 ∧ p2427 ∧ p4646 ∧ p4647)) := by
  classical
  tauto

theorem initial7434 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3741) ∨ (¬ (meaning t m 4645)) := by
  exact rule7434 (meaning t m 2427) (meaning t m 3569) (meaning t m 3741) (meaning t m 4646) (meaning t m 4647)

theorem rule7435 (p2427 p3569 p3741 p4646 p4647 : Prop) : (p2427) ∨ (¬ (p3569 ∧ p3741 ∧ p2427 ∧ p4646 ∧ p4647)) := by
  classical
  tauto

theorem initial7435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2427) ∨ (¬ (meaning t m 4645)) := by
  exact rule7435 (meaning t m 2427) (meaning t m 3569) (meaning t m 3741) (meaning t m 4646) (meaning t m 4647)

theorem rule7436 (p2427 p3569 p3741 p4646 p4647 : Prop) : (¬ (p3569 ∧ p3741 ∧ p2427 ∧ p4646 ∧ p4647)) ∨ (p4646) := by
  classical
  tauto

theorem initial7436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4645)) ∨ (meaning t m 4646) := by
  exact rule7436 (meaning t m 2427) (meaning t m 3569) (meaning t m 3741) (meaning t m 4646) (meaning t m 4647)

theorem rule7437 (p2427 p3569 p3741 p4646 p4647 : Prop) : (¬ (p3569 ∧ p3741 ∧ p2427 ∧ p4646 ∧ p4647)) ∨ (p4647) := by
  classical
  tauto

theorem initial7437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4645)) ∨ (meaning t m 4647) := by
  exact rule7437 (meaning t m 2427) (meaning t m 3569) (meaning t m 3741) (meaning t m 4646) (meaning t m 4647)

theorem rule7441 (p4643 p4645 : Prop) : (¬ (p4643 ∨ p4645)) ∨ (p4643) ∨ (p4645) := by
  classical
  tauto

theorem initial7441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4642)) ∨ (meaning t m 4643) ∨ (meaning t m 4645) := by
  exact rule7441 (meaning t m 4643) (meaning t m 4645)

theorem rule7442 (p2421 p4642 : Prop) (h : (p2421 ↔ p4642)) : (¬ p2421) ∨ (p4642) := by
  classical
  tauto

theorem initial7442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2421)) ∨ (meaning t m 4642) := by
  have source := ElevenTheory.theory1128 t (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule7442 (meaning t m 2421) (meaning t m 4642) source

theorem rule7444 (p2027 p2440 p2449 p3580 p4278 p4646 : Prop) (h : p2027 ∨ (¬ p3580) ∨ (¬ p2440) ∨ (¬ p4278) ∨ (¬ p4646) ∨ (¬ p2449)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2449) ∨ (¬ p3580) ∨ (¬ p4278) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial7444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory1129 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule7444 (meaning t m 2027) (meaning t m 2440) (meaning t m 2449) (meaning t m 3580) (meaning t m 4278) (meaning t m 4646) source

theorem rule7445 (p3740 p3742 p4112 p4327 p4650 : Prop) : (p4112) ∨ (¬ (p4112 ∧ p3740 ∧ p3742 ∧ p4650 ∧ p4327)) := by
  classical
  tauto

theorem initial7445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4112) ∨ (¬ (meaning t m 4649)) := by
  exact rule7445 (meaning t m 3740) (meaning t m 3742) (meaning t m 4112) (meaning t m 4327) (meaning t m 4650)

theorem rule7446 (p3740 p3742 p4112 p4327 p4650 : Prop) : (p3740) ∨ (¬ (p4112 ∧ p3740 ∧ p3742 ∧ p4650 ∧ p4327)) := by
  classical
  tauto

theorem initial7446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3740) ∨ (¬ (meaning t m 4649)) := by
  exact rule7446 (meaning t m 3740) (meaning t m 3742) (meaning t m 4112) (meaning t m 4327) (meaning t m 4650)

theorem rule7447 (p3740 p3742 p4112 p4327 p4650 : Prop) : (p3742) ∨ (¬ (p4112 ∧ p3740 ∧ p3742 ∧ p4650 ∧ p4327)) := by
  classical
  tauto

theorem initial7447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3742) ∨ (¬ (meaning t m 4649)) := by
  exact rule7447 (meaning t m 3740) (meaning t m 3742) (meaning t m 4112) (meaning t m 4327) (meaning t m 4650)

theorem rule7448 (p3740 p3742 p4112 p4327 p4650 : Prop) : (¬ (p4112 ∧ p3740 ∧ p3742 ∧ p4650 ∧ p4327)) ∨ (p4650) := by
  classical
  tauto

theorem initial7448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4649)) ∨ (meaning t m 4650) := by
  exact rule7448 (meaning t m 3740) (meaning t m 3742) (meaning t m 4112) (meaning t m 4327) (meaning t m 4650)

theorem rule7449 (p3740 p3742 p4112 p4327 p4650 : Prop) : (p4327) ∨ (¬ (p4112 ∧ p3740 ∧ p3742 ∧ p4650 ∧ p4327)) := by
  classical
  tauto

theorem initial7449 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4327) ∨ (¬ (meaning t m 4649)) := by
  exact rule7449 (meaning t m 3740) (meaning t m 3742) (meaning t m 4112) (meaning t m 4327) (meaning t m 4650)

theorem rule7451 (p2437 p3579 p3580 p4652 p4653 : Prop) : (p3579) ∨ (¬ (p3579 ∧ p3580 ∧ p2437 ∧ p4652 ∧ p4653)) := by
  classical
  tauto

theorem initial7451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3579) ∨ (¬ (meaning t m 4651)) := by
  exact rule7451 (meaning t m 2437) (meaning t m 3579) (meaning t m 3580) (meaning t m 4652) (meaning t m 4653)

theorem rule7452 (p2437 p3579 p3580 p4652 p4653 : Prop) : (p3580) ∨ (¬ (p3579 ∧ p3580 ∧ p2437 ∧ p4652 ∧ p4653)) := by
  classical
  tauto

theorem initial7452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3580) ∨ (¬ (meaning t m 4651)) := by
  exact rule7452 (meaning t m 2437) (meaning t m 3579) (meaning t m 3580) (meaning t m 4652) (meaning t m 4653)

theorem rule7453 (p2437 p3579 p3580 p4652 p4653 : Prop) : (p2437) ∨ (¬ (p3579 ∧ p3580 ∧ p2437 ∧ p4652 ∧ p4653)) := by
  classical
  tauto

theorem initial7453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2437) ∨ (¬ (meaning t m 4651)) := by
  exact rule7453 (meaning t m 2437) (meaning t m 3579) (meaning t m 3580) (meaning t m 4652) (meaning t m 4653)

theorem rule7454 (p2437 p3579 p3580 p4652 p4653 : Prop) : (¬ (p3579 ∧ p3580 ∧ p2437 ∧ p4652 ∧ p4653)) ∨ (p4652) := by
  classical
  tauto

theorem initial7454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4651)) ∨ (meaning t m 4652) := by
  exact rule7454 (meaning t m 2437) (meaning t m 3579) (meaning t m 3580) (meaning t m 4652) (meaning t m 4653)

theorem rule7455 (p2437 p3579 p3580 p4652 p4653 : Prop) : (¬ (p3579 ∧ p3580 ∧ p2437 ∧ p4652 ∧ p4653)) ∨ (p4653) := by
  classical
  tauto

theorem initial7455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4651)) ∨ (meaning t m 4653) := by
  exact rule7455 (meaning t m 2437) (meaning t m 3579) (meaning t m 3580) (meaning t m 4652) (meaning t m 4653)

theorem rule7459 (p4649 p4651 : Prop) : (¬ (p4649 ∨ p4651)) ∨ (p4649) ∨ (p4651) := by
  classical
  tauto

theorem initial7459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4648)) ∨ (meaning t m 4649) ∨ (meaning t m 4651) := by
  exact rule7459 (meaning t m 4649) (meaning t m 4651)

theorem rule7460 (p2431 p4648 : Prop) (h : (p2431 ↔ p4648)) : (¬ p2431) ∨ (p4648) := by
  classical
  tauto

theorem initial7460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2431)) ∨ (meaning t m 4648) := by
  have source := ElevenTheory.theory1130 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule7460 (meaning t m 2431) (meaning t m 4648) source

theorem rule7462 (p3947 p4429 p4656 p4657 p4658 : Prop) : (p4429) ∨ (¬ (p4429 ∧ p4656 ∧ p3947 ∧ p4657 ∧ p4658)) := by
  classical
  tauto

theorem initial7462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4429) ∨ (¬ (meaning t m 4655)) := by
  exact rule7462 (meaning t m 3947) (meaning t m 4429) (meaning t m 4656) (meaning t m 4657) (meaning t m 4658)

theorem rule7463 (p3947 p4429 p4656 p4657 p4658 : Prop) : (¬ (p4429 ∧ p4656 ∧ p3947 ∧ p4657 ∧ p4658)) ∨ (p4656) := by
  classical
  tauto

theorem initial7463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4655)) ∨ (meaning t m 4656) := by
  exact rule7463 (meaning t m 3947) (meaning t m 4429) (meaning t m 4656) (meaning t m 4657) (meaning t m 4658)

theorem rule7464 (p3947 p4429 p4656 p4657 p4658 : Prop) : (p3947) ∨ (¬ (p4429 ∧ p4656 ∧ p3947 ∧ p4657 ∧ p4658)) := by
  classical
  tauto

theorem initial7464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3947) ∨ (¬ (meaning t m 4655)) := by
  exact rule7464 (meaning t m 3947) (meaning t m 4429) (meaning t m 4656) (meaning t m 4657) (meaning t m 4658)

theorem rule7466 (p3947 p4429 p4656 p4657 p4658 : Prop) : (¬ (p4429 ∧ p4656 ∧ p3947 ∧ p4657 ∧ p4658)) ∨ (p4658) := by
  classical
  tauto

theorem initial7466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4655)) ∨ (meaning t m 4658) := by
  exact rule7466 (meaning t m 3947) (meaning t m 4429) (meaning t m 4656) (meaning t m 4657) (meaning t m 4658)

theorem rule7468 (p2449 p4660 p4661 p4662 p4663 : Prop) : (¬ (p4660 ∧ p4661 ∧ p2449 ∧ p4662 ∧ p4663)) ∨ (p4660) := by
  classical
  tauto

theorem initial7468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4659)) ∨ (meaning t m 4660) := by
  exact rule7468 (meaning t m 2449) (meaning t m 4660) (meaning t m 4661) (meaning t m 4662) (meaning t m 4663)

theorem rule7469 (p2449 p4660 p4661 p4662 p4663 : Prop) : (¬ (p4660 ∧ p4661 ∧ p2449 ∧ p4662 ∧ p4663)) ∨ (p4661) := by
  classical
  tauto

theorem initial7469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4659)) ∨ (meaning t m 4661) := by
  exact rule7469 (meaning t m 2449) (meaning t m 4660) (meaning t m 4661) (meaning t m 4662) (meaning t m 4663)

theorem rule7470 (p2449 p4660 p4661 p4662 p4663 : Prop) : (p2449) ∨ (¬ (p4660 ∧ p4661 ∧ p2449 ∧ p4662 ∧ p4663)) := by
  classical
  tauto

theorem initial7470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2449) ∨ (¬ (meaning t m 4659)) := by
  exact rule7470 (meaning t m 2449) (meaning t m 4660) (meaning t m 4661) (meaning t m 4662) (meaning t m 4663)

theorem rule7476 (p4655 p4659 : Prop) : (¬ (p4655 ∨ p4659)) ∨ (p4655) ∨ (p4659) := by
  classical
  tauto

theorem initial7476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4654)) ∨ (meaning t m 4655) ∨ (meaning t m 4659) := by
  exact rule7476 (meaning t m 4655) (meaning t m 4659)

theorem rule7477 (p2443 p4654 : Prop) (h : (p2443 ↔ p4654)) : (¬ p2443) ∨ (p4654) := by
  classical
  tauto

theorem initial7477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2443)) ∨ (meaning t m 4654) := by
  have source := ElevenTheory.theory1131 t (m.theta 3 7) (m.theta 3 9) (m.theta 7 9)
  exact rule7477 (meaning t m 2443) (meaning t m 4654) source

theorem rule7479 (p3657 p3950 p4348 p4445 p4666 : Prop) : (p3657) ∨ (¬ (p3657 ∧ p4445 ∧ p4348 ∧ p4666 ∧ p3950)) := by
  classical
  tauto

theorem initial7479 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3657) ∨ (¬ (meaning t m 4665)) := by
  exact rule7479 (meaning t m 3657) (meaning t m 3950) (meaning t m 4348) (meaning t m 4445) (meaning t m 4666)

theorem rule7480 (p3657 p3950 p4348 p4445 p4666 : Prop) : (p4445) ∨ (¬ (p3657 ∧ p4445 ∧ p4348 ∧ p4666 ∧ p3950)) := by
  classical
  tauto

theorem initial7480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4445) ∨ (¬ (meaning t m 4665)) := by
  exact rule7480 (meaning t m 3657) (meaning t m 3950) (meaning t m 4348) (meaning t m 4445) (meaning t m 4666)

theorem rule7481 (p3657 p3950 p4348 p4445 p4666 : Prop) : (p4348) ∨ (¬ (p3657 ∧ p4445 ∧ p4348 ∧ p4666 ∧ p3950)) := by
  classical
  tauto

theorem initial7481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4348) ∨ (¬ (meaning t m 4665)) := by
  exact rule7481 (meaning t m 3657) (meaning t m 3950) (meaning t m 4348) (meaning t m 4445) (meaning t m 4666)

theorem rule7482 (p3657 p3950 p4348 p4445 p4666 : Prop) : (¬ (p3657 ∧ p4445 ∧ p4348 ∧ p4666 ∧ p3950)) ∨ (p4666) := by
  classical
  tauto

theorem initial7482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4665)) ∨ (meaning t m 4666) := by
  exact rule7482 (meaning t m 3657) (meaning t m 3950) (meaning t m 4348) (meaning t m 4445) (meaning t m 4666)

theorem rule7483 (p3657 p3950 p4348 p4445 p4666 : Prop) : (p3950) ∨ (¬ (p3657 ∧ p4445 ∧ p4348 ∧ p4666 ∧ p3950)) := by
  classical
  tauto

theorem initial7483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3950) ∨ (¬ (meaning t m 4665)) := by
  exact rule7483 (meaning t m 3657) (meaning t m 3950) (meaning t m 4348) (meaning t m 4445) (meaning t m 4666)

theorem rule7485 (p2459 p3945 p4443 p4668 p4669 : Prop) : (p4443) ∨ (¬ (p4443 ∧ p3945 ∧ p2459 ∧ p4668 ∧ p4669)) := by
  classical
  tauto

theorem initial7485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4443) ∨ (¬ (meaning t m 4667)) := by
  exact rule7485 (meaning t m 2459) (meaning t m 3945) (meaning t m 4443) (meaning t m 4668) (meaning t m 4669)

theorem rule7486 (p2459 p3945 p4443 p4668 p4669 : Prop) : (p3945) ∨ (¬ (p4443 ∧ p3945 ∧ p2459 ∧ p4668 ∧ p4669)) := by
  classical
  tauto

theorem initial7486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3945) ∨ (¬ (meaning t m 4667)) := by
  exact rule7486 (meaning t m 2459) (meaning t m 3945) (meaning t m 4443) (meaning t m 4668) (meaning t m 4669)

theorem rule7487 (p2459 p3945 p4443 p4668 p4669 : Prop) : (p2459) ∨ (¬ (p4443 ∧ p3945 ∧ p2459 ∧ p4668 ∧ p4669)) := by
  classical
  tauto

theorem initial7487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2459) ∨ (¬ (meaning t m 4667)) := by
  exact rule7487 (meaning t m 2459) (meaning t m 3945) (meaning t m 4443) (meaning t m 4668) (meaning t m 4669)

theorem rule7488 (p2459 p3945 p4443 p4668 p4669 : Prop) : (¬ (p4443 ∧ p3945 ∧ p2459 ∧ p4668 ∧ p4669)) ∨ (p4668) := by
  classical
  tauto

theorem initial7488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4667)) ∨ (meaning t m 4668) := by
  exact rule7488 (meaning t m 2459) (meaning t m 3945) (meaning t m 4443) (meaning t m 4668) (meaning t m 4669)

theorem rule7489 (p2459 p3945 p4443 p4668 p4669 : Prop) : (¬ (p4443 ∧ p3945 ∧ p2459 ∧ p4668 ∧ p4669)) ∨ (p4669) := by
  classical
  tauto

theorem initial7489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4667)) ∨ (meaning t m 4669) := by
  exact rule7489 (meaning t m 2459) (meaning t m 3945) (meaning t m 4443) (meaning t m 4668) (meaning t m 4669)

theorem rule7493 (p4665 p4667 : Prop) : (¬ (p4665 ∨ p4667)) ∨ (p4665) ∨ (p4667) := by
  classical
  tauto

theorem initial7493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4664)) ∨ (meaning t m 4665) ∨ (meaning t m 4667) := by
  exact rule7493 (meaning t m 4665) (meaning t m 4667)

theorem rule7494 (p2453 p4664 : Prop) (h : (p2453 ↔ p4664)) : (¬ p2453) ∨ (p4664) := by
  classical
  tauto

theorem initial7494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2453)) ∨ (meaning t m 4664) := by
  have source := ElevenTheory.theory1132 t (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule7494 (meaning t m 2453) (meaning t m 4664) source

theorem rule7498 (p2473 p2480 : Prop) : (p2473) ∨ (p2480) ∨ (¬ (p2473 ∨ p2480)) := by
  classical
  tauto

theorem initial7498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2473) ∨ (meaning t m 2480) ∨ (¬ (meaning t m 4670)) := by
  exact rule7498 (meaning t m 2473) (meaning t m 2480)

theorem rule7499 (p2464 p4670 : Prop) (h : (p2464 ↔ p4670)) : (¬ p2464) ∨ (p4670) := by
  classical
  tauto

theorem initial7499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2464)) ∨ (meaning t m 4670) := by
  have source := ElevenTheory.theory1133 t (m.theta 0 4) (m.theta 0 8) (m.theta 4 8)
  exact rule7499 (meaning t m 2464) (meaning t m 4670) source

theorem rule7524 (p2496 p2503 : Prop) : (p2496) ∨ (p2503) ∨ (¬ (p2496 ∨ p2503)) := by
  classical
  tauto

theorem initial7524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2496) ∨ (meaning t m 2503) ∨ (¬ (meaning t m 4676)) := by
  exact rule7524 (meaning t m 2496) (meaning t m 2503)

theorem rule7525 (p2487 p4676 : Prop) (h : (p2487 ↔ p4676)) : (¬ p2487) ∨ (p4676) := by
  classical
  tauto

theorem initial7525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2487)) ∨ (meaning t m 4676) := by
  have source := ElevenTheory.theory1136 t (m.theta 1 4) (m.theta 1 6) (m.theta 4 6)
  exact rule7525 (meaning t m 2487) (meaning t m 4676) source

theorem rule7548 (p2509 p3453 p4370 p4684 p4685 : Prop) : (p3453) ∨ (¬ (p3453 ∧ p4370 ∧ p2509 ∧ p4684 ∧ p4685)) := by
  classical
  tauto

theorem initial7548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3453) ∨ (¬ (meaning t m 4683)) := by
  exact rule7548 (meaning t m 2509) (meaning t m 3453) (meaning t m 4370) (meaning t m 4684) (meaning t m 4685)

theorem rule7549 (p2509 p3453 p4370 p4684 p4685 : Prop) : (p4370) ∨ (¬ (p3453 ∧ p4370 ∧ p2509 ∧ p4684 ∧ p4685)) := by
  classical
  tauto

theorem initial7549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4370) ∨ (¬ (meaning t m 4683)) := by
  exact rule7549 (meaning t m 2509) (meaning t m 3453) (meaning t m 4370) (meaning t m 4684) (meaning t m 4685)

theorem rule7550 (p2509 p3453 p4370 p4684 p4685 : Prop) : (p2509) ∨ (¬ (p3453 ∧ p4370 ∧ p2509 ∧ p4684 ∧ p4685)) := by
  classical
  tauto

theorem initial7550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2509) ∨ (¬ (meaning t m 4683)) := by
  exact rule7550 (meaning t m 2509) (meaning t m 3453) (meaning t m 4370) (meaning t m 4684) (meaning t m 4685)

theorem rule7551 (p2509 p3453 p4370 p4684 p4685 : Prop) : (¬ (p3453 ∧ p4370 ∧ p2509 ∧ p4684 ∧ p4685)) ∨ (p4684) := by
  classical
  tauto

theorem initial7551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4683)) ∨ (meaning t m 4684) := by
  exact rule7551 (meaning t m 2509) (meaning t m 3453) (meaning t m 4370) (meaning t m 4684) (meaning t m 4685)

theorem rule7552 (p2509 p3453 p4370 p4684 p4685 : Prop) : (¬ (p3453 ∧ p4370 ∧ p2509 ∧ p4684 ∧ p4685)) ∨ (p4685) := by
  classical
  tauto

theorem initial7552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4683)) ∨ (meaning t m 4685) := by
  exact rule7552 (meaning t m 2509) (meaning t m 3453) (meaning t m 4370) (meaning t m 4684) (meaning t m 4685)

theorem rule7553 (p2509 p3453 p4370 p4684 p4685 : Prop) : (¬ p2509) ∨ (¬ p3453) ∨ (¬ p4370) ∨ ((p3453 ∧ p4370 ∧ p2509 ∧ p4684 ∧ p4685)) ∨ (¬ p4684) ∨ (¬ p4685) := by
  classical
  tauto

theorem initial7553 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3453)) ∨ (¬ (meaning t m 4370)) ∨ (meaning t m 4683) ∨ (¬ (meaning t m 4684)) ∨ (¬ (meaning t m 4685)) := by
  exact rule7553 (meaning t m 2509) (meaning t m 3453) (meaning t m 4370) (meaning t m 4684) (meaning t m 4685)

theorem rule7554 (p2518 p4687 p4688 p4689 p4690 : Prop) : (¬ (p4687 ∧ p4688 ∧ p2518 ∧ p4689 ∧ p4690)) ∨ (p4687) := by
  classical
  tauto

theorem initial7554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4686)) ∨ (meaning t m 4687) := by
  exact rule7554 (meaning t m 2518) (meaning t m 4687) (meaning t m 4688) (meaning t m 4689) (meaning t m 4690)

theorem rule7555 (p2518 p4687 p4688 p4689 p4690 : Prop) : (¬ (p4687 ∧ p4688 ∧ p2518 ∧ p4689 ∧ p4690)) ∨ (p4688) := by
  classical
  tauto

theorem initial7555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4686)) ∨ (meaning t m 4688) := by
  exact rule7555 (meaning t m 2518) (meaning t m 4687) (meaning t m 4688) (meaning t m 4689) (meaning t m 4690)

theorem rule7556 (p2518 p4687 p4688 p4689 p4690 : Prop) : (p2518) ∨ (¬ (p4687 ∧ p4688 ∧ p2518 ∧ p4689 ∧ p4690)) := by
  classical
  tauto

theorem initial7556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2518) ∨ (¬ (meaning t m 4686)) := by
  exact rule7556 (meaning t m 2518) (meaning t m 4687) (meaning t m 4688) (meaning t m 4689) (meaning t m 4690)

theorem rule7558 (p2518 p4687 p4688 p4689 p4690 : Prop) : (¬ (p4687 ∧ p4688 ∧ p2518 ∧ p4689 ∧ p4690)) ∨ (p4690) := by
  classical
  tauto

theorem initial7558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4686)) ∨ (meaning t m 4690) := by
  exact rule7558 (meaning t m 2518) (meaning t m 4687) (meaning t m 4688) (meaning t m 4689) (meaning t m 4690)

theorem rule7562 (p4683 p4686 : Prop) : (¬ (p4683 ∨ p4686)) ∨ (p4683) ∨ (p4686) := by
  classical
  tauto

theorem initial7562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4682)) ∨ (meaning t m 4683) ∨ (meaning t m 4686) := by
  exact rule7562 (meaning t m 4683) (meaning t m 4686)

theorem rule7563 (p2512 p4682 : Prop) (h : (p2512 ↔ p4682)) : (¬ p2512) ∨ (p4682) := by
  classical
  tauto

theorem initial7563 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2512)) ∨ (meaning t m 4682) := by
  have source := ElevenTheory.theory1139 t (m.theta 1 4) (m.theta 1 8) (m.theta 4 8)
  exact rule7563 (meaning t m 2512) (meaning t m 4682) source

theorem rule7565 (p2534 p4045 p4332 p4440 p4693 : Prop) : (p4045) ∨ (¬ (p4045 ∧ p4440 ∧ p2534 ∧ p4693 ∧ p4332)) := by
  classical
  tauto

theorem initial7565 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4045) ∨ (¬ (meaning t m 4692)) := by
  exact rule7565 (meaning t m 2534) (meaning t m 4045) (meaning t m 4332) (meaning t m 4440) (meaning t m 4693)

theorem rule7566 (p2534 p4045 p4332 p4440 p4693 : Prop) : (p4440) ∨ (¬ (p4045 ∧ p4440 ∧ p2534 ∧ p4693 ∧ p4332)) := by
  classical
  tauto

theorem initial7566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4440) ∨ (¬ (meaning t m 4692)) := by
  exact rule7566 (meaning t m 2534) (meaning t m 4045) (meaning t m 4332) (meaning t m 4440) (meaning t m 4693)

theorem rule7567 (p2534 p4045 p4332 p4440 p4693 : Prop) : (p2534) ∨ (¬ (p4045 ∧ p4440 ∧ p2534 ∧ p4693 ∧ p4332)) := by
  classical
  tauto

theorem initial7567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2534) ∨ (¬ (meaning t m 4692)) := by
  exact rule7567 (meaning t m 2534) (meaning t m 4045) (meaning t m 4332) (meaning t m 4440) (meaning t m 4693)

theorem rule7569 (p2534 p4045 p4332 p4440 p4693 : Prop) : (p4332) ∨ (¬ (p4045 ∧ p4440 ∧ p2534 ∧ p4693 ∧ p4332)) := by
  classical
  tauto

theorem initial7569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4332) ∨ (¬ (meaning t m 4692)) := by
  exact rule7569 (meaning t m 2534) (meaning t m 4045) (meaning t m 4332) (meaning t m 4440) (meaning t m 4693)

theorem rule7571 (p2528 p3358 p4695 p4696 p4697 : Prop) : (¬ (p4695 ∧ p3358 ∧ p2528 ∧ p4696 ∧ p4697)) ∨ (p4695) := by
  classical
  tauto

theorem initial7571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4694)) ∨ (meaning t m 4695) := by
  exact rule7571 (meaning t m 2528) (meaning t m 3358) (meaning t m 4695) (meaning t m 4696) (meaning t m 4697)

end SunPrize.SMT
