import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory001
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule4317 (p950 p956 : Prop) : (¬ p950) ∨ ((p950 ∨ p956)) := by
  classical
  tauto

theorem initial4317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 950)) ∨ (meaning t m 3098) := by
  exact rule4317 (meaning t m 950) (meaning t m 956)

theorem rule4318 (p950 p956 : Prop) : (¬ p956) ∨ ((p950 ∨ p956)) := by
  classical
  tauto

theorem initial4318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 956)) ∨ (meaning t m 3098) := by
  exact rule4318 (meaning t m 950) (meaning t m 956)

theorem rule4335 (p3098 p3099 : Prop) (h : (p3098 ↔ p3099)) : (¬ p3098) ∨ (p3099) := by
  classical
  tauto

theorem initial4335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3098)) ∨ (meaning t m 3099) := by
  have source := ElevenTheory.theory207 t (m.theta 2 5) (m.theta 2 9) (m.theta 5 9)
  exact rule4335 (meaning t m 3098) (meaning t m 3099) source

theorem rule4337 (p962 p968 : Prop) : (¬ p962) ∨ ((p962 ∨ p968)) := by
  classical
  tauto

theorem initial4337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 962)) ∨ (meaning t m 3108) := by
  exact rule4337 (meaning t m 962) (meaning t m 968)

theorem rule4338 (p962 p968 : Prop) : (¬ p968) ∨ ((p962 ∨ p968)) := by
  classical
  tauto

theorem initial4338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 968)) ∨ (meaning t m 3108) := by
  exact rule4338 (meaning t m 962) (meaning t m 968)

theorem rule4355 (p3108 p3109 : Prop) (h : (p3108 ↔ p3109)) : (¬ p3108) ∨ (p3109) := by
  classical
  tauto

theorem initial4355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3108)) ∨ (meaning t m 3109) := by
  have source := ElevenTheory.theory208 t (m.theta 3 5) (m.theta 3 9) (m.theta 5 9)
  exact rule4355 (meaning t m 3108) (meaning t m 3109) source

theorem rule4357 (p974 p980 : Prop) : (¬ p974) ∨ ((p974 ∨ p980)) := by
  classical
  tauto

theorem initial4357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 974)) ∨ (meaning t m 3118) := by
  exact rule4357 (meaning t m 974) (meaning t m 980)

theorem rule4358 (p974 p980 : Prop) : (¬ p980) ∨ ((p974 ∨ p980)) := by
  classical
  tauto

theorem initial4358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 980)) ∨ (meaning t m 3118) := by
  exact rule4358 (meaning t m 974) (meaning t m 980)

theorem rule4375 (p3118 p3119 : Prop) (h : (p3118 ↔ p3119)) : (¬ p3118) ∨ (p3119) := by
  classical
  tauto

theorem initial4375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3118)) ∨ (meaning t m 3119) := by
  have source := ElevenTheory.theory209 t (m.theta 5 6) (m.theta 5 9) (m.theta 6 9)
  exact rule4375 (meaning t m 3118) (meaning t m 3119) source

theorem rule4377 (p2058 p3128 : Prop) (h : ((¬ p2058) ↔ (¬ p3128))) : (p2058) ∨ (¬ p3128) := by
  classical
  tauto

theorem initial4377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2058) ∨ (¬ (meaning t m 3128)) := by
  have source := ElevenTheory.theory210 t (m.theta 6 9)
  exact rule4377 (meaning t m 2058) (meaning t m 3128) source

theorem rule4379 (p986 p992 : Prop) : (¬ p986) ∨ ((p986 ∨ p992)) := by
  classical
  tauto

theorem initial4379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 986)) ∨ (meaning t m 3129) := by
  exact rule4379 (meaning t m 986) (meaning t m 992)

theorem rule4380 (p986 p992 : Prop) : (¬ p992) ∨ ((p986 ∨ p992)) := by
  classical
  tauto

theorem initial4380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 992)) ∨ (meaning t m 3129) := by
  exact rule4380 (meaning t m 986) (meaning t m 992)

theorem rule4397 (p3129 p3130 : Prop) (h : (p3129 ↔ p3130)) : (¬ p3129) ∨ (p3130) := by
  classical
  tauto

theorem initial4397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3129)) ∨ (meaning t m 3130) := by
  have source := ElevenTheory.theory211 t (m.theta 2 3) (m.theta 2 5) (m.theta 3 5)
  exact rule4397 (meaning t m 3129) (meaning t m 3130) source

theorem rule4399 (p998 p1004 : Prop) : (¬ p998) ∨ ((p998 ∨ p1004)) := by
  classical
  tauto

theorem initial4399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 998)) ∨ (meaning t m 3139) := by
  exact rule4399 (meaning t m 998) (meaning t m 1004)

theorem rule4400 (p998 p1004 : Prop) : (¬ p1004) ∨ ((p998 ∨ p1004)) := by
  classical
  tauto

theorem initial4400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1004)) ∨ (meaning t m 3139) := by
  exact rule4400 (meaning t m 998) (meaning t m 1004)

theorem rule4417 (p3139 p3140 : Prop) (h : (p3139 ↔ p3140)) : (¬ p3139) ∨ (p3140) := by
  classical
  tauto

theorem initial4417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3139)) ∨ (meaning t m 3140) := by
  have source := ElevenTheory.theory212 t (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule4417 (meaning t m 3139) (meaning t m 3140) source

theorem rule4419 (p1010 p1016 : Prop) : (¬ p1010) ∨ ((p1010 ∨ p1016)) := by
  classical
  tauto

theorem initial4419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1010)) ∨ (meaning t m 3149) := by
  exact rule4419 (meaning t m 1010) (meaning t m 1016)

theorem rule4420 (p1010 p1016 : Prop) : (¬ p1016) ∨ ((p1010 ∨ p1016)) := by
  classical
  tauto

theorem initial4420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1016)) ∨ (meaning t m 3149) := by
  exact rule4420 (meaning t m 1010) (meaning t m 1016)

theorem rule4437 (p3149 p3150 : Prop) (h : (p3149 ↔ p3150)) : (¬ p3149) ∨ (p3150) := by
  classical
  tauto

theorem initial4437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3149)) ∨ (meaning t m 3150) := by
  have source := ElevenTheory.theory213 t (m.theta 3 5) (m.theta 3 8) (m.theta 5 8)
  exact rule4437 (meaning t m 3149) (meaning t m 3150) source

theorem rule4439 (p1022 p1028 : Prop) : (¬ p1022) ∨ ((p1022 ∨ p1028)) := by
  classical
  tauto

theorem initial4439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1022)) ∨ (meaning t m 3159) := by
  exact rule4439 (meaning t m 1022) (meaning t m 1028)

theorem rule4440 (p1022 p1028 : Prop) : (¬ p1028) ∨ ((p1022 ∨ p1028)) := by
  classical
  tauto

theorem initial4440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1028)) ∨ (meaning t m 3159) := by
  exact rule4440 (meaning t m 1022) (meaning t m 1028)

theorem rule4457 (p3159 p3160 : Prop) (h : (p3159 ↔ p3160)) : (¬ p3159) ∨ (p3160) := by
  classical
  tauto

theorem initial4457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3159)) ∨ (meaning t m 3160) := by
  have source := ElevenTheory.theory214 t (m.theta 0 3) (m.theta 0 8) (m.theta 3 8)
  exact rule4457 (meaning t m 3159) (meaning t m 3160) source

theorem rule4459 (p3170 p3171 p3172 p3173 p3174 : Prop) : (¬ (p3170 ∧ p3171 ∧ p3172 ∧ p3173 ∧ p3174)) ∨ (p3170) := by
  classical
  tauto

theorem initial4459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3169)) ∨ (meaning t m 3170) := by
  exact rule4459 (meaning t m 3170) (meaning t m 3171) (meaning t m 3172) (meaning t m 3173) (meaning t m 3174)

theorem rule4460 (p3170 p3171 p3172 p3173 p3174 : Prop) : (¬ (p3170 ∧ p3171 ∧ p3172 ∧ p3173 ∧ p3174)) ∨ (p3171) := by
  classical
  tauto

theorem initial4460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3169)) ∨ (meaning t m 3171) := by
  exact rule4460 (meaning t m 3170) (meaning t m 3171) (meaning t m 3172) (meaning t m 3173) (meaning t m 3174)

theorem rule4461 (p3170 p3171 p3172 p3173 p3174 : Prop) : (¬ (p3170 ∧ p3171 ∧ p3172 ∧ p3173 ∧ p3174)) ∨ (p3172) := by
  classical
  tauto

theorem initial4461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3169)) ∨ (meaning t m 3172) := by
  exact rule4461 (meaning t m 3170) (meaning t m 3171) (meaning t m 3172) (meaning t m 3173) (meaning t m 3174)

theorem rule4466 (p3170 p3171 p3172 p3173 p3174 : Prop) : (p3171) ∨ (((¬ p3173) ∨ (¬ p3171) ∨ (¬ p3174) ∨ (¬ p3170) ∨ (¬ p3172))) := by
  classical
  tauto

theorem initial4466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3171) ∨ (meaning t m 3175) := by
  exact rule4466 (meaning t m 3170) (meaning t m 3171) (meaning t m 3172) (meaning t m 3173) (meaning t m 3174)

theorem rule4468 (p3170 p3171 p3172 p3173 p3174 : Prop) : (p3170) ∨ (((¬ p3173) ∨ (¬ p3171) ∨ (¬ p3174) ∨ (¬ p3170) ∨ (¬ p3172))) := by
  classical
  tauto

theorem initial4468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3170) ∨ (meaning t m 3175) := by
  exact rule4468 (meaning t m 3170) (meaning t m 3171) (meaning t m 3172) (meaning t m 3173) (meaning t m 3174)

theorem rule4471 (p3169 p3175 : Prop) (h : (p3169 ↔ (¬ p3175))) : (¬ p3169) ∨ (¬ p3175) := by
  classical
  tauto

theorem initial4471 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3169)) ∨ (¬ (meaning t m 3175)) := by
  have source := ElevenTheory.theory215 t (m.theta 0 3) (m.theta 0 8) (m.theta 3 8)
  exact rule4471 (meaning t m 3169) (meaning t m 3175) source

theorem rule4473 (p3166 p3177 p3178 p3179 p3180 : Prop) : (¬ (p3177 ∧ p3178 ∧ p3166 ∧ p3179 ∧ p3180)) ∨ (p3177) := by
  classical
  tauto

theorem initial4473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3176)) ∨ (meaning t m 3177) := by
  exact rule4473 (meaning t m 3166) (meaning t m 3177) (meaning t m 3178) (meaning t m 3179) (meaning t m 3180)

theorem rule4474 (p3166 p3177 p3178 p3179 p3180 : Prop) : (¬ (p3177 ∧ p3178 ∧ p3166 ∧ p3179 ∧ p3180)) ∨ (p3178) := by
  classical
  tauto

theorem initial4474 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3176)) ∨ (meaning t m 3178) := by
  exact rule4474 (meaning t m 3166) (meaning t m 3177) (meaning t m 3178) (meaning t m 3179) (meaning t m 3180)

theorem rule4475 (p3166 p3177 p3178 p3179 p3180 : Prop) : (p3166) ∨ (¬ (p3177 ∧ p3178 ∧ p3166 ∧ p3179 ∧ p3180)) := by
  classical
  tauto

theorem initial4475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3166) ∨ (¬ (meaning t m 3176)) := by
  exact rule4475 (meaning t m 3166) (meaning t m 3177) (meaning t m 3178) (meaning t m 3179) (meaning t m 3180)

theorem rule4477 (p3166 p3177 p3178 p3179 p3180 : Prop) : (¬ (p3177 ∧ p3178 ∧ p3166 ∧ p3179 ∧ p3180)) ∨ (p3180) := by
  classical
  tauto

theorem initial4477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3176)) ∨ (meaning t m 3180) := by
  exact rule4477 (meaning t m 3166) (meaning t m 3177) (meaning t m 3178) (meaning t m 3179) (meaning t m 3180)

theorem rule4480 (p3166 p3177 p3178 p3179 p3180 : Prop) : (p3178) ∨ (((¬ p3166) ∨ (¬ p3178) ∨ (¬ p3180) ∨ (¬ p3179) ∨ (¬ p3177))) := by
  classical
  tauto

theorem initial4480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3178) ∨ (meaning t m 3181) := by
  exact rule4480 (meaning t m 3166) (meaning t m 3177) (meaning t m 3178) (meaning t m 3179) (meaning t m 3180)

theorem rule4481 (p3166 p3177 p3178 p3179 p3180 : Prop) : (p3180) ∨ (((¬ p3166) ∨ (¬ p3178) ∨ (¬ p3180) ∨ (¬ p3179) ∨ (¬ p3177))) := by
  classical
  tauto

theorem initial4481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3180) ∨ (meaning t m 3181) := by
  exact rule4481 (meaning t m 3166) (meaning t m 3177) (meaning t m 3178) (meaning t m 3179) (meaning t m 3180)

theorem rule4483 (p3166 p3177 p3178 p3179 p3180 : Prop) : (p3177) ∨ (((¬ p3166) ∨ (¬ p3178) ∨ (¬ p3180) ∨ (¬ p3179) ∨ (¬ p3177))) := by
  classical
  tauto

theorem initial4483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3177) ∨ (meaning t m 3181) := by
  exact rule4483 (meaning t m 3166) (meaning t m 3177) (meaning t m 3178) (meaning t m 3179) (meaning t m 3180)

theorem rule4485 (p3176 p3181 : Prop) (h : (p3176 ↔ (¬ p3181))) : (¬ p3176) ∨ (¬ p3181) := by
  classical
  tauto

theorem initial4485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3176)) ∨ (¬ (meaning t m 3181)) := by
  have source := ElevenTheory.theory216 t (m.theta 0 3) (m.theta 0 8) (m.theta 3 8)
  exact rule4485 (meaning t m 3176) (meaning t m 3181) source

theorem rule4487 (p1034 p1040 : Prop) : (¬ p1034) ∨ ((p1034 ∨ p1040)) := by
  classical
  tauto

theorem initial4487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1034)) ∨ (meaning t m 3182) := by
  exact rule4487 (meaning t m 1034) (meaning t m 1040)

theorem rule4488 (p1034 p1040 : Prop) : (¬ p1040) ∨ ((p1034 ∨ p1040)) := by
  classical
  tauto

theorem initial4488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1040)) ∨ (meaning t m 3182) := by
  exact rule4488 (meaning t m 1034) (meaning t m 1040)

theorem rule4505 (p3182 p3183 : Prop) (h : (p3182 ↔ p3183)) : (¬ p3182) ∨ (p3183) := by
  classical
  tauto

theorem initial4505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3182)) ∨ (meaning t m 3183) := by
  have source := ElevenTheory.theory217 t (m.theta 1 3) (m.theta 1 8) (m.theta 3 8)
  exact rule4505 (meaning t m 3182) (meaning t m 3183) source

theorem rule4507 (p2922 p3192 p3193 : Prop) (h : (¬ p3192) ∨ (¬ p3193) ∨ (¬ p2922)) : (¬ p2922) ∨ (¬ p3192) ∨ (¬ p3193) := by
  classical
  tauto

theorem initial4507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3192)) ∨ (¬ (meaning t m 3193)) := by
  have source := ElevenTheory.theory218 (m.theta 1 4) (m.theta 4 7) (m.theta 4 9)
  exact rule4507 (meaning t m 2922) (meaning t m 3192) (meaning t m 3193) source

theorem rule4508 (p1046 p1052 : Prop) : (¬ p1046) ∨ ((p1046 ∨ p1052)) := by
  classical
  tauto

theorem initial4508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1046)) ∨ (meaning t m 3194) := by
  exact rule4508 (meaning t m 1046) (meaning t m 1052)

theorem rule4509 (p1046 p1052 : Prop) : (¬ p1052) ∨ ((p1046 ∨ p1052)) := by
  classical
  tauto

theorem initial4509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1052)) ∨ (meaning t m 3194) := by
  exact rule4509 (meaning t m 1046) (meaning t m 1052)

theorem rule4526 (p3194 p3195 : Prop) (h : (p3194 ↔ p3195)) : (¬ p3194) ∨ (p3195) := by
  classical
  tauto

theorem initial4526 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3194)) ∨ (meaning t m 3195) := by
  have source := ElevenTheory.theory219 t (m.theta 2 4) (m.theta 2 7) (m.theta 4 7)
  exact rule4526 (meaning t m 3194) (meaning t m 3195) source

theorem rule4529 (p1058 p1064 : Prop) : (¬ p1058) ∨ ((p1058 ∨ p1064)) := by
  classical
  tauto

theorem initial4529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1058)) ∨ (meaning t m 3205) := by
  exact rule4529 (meaning t m 1058) (meaning t m 1064)

theorem rule4530 (p1058 p1064 : Prop) : (¬ p1064) ∨ ((p1058 ∨ p1064)) := by
  classical
  tauto

theorem initial4530 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1064)) ∨ (meaning t m 3205) := by
  exact rule4530 (meaning t m 1058) (meaning t m 1064)

theorem rule4547 (p3205 p3206 : Prop) (h : (p3205 ↔ p3206)) : (¬ p3205) ∨ (p3206) := by
  classical
  tauto

theorem initial4547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3205)) ∨ (meaning t m 3206) := by
  have source := ElevenTheory.theory221 t (m.theta 0 5) (m.theta 0 9) (m.theta 5 9)
  exact rule4547 (meaning t m 3205) (meaning t m 3206) source

theorem rule4549 (p1070 p1076 : Prop) : (¬ p1070) ∨ ((p1070 ∨ p1076)) := by
  classical
  tauto

theorem initial4549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1070)) ∨ (meaning t m 3215) := by
  exact rule4549 (meaning t m 1070) (meaning t m 1076)

theorem rule4550 (p1070 p1076 : Prop) : (¬ p1076) ∨ ((p1070 ∨ p1076)) := by
  classical
  tauto

theorem initial4550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1076)) ∨ (meaning t m 3215) := by
  exact rule4550 (meaning t m 1070) (meaning t m 1076)

theorem rule4567 (p3215 p3216 : Prop) (h : (p3215 ↔ p3216)) : (¬ p3215) ∨ (p3216) := by
  classical
  tauto

theorem initial4567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3215)) ∨ (meaning t m 3216) := by
  have source := ElevenTheory.theory222 t (m.theta 1 4) (m.theta 1 9) (m.theta 4 9)
  exact rule4567 (meaning t m 3215) (meaning t m 3216) source

theorem rule4569 (p3193 p3226 p3227 p3228 p3229 : Prop) : (¬ (p3226 ∧ p3227 ∧ p3193 ∧ p3228 ∧ p3229)) ∨ (p3226) := by
  classical
  tauto

theorem initial4569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3225)) ∨ (meaning t m 3226) := by
  exact rule4569 (meaning t m 3193) (meaning t m 3226) (meaning t m 3227) (meaning t m 3228) (meaning t m 3229)

theorem rule4570 (p3193 p3226 p3227 p3228 p3229 : Prop) : (¬ (p3226 ∧ p3227 ∧ p3193 ∧ p3228 ∧ p3229)) ∨ (p3227) := by
  classical
  tauto

theorem initial4570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3225)) ∨ (meaning t m 3227) := by
  exact rule4570 (meaning t m 3193) (meaning t m 3226) (meaning t m 3227) (meaning t m 3228) (meaning t m 3229)

theorem rule4571 (p3193 p3226 p3227 p3228 p3229 : Prop) : (p3193) ∨ (¬ (p3226 ∧ p3227 ∧ p3193 ∧ p3228 ∧ p3229)) := by
  classical
  tauto

theorem initial4571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3193) ∨ (¬ (meaning t m 3225)) := by
  exact rule4571 (meaning t m 3193) (meaning t m 3226) (meaning t m 3227) (meaning t m 3228) (meaning t m 3229)

theorem rule4576 (p3193 p3226 p3227 p3228 p3229 : Prop) : (p3229) ∨ (((¬ p3228) ∨ (¬ p3229) ∨ (¬ p3193) ∨ (¬ p3227) ∨ (¬ p3226))) := by
  classical
  tauto

theorem initial4576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3229) ∨ (meaning t m 3230) := by
  exact rule4576 (meaning t m 3193) (meaning t m 3226) (meaning t m 3227) (meaning t m 3228) (meaning t m 3229)

theorem rule4578 (p3193 p3226 p3227 p3228 p3229 : Prop) : (p3227) ∨ (((¬ p3228) ∨ (¬ p3229) ∨ (¬ p3193) ∨ (¬ p3227) ∨ (¬ p3226))) := by
  classical
  tauto

theorem initial4578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3227) ∨ (meaning t m 3230) := by
  exact rule4578 (meaning t m 3193) (meaning t m 3226) (meaning t m 3227) (meaning t m 3228) (meaning t m 3229)

theorem rule4579 (p3193 p3226 p3227 p3228 p3229 : Prop) : (p3226) ∨ (((¬ p3228) ∨ (¬ p3229) ∨ (¬ p3193) ∨ (¬ p3227) ∨ (¬ p3226))) := by
  classical
  tauto

theorem initial4579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3226) ∨ (meaning t m 3230) := by
  exact rule4579 (meaning t m 3193) (meaning t m 3226) (meaning t m 3227) (meaning t m 3228) (meaning t m 3229)

theorem rule4581 (p3225 p3230 : Prop) (h : (p3225 ↔ (¬ p3230))) : (¬ p3225) ∨ (¬ p3230) := by
  classical
  tauto

theorem initial4581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3225)) ∨ (¬ (meaning t m 3230)) := by
  have source := ElevenTheory.theory223 t (m.theta 1 4) (m.theta 1 9) (m.theta 4 9)
  exact rule4581 (meaning t m 3225) (meaning t m 3230) source

theorem rule4583 (p3222 p3232 p3233 p3234 p3235 : Prop) : (¬ (p3232 ∧ p3233 ∧ p3222 ∧ p3234 ∧ p3235)) ∨ (p3232) := by
  classical
  tauto

theorem initial4583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3231)) ∨ (meaning t m 3232) := by
  exact rule4583 (meaning t m 3222) (meaning t m 3232) (meaning t m 3233) (meaning t m 3234) (meaning t m 3235)

theorem rule4584 (p3222 p3232 p3233 p3234 p3235 : Prop) : (¬ (p3232 ∧ p3233 ∧ p3222 ∧ p3234 ∧ p3235)) ∨ (p3233) := by
  classical
  tauto

theorem initial4584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3231)) ∨ (meaning t m 3233) := by
  exact rule4584 (meaning t m 3222) (meaning t m 3232) (meaning t m 3233) (meaning t m 3234) (meaning t m 3235)

theorem rule4585 (p3222 p3232 p3233 p3234 p3235 : Prop) : (p3222) ∨ (¬ (p3232 ∧ p3233 ∧ p3222 ∧ p3234 ∧ p3235)) := by
  classical
  tauto

theorem initial4585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3222) ∨ (¬ (meaning t m 3231)) := by
  exact rule4585 (meaning t m 3222) (meaning t m 3232) (meaning t m 3233) (meaning t m 3234) (meaning t m 3235)

theorem rule4592 (p3222 p3232 p3233 p3234 p3235 : Prop) : (p3232) ∨ (((¬ p3222) ∨ (¬ p3234) ∨ (¬ p3235) ∨ (¬ p3232) ∨ (¬ p3233))) := by
  classical
  tauto

theorem initial4592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3232) ∨ (meaning t m 3236) := by
  exact rule4592 (meaning t m 3222) (meaning t m 3232) (meaning t m 3233) (meaning t m 3234) (meaning t m 3235)

theorem rule4593 (p3222 p3232 p3233 p3234 p3235 : Prop) : (p3233) ∨ (((¬ p3222) ∨ (¬ p3234) ∨ (¬ p3235) ∨ (¬ p3232) ∨ (¬ p3233))) := by
  classical
  tauto

theorem initial4593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3233) ∨ (meaning t m 3236) := by
  exact rule4593 (meaning t m 3222) (meaning t m 3232) (meaning t m 3233) (meaning t m 3234) (meaning t m 3235)

theorem rule4595 (p3231 p3236 : Prop) (h : (p3231 ↔ (¬ p3236))) : (¬ p3231) ∨ (¬ p3236) := by
  classical
  tauto

theorem initial4595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3231)) ∨ (¬ (meaning t m 3236)) := by
  have source := ElevenTheory.theory224 t (m.theta 1 4) (m.theta 1 9) (m.theta 4 9)
  exact rule4595 (meaning t m 3231) (meaning t m 3236) source

theorem rule4597 (p3222 p3237 p3238 : Prop) (h : (¬ p3222) ∨ (¬ p3237) ∨ (¬ p3238)) : (¬ p3222) ∨ (¬ p3237) ∨ (¬ p3238) := by
  classical
  tauto

theorem initial4597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3237)) ∨ (¬ (meaning t m 3238)) := by
  have source := ElevenTheory.theory225 (m.theta 1 4) (m.theta 4 5) (m.theta 4 9)
  exact rule4597 (meaning t m 3222) (meaning t m 3237) (meaning t m 3238) source

theorem rule4598 (p2441 p2922 p3238 : Prop) (h : (¬ p2441) ∨ (¬ p2922) ∨ (¬ p3238)) : (¬ p2441) ∨ (¬ p2922) ∨ (¬ p3238) := by
  classical
  tauto

theorem initial4598 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) := by
  have source := ElevenTheory.theory226 (m.theta 1 4) (m.theta 4 5) (m.theta 4 7)
  exact rule4598 (meaning t m 2441) (meaning t m 2922) (meaning t m 3238) source

theorem rule4599 (p1082 p1088 : Prop) : (¬ p1082) ∨ ((p1082 ∨ p1088)) := by
  classical
  tauto

theorem initial4599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1082)) ∨ (meaning t m 3239) := by
  exact rule4599 (meaning t m 1082) (meaning t m 1088)

theorem rule4600 (p1082 p1088 : Prop) : (¬ p1088) ∨ ((p1082 ∨ p1088)) := by
  classical
  tauto

theorem initial4600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1088)) ∨ (meaning t m 3239) := by
  exact rule4600 (meaning t m 1082) (meaning t m 1088)

theorem rule4617 (p3239 p3240 : Prop) (h : (p3239 ↔ p3240)) : (¬ p3239) ∨ (p3240) := by
  classical
  tauto

theorem initial4617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3239)) ∨ (meaning t m 3240) := by
  have source := ElevenTheory.theory227 t (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule4617 (meaning t m 3239) (meaning t m 3240) source

theorem rule4619 (p1094 p1100 : Prop) : (¬ p1094) ∨ ((p1094 ∨ p1100)) := by
  classical
  tauto

theorem initial4619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1094)) ∨ (meaning t m 3249) := by
  exact rule4619 (meaning t m 1094) (meaning t m 1100)

theorem rule4620 (p1094 p1100 : Prop) : (¬ p1100) ∨ ((p1094 ∨ p1100)) := by
  classical
  tauto

theorem initial4620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1100)) ∨ (meaning t m 3249) := by
  exact rule4620 (meaning t m 1094) (meaning t m 1100)

theorem rule4637 (p3249 p3250 : Prop) (h : (p3249 ↔ p3250)) : (¬ p3249) ∨ (p3250) := by
  classical
  tauto

theorem initial4637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3249)) ∨ (meaning t m 3250) := by
  have source := ElevenTheory.theory228 t (m.theta 3 8) (m.theta 3 9) (m.theta 8 9)
  exact rule4637 (meaning t m 3249) (meaning t m 3250) source

theorem rule4639 (p1106 p1112 : Prop) : (¬ p1106) ∨ ((p1106 ∨ p1112)) := by
  classical
  tauto

theorem initial4639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1106)) ∨ (meaning t m 3259) := by
  exact rule4639 (meaning t m 1106) (meaning t m 1112)

theorem rule4640 (p1106 p1112 : Prop) : (¬ p1112) ∨ ((p1106 ∨ p1112)) := by
  classical
  tauto

theorem initial4640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1112)) ∨ (meaning t m 3259) := by
  exact rule4640 (meaning t m 1106) (meaning t m 1112)

theorem rule4657 (p3259 p3260 : Prop) (h : (p3259 ↔ p3260)) : (¬ p3259) ∨ (p3260) := by
  classical
  tauto

theorem initial4657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3259)) ∨ (meaning t m 3260) := by
  have source := ElevenTheory.theory229 t (m.theta 8 10) (m.theta 8 9) (m.theta 9 10)
  exact rule4657 (meaning t m 3259) (meaning t m 3260) source

theorem rule4659 (p1118 p1124 : Prop) : (¬ p1118) ∨ ((p1118 ∨ p1124)) := by
  classical
  tauto

theorem initial4659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1118)) ∨ (meaning t m 3269) := by
  exact rule4659 (meaning t m 1118) (meaning t m 1124)

theorem rule4660 (p1118 p1124 : Prop) : (¬ p1124) ∨ ((p1118 ∨ p1124)) := by
  classical
  tauto

theorem initial4660 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1124)) ∨ (meaning t m 3269) := by
  exact rule4660 (meaning t m 1118) (meaning t m 1124)

theorem rule4677 (p3269 p3270 : Prop) (h : (p3269 ↔ p3270)) : (¬ p3269) ∨ (p3270) := by
  classical
  tauto

theorem initial4677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3269)) ∨ (meaning t m 3270) := by
  have source := ElevenTheory.theory230 t (m.theta 4 10) (m.theta 4 9) (m.theta 9 10)
  exact rule4677 (meaning t m 3269) (meaning t m 3270) source

theorem rule4679 (p1130 p1136 : Prop) : (¬ p1130) ∨ ((p1130 ∨ p1136)) := by
  classical
  tauto

theorem initial4679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1130)) ∨ (meaning t m 3279) := by
  exact rule4679 (meaning t m 1130) (meaning t m 1136)

theorem rule4680 (p1130 p1136 : Prop) : (¬ p1136) ∨ ((p1130 ∨ p1136)) := by
  classical
  tauto

theorem initial4680 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1136)) ∨ (meaning t m 3279) := by
  exact rule4680 (meaning t m 1130) (meaning t m 1136)

theorem rule4697 (p3279 p3280 : Prop) (h : (p3279 ↔ p3280)) : (¬ p3279) ∨ (p3280) := by
  classical
  tauto

theorem initial4697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3279)) ∨ (meaning t m 3280) := by
  have source := ElevenTheory.theory231 t (m.theta 0 3) (m.theta 0 9) (m.theta 3 9)
  exact rule4697 (meaning t m 3279) (meaning t m 3280) source

theorem rule4699 (p3290 p3291 p3292 p3293 p3294 : Prop) : (¬ (p3290 ∧ p3291 ∧ p3292 ∧ p3293 ∧ p3294)) ∨ (p3290) := by
  classical
  tauto

theorem initial4699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3289)) ∨ (meaning t m 3290) := by
  exact rule4699 (meaning t m 3290) (meaning t m 3291) (meaning t m 3292) (meaning t m 3293) (meaning t m 3294)

theorem rule4701 (p3290 p3291 p3292 p3293 p3294 : Prop) : (¬ (p3290 ∧ p3291 ∧ p3292 ∧ p3293 ∧ p3294)) ∨ (p3292) := by
  classical
  tauto

theorem initial4701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3289)) ∨ (meaning t m 3292) := by
  exact rule4701 (meaning t m 3290) (meaning t m 3291) (meaning t m 3292) (meaning t m 3293) (meaning t m 3294)

theorem rule4707 (p3290 p3291 p3292 p3293 p3294 : Prop) : (p3291) ∨ (((¬ p3294) ∨ (¬ p3293) ∨ (¬ p3291) ∨ (¬ p3292) ∨ (¬ p3290))) := by
  classical
  tauto

theorem initial4707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3291) ∨ (meaning t m 3295) := by
  exact rule4707 (meaning t m 3290) (meaning t m 3291) (meaning t m 3292) (meaning t m 3293) (meaning t m 3294)

theorem rule4711 (p3289 p3295 : Prop) (h : (p3289 ↔ (¬ p3295))) : (¬ p3289) ∨ (¬ p3295) := by
  classical
  tauto

theorem initial4711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3289)) ∨ (¬ (meaning t m 3295)) := by
  have source := ElevenTheory.theory232 t (m.theta 0 3) (m.theta 0 9) (m.theta 3 9)
  exact rule4711 (meaning t m 3289) (meaning t m 3295) source

theorem rule4713 (p3286 p3297 p3298 p3299 p3300 : Prop) : (¬ (p3297 ∧ p3298 ∧ p3286 ∧ p3299 ∧ p3300)) ∨ (p3297) := by
  classical
  tauto

theorem initial4713 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3296)) ∨ (meaning t m 3297) := by
  exact rule4713 (meaning t m 3286) (meaning t m 3297) (meaning t m 3298) (meaning t m 3299) (meaning t m 3300)

theorem rule4715 (p3286 p3297 p3298 p3299 p3300 : Prop) : (p3286) ∨ (¬ (p3297 ∧ p3298 ∧ p3286 ∧ p3299 ∧ p3300)) := by
  classical
  tauto

theorem initial4715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3286) ∨ (¬ (meaning t m 3296)) := by
  exact rule4715 (meaning t m 3286) (meaning t m 3297) (meaning t m 3298) (meaning t m 3299) (meaning t m 3300)

theorem rule4721 (p3286 p3297 p3298 p3299 p3300 : Prop) : (p3297) ∨ (((¬ p3286) ∨ (¬ p3299) ∨ (¬ p3297) ∨ (¬ p3298) ∨ (¬ p3300))) := by
  classical
  tauto

theorem initial4721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3297) ∨ (meaning t m 3301) := by
  exact rule4721 (meaning t m 3286) (meaning t m 3297) (meaning t m 3298) (meaning t m 3299) (meaning t m 3300)

theorem rule4722 (p3286 p3297 p3298 p3299 p3300 : Prop) : (p3298) ∨ (((¬ p3286) ∨ (¬ p3299) ∨ (¬ p3297) ∨ (¬ p3298) ∨ (¬ p3300))) := by
  classical
  tauto

theorem initial4722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3298) ∨ (meaning t m 3301) := by
  exact rule4722 (meaning t m 3286) (meaning t m 3297) (meaning t m 3298) (meaning t m 3299) (meaning t m 3300)

theorem rule4725 (p3296 p3301 : Prop) (h : (p3296 ↔ (¬ p3301))) : (¬ p3296) ∨ (¬ p3301) := by
  classical
  tauto

theorem initial4725 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3296)) ∨ (¬ (meaning t m 3301)) := by
  have source := ElevenTheory.theory233 t (m.theta 0 3) (m.theta 0 9) (m.theta 3 9)
  exact rule4725 (meaning t m 3296) (meaning t m 3301) source

theorem rule4727 (p1142 p1148 : Prop) : (¬ p1142) ∨ ((p1142 ∨ p1148)) := by
  classical
  tauto

theorem initial4727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1142)) ∨ (meaning t m 3302) := by
  exact rule4727 (meaning t m 1142) (meaning t m 1148)

theorem rule4728 (p1142 p1148 : Prop) : (¬ p1148) ∨ ((p1142 ∨ p1148)) := by
  classical
  tauto

theorem initial4728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1148)) ∨ (meaning t m 3302) := by
  exact rule4728 (meaning t m 1142) (meaning t m 1148)

theorem rule4745 (p3302 p3303 : Prop) (h : (p3302 ↔ p3303)) : (¬ p3302) ∨ (p3303) := by
  classical
  tauto

theorem initial4745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3302)) ∨ (meaning t m 3303) := by
  have source := ElevenTheory.theory234 t (m.theta 1 6) (m.theta 1 7) (m.theta 6 7)
  exact rule4745 (meaning t m 3302) (meaning t m 3303) source

theorem rule4747 (p1154 p1160 : Prop) : (¬ p1154) ∨ ((p1154 ∨ p1160)) := by
  classical
  tauto

theorem initial4747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1154)) ∨ (meaning t m 3312) := by
  exact rule4747 (meaning t m 1154) (meaning t m 1160)

theorem rule4748 (p1154 p1160 : Prop) : (¬ p1160) ∨ ((p1154 ∨ p1160)) := by
  classical
  tauto

theorem initial4748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1160)) ∨ (meaning t m 3312) := by
  exact rule4748 (meaning t m 1154) (meaning t m 1160)

theorem rule4765 (p3312 p3313 : Prop) (h : (p3312 ↔ p3313)) : (¬ p3312) ∨ (p3313) := by
  classical
  tauto

theorem initial4765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3312)) ∨ (meaning t m 3313) := by
  have source := ElevenTheory.theory235 t (m.theta 1 6) (m.theta 1 9) (m.theta 6 9)
  exact rule4765 (meaning t m 3312) (meaning t m 3313) source

theorem rule4767 (p3322 p3323 p3324 : Prop) (h : (¬ p3322) ∨ (¬ p3323) ∨ (¬ p3324)) : (¬ p3322) ∨ (¬ p3323) ∨ (¬ p3324) := by
  classical
  tauto

theorem initial4767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3324)) := by
  have source := ElevenTheory.theory236 (m.theta 3 6) (m.theta 6 8) (m.theta 6 9)
  exact rule4767 (meaning t m 3322) (meaning t m 3323) (meaning t m 3324) source

theorem rule4768 (p3063 p3309 p3325 : Prop) (h : (¬ p3325) ∨ (¬ p3309) ∨ p3063) : (p3063) ∨ (¬ p3309) ∨ (¬ p3325) := by
  classical
  tauto

theorem initial4768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3063) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3325)) := by
  have source := ElevenTheory.theory237 (m.theta 1 6) (m.theta 6 7) (m.theta 6 8)
  exact rule4768 (meaning t m 3063) (meaning t m 3309) (meaning t m 3325) source

theorem rule4769 (p1166 p1172 : Prop) : (¬ p1166) ∨ ((p1166 ∨ p1172)) := by
  classical
  tauto

theorem initial4769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1166)) ∨ (meaning t m 3326) := by
  exact rule4769 (meaning t m 1166) (meaning t m 1172)

theorem rule4770 (p1166 p1172 : Prop) : (¬ p1172) ∨ ((p1166 ∨ p1172)) := by
  classical
  tauto

theorem initial4770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1172)) ∨ (meaning t m 3326) := by
  exact rule4770 (meaning t m 1166) (meaning t m 1172)

theorem rule4787 (p3326 p3327 : Prop) (h : (p3326 ↔ p3327)) : (¬ p3326) ∨ (p3327) := by
  classical
  tauto

theorem initial4787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3326)) ∨ (meaning t m 3327) := by
  have source := ElevenTheory.theory238 t (m.theta 2 4) (m.theta 2 9) (m.theta 4 9)
  exact rule4787 (meaning t m 3326) (meaning t m 3327) source

theorem rule4789 (p1178 p1184 : Prop) : (¬ p1178) ∨ ((p1178 ∨ p1184)) := by
  classical
  tauto

theorem initial4789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1178)) ∨ (meaning t m 3336) := by
  exact rule4789 (meaning t m 1178) (meaning t m 1184)

theorem rule4790 (p1178 p1184 : Prop) : (¬ p1184) ∨ ((p1178 ∨ p1184)) := by
  classical
  tauto

theorem initial4790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1184)) ∨ (meaning t m 3336) := by
  exact rule4790 (meaning t m 1178) (meaning t m 1184)

theorem rule4807 (p3336 p3337 : Prop) (h : (p3336 ↔ p3337)) : (¬ p3336) ∨ (p3337) := by
  classical
  tauto

theorem initial4807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3336)) ∨ (meaning t m 3337) := by
  have source := ElevenTheory.theory239 t (m.theta 3 4) (m.theta 3 9) (m.theta 4 9)
  exact rule4807 (meaning t m 3336) (meaning t m 3337) source

theorem rule4809 (p3222 p3346 p3347 : Prop) (h : (¬ p3346) ∨ (¬ p3347) ∨ (¬ p3222)) : (¬ p3222) ∨ (¬ p3346) ∨ (¬ p3347) := by
  classical
  tauto

theorem initial4809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3347)) := by
  have source := ElevenTheory.theory240 (m.theta 0 4) (m.theta 1 4) (m.theta 4 9)
  exact rule4809 (meaning t m 3222) (meaning t m 3346) (meaning t m 3347) source

theorem rule4810 (p1190 p1196 : Prop) : (¬ p1190) ∨ ((p1190 ∨ p1196)) := by
  classical
  tauto

theorem initial4810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1190)) ∨ (meaning t m 3348) := by
  exact rule4810 (meaning t m 1190) (meaning t m 1196)

theorem rule4811 (p1190 p1196 : Prop) : (¬ p1196) ∨ ((p1190 ∨ p1196)) := by
  classical
  tauto

theorem initial4811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1196)) ∨ (meaning t m 3348) := by
  exact rule4811 (meaning t m 1190) (meaning t m 1196)

theorem rule4828 (p3348 p3349 : Prop) (h : (p3348 ↔ p3349)) : (¬ p3348) ∨ (p3349) := by
  classical
  tauto

theorem initial4828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3348)) ∨ (meaning t m 3349) := by
  have source := ElevenTheory.theory241 t (m.theta 0 4) (m.theta 0 9) (m.theta 4 9)
  exact rule4828 (meaning t m 3348) (meaning t m 3349) source

theorem rule4830 (p3083 p3358 p3359 : Prop) (h : (¬ p3083) ∨ (¬ p3358) ∨ (¬ p3359)) : (¬ p3083) ∨ (¬ p3358) ∨ (¬ p3359) := by
  classical
  tauto

theorem initial4830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3358)) ∨ (¬ (meaning t m 3359)) := by
  have source := ElevenTheory.theory242 (m.theta 3 4) (m.theta 4 8) (m.theta 4 9)
  exact rule4830 (meaning t m 3083) (meaning t m 3358) (meaning t m 3359) source

theorem rule4831 (p2059 p3360 : Prop) (h : ((¬ p2059) ↔ (¬ p3360))) : (p2059) ∨ (¬ p3360) := by
  classical
  tauto

theorem initial4831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2059) ∨ (¬ (meaning t m 3360)) := by
  have source := ElevenTheory.theory243 t (m.theta 0 7)
  exact rule4831 (meaning t m 2059) (meaning t m 3360) source

theorem rule4833 (p2630 p2657 p3361 : Prop) (h : (¬ p3361) ∨ (¬ p2630) ∨ (¬ p2657)) : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3361) := by
  classical
  tauto

theorem initial4833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3361)) := by
  have source := ElevenTheory.theory244 (m.theta 0 3) (m.theta 2 3) (m.theta 3 4)
  exact rule4833 (meaning t m 2630) (meaning t m 2657) (meaning t m 3361) source

theorem rule4834 (p3362 p3363 p3364 p3365 : Prop) (h : (¬ p3362) ∨ (¬ p3363) ∨ (¬ p3364) ∨ (¬ p3365)) : (¬ p3362) ∨ (¬ p3363) ∨ (¬ p3364) ∨ (¬ p3365) := by
  classical
  tauto

theorem initial4834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3365)) := by
  have source := ElevenTheory.theory245 (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4)
  exact rule4834 (meaning t m 3362) (meaning t m 3363) (meaning t m 3364) (meaning t m 3365) source

theorem rule4835 (p3055 p3366 p3367 : Prop) (h : (¬ p3366) ∨ (¬ p3367) ∨ (¬ p3055)) : (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial4835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory246 (m.theta 0 2) (m.theta 1 2) (m.theta 2 4)
  exact rule4835 (meaning t m 3055) (meaning t m 3366) (meaning t m 3367) source

theorem rule4836 (p2210 p2247 p3368 : Prop) (h : (¬ p2247) ∨ (¬ p3368) ∨ (¬ p2210)) : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p3368) := by
  classical
  tauto

theorem initial4836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3368)) := by
  have source := ElevenTheory.theory247 (m.theta 0 1) (m.theta 1 3) (m.theta 1 5)
  exact rule4836 (meaning t m 2210) (meaning t m 2247) (meaning t m 3368) source

theorem rule4837 (p2737 p3365 p3366 : Prop) (h : (¬ p3365) ∨ (¬ p2737) ∨ (¬ p3366)) : (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3366) := by
  classical
  tauto

theorem initial4837 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) := by
  have source := ElevenTheory.theory248 (m.theta 0 2) (m.theta 1 2) (m.theta 2 3)
  exact rule4837 (meaning t m 2737) (meaning t m 3365) (meaning t m 3366) source

theorem rule4838 (p2608 p3369 p3370 p3371 : Prop) (h : (¬ p2608) ∨ (¬ p3369) ∨ (¬ p3370) ∨ (¬ p3371)) : (¬ p2608) ∨ (¬ p3369) ∨ (¬ p3370) ∨ (¬ p3371) := by
  classical
  tauto

theorem initial4838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3371)) := by
  have source := ElevenTheory.theory249 (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5)
  exact rule4838 (meaning t m 2608) (meaning t m 3369) (meaning t m 3370) (meaning t m 3371) source

theorem rule4839 (p1202 p1208 : Prop) : (¬ p1202) ∨ ((p1202 ∨ p1208)) := by
  classical
  tauto

theorem initial4839 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1202)) ∨ (meaning t m 3372) := by
  exact rule4839 (meaning t m 1202) (meaning t m 1208)

theorem rule4840 (p1202 p1208 : Prop) : (¬ p1208) ∨ ((p1202 ∨ p1208)) := by
  classical
  tauto

theorem initial4840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1208)) ∨ (meaning t m 3372) := by
  exact rule4840 (meaning t m 1202) (meaning t m 1208)

theorem rule4857 (p3372 p3373 : Prop) (h : (p3372 ↔ p3373)) : (¬ p3372) ∨ (p3373) := by
  classical
  tauto

theorem initial4857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3372)) ∨ (meaning t m 3373) := by
  have source := ElevenTheory.theory250 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4)
  exact rule4857 (meaning t m 3372) (meaning t m 3373) source

theorem rule4859 (p1214 p1220 : Prop) : (¬ p1214) ∨ ((p1214 ∨ p1220)) := by
  classical
  tauto

theorem initial4859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1214)) ∨ (meaning t m 3382) := by
  exact rule4859 (meaning t m 1214) (meaning t m 1220)

theorem rule4860 (p1214 p1220 : Prop) : (¬ p1220) ∨ ((p1214 ∨ p1220)) := by
  classical
  tauto

theorem initial4860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1220)) ∨ (meaning t m 3382) := by
  exact rule4860 (meaning t m 1214) (meaning t m 1220)

theorem rule4877 (p3382 p3383 : Prop) (h : (p3382 ↔ p3383)) : (¬ p3382) ∨ (p3383) := by
  classical
  tauto

theorem initial4877 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3382)) ∨ (meaning t m 3383) := by
  have source := ElevenTheory.theory251 t (m.theta 0 4) (m.theta 0 7) (m.theta 4 7)
  exact rule4877 (meaning t m 3382) (meaning t m 3383) source

theorem rule4879 (p1226 p1232 : Prop) : (¬ p1226) ∨ ((p1226 ∨ p1232)) := by
  classical
  tauto

theorem initial4879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1226)) ∨ (meaning t m 3392) := by
  exact rule4879 (meaning t m 1226) (meaning t m 1232)

theorem rule4880 (p1226 p1232 : Prop) : (¬ p1232) ∨ ((p1226 ∨ p1232)) := by
  classical
  tauto

theorem initial4880 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1232)) ∨ (meaning t m 3392) := by
  exact rule4880 (meaning t m 1226) (meaning t m 1232)

theorem rule4897 (p3392 p3393 : Prop) (h : (p3392 ↔ p3393)) : (¬ p3392) ∨ (p3393) := by
  classical
  tauto

theorem initial4897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3392)) ∨ (meaning t m 3393) := by
  have source := ElevenTheory.theory252 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 7)
  exact rule4897 (meaning t m 3392) (meaning t m 3393) source

theorem rule4899 (p2247 p3379 p3402 : Prop) (h : (¬ p3402) ∨ (¬ p2247) ∨ (¬ p3379)) : (¬ p2247) ∨ (¬ p3379) ∨ (¬ p3402) := by
  classical
  tauto

theorem initial4899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3402)) := by
  have source := ElevenTheory.theory253 (m.theta 0 1) (m.theta 1 3) (m.theta 1 4)
  exact rule4899 (meaning t m 2247) (meaning t m 3379) (meaning t m 3402) source

theorem rule4900 (p1238 p1244 : Prop) : (¬ p1238) ∨ ((p1238 ∨ p1244)) := by
  classical
  tauto

theorem initial4900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1238)) ∨ (meaning t m 3403) := by
  exact rule4900 (meaning t m 1238) (meaning t m 1244)

theorem rule4901 (p1238 p1244 : Prop) : (¬ p1244) ∨ ((p1238 ∨ p1244)) := by
  classical
  tauto

theorem initial4901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1244)) ∨ (meaning t m 3403) := by
  exact rule4901 (meaning t m 1238) (meaning t m 1244)

theorem rule4918 (p3403 p3404 : Prop) (h : (p3403 ↔ p3404)) : (¬ p3403) ∨ (p3404) := by
  classical
  tauto

theorem initial4918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3403)) ∨ (meaning t m 3404) := by
  have source := ElevenTheory.theory254 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 4)
  exact rule4918 (meaning t m 3403) (meaning t m 3404) source

theorem rule4920 (p2727 p3368 p3412 p3413 : Prop) (h : (¬ p3412) ∨ (¬ p3413) ∨ (¬ p3368) ∨ (¬ p2727)) : (¬ p2727) ∨ (¬ p3368) ∨ (¬ p3412) ∨ (¬ p3413) := by
  classical
  tauto

theorem initial4920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3413)) := by
  have source := ElevenTheory.theory255 (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5)
  exact rule4920 (meaning t m 2727) (meaning t m 3368) (meaning t m 3412) (meaning t m 3413) source

theorem rule4921 (p2685 p3361 p3414 : Prop) (h : (¬ p3361) ∨ (¬ p3414) ∨ (¬ p2685)) : (¬ p2685) ∨ (¬ p3361) ∨ (¬ p3414) := by
  classical
  tauto

theorem initial4921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3414)) := by
  have source := ElevenTheory.theory256 (m.theta 0 3) (m.theta 2 3) (m.theta 3 7)
  exact rule4921 (meaning t m 2685) (meaning t m 3361) (meaning t m 3414) source

theorem rule4922 (p1250 p1256 : Prop) : (¬ p1250) ∨ ((p1250 ∨ p1256)) := by
  classical
  tauto

theorem initial4922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1250)) ∨ (meaning t m 3415) := by
  exact rule4922 (meaning t m 1250) (meaning t m 1256)

theorem rule4923 (p1250 p1256 : Prop) : (¬ p1256) ∨ ((p1250 ∨ p1256)) := by
  classical
  tauto

theorem initial4923 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1256)) ∨ (meaning t m 3415) := by
  exact rule4923 (meaning t m 1250) (meaning t m 1256)

theorem rule4940 (p3415 p3416 : Prop) (h : (p3415 ↔ p3416)) : (¬ p3415) ∨ (p3416) := by
  classical
  tauto

theorem initial4940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3415)) ∨ (meaning t m 3416) := by
  have source := ElevenTheory.theory257 t (m.theta 2 4) (m.theta 2 6) (m.theta 4 6)
  exact rule4940 (meaning t m 3415) (meaning t m 3416) source

theorem rule4942 (p2797 p2963 p3361 : Prop) (h : (¬ p2963) ∨ (¬ p3361) ∨ (¬ p2797)) : (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3361) := by
  classical
  tauto

theorem initial4942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3361)) := by
  have source := ElevenTheory.theory258 (m.theta 0 3) (m.theta 2 3) (m.theta 3 6)
  exact rule4942 (meaning t m 2797) (meaning t m 2963) (meaning t m 3361) source

theorem rule4943 (p2774 p3425 p3426 : Prop) (h : (¬ p3425) ∨ (¬ p2774) ∨ (¬ p3426)) : (¬ p2774) ∨ (¬ p3425) ∨ (¬ p3426) := by
  classical
  tauto

theorem initial4943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3426)) := by
  have source := ElevenTheory.theory259 (m.theta 0 2) (m.theta 2 6) (m.theta 2 7)
  exact rule4943 (meaning t m 2774) (meaning t m 3425) (meaning t m 3426) source

theorem rule4944 (p1262 p1268 : Prop) : (¬ p1262) ∨ ((p1262 ∨ p1268)) := by
  classical
  tauto

theorem initial4944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1262)) ∨ (meaning t m 3427) := by
  exact rule4944 (meaning t m 1262) (meaning t m 1268)

theorem rule4945 (p1262 p1268 : Prop) : (¬ p1268) ∨ ((p1262 ∨ p1268)) := by
  classical
  tauto

theorem initial4945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1268)) ∨ (meaning t m 3427) := by
  exact rule4945 (meaning t m 1262) (meaning t m 1268)

theorem rule4962 (p3427 p3428 : Prop) (h : (p3427 ↔ p3428)) : (¬ p3427) ∨ (p3428) := by
  classical
  tauto

theorem initial4962 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3427)) ∨ (meaning t m 3428) := by
  have source := ElevenTheory.theory260 t (m.theta 2 7) (m.theta 2 9) (m.theta 7 9)
  exact rule4962 (meaning t m 3427) (meaning t m 3428) source

theorem rule4964 (p2060 p3437 : Prop) (h : ((¬ p2060) ↔ (¬ p3437))) : (p2060) ∨ (¬ p3437) := by
  classical
  tauto

theorem initial4964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2060) ∨ (¬ (meaning t m 3437)) := by
  have source := ElevenTheory.theory261 t (m.theta 2 7)
  exact rule4964 (meaning t m 2060) (meaning t m 3437) source

theorem rule4966 (p2088 p3438 p3439 p3440 : Prop) (h : (¬ p3438) ∨ (¬ p2088) ∨ (¬ p3439) ∨ (¬ p3440)) : (¬ p2088) ∨ (¬ p3438) ∨ (¬ p3439) ∨ (¬ p3440) := by
  classical
  tauto

theorem initial4966 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3438)) ∨ (¬ (meaning t m 3439)) ∨ (¬ (meaning t m 3440)) := by
  have source := ElevenTheory.theory262 (m.theta 0 8) (m.theta 1 8) (m.theta 1 9) (m.theta 8 9)
  exact rule4966 (meaning t m 2088) (meaning t m 3438) (meaning t m 3439) (meaning t m 3440) source

theorem rule4967 (p2061 p3441 : Prop) (h : ((¬ p2061) ↔ (¬ p3441))) : (p2061) ∨ (¬ p3441) := by
  classical
  tauto

theorem initial4967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2061) ∨ (¬ (meaning t m 3441)) := by
  have source := ElevenTheory.theory263 t (m.theta 1 8)
  exact rule4967 (meaning t m 2061) (meaning t m 3441) source

theorem rule4969 (p1274 p1280 : Prop) : (¬ p1274) ∨ ((p1274 ∨ p1280)) := by
  classical
  tauto

theorem initial4969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1274)) ∨ (meaning t m 3442) := by
  exact rule4969 (meaning t m 1274) (meaning t m 1280)

theorem rule4970 (p1274 p1280 : Prop) : (¬ p1280) ∨ ((p1274 ∨ p1280)) := by
  classical
  tauto

theorem initial4970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1280)) ∨ (meaning t m 3442) := by
  exact rule4970 (meaning t m 1274) (meaning t m 1280)

theorem rule4987 (p3442 p3443 : Prop) (h : (p3442 ↔ p3443)) : (¬ p3442) ∨ (p3443) := by
  classical
  tauto

theorem initial4987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3442)) ∨ (meaning t m 3443) := by
  have source := ElevenTheory.theory264 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 8)
  exact rule4987 (meaning t m 3442) (meaning t m 3443) source

theorem rule4989 (p3449 p3452 p3453 : Prop) (h : (¬ p3452) ∨ (¬ p3453) ∨ (¬ p3449)) : (¬ p3449) ∨ (¬ p3452) ∨ (¬ p3453) := by
  classical
  tauto

theorem initial4989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3453)) := by
  have source := ElevenTheory.theory265 (m.theta 0 1) (m.theta 1 4) (m.theta 1 8)
  exact rule4989 (meaning t m 3449) (meaning t m 3452) (meaning t m 3453) source

theorem rule4990 (p1286 p1292 : Prop) : (¬ p1286) ∨ ((p1286 ∨ p1292)) := by
  classical
  tauto

theorem initial4990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1286)) ∨ (meaning t m 3454) := by
  exact rule4990 (meaning t m 1286) (meaning t m 1292)

theorem rule4991 (p1286 p1292 : Prop) : (¬ p1292) ∨ ((p1286 ∨ p1292)) := by
  classical
  tauto

theorem initial4991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1292)) ∨ (meaning t m 3454) := by
  exact rule4991 (meaning t m 1286) (meaning t m 1292)

theorem rule5008 (p3454 p3455 : Prop) (h : (p3454 ↔ p3455)) : (¬ p3454) ∨ (p3455) := by
  classical
  tauto

theorem initial5008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3454)) ∨ (meaning t m 3455) := by
  have source := ElevenTheory.theory266 t (m.theta 6 10) (m.theta 6 9) (m.theta 9 10)
  exact rule5008 (meaning t m 3454) (meaning t m 3455) source

theorem rule5010 (p1298 p1304 : Prop) : (¬ p1298) ∨ ((p1298 ∨ p1304)) := by
  classical
  tauto

theorem initial5010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1298)) ∨ (meaning t m 3464) := by
  exact rule5010 (meaning t m 1298) (meaning t m 1304)

theorem rule5011 (p1298 p1304 : Prop) : (¬ p1304) ∨ ((p1298 ∨ p1304)) := by
  classical
  tauto

theorem initial5011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1304)) ∨ (meaning t m 3464) := by
  exact rule5011 (meaning t m 1298) (meaning t m 1304)

theorem rule5028 (p3464 p3465 : Prop) (h : (p3464 ↔ p3465)) : (¬ p3464) ∨ (p3465) := by
  classical
  tauto

theorem initial5028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3464)) ∨ (meaning t m 3465) := by
  have source := ElevenTheory.theory267 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 7)
  exact rule5028 (meaning t m 3464) (meaning t m 3465) source

theorem rule5030 (p2062 p3474 : Prop) (h : ((¬ p2062) ↔ (¬ p3474))) : (p2062) ∨ (¬ p3474) := by
  classical
  tauto

theorem initial5030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2062) ∨ (¬ (meaning t m 3474)) := by
  have source := ElevenTheory.theory268 t (m.theta 2 5)
  exact rule5030 (meaning t m 2062) (meaning t m 3474) source

theorem rule5032 (p2696 p3055 p3475 : Prop) (h : (¬ p2696) ∨ (¬ p3475) ∨ (¬ p3055)) : (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3475) := by
  classical
  tauto

theorem initial5032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3475)) := by
  have source := ElevenTheory.theory269 (m.theta 0 2) (m.theta 2 3) (m.theta 2 4)
  exact rule5032 (meaning t m 2696) (meaning t m 3055) (meaning t m 3475) source

theorem rule5033 (p2952 p3136 p3361 : Prop) (h : (¬ p3361) ∨ (¬ p3136) ∨ (¬ p2952)) : (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3361) := by
  classical
  tauto

theorem initial5033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3361)) := by
  have source := ElevenTheory.theory270 (m.theta 0 3) (m.theta 2 3) (m.theta 3 5)
  exact rule5033 (meaning t m 2952) (meaning t m 3136) (meaning t m 3361) source

theorem rule5034 (p3005 p3172 p3361 : Prop) (h : (¬ p3361) ∨ (¬ p3005) ∨ (¬ p3172)) : (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3361) := by
  classical
  tauto

theorem initial5034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3361)) := by
  have source := ElevenTheory.theory271 (m.theta 0 3) (m.theta 2 3) (m.theta 3 8)
  exact rule5034 (meaning t m 3005) (meaning t m 3172) (meaning t m 3361) source

theorem rule5035 (p1310 p1316 : Prop) : (¬ p1310) ∨ ((p1310 ∨ p1316)) := by
  classical
  tauto

theorem initial5035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1310)) ∨ (meaning t m 3476) := by
  exact rule5035 (meaning t m 1310) (meaning t m 1316)

theorem rule5036 (p1310 p1316 : Prop) : (¬ p1316) ∨ ((p1310 ∨ p1316)) := by
  classical
  tauto

theorem initial5036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1316)) ∨ (meaning t m 3476) := by
  exact rule5036 (meaning t m 1310) (meaning t m 1316)

theorem rule5053 (p3476 p3477 : Prop) (h : (p3476 ↔ p3477)) : (¬ p3476) ∨ (p3477) := by
  classical
  tauto

theorem initial5053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3476)) ∨ (meaning t m 3477) := by
  have source := ElevenTheory.theory272 t (m.theta 2 6) (m.theta 2 9) (m.theta 6 9)
  exact rule5053 (meaning t m 3476) (meaning t m 3477) source

theorem rule5055 (p3051 p3370 p3486 : Prop) (h : (¬ p3370) ∨ (¬ p3486) ∨ (¬ p3051)) : (¬ p3051) ∨ (¬ p3370) ∨ (¬ p3486) := by
  classical
  tauto

theorem initial5055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3486)) := by
  have source := ElevenTheory.theory273 (m.theta 0 5) (m.theta 1 5) (m.theta 5 7)
  exact rule5055 (meaning t m 3051) (meaning t m 3370) (meaning t m 3486) source

theorem rule5056 (p2542 p3238 p3487 : Prop) (h : (¬ p2542) ∨ (¬ p3487) ∨ (¬ p3238)) : (¬ p2542) ∨ (¬ p3238) ∨ (¬ p3487) := by
  classical
  tauto

theorem initial5056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3487)) := by
  have source := ElevenTheory.theory274 (m.theta 1 4) (m.theta 3 4) (m.theta 4 5)
  exact rule5056 (meaning t m 2542) (meaning t m 3238) (meaning t m 3487) source

theorem rule5057 (p1322 p1328 : Prop) : (¬ p1322) ∨ ((p1322 ∨ p1328)) := by
  classical
  tauto

theorem initial5057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1322)) ∨ (meaning t m 3488) := by
  exact rule5057 (meaning t m 1322) (meaning t m 1328)

theorem rule5058 (p1322 p1328 : Prop) : (¬ p1328) ∨ ((p1322 ∨ p1328)) := by
  classical
  tauto

theorem initial5058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1328)) ∨ (meaning t m 3488) := by
  exact rule5058 (meaning t m 1322) (meaning t m 1328)

theorem rule5075 (p3488 p3489 : Prop) (h : (p3488 ↔ p3489)) : (¬ p3488) ∨ (p3489) := by
  classical
  tauto

theorem initial5075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3488)) ∨ (meaning t m 3489) := by
  have source := ElevenTheory.theory275 t (m.theta 3 6) (m.theta 3 9) (m.theta 6 9)
  exact rule5075 (meaning t m 3488) (meaning t m 3489) source

theorem rule5077 (p2437 p2928 p3487 : Prop) (h : (¬ p3487) ∨ (¬ p2928) ∨ (¬ p2437)) : (¬ p2437) ∨ (¬ p2928) ∨ (¬ p3487) := by
  classical
  tauto

theorem initial5077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3487)) := by
  have source := ElevenTheory.theory276 (m.theta 1 4) (m.theta 3 4) (m.theta 4 7)
  exact rule5077 (meaning t m 2437) (meaning t m 2928) (meaning t m 3487) source

theorem rule5078 (p2190 p2284 p3497 : Prop) (h : (¬ p3497) ∨ (¬ p2284) ∨ (¬ p2190)) : (¬ p2190) ∨ (¬ p2284) ∨ (¬ p3497) := by
  classical
  tauto

theorem initial5078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3497)) := by
  have source := ElevenTheory.theory277 (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule5078 (meaning t m 2190) (meaning t m 2284) (meaning t m 3497) source

theorem rule5079 (p2063 p3498 : Prop) (h : ((¬ p2063) ↔ (¬ p3498))) : (p2063) ∨ (¬ p3498) := by
  classical
  tauto

theorem initial5079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2063) ∨ (¬ (meaning t m 3498)) := by
  have source := ElevenTheory.theory278 t (m.theta 4 8)
  exact rule5079 (meaning t m 2063) (meaning t m 3498) source

theorem rule5081 (p1334 p1340 : Prop) : (¬ p1334) ∨ ((p1334 ∨ p1340)) := by
  classical
  tauto

theorem initial5081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1334)) ∨ (meaning t m 3499) := by
  exact rule5081 (meaning t m 1334) (meaning t m 1340)

theorem rule5082 (p1334 p1340 : Prop) : (¬ p1340) ∨ ((p1334 ∨ p1340)) := by
  classical
  tauto

theorem initial5082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1340)) ∨ (meaning t m 3499) := by
  exact rule5082 (meaning t m 1334) (meaning t m 1340)

theorem rule5099 (p3499 p3500 : Prop) (h : (p3499 ↔ p3500)) : (¬ p3499) ∨ (p3500) := by
  classical
  tauto

theorem initial5099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3499)) ∨ (meaning t m 3500) := by
  have source := ElevenTheory.theory279 t (m.theta 3 10) (m.theta 3 9) (m.theta 9 10)
  exact rule5099 (meaning t m 3499) (meaning t m 3500) source

theorem rule5101 (p1346 p1352 : Prop) : (¬ p1346) ∨ ((p1346 ∨ p1352)) := by
  classical
  tauto

theorem initial5101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1346)) ∨ (meaning t m 3509) := by
  exact rule5101 (meaning t m 1346) (meaning t m 1352)

theorem rule5102 (p1346 p1352 : Prop) : (¬ p1352) ∨ ((p1346 ∨ p1352)) := by
  classical
  tauto

theorem initial5102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1352)) ∨ (meaning t m 3509) := by
  exact rule5102 (meaning t m 1346) (meaning t m 1352)

theorem rule5119 (p3509 p3510 : Prop) (h : (p3509 ↔ p3510)) : (¬ p3509) ∨ (p3510) := by
  classical
  tauto

theorem initial5119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3509)) ∨ (meaning t m 3510) := by
  have source := ElevenTheory.theory280 t (m.theta 0 7) (m.theta 0 9) (m.theta 7 9)
  exact rule5119 (meaning t m 3509) (meaning t m 3510) source

theorem rule5121 (p2928 p3389 p3519 : Prop) (h : (¬ p3519) ∨ (¬ p2928) ∨ (¬ p3389)) : (¬ p2928) ∨ (¬ p3389) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial5121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory281 (m.theta 0 4) (m.theta 1 4) (m.theta 4 7)
  exact rule5121 (meaning t m 2928) (meaning t m 3389) (meaning t m 3519) source

theorem rule5122 (p1358 p1364 : Prop) : (¬ p1358) ∨ ((p1358 ∨ p1364)) := by
  classical
  tauto

theorem initial5122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1358)) ∨ (meaning t m 3520) := by
  exact rule5122 (meaning t m 1358) (meaning t m 1364)

theorem rule5123 (p1358 p1364 : Prop) : (¬ p1364) ∨ ((p1358 ∨ p1364)) := by
  classical
  tauto

theorem initial5123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1364)) ∨ (meaning t m 3520) := by
  exact rule5123 (meaning t m 1358) (meaning t m 1364)

theorem rule5140 (p3520 p3521 : Prop) (h : (p3520 ↔ p3521)) : (¬ p3520) ∨ (p3521) := by
  classical
  tauto

theorem initial5140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3520)) ∨ (meaning t m 3521) := by
  have source := ElevenTheory.theory282 t (m.theta 1 7) (m.theta 1 8) (m.theta 7 8)
  exact rule5140 (meaning t m 3520) (meaning t m 3521) source

theorem rule5142 (p1370 p1376 : Prop) : (¬ p1370) ∨ ((p1370 ∨ p1376)) := by
  classical
  tauto

theorem initial5142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1370)) ∨ (meaning t m 3530) := by
  exact rule5142 (meaning t m 1370) (meaning t m 1376)

theorem rule5143 (p1370 p1376 : Prop) : (¬ p1376) ∨ ((p1370 ∨ p1376)) := by
  classical
  tauto

theorem initial5143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1376)) ∨ (meaning t m 3530) := by
  exact rule5143 (meaning t m 1370) (meaning t m 1376)

theorem rule5160 (p3530 p3531 : Prop) (h : (p3530 ↔ p3531)) : (¬ p3530) ∨ (p3531) := by
  classical
  tauto

theorem initial5160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3530)) ∨ (meaning t m 3531) := by
  have source := ElevenTheory.theory283 t (m.theta 1 2) (m.theta 1 8) (m.theta 2 8)
  exact rule5160 (meaning t m 3530) (meaning t m 3531) source

theorem rule5162 (p2922 p3347 p3540 : Prop) (h : (¬ p3347) ∨ (¬ p2922) ∨ (¬ p3540)) : (¬ p2922) ∨ (¬ p3347) ∨ (¬ p3540) := by
  classical
  tauto

theorem initial5162 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) := by
  have source := ElevenTheory.theory284 (m.theta 0 4) (m.theta 1 4) (m.theta 4 7)
  exact rule5162 (meaning t m 2922) (meaning t m 3347) (meaning t m 3540) source

theorem rule5163 (p2608 p3452 p3541 : Prop) (h : (¬ p2608) ∨ (¬ p3541) ∨ (¬ p3452)) : (¬ p2608) ∨ (¬ p3452) ∨ (¬ p3541) := by
  classical
  tauto

theorem initial5163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3541)) := by
  have source := ElevenTheory.theory285 (m.theta 0 1) (m.theta 1 2) (m.theta 1 4)
  exact rule5163 (meaning t m 2608) (meaning t m 3452) (meaning t m 3541) source

theorem rule5164 (p2341 p3542 p3543 p3544 : Prop) (h : (¬ p3542) ∨ (¬ p2341) ∨ (¬ p3543) ∨ (¬ p3544)) : (¬ p2341) ∨ (¬ p3542) ∨ (¬ p3543) ∨ (¬ p3544) := by
  classical
  tauto

theorem initial5164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3542)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3544)) := by
  have source := ElevenTheory.theory286 (m.theta 0 7) (m.theta 1 7) (m.theta 1 8) (m.theta 7 8)
  exact rule5164 (meaning t m 2341) (meaning t m 3542) (meaning t m 3543) (meaning t m 3544) source

theorem rule5166 (p2177 p3547 p3548 : Prop) (h : (¬ p3547) ∨ (¬ p3548) ∨ (¬ p2177)) : (¬ p2177) ∨ (¬ p3547) ∨ (¬ p3548) := by
  classical
  tauto

theorem initial5166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 3548)) := by
  have source := ElevenTheory.theory288 (m.theta 1 7) (m.theta 6 7) (m.theta 7 8)
  exact rule5166 (meaning t m 2177) (meaning t m 3547) (meaning t m 3548) source

theorem rule5167 (p2504 p2553 p3549 : Prop) (h : (¬ p2553) ∨ (¬ p3549) ∨ (¬ p2504)) : (¬ p2504) ∨ (¬ p2553) ∨ (¬ p3549) := by
  classical
  tauto

theorem initial5167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3549)) := by
  have source := ElevenTheory.theory289 (m.theta 1 6) (m.theta 4 6) (m.theta 6 7)
  exact rule5167 (meaning t m 2504) (meaning t m 2553) (meaning t m 3549) source

theorem rule5169 (p2311 p2383 p3550 p3551 : Prop) (h : (¬ p3550) ∨ (¬ p2311) ∨ (¬ p2383) ∨ (¬ p3551)) : (¬ p2311) ∨ (¬ p2383) ∨ (¬ p3550) ∨ (¬ p3551) := by
  classical
  tauto

theorem initial5169 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3551)) := by
  have source := ElevenTheory.theory291 (m.theta 0 6) (m.theta 0 7) (m.theta 6 8) (m.theta 7 8)
  exact rule5169 (meaning t m 2311) (meaning t m 2383) (meaning t m 3550) (meaning t m 3551) source

theorem rule5170 (p2177 p3552 p3553 : Prop) (h : (¬ p3552) ∨ (¬ p3553) ∨ (¬ p2177)) : (¬ p2177) ∨ (¬ p3552) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial5170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory292 (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule5170 (meaning t m 2177) (meaning t m 3552) (meaning t m 3553) source

theorem rule5171 (p3399 p3554 p3555 : Prop) (h : (¬ p3554) ∨ (¬ p3399) ∨ (¬ p3555)) : (¬ p3399) ∨ (¬ p3554) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial5171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3554)) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory293 (m.theta 0 1) (m.theta 1 5) (m.theta 1 7)
  exact rule5171 (meaning t m 3399) (meaning t m 3554) (meaning t m 3555) source

theorem rule5172 (p2901 p2957 p3556 : Prop) (h : (¬ p2957) ∨ (¬ p3556) ∨ (¬ p2901)) : (¬ p2901) ∨ (¬ p2957) ∨ (¬ p3556) := by
  classical
  tauto

theorem initial5172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) := by
  have source := ElevenTheory.theory294 (m.theta 0 5) (m.theta 3 5) (m.theta 5 7)
  exact rule5172 (meaning t m 2901) (meaning t m 2957) (meaning t m 3556) source

theorem rule5173 (p2952 p2957 p2958 : Prop) (h : (¬ p2957) ∨ (¬ p2958) ∨ (¬ p2952)) : (¬ p2952) ∨ (¬ p2957) ∨ (¬ p2958) := by
  classical
  tauto

theorem initial5173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 2958)) := by
  have source := ElevenTheory.theory295 (m.theta 0 3) (m.theta 0 5) (m.theta 3 5)
  exact rule5173 (meaning t m 2952) (meaning t m 2957) (meaning t m 2958) source

theorem rule5174 (p2230 p2656 p3238 p3487 : Prop) (h : (¬ p3238) ∨ (¬ p2656) ∨ (¬ p3487) ∨ (¬ p2230)) : (¬ p2230) ∨ (¬ p2656) ∨ (¬ p3238) ∨ (¬ p3487) := by
  classical
  tauto

theorem initial5174 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3487)) := by
  have source := ElevenTheory.theory296 (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5)
  exact rule5174 (meaning t m 2230) (meaning t m 2656) (meaning t m 3238) (meaning t m 3487) source

theorem rule5175 (p1382 p1388 : Prop) : (¬ p1382) ∨ ((p1382 ∨ p1388)) := by
  classical
  tauto

theorem initial5175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1382)) ∨ (meaning t m 3557) := by
  exact rule5175 (meaning t m 1382) (meaning t m 1388)

theorem rule5176 (p1382 p1388 : Prop) : (¬ p1388) ∨ ((p1382 ∨ p1388)) := by
  classical
  tauto

theorem initial5176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1388)) ∨ (meaning t m 3557) := by
  exact rule5176 (meaning t m 1382) (meaning t m 1388)

theorem rule5193 (p3557 p3558 : Prop) (h : (p3557 ↔ p3558)) : (¬ p3557) ∨ (p3558) := by
  classical
  tauto

theorem initial5193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3557)) ∨ (meaning t m 3558) := by
  have source := ElevenTheory.theory297 t (m.theta 4 6) (m.theta 4 9) (m.theta 6 9)
  exact rule5193 (meaning t m 3557) (meaning t m 3558) source

theorem rule5195 (p2318 p2319 p3567 p3568 : Prop) (h : (¬ p3567) ∨ (¬ p2319) ∨ (¬ p2318) ∨ (¬ p3568)) : (¬ p2318) ∨ (¬ p2319) ∨ (¬ p3567) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial5195 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory298 (m.theta 0 6) (m.theta 0 7) (m.theta 3 6) (m.theta 6 7)
  exact rule5195 (meaning t m 2318) (meaning t m 2319) (meaning t m 3567) (meaning t m 3568) source

theorem rule5196 (p2312 p2318 : Prop) (h : p2318 ∨ p2312) : (p2312) ∨ (p2318) := by
  classical
  tauto

theorem initial5196 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2312) ∨ (meaning t m 2318) := by
  have source := ElevenTheory.theory299 (m.theta 0 7) (m.theta 6 7)
  exact rule5196 (meaning t m 2312) (meaning t m 2318) source

theorem rule5198 (p2933 p3569 p3571 : Prop) (h : (¬ p3569) ∨ (¬ p2933) ∨ p3571) : (¬ p2933) ∨ (¬ p3569) ∨ (p3571) := by
  classical
  tauto

theorem initial5198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3569)) ∨ (meaning t m 3571) := by
  have source := ElevenTheory.theory301 (m.theta 1 7) (m.theta 4 7) (m.theta 5 7)
  exact rule5198 (meaning t m 2933) (meaning t m 3569) (meaning t m 3571) source

theorem rule5199 (p2264 p3037 p3548 : Prop) (h : (¬ p3548) ∨ (¬ p3037) ∨ (¬ p2264)) : (¬ p2264) ∨ (¬ p3037) ∨ (¬ p3548) := by
  classical
  tauto

theorem initial5199 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3548)) := by
  have source := ElevenTheory.theory302 (m.theta 1 7) (m.theta 3 7) (m.theta 7 8)
  exact rule5199 (meaning t m 2264) (meaning t m 3037) (meaning t m 3548) source

theorem rule5200 (p2807 p2811 p3572 : Prop) (h : (¬ p2811) ∨ (¬ p3572) ∨ (¬ p2807)) : (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial5200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory303 (m.theta 0 3) (m.theta 2 3) (m.theta 3 7)
  exact rule5200 (meaning t m 2807) (meaning t m 2811) (meaning t m 3572) source

theorem rule5201 (p2470 p2656 p3573 p3574 : Prop) (h : (¬ p3573) ∨ (¬ p2470) ∨ (¬ p3574) ∨ (¬ p2656)) : (¬ p2470) ∨ (¬ p2656) ∨ (¬ p3573) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial5201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory304 (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule5201 (meaning t m 2470) (meaning t m 2656) (meaning t m 3573) (meaning t m 3574) source

theorem rule5204 (p2064 p3578 : Prop) (h : ((¬ p2064) ↔ (¬ p3578))) : (p2064) ∨ (¬ p3578) := by
  classical
  tauto

theorem initial5204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2064) ∨ (¬ (meaning t m 3578)) := by
  have source := ElevenTheory.theory307 t (m.theta 5 8)
  exact rule5204 (meaning t m 2064) (meaning t m 3578) source

theorem rule5206 (p3574 p3579 p3580 p3581 : Prop) (h : (¬ p3579) ∨ (¬ p3580) ∨ (¬ p3574) ∨ (¬ p3581)) : (¬ p3574) ∨ (¬ p3579) ∨ (¬ p3580) ∨ (¬ p3581) := by
  classical
  tauto

theorem initial5206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3581)) := by
  have source := ElevenTheory.theory308 (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7)
  exact rule5206 (meaning t m 3574) (meaning t m 3579) (meaning t m 3580) (meaning t m 3581) source

end SunPrize.SMT
