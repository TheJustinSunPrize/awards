import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory005
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule8709 (p3309 p3547 p4452 p5144 p5145 : Prop) : (p3547) ∨ (¬ (p3547 ∧ p4452 ∧ p3309 ∧ p5144 ∧ p5145)) := by
  classical
  tauto

theorem initial8709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3547) ∨ (¬ (meaning t m 5143)) := by
  exact rule8709 (meaning t m 3309) (meaning t m 3547) (meaning t m 4452) (meaning t m 5144) (meaning t m 5145)

theorem rule8710 (p3309 p3547 p4452 p5144 p5145 : Prop) : (p4452) ∨ (¬ (p3547 ∧ p4452 ∧ p3309 ∧ p5144 ∧ p5145)) := by
  classical
  tauto

theorem initial8710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4452) ∨ (¬ (meaning t m 5143)) := by
  exact rule8710 (meaning t m 3309) (meaning t m 3547) (meaning t m 4452) (meaning t m 5144) (meaning t m 5145)

theorem rule8711 (p3309 p3547 p4452 p5144 p5145 : Prop) : (p3309) ∨ (¬ (p3547 ∧ p4452 ∧ p3309 ∧ p5144 ∧ p5145)) := by
  classical
  tauto

theorem initial8711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3309) ∨ (¬ (meaning t m 5143)) := by
  exact rule8711 (meaning t m 3309) (meaning t m 3547) (meaning t m 4452) (meaning t m 5144) (meaning t m 5145)

theorem rule8713 (p3309 p3547 p4452 p5144 p5145 : Prop) : (¬ (p3547 ∧ p4452 ∧ p3309 ∧ p5144 ∧ p5145)) ∨ (p5145) := by
  classical
  tauto

theorem initial8713 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5143)) ∨ (meaning t m 5145) := by
  exact rule8713 (meaning t m 3309) (meaning t m 3547) (meaning t m 4452) (meaning t m 5144) (meaning t m 5145)

theorem rule8717 (p5140 p5143 : Prop) : (¬ (p5140 ∨ p5143)) ∨ (p5140) ∨ (p5143) := by
  classical
  tauto

theorem initial8717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5139)) ∨ (meaning t m 5140) ∨ (meaning t m 5143) := by
  exact rule8717 (meaning t m 5140) (meaning t m 5143)

theorem rule8718 (p3303 p5139 : Prop) (h : (p3303 ↔ p5139)) : (¬ p3303) ∨ (p5139) := by
  classical
  tauto

theorem initial8718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3303)) ∨ (meaning t m 5139) := by
  have source := ElevenTheory.theory1257 t (m.theta 1 6) (m.theta 1 7) (m.theta 6 7)
  exact rule8718 (meaning t m 3303) (meaning t m 5139) source

theorem rule8720 (p2396 p4107 : Prop) (h : (¬ p4107) ∨ (¬ p2396)) : (¬ p2396) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial8720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory1258 (m.theta 6 7) (m.theta 7 9)
  exact rule8720 (meaning t m 2396) (meaning t m 4107) source

theorem rule8721 (p4026 p4430 p5148 p5149 p5150 : Prop) : (p4430) ∨ (¬ (p4430 ∧ p5148 ∧ p4026 ∧ p5149 ∧ p5150)) := by
  classical
  tauto

theorem initial8721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4430) ∨ (¬ (meaning t m 5147)) := by
  exact rule8721 (meaning t m 4026) (meaning t m 4430) (meaning t m 5148) (meaning t m 5149) (meaning t m 5150)

theorem rule8722 (p4026 p4430 p5148 p5149 p5150 : Prop) : (¬ (p4430 ∧ p5148 ∧ p4026 ∧ p5149 ∧ p5150)) ∨ (p5148) := by
  classical
  tauto

theorem initial8722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5147)) ∨ (meaning t m 5148) := by
  exact rule8722 (meaning t m 4026) (meaning t m 4430) (meaning t m 5148) (meaning t m 5149) (meaning t m 5150)

theorem rule8723 (p4026 p4430 p5148 p5149 p5150 : Prop) : (p4026) ∨ (¬ (p4430 ∧ p5148 ∧ p4026 ∧ p5149 ∧ p5150)) := by
  classical
  tauto

theorem initial8723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4026) ∨ (¬ (meaning t m 5147)) := by
  exact rule8723 (meaning t m 4026) (meaning t m 4430) (meaning t m 5148) (meaning t m 5149) (meaning t m 5150)

theorem rule8727 (p3319 p5152 p5153 p5154 p5155 : Prop) : (¬ (p5152 ∧ p5153 ∧ p3319 ∧ p5154 ∧ p5155)) ∨ (p5152) := by
  classical
  tauto

theorem initial8727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5151)) ∨ (meaning t m 5152) := by
  exact rule8727 (meaning t m 3319) (meaning t m 5152) (meaning t m 5153) (meaning t m 5154) (meaning t m 5155)

theorem rule8728 (p3319 p5152 p5153 p5154 p5155 : Prop) : (¬ (p5152 ∧ p5153 ∧ p3319 ∧ p5154 ∧ p5155)) ∨ (p5153) := by
  classical
  tauto

theorem initial8728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5151)) ∨ (meaning t m 5153) := by
  exact rule8728 (meaning t m 3319) (meaning t m 5152) (meaning t m 5153) (meaning t m 5154) (meaning t m 5155)

theorem rule8729 (p3319 p5152 p5153 p5154 p5155 : Prop) : (p3319) ∨ (¬ (p5152 ∧ p5153 ∧ p3319 ∧ p5154 ∧ p5155)) := by
  classical
  tauto

theorem initial8729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3319) ∨ (¬ (meaning t m 5151)) := by
  exact rule8729 (meaning t m 3319) (meaning t m 5152) (meaning t m 5153) (meaning t m 5154) (meaning t m 5155)

theorem rule8735 (p5147 p5151 : Prop) : (¬ (p5147 ∨ p5151)) ∨ (p5147) ∨ (p5151) := by
  classical
  tauto

theorem initial8735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5146)) ∨ (meaning t m 5147) ∨ (meaning t m 5151) := by
  exact rule8735 (meaning t m 5147) (meaning t m 5151)

theorem rule8736 (p3313 p5146 : Prop) (h : (p3313 ↔ p5146)) : (¬ p3313) ∨ (p5146) := by
  classical
  tauto

theorem initial8736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3313)) ∨ (meaning t m 5146) := by
  have source := ElevenTheory.theory1259 t (m.theta 1 6) (m.theta 1 9) (m.theta 6 9)
  exact rule8736 (meaning t m 3313) (meaning t m 5146) source

theorem rule8738 (p2027 p2528 p3063 p4026 p4171 p4384 : Prop) (h : (¬ p2528) ∨ (¬ p4384) ∨ (¬ p3063) ∨ (¬ p4171) ∨ (¬ p4026) ∨ p2027) : (p2027) ∨ (¬ p2528) ∨ (¬ p3063) ∨ (¬ p4026) ∨ (¬ p4171) ∨ (¬ p4384) := by
  classical
  tauto

theorem initial8738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4171)) ∨ (¬ (meaning t m 4384)) := by
  have source := ElevenTheory.theory1260 t (m.theta 1 6) (m.theta 4 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule8738 (meaning t m 2027) (meaning t m 2528) (meaning t m 3063) (meaning t m 4026) (meaning t m 4171) (meaning t m 4384) source

theorem rule8739 (p5158 p5159 p5160 p5161 p5162 : Prop) : (¬ (p5158 ∧ p5159 ∧ p5160 ∧ p5161 ∧ p5162)) ∨ (p5158) := by
  classical
  tauto

theorem initial8739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5157)) ∨ (meaning t m 5158) := by
  exact rule8739 (meaning t m 5158) (meaning t m 5159) (meaning t m 5160) (meaning t m 5161) (meaning t m 5162)

theorem rule8740 (p5158 p5159 p5160 p5161 p5162 : Prop) : (¬ (p5158 ∧ p5159 ∧ p5160 ∧ p5161 ∧ p5162)) ∨ (p5159) := by
  classical
  tauto

theorem initial8740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5157)) ∨ (meaning t m 5159) := by
  exact rule8740 (meaning t m 5158) (meaning t m 5159) (meaning t m 5160) (meaning t m 5161) (meaning t m 5162)

theorem rule8741 (p5158 p5159 p5160 p5161 p5162 : Prop) : (¬ (p5158 ∧ p5159 ∧ p5160 ∧ p5161 ∧ p5162)) ∨ (p5160) := by
  classical
  tauto

theorem initial8741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5157)) ∨ (meaning t m 5160) := by
  exact rule8741 (meaning t m 5158) (meaning t m 5159) (meaning t m 5160) (meaning t m 5161) (meaning t m 5162)

theorem rule8745 (p3333 p5164 p5165 p5166 p5167 : Prop) : (¬ (p5164 ∧ p5165 ∧ p3333 ∧ p5166 ∧ p5167)) ∨ (p5164) := by
  classical
  tauto

theorem initial8745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5163)) ∨ (meaning t m 5164) := by
  exact rule8745 (meaning t m 3333) (meaning t m 5164) (meaning t m 5165) (meaning t m 5166) (meaning t m 5167)

theorem rule8746 (p3333 p5164 p5165 p5166 p5167 : Prop) : (¬ (p5164 ∧ p5165 ∧ p3333 ∧ p5166 ∧ p5167)) ∨ (p5165) := by
  classical
  tauto

theorem initial8746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5163)) ∨ (meaning t m 5165) := by
  exact rule8746 (meaning t m 3333) (meaning t m 5164) (meaning t m 5165) (meaning t m 5166) (meaning t m 5167)

theorem rule8747 (p3333 p5164 p5165 p5166 p5167 : Prop) : (p3333) ∨ (¬ (p5164 ∧ p5165 ∧ p3333 ∧ p5166 ∧ p5167)) := by
  classical
  tauto

theorem initial8747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3333) ∨ (¬ (meaning t m 5163)) := by
  exact rule8747 (meaning t m 3333) (meaning t m 5164) (meaning t m 5165) (meaning t m 5166) (meaning t m 5167)

theorem rule8753 (p5157 p5163 : Prop) : (¬ (p5157 ∨ p5163)) ∨ (p5157) ∨ (p5163) := by
  classical
  tauto

theorem initial8753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5156)) ∨ (meaning t m 5157) ∨ (meaning t m 5163) := by
  exact rule8753 (meaning t m 5157) (meaning t m 5163)

theorem rule8754 (p3327 p5156 : Prop) (h : (p3327 ↔ p5156)) : (¬ p3327) ∨ (p5156) := by
  classical
  tauto

theorem initial8754 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3327)) ∨ (meaning t m 5156) := by
  have source := ElevenTheory.theory1261 t (m.theta 2 4) (m.theta 2 9) (m.theta 4 9)
  exact rule8754 (meaning t m 3327) (meaning t m 5156) source

theorem rule8756 (p2027 p3333 p3359 p3475 p4195 p4972 : Prop) (h : (¬ p4195) ∨ (¬ p3333) ∨ (¬ p3475) ∨ (¬ p3359) ∨ (¬ p4972) ∨ p2027) : (p2027) ∨ (¬ p3333) ∨ (¬ p3359) ∨ (¬ p3475) ∨ (¬ p4195) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial8756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory1262 t (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 9)
  exact rule8756 (meaning t m 2027) (meaning t m 3333) (meaning t m 3359) (meaning t m 3475) (meaning t m 4195) (meaning t m 4972) source

theorem rule8757 (p3359 p5170 p5171 p5172 p5173 : Prop) : (¬ (p5170 ∧ p5171 ∧ p3359 ∧ p5172 ∧ p5173)) ∨ (p5170) := by
  classical
  tauto

theorem initial8757 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5169)) ∨ (meaning t m 5170) := by
  exact rule8757 (meaning t m 3359) (meaning t m 5170) (meaning t m 5171) (meaning t m 5172) (meaning t m 5173)

theorem rule8758 (p3359 p5170 p5171 p5172 p5173 : Prop) : (¬ (p5170 ∧ p5171 ∧ p3359 ∧ p5172 ∧ p5173)) ∨ (p5171) := by
  classical
  tauto

theorem initial8758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5169)) ∨ (meaning t m 5171) := by
  exact rule8758 (meaning t m 3359) (meaning t m 5170) (meaning t m 5171) (meaning t m 5172) (meaning t m 5173)

theorem rule8759 (p3359 p5170 p5171 p5172 p5173 : Prop) : (p3359) ∨ (¬ (p5170 ∧ p5171 ∧ p3359 ∧ p5172 ∧ p5173)) := by
  classical
  tauto

theorem initial8759 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3359) ∨ (¬ (meaning t m 5169)) := by
  exact rule8759 (meaning t m 3359) (meaning t m 5170) (meaning t m 5171) (meaning t m 5172) (meaning t m 5173)

theorem rule8760 (p3359 p5170 p5171 p5172 p5173 : Prop) : (¬ (p5170 ∧ p5171 ∧ p3359 ∧ p5172 ∧ p5173)) ∨ (p5172) := by
  classical
  tauto

theorem initial8760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5169)) ∨ (meaning t m 5172) := by
  exact rule8760 (meaning t m 3359) (meaning t m 5170) (meaning t m 5171) (meaning t m 5172) (meaning t m 5173)

theorem rule8763 (p3343 p5175 p5176 p5177 p5178 : Prop) : (¬ (p5175 ∧ p5176 ∧ p3343 ∧ p5177 ∧ p5178)) ∨ (p5175) := by
  classical
  tauto

theorem initial8763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5174)) ∨ (meaning t m 5175) := by
  exact rule8763 (meaning t m 3343) (meaning t m 5175) (meaning t m 5176) (meaning t m 5177) (meaning t m 5178)

theorem rule8764 (p3343 p5175 p5176 p5177 p5178 : Prop) : (¬ (p5175 ∧ p5176 ∧ p3343 ∧ p5177 ∧ p5178)) ∨ (p5176) := by
  classical
  tauto

theorem initial8764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5174)) ∨ (meaning t m 5176) := by
  exact rule8764 (meaning t m 3343) (meaning t m 5175) (meaning t m 5176) (meaning t m 5177) (meaning t m 5178)

theorem rule8765 (p3343 p5175 p5176 p5177 p5178 : Prop) : (p3343) ∨ (¬ (p5175 ∧ p5176 ∧ p3343 ∧ p5177 ∧ p5178)) := by
  classical
  tauto

theorem initial8765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3343) ∨ (¬ (meaning t m 5174)) := by
  exact rule8765 (meaning t m 3343) (meaning t m 5175) (meaning t m 5176) (meaning t m 5177) (meaning t m 5178)

theorem rule8766 (p3343 p5175 p5176 p5177 p5178 : Prop) : (¬ (p5175 ∧ p5176 ∧ p3343 ∧ p5177 ∧ p5178)) ∨ (p5177) := by
  classical
  tauto

theorem initial8766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5174)) ∨ (meaning t m 5177) := by
  exact rule8766 (meaning t m 3343) (meaning t m 5175) (meaning t m 5176) (meaning t m 5177) (meaning t m 5178)

theorem rule8771 (p5169 p5174 : Prop) : (¬ (p5169 ∨ p5174)) ∨ (p5169) ∨ (p5174) := by
  classical
  tauto

theorem initial8771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5168)) ∨ (meaning t m 5169) ∨ (meaning t m 5174) := by
  exact rule8771 (meaning t m 5169) (meaning t m 5174)

theorem rule8772 (p3337 p5168 : Prop) (h : (p3337 ↔ p5168)) : (¬ p3337) ∨ (p5168) := by
  classical
  tauto

theorem initial8772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3337)) ∨ (meaning t m 5168) := by
  have source := ElevenTheory.theory1263 t (m.theta 3 4) (m.theta 3 9) (m.theta 4 9)
  exact rule8772 (meaning t m 3337) (meaning t m 5168) source

theorem rule8774 (p3346 p5181 p5182 p5183 p5184 : Prop) : (¬ (p5181 ∧ p5182 ∧ p3346 ∧ p5183 ∧ p5184)) ∨ (p5181) := by
  classical
  tauto

theorem initial8774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5180)) ∨ (meaning t m 5181) := by
  exact rule8774 (meaning t m 3346) (meaning t m 5181) (meaning t m 5182) (meaning t m 5183) (meaning t m 5184)

theorem rule8775 (p3346 p5181 p5182 p5183 p5184 : Prop) : (¬ (p5181 ∧ p5182 ∧ p3346 ∧ p5183 ∧ p5184)) ∨ (p5182) := by
  classical
  tauto

theorem initial8775 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5180)) ∨ (meaning t m 5182) := by
  exact rule8775 (meaning t m 3346) (meaning t m 5181) (meaning t m 5182) (meaning t m 5183) (meaning t m 5184)

theorem rule8776 (p3346 p5181 p5182 p5183 p5184 : Prop) : (p3346) ∨ (¬ (p5181 ∧ p5182 ∧ p3346 ∧ p5183 ∧ p5184)) := by
  classical
  tauto

theorem initial8776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3346) ∨ (¬ (meaning t m 5180)) := by
  exact rule8776 (meaning t m 3346) (meaning t m 5181) (meaning t m 5182) (meaning t m 5183) (meaning t m 5184)

theorem rule8780 (p3355 p4263 p4264 p5186 p5187 : Prop) : (p4264) ∨ (¬ (p4264 ∧ p4263 ∧ p3355 ∧ p5186 ∧ p5187)) := by
  classical
  tauto

theorem initial8780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4264) ∨ (¬ (meaning t m 5185)) := by
  exact rule8780 (meaning t m 3355) (meaning t m 4263) (meaning t m 4264) (meaning t m 5186) (meaning t m 5187)

theorem rule8781 (p3355 p4263 p4264 p5186 p5187 : Prop) : (p4263) ∨ (¬ (p4264 ∧ p4263 ∧ p3355 ∧ p5186 ∧ p5187)) := by
  classical
  tauto

theorem initial8781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4263) ∨ (¬ (meaning t m 5185)) := by
  exact rule8781 (meaning t m 3355) (meaning t m 4263) (meaning t m 4264) (meaning t m 5186) (meaning t m 5187)

theorem rule8782 (p3355 p4263 p4264 p5186 p5187 : Prop) : (p3355) ∨ (¬ (p4264 ∧ p4263 ∧ p3355 ∧ p5186 ∧ p5187)) := by
  classical
  tauto

theorem initial8782 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3355) ∨ (¬ (meaning t m 5185)) := by
  exact rule8782 (meaning t m 3355) (meaning t m 4263) (meaning t m 4264) (meaning t m 5186) (meaning t m 5187)

theorem rule8788 (p5180 p5185 : Prop) : (¬ (p5180 ∨ p5185)) ∨ (p5180) ∨ (p5185) := by
  classical
  tauto

theorem initial8788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5179)) ∨ (meaning t m 5180) ∨ (meaning t m 5185) := by
  exact rule8788 (meaning t m 5180) (meaning t m 5185)

theorem rule8789 (p3349 p5179 : Prop) (h : (p3349 ↔ p5179)) : (¬ p3349) ∨ (p5179) := by
  classical
  tauto

theorem initial8789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3349)) ∨ (meaning t m 5179) := by
  have source := ElevenTheory.theory1264 t (m.theta 0 4) (m.theta 0 9) (m.theta 4 9)
  exact rule8789 (meaning t m 3349) (meaning t m 5179) source

theorem rule8791 (p2027 p2476 p3355 p4348 p4438 p4695 : Prop) (h : (¬ p4348) ∨ (¬ p2476) ∨ (¬ p4438) ∨ p2027 ∨ (¬ p3355) ∨ (¬ p4695)) : (p2027) ∨ (¬ p2476) ∨ (¬ p3355) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4695) := by
  classical
  tauto

theorem initial8791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4695)) := by
  have source := ElevenTheory.theory1265 t (m.theta 0 4) (m.theta 4 8) (m.theta 4 9) (m.theta 7 8) (m.theta 8 9)
  exact rule8791 (meaning t m 2027) (meaning t m 2476) (meaning t m 3355) (meaning t m 4348) (meaning t m 4438) (meaning t m 4695) source

theorem rule8792 (p2027 p2743 p3367 p3683 p4315 p4701 : Prop) (h : (¬ p4701) ∨ (¬ p4315) ∨ (¬ p2743) ∨ (¬ p3683) ∨ (¬ p3367) ∨ p2027) : (p2027) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p4315) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial8792 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory1266 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5)
  exact rule8792 (meaning t m 2027) (meaning t m 2743) (meaning t m 3367) (meaning t m 3683) (meaning t m 4315) (meaning t m 4701) source

theorem rule8793 (p2027 p2741 p2811 p2946 p3367 p3662 p4752 : Prop) (h : p2027 ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p2741) ∨ (¬ p3367) ∨ (¬ p2811) ∨ (¬ p4752)) : (p2027) ∨ (¬ p2741) ∨ (¬ p2811) ∨ (¬ p2946) ∨ (¬ p3367) ∨ (¬ p3662) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial8793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory1267 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5)
  exact rule8793 (meaning t m 2027) (meaning t m 2741) (meaning t m 2811) (meaning t m 2946) (meaning t m 3367) (meaning t m 3662) (meaning t m 4752) source

theorem rule8794 (p2241 p2247 : Prop) (h : (¬ p2247) ∨ (¬ p2241)) : (¬ p2241) ∨ (¬ p2247) := by
  classical
  tauto

theorem initial8794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2247)) := by
  have source := ElevenTheory.theory1268 (m.theta 0 1) (m.theta 1 3)
  exact rule8794 (meaning t m 2241) (meaning t m 2247) source

theorem rule8795 (p2027 p2630 p2737 p3688 p4337 p4972 : Prop) (h : (¬ p4972) ∨ (¬ p3688) ∨ (¬ p4337) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4337) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial8795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory1269 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6)
  exact rule8795 (meaning t m 2027) (meaning t m 2630) (meaning t m 2737) (meaning t m 3688) (meaning t m 4337) (meaning t m 4972) source

theorem rule8796 (p2027 p2743 p3367 p3683 p4195 p4972 : Prop) (h : (¬ p4972) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p2743) ∨ (¬ p3683) ∨ (¬ p4195)) : (p2027) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p4195) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial8796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory1270 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6)
  exact rule8796 (meaning t m 2027) (meaning t m 2743) (meaning t m 3367) (meaning t m 3683) (meaning t m 4195) (meaning t m 4972) source

theorem rule8797 (p3452 p3519 p4108 p5190 p5191 : Prop) : (p4108) ∨ (¬ (p4108 ∧ p3519 ∧ p3452 ∧ p5190 ∧ p5191)) := by
  classical
  tauto

theorem initial8797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4108) ∨ (¬ (meaning t m 5189)) := by
  exact rule8797 (meaning t m 3452) (meaning t m 3519) (meaning t m 4108) (meaning t m 5190) (meaning t m 5191)

theorem rule8798 (p3452 p3519 p4108 p5190 p5191 : Prop) : (p3519) ∨ (¬ (p4108 ∧ p3519 ∧ p3452 ∧ p5190 ∧ p5191)) := by
  classical
  tauto

theorem initial8798 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3519) ∨ (¬ (meaning t m 5189)) := by
  exact rule8798 (meaning t m 3452) (meaning t m 3519) (meaning t m 4108) (meaning t m 5190) (meaning t m 5191)

theorem rule8799 (p3452 p3519 p4108 p5190 p5191 : Prop) : (p3452) ∨ (¬ (p4108 ∧ p3519 ∧ p3452 ∧ p5190 ∧ p5191)) := by
  classical
  tauto

theorem initial8799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3452) ∨ (¬ (meaning t m 5189)) := by
  exact rule8799 (meaning t m 3452) (meaning t m 3519) (meaning t m 4108) (meaning t m 5190) (meaning t m 5191)

theorem rule8800 (p3452 p3519 p4108 p5190 p5191 : Prop) : (¬ (p4108 ∧ p3519 ∧ p3452 ∧ p5190 ∧ p5191)) ∨ (p5190) := by
  classical
  tauto

theorem initial8800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5189)) ∨ (meaning t m 5190) := by
  exact rule8800 (meaning t m 3452) (meaning t m 3519) (meaning t m 4108) (meaning t m 5190) (meaning t m 5191)

theorem rule8801 (p3452 p3519 p4108 p5190 p5191 : Prop) : (¬ (p4108 ∧ p3519 ∧ p3452 ∧ p5190 ∧ p5191)) ∨ (p5191) := by
  classical
  tauto

theorem initial8801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5189)) ∨ (meaning t m 5191) := by
  exact rule8801 (meaning t m 3452) (meaning t m 3519) (meaning t m 4108) (meaning t m 5190) (meaning t m 5191)

theorem rule8803 (p3347 p3379 p4079 p5193 p5194 : Prop) : (p3347) ∨ (¬ (p3347 ∧ p4079 ∧ p3379 ∧ p5193 ∧ p5194)) := by
  classical
  tauto

theorem initial8803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3347) ∨ (¬ (meaning t m 5192)) := by
  exact rule8803 (meaning t m 3347) (meaning t m 3379) (meaning t m 4079) (meaning t m 5193) (meaning t m 5194)

theorem rule8804 (p3347 p3379 p4079 p5193 p5194 : Prop) : (p4079) ∨ (¬ (p3347 ∧ p4079 ∧ p3379 ∧ p5193 ∧ p5194)) := by
  classical
  tauto

theorem initial8804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4079) ∨ (¬ (meaning t m 5192)) := by
  exact rule8804 (meaning t m 3347) (meaning t m 3379) (meaning t m 4079) (meaning t m 5193) (meaning t m 5194)

theorem rule8805 (p3347 p3379 p4079 p5193 p5194 : Prop) : (p3379) ∨ (¬ (p3347 ∧ p4079 ∧ p3379 ∧ p5193 ∧ p5194)) := by
  classical
  tauto

theorem initial8805 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3379) ∨ (¬ (meaning t m 5192)) := by
  exact rule8805 (meaning t m 3347) (meaning t m 3379) (meaning t m 4079) (meaning t m 5193) (meaning t m 5194)

theorem rule8806 (p3347 p3379 p4079 p5193 p5194 : Prop) : (¬ (p3347 ∧ p4079 ∧ p3379 ∧ p5193 ∧ p5194)) ∨ (p5193) := by
  classical
  tauto

theorem initial8806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5192)) ∨ (meaning t m 5193) := by
  exact rule8806 (meaning t m 3347) (meaning t m 3379) (meaning t m 4079) (meaning t m 5193) (meaning t m 5194)

theorem rule8807 (p3347 p3379 p4079 p5193 p5194 : Prop) : (¬ (p3347 ∧ p4079 ∧ p3379 ∧ p5193 ∧ p5194)) ∨ (p5194) := by
  classical
  tauto

theorem initial8807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5192)) ∨ (meaning t m 5194) := by
  exact rule8807 (meaning t m 3347) (meaning t m 3379) (meaning t m 4079) (meaning t m 5193) (meaning t m 5194)

theorem rule8811 (p5189 p5192 : Prop) : (¬ (p5189 ∨ p5192)) ∨ (p5189) ∨ (p5192) := by
  classical
  tauto

theorem initial8811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5188)) ∨ (meaning t m 5189) ∨ (meaning t m 5192) := by
  exact rule8811 (meaning t m 5189) (meaning t m 5192)

theorem rule8812 (p3373 p5188 : Prop) (h : (p3373 ↔ p5188)) : (¬ p3373) ∨ (p5188) := by
  classical
  tauto

theorem initial8812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3373)) ∨ (meaning t m 5188) := by
  have source := ElevenTheory.theory1271 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4)
  exact rule8812 (meaning t m 3373) (meaning t m 5188) source

theorem rule8814 (p3540 p3575 p5197 p5198 p5199 : Prop) : (¬ (p5197 ∧ p3575 ∧ p3540 ∧ p5198 ∧ p5199)) ∨ (p5197) := by
  classical
  tauto

theorem initial8814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5196)) ∨ (meaning t m 5197) := by
  exact rule8814 (meaning t m 3540) (meaning t m 3575) (meaning t m 5197) (meaning t m 5198) (meaning t m 5199)

theorem rule8815 (p3540 p3575 p5197 p5198 p5199 : Prop) : (p3575) ∨ (¬ (p5197 ∧ p3575 ∧ p3540 ∧ p5198 ∧ p5199)) := by
  classical
  tauto

theorem initial8815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3575) ∨ (¬ (meaning t m 5196)) := by
  exact rule8815 (meaning t m 3540) (meaning t m 3575) (meaning t m 5197) (meaning t m 5198) (meaning t m 5199)

theorem rule8816 (p3540 p3575 p5197 p5198 p5199 : Prop) : (p3540) ∨ (¬ (p5197 ∧ p3575 ∧ p3540 ∧ p5198 ∧ p5199)) := by
  classical
  tauto

theorem initial8816 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3540) ∨ (¬ (meaning t m 5196)) := by
  exact rule8816 (meaning t m 3540) (meaning t m 3575) (meaning t m 5197) (meaning t m 5198) (meaning t m 5199)

theorem rule8818 (p3540 p3575 p5197 p5198 p5199 : Prop) : (¬ (p5197 ∧ p3575 ∧ p3540 ∧ p5198 ∧ p5199)) ∨ (p5199) := by
  classical
  tauto

theorem initial8818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5196)) ∨ (meaning t m 5199) := by
  exact rule8818 (meaning t m 3540) (meaning t m 3575) (meaning t m 5197) (meaning t m 5198) (meaning t m 5199)

theorem rule8820 (p3389 p4279 p5201 p5202 p5203 : Prop) : (p4279) ∨ (¬ (p4279 ∧ p5201 ∧ p3389 ∧ p5202 ∧ p5203)) := by
  classical
  tauto

theorem initial8820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4279) ∨ (¬ (meaning t m 5200)) := by
  exact rule8820 (meaning t m 3389) (meaning t m 4279) (meaning t m 5201) (meaning t m 5202) (meaning t m 5203)

theorem rule8821 (p3389 p4279 p5201 p5202 p5203 : Prop) : (¬ (p4279 ∧ p5201 ∧ p3389 ∧ p5202 ∧ p5203)) ∨ (p5201) := by
  classical
  tauto

theorem initial8821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5200)) ∨ (meaning t m 5201) := by
  exact rule8821 (meaning t m 3389) (meaning t m 4279) (meaning t m 5201) (meaning t m 5202) (meaning t m 5203)

theorem rule8822 (p3389 p4279 p5201 p5202 p5203 : Prop) : (p3389) ∨ (¬ (p4279 ∧ p5201 ∧ p3389 ∧ p5202 ∧ p5203)) := by
  classical
  tauto

theorem initial8822 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3389) ∨ (¬ (meaning t m 5200)) := by
  exact rule8822 (meaning t m 3389) (meaning t m 4279) (meaning t m 5201) (meaning t m 5202) (meaning t m 5203)

theorem rule8824 (p3389 p4279 p5201 p5202 p5203 : Prop) : (¬ (p4279 ∧ p5201 ∧ p3389 ∧ p5202 ∧ p5203)) ∨ (p5203) := by
  classical
  tauto

theorem initial8824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5200)) ∨ (meaning t m 5203) := by
  exact rule8824 (meaning t m 3389) (meaning t m 4279) (meaning t m 5201) (meaning t m 5202) (meaning t m 5203)

theorem rule8828 (p5196 p5200 : Prop) : (¬ (p5196 ∨ p5200)) ∨ (p5196) ∨ (p5200) := by
  classical
  tauto

theorem initial8828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5195)) ∨ (meaning t m 5196) ∨ (meaning t m 5200) := by
  exact rule8828 (meaning t m 5196) (meaning t m 5200)

theorem rule8829 (p3383 p5195 : Prop) (h : (p3383 ↔ p5195)) : (¬ p3383) ∨ (p5195) := by
  classical
  tauto

theorem initial8829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3383)) ∨ (meaning t m 5195) := by
  have source := ElevenTheory.theory1272 t (m.theta 0 4) (m.theta 0 7) (m.theta 4 7)
  exact rule8829 (meaning t m 3383) (meaning t m 5195) source

theorem rule8831 (p3543 p4366 p5206 p5207 p5208 : Prop) : (¬ (p5206 ∧ p3543 ∧ p4366 ∧ p5207 ∧ p5208)) ∨ (p5206) := by
  classical
  tauto

theorem initial8831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5205)) ∨ (meaning t m 5206) := by
  exact rule8831 (meaning t m 3543) (meaning t m 4366) (meaning t m 5206) (meaning t m 5207) (meaning t m 5208)

theorem rule8832 (p3543 p4366 p5206 p5207 p5208 : Prop) : (p3543) ∨ (¬ (p5206 ∧ p3543 ∧ p4366 ∧ p5207 ∧ p5208)) := by
  classical
  tauto

theorem initial8832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3543) ∨ (¬ (meaning t m 5205)) := by
  exact rule8832 (meaning t m 3543) (meaning t m 4366) (meaning t m 5206) (meaning t m 5207) (meaning t m 5208)

theorem rule8833 (p3543 p4366 p5206 p5207 p5208 : Prop) : (p4366) ∨ (¬ (p5206 ∧ p3543 ∧ p4366 ∧ p5207 ∧ p5208)) := by
  classical
  tauto

theorem initial8833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4366) ∨ (¬ (meaning t m 5205)) := by
  exact rule8833 (meaning t m 3543) (meaning t m 4366) (meaning t m 5206) (meaning t m 5207) (meaning t m 5208)

theorem rule8834 (p3543 p4366 p5206 p5207 p5208 : Prop) : (¬ (p5206 ∧ p3543 ∧ p4366 ∧ p5207 ∧ p5208)) ∨ (p5207) := by
  classical
  tauto

theorem initial8834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5205)) ∨ (meaning t m 5207) := by
  exact rule8834 (meaning t m 3543) (meaning t m 4366) (meaning t m 5206) (meaning t m 5207) (meaning t m 5208)

theorem rule8837 (p3399 p3545 p3546 p5210 p5211 : Prop) : (p3546) ∨ (¬ (p3546 ∧ p3545 ∧ p3399 ∧ p5210 ∧ p5211)) := by
  classical
  tauto

theorem initial8837 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3546) ∨ (¬ (meaning t m 5209)) := by
  exact rule8837 (meaning t m 3399) (meaning t m 3545) (meaning t m 3546) (meaning t m 5210) (meaning t m 5211)

theorem rule8838 (p3399 p3545 p3546 p5210 p5211 : Prop) : (p3545) ∨ (¬ (p3546 ∧ p3545 ∧ p3399 ∧ p5210 ∧ p5211)) := by
  classical
  tauto

theorem initial8838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3545) ∨ (¬ (meaning t m 5209)) := by
  exact rule8838 (meaning t m 3399) (meaning t m 3545) (meaning t m 3546) (meaning t m 5210) (meaning t m 5211)

theorem rule8839 (p3399 p3545 p3546 p5210 p5211 : Prop) : (p3399) ∨ (¬ (p3546 ∧ p3545 ∧ p3399 ∧ p5210 ∧ p5211)) := by
  classical
  tauto

theorem initial8839 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3399) ∨ (¬ (meaning t m 5209)) := by
  exact rule8839 (meaning t m 3399) (meaning t m 3545) (meaning t m 3546) (meaning t m 5210) (meaning t m 5211)

theorem rule8840 (p3399 p3545 p3546 p5210 p5211 : Prop) : (¬ (p3546 ∧ p3545 ∧ p3399 ∧ p5210 ∧ p5211)) ∨ (p5210) := by
  classical
  tauto

theorem initial8840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5209)) ∨ (meaning t m 5210) := by
  exact rule8840 (meaning t m 3399) (meaning t m 3545) (meaning t m 3546) (meaning t m 5210) (meaning t m 5211)

theorem rule8845 (p5205 p5209 : Prop) : (¬ (p5205 ∨ p5209)) ∨ (p5205) ∨ (p5209) := by
  classical
  tauto

theorem initial8845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5204)) ∨ (meaning t m 5205) ∨ (meaning t m 5209) := by
  exact rule8845 (meaning t m 5205) (meaning t m 5209)

theorem rule8846 (p3393 p5204 : Prop) (h : (p3393 ↔ p5204)) : (¬ p3393) ∨ (p5204) := by
  classical
  tauto

theorem initial8846 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3393)) ∨ (meaning t m 5204) := by
  have source := ElevenTheory.theory1273 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 7)
  exact rule8846 (meaning t m 3393) (meaning t m 5204) source

theorem rule8848 (p2027 p2241 p2727 p3032 p4366 p4650 : Prop) (h : (¬ p3032) ∨ (¬ p4366) ∨ (¬ p2727) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p4650)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3032) ∨ (¬ p4366) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial8848 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory1274 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 7)
  exact rule8848 (meaning t m 2027) (meaning t m 2241) (meaning t m 2727) (meaning t m 3032) (meaning t m 4366) (meaning t m 4650) source

theorem rule8849 (p2027 p2241 p2254 p3027 p3414 : Prop) (h : (¬ p2254) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p2241) ∨ (¬ p3414)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2254) ∨ (¬ p3027) ∨ (¬ p3414) := by
  classical
  tauto

theorem initial8849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) := by
  have source := ElevenTheory.theory1275 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 7)
  exact rule8849 (meaning t m 2027) (meaning t m 2241) (meaning t m 2254) (meaning t m 3027) (meaning t m 3414) source

theorem rule8850 (p2027 p2247 p3379 p3487 p3662 p4701 : Prop) (h : (¬ p4701) ∨ (¬ p3487) ∨ (¬ p3662) ∨ (¬ p3379) ∨ (¬ p2247) ∨ p2027) : (p2027) ∨ (¬ p2247) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p3662) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial8850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory1276 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5)
  exact rule8850 (meaning t m 2027) (meaning t m 2247) (meaning t m 3379) (meaning t m 3487) (meaning t m 3662) (meaning t m 4701) source

theorem rule8851 (p3585 p3590 p4257 p4376 p5214 : Prop) : (p4257) ∨ (¬ (p4257 ∧ p3590 ∧ p3585 ∧ p4376 ∧ p5214)) := by
  classical
  tauto

theorem initial8851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4257) ∨ (¬ (meaning t m 5213)) := by
  exact rule8851 (meaning t m 3585) (meaning t m 3590) (meaning t m 4257) (meaning t m 4376) (meaning t m 5214)

theorem rule8852 (p3585 p3590 p4257 p4376 p5214 : Prop) : (p3590) ∨ (¬ (p4257 ∧ p3590 ∧ p3585 ∧ p4376 ∧ p5214)) := by
  classical
  tauto

theorem initial8852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3590) ∨ (¬ (meaning t m 5213)) := by
  exact rule8852 (meaning t m 3585) (meaning t m 3590) (meaning t m 4257) (meaning t m 4376) (meaning t m 5214)

theorem rule8853 (p3585 p3590 p4257 p4376 p5214 : Prop) : (p3585) ∨ (¬ (p4257 ∧ p3590 ∧ p3585 ∧ p4376 ∧ p5214)) := by
  classical
  tauto

theorem initial8853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3585) ∨ (¬ (meaning t m 5213)) := by
  exact rule8853 (meaning t m 3585) (meaning t m 3590) (meaning t m 4257) (meaning t m 4376) (meaning t m 5214)

theorem rule8854 (p3585 p3590 p4257 p4376 p5214 : Prop) : (p4376) ∨ (¬ (p4257 ∧ p3590 ∧ p3585 ∧ p4376 ∧ p5214)) := by
  classical
  tauto

theorem initial8854 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4376) ∨ (¬ (meaning t m 5213)) := by
  exact rule8854 (meaning t m 3585) (meaning t m 3590) (meaning t m 4257) (meaning t m 4376) (meaning t m 5214)

theorem rule8855 (p3585 p3590 p4257 p4376 p5214 : Prop) : (¬ (p4257 ∧ p3590 ∧ p3585 ∧ p4376 ∧ p5214)) ∨ (p5214) := by
  classical
  tauto

theorem initial8855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5213)) ∨ (meaning t m 5214) := by
  exact rule8855 (meaning t m 3585) (meaning t m 3590) (meaning t m 4257) (meaning t m 4376) (meaning t m 5214)

theorem rule8857 (p3367 p3541 p4030 p5216 p5217 : Prop) : (p4030) ∨ (¬ (p4030 ∧ p3541 ∧ p3367 ∧ p5216 ∧ p5217)) := by
  classical
  tauto

theorem initial8857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4030) ∨ (¬ (meaning t m 5215)) := by
  exact rule8857 (meaning t m 3367) (meaning t m 3541) (meaning t m 4030) (meaning t m 5216) (meaning t m 5217)

theorem rule8858 (p3367 p3541 p4030 p5216 p5217 : Prop) : (p3541) ∨ (¬ (p4030 ∧ p3541 ∧ p3367 ∧ p5216 ∧ p5217)) := by
  classical
  tauto

theorem initial8858 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3541) ∨ (¬ (meaning t m 5215)) := by
  exact rule8858 (meaning t m 3367) (meaning t m 3541) (meaning t m 4030) (meaning t m 5216) (meaning t m 5217)

theorem rule8859 (p3367 p3541 p4030 p5216 p5217 : Prop) : (p3367) ∨ (¬ (p4030 ∧ p3541 ∧ p3367 ∧ p5216 ∧ p5217)) := by
  classical
  tauto

theorem initial8859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3367) ∨ (¬ (meaning t m 5215)) := by
  exact rule8859 (meaning t m 3367) (meaning t m 3541) (meaning t m 4030) (meaning t m 5216) (meaning t m 5217)

theorem rule8860 (p3367 p3541 p4030 p5216 p5217 : Prop) : (¬ (p4030 ∧ p3541 ∧ p3367 ∧ p5216 ∧ p5217)) ∨ (p5216) := by
  classical
  tauto

theorem initial8860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5215)) ∨ (meaning t m 5216) := by
  exact rule8860 (meaning t m 3367) (meaning t m 3541) (meaning t m 4030) (meaning t m 5216) (meaning t m 5217)

theorem rule8861 (p3367 p3541 p4030 p5216 p5217 : Prop) : (¬ (p4030 ∧ p3541 ∧ p3367 ∧ p5216 ∧ p5217)) ∨ (p5217) := by
  classical
  tauto

theorem initial8861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5215)) ∨ (meaning t m 5217) := by
  exact rule8861 (meaning t m 3367) (meaning t m 3541) (meaning t m 4030) (meaning t m 5216) (meaning t m 5217)

theorem rule8865 (p5213 p5215 : Prop) : (¬ (p5213 ∨ p5215)) ∨ (p5213) ∨ (p5215) := by
  classical
  tauto

theorem initial8865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5212)) ∨ (meaning t m 5213) ∨ (meaning t m 5215) := by
  exact rule8865 (meaning t m 5213) (meaning t m 5215)

theorem rule8866 (p3404 p5212 : Prop) (h : (p3404 ↔ p5212)) : (¬ p3404) ∨ (p5212) := by
  classical
  tauto

theorem initial8866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3404)) ∨ (meaning t m 5212) := by
  have source := ElevenTheory.theory1277 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 4)
  exact rule8866 (meaning t m 3404) (meaning t m 5212) source

theorem rule8868 (p2027 p2437 p2727 p3662 p3879 p4646 : Prop) (h : (¬ p3879) ∨ (¬ p2727) ∨ (¬ p2437) ∨ (¬ p4646) ∨ p2027 ∨ (¬ p3662)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial8868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory1278 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7)
  exact rule8868 (meaning t m 2027) (meaning t m 2437) (meaning t m 2727) (meaning t m 3662) (meaning t m 3879) (meaning t m 4646) source

theorem rule8869 (p2992 p3662 : Prop) (h : (¬ p3662) ∨ (¬ p2992)) : (¬ p2992) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial8869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory1279 (m.theta 1 3) (m.theta 3 5)
  exact rule8869 (meaning t m 2992) (meaning t m 3662) source

theorem rule8871 (p3584 p4342 p5220 p5221 p5222 : Prop) : (¬ (p5220 ∧ p4342 ∧ p3584 ∧ p5221 ∧ p5222)) ∨ (p5220) := by
  classical
  tauto

theorem initial8871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5219)) ∨ (meaning t m 5220) := by
  exact rule8871 (meaning t m 3584) (meaning t m 4342) (meaning t m 5220) (meaning t m 5221) (meaning t m 5222)

theorem rule8872 (p3584 p4342 p5220 p5221 p5222 : Prop) : (p4342) ∨ (¬ (p5220 ∧ p4342 ∧ p3584 ∧ p5221 ∧ p5222)) := by
  classical
  tauto

theorem initial8872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4342) ∨ (¬ (meaning t m 5219)) := by
  exact rule8872 (meaning t m 3584) (meaning t m 4342) (meaning t m 5220) (meaning t m 5221) (meaning t m 5222)

theorem rule8873 (p3584 p4342 p5220 p5221 p5222 : Prop) : (p3584) ∨ (¬ (p5220 ∧ p4342 ∧ p3584 ∧ p5221 ∧ p5222)) := by
  classical
  tauto

theorem initial8873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3584) ∨ (¬ (meaning t m 5219)) := by
  exact rule8873 (meaning t m 3584) (meaning t m 4342) (meaning t m 5220) (meaning t m 5221) (meaning t m 5222)

theorem rule8874 (p3584 p4342 p5220 p5221 p5222 : Prop) : (¬ (p5220 ∧ p4342 ∧ p3584 ∧ p5221 ∧ p5222)) ∨ (p5221) := by
  classical
  tauto

theorem initial8874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5219)) ∨ (meaning t m 5221) := by
  exact rule8874 (meaning t m 3584) (meaning t m 4342) (meaning t m 5220) (meaning t m 5221) (meaning t m 5222)

theorem rule8875 (p3584 p4342 p5220 p5221 p5222 : Prop) : (¬ (p5220 ∧ p4342 ∧ p3584 ∧ p5221 ∧ p5222)) ∨ (p5222) := by
  classical
  tauto

theorem initial8875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5219)) ∨ (meaning t m 5222) := by
  exact rule8875 (meaning t m 3584) (meaning t m 4342) (meaning t m 5220) (meaning t m 5221) (meaning t m 5222)

theorem rule8877 (p3422 p4375 p4390 p5224 p5225 : Prop) : (p4390) ∨ (¬ (p4390 ∧ p4375 ∧ p3422 ∧ p5224 ∧ p5225)) := by
  classical
  tauto

theorem initial8877 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4390) ∨ (¬ (meaning t m 5223)) := by
  exact rule8877 (meaning t m 3422) (meaning t m 4375) (meaning t m 4390) (meaning t m 5224) (meaning t m 5225)

theorem rule8878 (p3422 p4375 p4390 p5224 p5225 : Prop) : (p4375) ∨ (¬ (p4390 ∧ p4375 ∧ p3422 ∧ p5224 ∧ p5225)) := by
  classical
  tauto

theorem initial8878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4375) ∨ (¬ (meaning t m 5223)) := by
  exact rule8878 (meaning t m 3422) (meaning t m 4375) (meaning t m 4390) (meaning t m 5224) (meaning t m 5225)

theorem rule8879 (p3422 p4375 p4390 p5224 p5225 : Prop) : (p3422) ∨ (¬ (p4390 ∧ p4375 ∧ p3422 ∧ p5224 ∧ p5225)) := by
  classical
  tauto

theorem initial8879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3422) ∨ (¬ (meaning t m 5223)) := by
  exact rule8879 (meaning t m 3422) (meaning t m 4375) (meaning t m 4390) (meaning t m 5224) (meaning t m 5225)

theorem rule8880 (p3422 p4375 p4390 p5224 p5225 : Prop) : (¬ (p4390 ∧ p4375 ∧ p3422 ∧ p5224 ∧ p5225)) ∨ (p5224) := by
  classical
  tauto

theorem initial8880 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5223)) ∨ (meaning t m 5224) := by
  exact rule8880 (meaning t m 3422) (meaning t m 4375) (meaning t m 4390) (meaning t m 5224) (meaning t m 5225)

theorem rule8881 (p3422 p4375 p4390 p5224 p5225 : Prop) : (¬ (p4390 ∧ p4375 ∧ p3422 ∧ p5224 ∧ p5225)) ∨ (p5225) := by
  classical
  tauto

theorem initial8881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5223)) ∨ (meaning t m 5225) := by
  exact rule8881 (meaning t m 3422) (meaning t m 4375) (meaning t m 4390) (meaning t m 5224) (meaning t m 5225)

theorem rule8885 (p5219 p5223 : Prop) : (¬ (p5219 ∨ p5223)) ∨ (p5219) ∨ (p5223) := by
  classical
  tauto

theorem initial8885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5218)) ∨ (meaning t m 5219) ∨ (meaning t m 5223) := by
  exact rule8885 (meaning t m 5219) (meaning t m 5223)

theorem rule8886 (p3416 p5218 : Prop) (h : (p3416 ↔ p5218)) : (¬ p3416) ∨ (p5218) := by
  classical
  tauto

theorem initial8886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3416)) ∨ (meaning t m 5218) := by
  have source := ElevenTheory.theory1281 t (m.theta 2 4) (m.theta 2 6) (m.theta 4 6)
  exact rule8886 (meaning t m 3416) (meaning t m 5218) source

theorem rule8888 (p2027 p2598 p3005 p3172 p4236 p4752 : Prop) (h : p2027 ∨ (¬ p4236) ∨ (¬ p2598) ∨ (¬ p4752) ∨ (¬ p3172) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p4236) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial8888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory1282 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 8)
  exact rule8888 (meaning t m 2027) (meaning t m 2598) (meaning t m 3005) (meaning t m 3172) (meaning t m 4236) (meaning t m 4752) source

theorem rule8889 (p2027 p2651 p2780 p2810 p4117 p4842 : Prop) (h : p2027 ∨ (¬ p4117) ∨ (¬ p2780) ∨ (¬ p4842) ∨ (¬ p2810) ∨ (¬ p2651)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2780) ∨ (¬ p2810) ∨ (¬ p4117) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial8889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory1283 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4)
  exact rule8889 (meaning t m 2027) (meaning t m 2651) (meaning t m 2780) (meaning t m 2810) (meaning t m 4117) (meaning t m 4842) source

theorem rule8890 (p2027 p2299 p2319 p2341 p2788 p3822 : Prop) (h : (¬ p2788) ∨ p2027 ∨ (¬ p2319) ∨ (¬ p3822) ∨ (¬ p2341) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2788) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial8890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2788)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory1284 t (m.theta 0 6) (m.theta 0 7) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule8890 (meaning t m 2027) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 2788) (meaning t m 3822) source

theorem rule8891 (p4324 p5228 p5229 p5230 p5231 : Prop) : (¬ (p5228 ∧ p5229 ∧ p4324 ∧ p5230 ∧ p5231)) ∨ (p5228) := by
  classical
  tauto

theorem initial8891 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5227)) ∨ (meaning t m 5228) := by
  exact rule8891 (meaning t m 4324) (meaning t m 5228) (meaning t m 5229) (meaning t m 5230) (meaning t m 5231)

theorem rule8892 (p4324 p5228 p5229 p5230 p5231 : Prop) : (¬ (p5228 ∧ p5229 ∧ p4324 ∧ p5230 ∧ p5231)) ∨ (p5229) := by
  classical
  tauto

theorem initial8892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5227)) ∨ (meaning t m 5229) := by
  exact rule8892 (meaning t m 4324) (meaning t m 5228) (meaning t m 5229) (meaning t m 5230) (meaning t m 5231)

theorem rule8893 (p4324 p5228 p5229 p5230 p5231 : Prop) : (p4324) ∨ (¬ (p5228 ∧ p5229 ∧ p4324 ∧ p5230 ∧ p5231)) := by
  classical
  tauto

theorem initial8893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4324) ∨ (¬ (meaning t m 5227)) := by
  exact rule8893 (meaning t m 4324) (meaning t m 5228) (meaning t m 5229) (meaning t m 5230) (meaning t m 5231)

theorem rule8897 (p3434 p5233 p5234 p5235 p5236 : Prop) : (¬ (p5233 ∧ p5234 ∧ p3434 ∧ p5235 ∧ p5236)) ∨ (p5233) := by
  classical
  tauto

theorem initial8897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5232)) ∨ (meaning t m 5233) := by
  exact rule8897 (meaning t m 3434) (meaning t m 5233) (meaning t m 5234) (meaning t m 5235) (meaning t m 5236)

theorem rule8898 (p3434 p5233 p5234 p5235 p5236 : Prop) : (¬ (p5233 ∧ p5234 ∧ p3434 ∧ p5235 ∧ p5236)) ∨ (p5234) := by
  classical
  tauto

theorem initial8898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5232)) ∨ (meaning t m 5234) := by
  exact rule8898 (meaning t m 3434) (meaning t m 5233) (meaning t m 5234) (meaning t m 5235) (meaning t m 5236)

theorem rule8899 (p3434 p5233 p5234 p5235 p5236 : Prop) : (p3434) ∨ (¬ (p5233 ∧ p5234 ∧ p3434 ∧ p5235 ∧ p5236)) := by
  classical
  tauto

theorem initial8899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3434) ∨ (¬ (meaning t m 5232)) := by
  exact rule8899 (meaning t m 3434) (meaning t m 5233) (meaning t m 5234) (meaning t m 5235) (meaning t m 5236)

theorem rule8905 (p5227 p5232 : Prop) : (¬ (p5227 ∨ p5232)) ∨ (p5227) ∨ (p5232) := by
  classical
  tauto

theorem initial8905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5226)) ∨ (meaning t m 5227) ∨ (meaning t m 5232) := by
  exact rule8905 (meaning t m 5227) (meaning t m 5232)

theorem rule8906 (p3428 p5226 : Prop) (h : (p3428 ↔ p5226)) : (¬ p3428) ∨ (p5226) := by
  classical
  tauto

theorem initial8906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3428)) ∨ (meaning t m 5226) := by
  have source := ElevenTheory.theory1285 t (m.theta 2 7) (m.theta 2 9) (m.theta 7 9)
  exact rule8906 (meaning t m 3428) (meaning t m 5226) source

theorem rule8908 (p2027 p2518 p2651 p3172 p4437 p4814 : Prop) (h : p2027 ∨ (¬ p2518) ∨ (¬ p4437) ∨ (¬ p3172) ∨ (¬ p2651) ∨ (¬ p4814)) : (p2027) ∨ (¬ p2518) ∨ (¬ p2651) ∨ (¬ p3172) ∨ (¬ p4437) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial8908 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4437)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory1286 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule8908 (meaning t m 2027) (meaning t m 2518) (meaning t m 2651) (meaning t m 3172) (meaning t m 4437) (meaning t m 4814) source

theorem rule8909 (p3439 p3860 p4416 p5239 p5240 : Prop) : (p4416) ∨ (¬ (p4416 ∧ p3439 ∧ p3860 ∧ p5239 ∧ p5240)) := by
  classical
  tauto

theorem initial8909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4416) ∨ (¬ (meaning t m 5238)) := by
  exact rule8909 (meaning t m 3439) (meaning t m 3860) (meaning t m 4416) (meaning t m 5239) (meaning t m 5240)

theorem rule8910 (p3439 p3860 p4416 p5239 p5240 : Prop) : (p3439) ∨ (¬ (p4416 ∧ p3439 ∧ p3860 ∧ p5239 ∧ p5240)) := by
  classical
  tauto

theorem initial8910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3439) ∨ (¬ (meaning t m 5238)) := by
  exact rule8910 (meaning t m 3439) (meaning t m 3860) (meaning t m 4416) (meaning t m 5239) (meaning t m 5240)

theorem rule8911 (p3439 p3860 p4416 p5239 p5240 : Prop) : (p3860) ∨ (¬ (p4416 ∧ p3439 ∧ p3860 ∧ p5239 ∧ p5240)) := by
  classical
  tauto

theorem initial8911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3860) ∨ (¬ (meaning t m 5238)) := by
  exact rule8911 (meaning t m 3439) (meaning t m 3860) (meaning t m 4416) (meaning t m 5239) (meaning t m 5240)

theorem rule8916 (p3449 p3858 p5242 p5243 p5244 : Prop) : (¬ (p3858 ∧ p5242 ∧ p3449 ∧ p5243 ∧ p5244)) ∨ (p5242) := by
  classical
  tauto

theorem initial8916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5241)) ∨ (meaning t m 5242) := by
  exact rule8916 (meaning t m 3449) (meaning t m 3858) (meaning t m 5242) (meaning t m 5243) (meaning t m 5244)

theorem rule8917 (p3449 p3858 p5242 p5243 p5244 : Prop) : (p3449) ∨ (¬ (p3858 ∧ p5242 ∧ p3449 ∧ p5243 ∧ p5244)) := by
  classical
  tauto

theorem initial8917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3449) ∨ (¬ (meaning t m 5241)) := by
  exact rule8917 (meaning t m 3449) (meaning t m 3858) (meaning t m 5242) (meaning t m 5243) (meaning t m 5244)

theorem rule8923 (p5238 p5241 : Prop) : (¬ (p5238 ∨ p5241)) ∨ (p5238) ∨ (p5241) := by
  classical
  tauto

theorem initial8923 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5237)) ∨ (meaning t m 5238) ∨ (meaning t m 5241) := by
  exact rule8923 (meaning t m 5238) (meaning t m 5241)

theorem rule8924 (p3443 p5237 : Prop) (h : (p3443 ↔ p5237)) : (¬ p3443) ∨ (p5237) := by
  classical
  tauto

theorem initial8924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3443)) ∨ (meaning t m 5237) := by
  have source := ElevenTheory.theory1287 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 8)
  exact rule8924 (meaning t m 3443) (meaning t m 5237) source

theorem rule8928 (p4191 p5247 p5248 p5249 p5250 : Prop) : (p4191) ∨ (¬ (p5247 ∧ p5248 ∧ p4191 ∧ p5249 ∧ p5250)) := by
  classical
  tauto

theorem initial8928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4191) ∨ (¬ (meaning t m 5246)) := by
  exact rule8928 (meaning t m 4191) (meaning t m 5247) (meaning t m 5248) (meaning t m 5249) (meaning t m 5250)

theorem rule8929 (p4191 p5247 p5248 p5249 p5250 : Prop) : (¬ (p5247 ∧ p5248 ∧ p4191 ∧ p5249 ∧ p5250)) ∨ (p5249) := by
  classical
  tauto

theorem initial8929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5246)) ∨ (meaning t m 5249) := by
  exact rule8929 (meaning t m 4191) (meaning t m 5247) (meaning t m 5248) (meaning t m 5249) (meaning t m 5250)

theorem rule8930 (p4191 p5247 p5248 p5249 p5250 : Prop) : (¬ (p5247 ∧ p5248 ∧ p4191 ∧ p5249 ∧ p5250)) ∨ (p5250) := by
  classical
  tauto

theorem initial8930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5246)) ∨ (meaning t m 5250) := by
  exact rule8930 (meaning t m 4191) (meaning t m 5247) (meaning t m 5248) (meaning t m 5249) (meaning t m 5250)

theorem rule8933 (p3461 p4394 p5252 p5253 p5254 : Prop) : (p4394) ∨ (¬ (p5252 ∧ p4394 ∧ p3461 ∧ p5253 ∧ p5254)) := by
  classical
  tauto

theorem initial8933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4394) ∨ (¬ (meaning t m 5251)) := by
  exact rule8933 (meaning t m 3461) (meaning t m 4394) (meaning t m 5252) (meaning t m 5253) (meaning t m 5254)

theorem rule8934 (p3461 p4394 p5252 p5253 p5254 : Prop) : (p3461) ∨ (¬ (p5252 ∧ p4394 ∧ p3461 ∧ p5253 ∧ p5254)) := by
  classical
  tauto

theorem initial8934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3461) ∨ (¬ (meaning t m 5251)) := by
  exact rule8934 (meaning t m 3461) (meaning t m 4394) (meaning t m 5252) (meaning t m 5253) (meaning t m 5254)

theorem rule8936 (p3461 p4394 p5252 p5253 p5254 : Prop) : (¬ (p5252 ∧ p4394 ∧ p3461 ∧ p5253 ∧ p5254)) ∨ (p5254) := by
  classical
  tauto

theorem initial8936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5251)) ∨ (meaning t m 5254) := by
  exact rule8936 (meaning t m 3461) (meaning t m 4394) (meaning t m 5252) (meaning t m 5253) (meaning t m 5254)

theorem rule8940 (p5246 p5251 : Prop) : (¬ (p5246 ∨ p5251)) ∨ (p5246) ∨ (p5251) := by
  classical
  tauto

theorem initial8940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5245)) ∨ (meaning t m 5246) ∨ (meaning t m 5251) := by
  exact rule8940 (meaning t m 5246) (meaning t m 5251)

theorem rule8941 (p3455 p5245 : Prop) (h : (p3455 ↔ p5245)) : (¬ p3455) ∨ (p5245) := by
  classical
  tauto

theorem initial8941 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3455)) ∨ (meaning t m 5245) := by
  have source := ElevenTheory.theory1288 t (m.theta 6 10) (m.theta 6 9) (m.theta 9 10)
  exact rule8941 (meaning t m 3455) (meaning t m 5245) source

theorem rule8943 (p3425 p3577 p3820 p5257 p5258 : Prop) : (p3820) ∨ (¬ (p3820 ∧ p3577 ∧ p3425 ∧ p5257 ∧ p5258)) := by
  classical
  tauto

theorem initial8943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3820) ∨ (¬ (meaning t m 5256)) := by
  exact rule8943 (meaning t m 3425) (meaning t m 3577) (meaning t m 3820) (meaning t m 5257) (meaning t m 5258)

theorem rule8944 (p3425 p3577 p3820 p5257 p5258 : Prop) : (p3577) ∨ (¬ (p3820 ∧ p3577 ∧ p3425 ∧ p5257 ∧ p5258)) := by
  classical
  tauto

theorem initial8944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3577) ∨ (¬ (meaning t m 5256)) := by
  exact rule8944 (meaning t m 3425) (meaning t m 3577) (meaning t m 3820) (meaning t m 5257) (meaning t m 5258)

theorem rule8945 (p3425 p3577 p3820 p5257 p5258 : Prop) : (p3425) ∨ (¬ (p3820 ∧ p3577 ∧ p3425 ∧ p5257 ∧ p5258)) := by
  classical
  tauto

theorem initial8945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3425) ∨ (¬ (meaning t m 5256)) := by
  exact rule8945 (meaning t m 3425) (meaning t m 3577) (meaning t m 3820) (meaning t m 5257) (meaning t m 5258)

theorem rule8946 (p3425 p3577 p3820 p5257 p5258 : Prop) : (¬ (p3820 ∧ p3577 ∧ p3425 ∧ p5257 ∧ p5258)) ∨ (p5257) := by
  classical
  tauto

theorem initial8946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5256)) ∨ (meaning t m 5257) := by
  exact rule8946 (meaning t m 3425) (meaning t m 3577) (meaning t m 3820) (meaning t m 5257) (meaning t m 5258)

theorem rule8949 (p3471 p3819 p3959 p5260 p5261 : Prop) : (p3959) ∨ (¬ (p3959 ∧ p3819 ∧ p3471 ∧ p5260 ∧ p5261)) := by
  classical
  tauto

theorem initial8949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3959) ∨ (¬ (meaning t m 5259)) := by
  exact rule8949 (meaning t m 3471) (meaning t m 3819) (meaning t m 3959) (meaning t m 5260) (meaning t m 5261)

theorem rule8950 (p3471 p3819 p3959 p5260 p5261 : Prop) : (p3819) ∨ (¬ (p3959 ∧ p3819 ∧ p3471 ∧ p5260 ∧ p5261)) := by
  classical
  tauto

theorem initial8950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3819) ∨ (¬ (meaning t m 5259)) := by
  exact rule8950 (meaning t m 3471) (meaning t m 3819) (meaning t m 3959) (meaning t m 5260) (meaning t m 5261)

theorem rule8951 (p3471 p3819 p3959 p5260 p5261 : Prop) : (p3471) ∨ (¬ (p3959 ∧ p3819 ∧ p3471 ∧ p5260 ∧ p5261)) := by
  classical
  tauto

theorem initial8951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3471) ∨ (¬ (meaning t m 5259)) := by
  exact rule8951 (meaning t m 3471) (meaning t m 3819) (meaning t m 3959) (meaning t m 5260) (meaning t m 5261)

theorem rule8952 (p3471 p3819 p3959 p5260 p5261 : Prop) : (¬ (p3959 ∧ p3819 ∧ p3471 ∧ p5260 ∧ p5261)) ∨ (p5260) := by
  classical
  tauto

theorem initial8952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5259)) ∨ (meaning t m 5260) := by
  exact rule8952 (meaning t m 3471) (meaning t m 3819) (meaning t m 3959) (meaning t m 5260) (meaning t m 5261)

theorem rule8953 (p3471 p3819 p3959 p5260 p5261 : Prop) : (¬ (p3959 ∧ p3819 ∧ p3471 ∧ p5260 ∧ p5261)) ∨ (p5261) := by
  classical
  tauto

theorem initial8953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5259)) ∨ (meaning t m 5261) := by
  exact rule8953 (meaning t m 3471) (meaning t m 3819) (meaning t m 3959) (meaning t m 5260) (meaning t m 5261)

theorem rule8957 (p5256 p5259 : Prop) : (¬ (p5256 ∨ p5259)) ∨ (p5256) ∨ (p5259) := by
  classical
  tauto

theorem initial8957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5255)) ∨ (meaning t m 5256) ∨ (meaning t m 5259) := by
  exact rule8957 (meaning t m 5256) (meaning t m 5259)

theorem rule8958 (p3465 p5255 : Prop) (h : (p3465 ↔ p5255)) : (¬ p3465) ∨ (p5255) := by
  classical
  tauto

theorem initial8958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3465)) ∨ (meaning t m 5255) := by
  have source := ElevenTheory.theory1289 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 7)
  exact rule8958 (meaning t m 3465) (meaning t m 5255) source

theorem rule8960 (p3917 p5264 p5265 p5266 p5267 : Prop) : (¬ (p5264 ∧ p5265 ∧ p3917 ∧ p5266 ∧ p5267)) ∨ (p5264) := by
  classical
  tauto

theorem initial8960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5263)) ∨ (meaning t m 5264) := by
  exact rule8960 (meaning t m 3917) (meaning t m 5264) (meaning t m 5265) (meaning t m 5266) (meaning t m 5267)

theorem rule8961 (p3917 p5264 p5265 p5266 p5267 : Prop) : (¬ (p5264 ∧ p5265 ∧ p3917 ∧ p5266 ∧ p5267)) ∨ (p5265) := by
  classical
  tauto

theorem initial8961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5263)) ∨ (meaning t m 5265) := by
  exact rule8961 (meaning t m 3917) (meaning t m 5264) (meaning t m 5265) (meaning t m 5266) (meaning t m 5267)

theorem rule8962 (p3917 p5264 p5265 p5266 p5267 : Prop) : (p3917) ∨ (¬ (p5264 ∧ p5265 ∧ p3917 ∧ p5266 ∧ p5267)) := by
  classical
  tauto

theorem initial8962 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3917) ∨ (¬ (meaning t m 5263)) := by
  exact rule8962 (meaning t m 3917) (meaning t m 5264) (meaning t m 5265) (meaning t m 5266) (meaning t m 5267)

theorem rule8964 (p3917 p5264 p5265 p5266 p5267 : Prop) : (¬ (p5264 ∧ p5265 ∧ p3917 ∧ p5266 ∧ p5267)) ∨ (p5267) := by
  classical
  tauto

theorem initial8964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5263)) ∨ (meaning t m 5267) := by
  exact rule8964 (meaning t m 3917) (meaning t m 5264) (meaning t m 5265) (meaning t m 5266) (meaning t m 5267)

theorem rule8966 (p3483 p4231 p5269 p5270 p5271 : Prop) : (¬ (p5269 ∧ p4231 ∧ p3483 ∧ p5270 ∧ p5271)) ∨ (p5269) := by
  classical
  tauto

theorem initial8966 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5268)) ∨ (meaning t m 5269) := by
  exact rule8966 (meaning t m 3483) (meaning t m 4231) (meaning t m 5269) (meaning t m 5270) (meaning t m 5271)

theorem rule8967 (p3483 p4231 p5269 p5270 p5271 : Prop) : (p4231) ∨ (¬ (p5269 ∧ p4231 ∧ p3483 ∧ p5270 ∧ p5271)) := by
  classical
  tauto

theorem initial8967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4231) ∨ (¬ (meaning t m 5268)) := by
  exact rule8967 (meaning t m 3483) (meaning t m 4231) (meaning t m 5269) (meaning t m 5270) (meaning t m 5271)

theorem rule8968 (p3483 p4231 p5269 p5270 p5271 : Prop) : (p3483) ∨ (¬ (p5269 ∧ p4231 ∧ p3483 ∧ p5270 ∧ p5271)) := by
  classical
  tauto

theorem initial8968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3483) ∨ (¬ (meaning t m 5268)) := by
  exact rule8968 (meaning t m 3483) (meaning t m 4231) (meaning t m 5269) (meaning t m 5270) (meaning t m 5271)

theorem rule8970 (p3483 p4231 p5269 p5270 p5271 : Prop) : (¬ (p5269 ∧ p4231 ∧ p3483 ∧ p5270 ∧ p5271)) ∨ (p5271) := by
  classical
  tauto

theorem initial8970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5268)) ∨ (meaning t m 5271) := by
  exact rule8970 (meaning t m 3483) (meaning t m 4231) (meaning t m 5269) (meaning t m 5270) (meaning t m 5271)

theorem rule8974 (p5263 p5268 : Prop) : (¬ (p5263 ∨ p5268)) ∨ (p5263) ∨ (p5268) := by
  classical
  tauto

theorem initial8974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5262)) ∨ (meaning t m 5263) ∨ (meaning t m 5268) := by
  exact rule8974 (meaning t m 5263) (meaning t m 5268)

theorem rule8975 (p3477 p5262 : Prop) (h : (p3477 ↔ p5262)) : (¬ p3477) ∨ (p5262) := by
  classical
  tauto

theorem initial8975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3477)) ∨ (meaning t m 5262) := by
  have source := ElevenTheory.theory1290 t (m.theta 2 6) (m.theta 2 9) (m.theta 6 9)
  exact rule8975 (meaning t m 3477) (meaning t m 5262) source

theorem rule8977 (p2406 p3238 : Prop) (h : (¬ p3238) ∨ (¬ p2406)) : (¬ p2406) ∨ (¬ p3238) := by
  classical
  tauto

theorem initial8977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3238)) := by
  have source := ElevenTheory.theory1291 (m.theta 1 4) (m.theta 4 5)
  exact rule8977 (meaning t m 2406) (meaning t m 3238) source

theorem rule8978 (p2027 p2696 p2751 p3027 p3425 p4777 : Prop) (h : (¬ p2751) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p3027) ∨ (¬ p4777)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3425) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial8978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory1292 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7)
  exact rule8978 (meaning t m 2027) (meaning t m 2696) (meaning t m 2751) (meaning t m 3027) (meaning t m 3425) (meaning t m 4777) source

theorem rule8979 (p4037 p4190 p5274 p5275 p5276 : Prop) : (¬ (p5274 ∧ p4190 ∧ p4037 ∧ p5275 ∧ p5276)) ∨ (p5274) := by
  classical
  tauto

theorem initial8979 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5273)) ∨ (meaning t m 5274) := by
  exact rule8979 (meaning t m 4037) (meaning t m 4190) (meaning t m 5274) (meaning t m 5275) (meaning t m 5276)

theorem rule8980 (p4037 p4190 p5274 p5275 p5276 : Prop) : (p4190) ∨ (¬ (p5274 ∧ p4190 ∧ p4037 ∧ p5275 ∧ p5276)) := by
  classical
  tauto

theorem initial8980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4190) ∨ (¬ (meaning t m 5273)) := by
  exact rule8980 (meaning t m 4037) (meaning t m 4190) (meaning t m 5274) (meaning t m 5275) (meaning t m 5276)

theorem rule8981 (p4037 p4190 p5274 p5275 p5276 : Prop) : (p4037) ∨ (¬ (p5274 ∧ p4190 ∧ p4037 ∧ p5275 ∧ p5276)) := by
  classical
  tauto

theorem initial8981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4037) ∨ (¬ (meaning t m 5273)) := by
  exact rule8981 (meaning t m 4037) (meaning t m 4190) (meaning t m 5274) (meaning t m 5275) (meaning t m 5276)

theorem rule8983 (p4037 p4190 p5274 p5275 p5276 : Prop) : (¬ (p5274 ∧ p4190 ∧ p4037 ∧ p5275 ∧ p5276)) ∨ (p5276) := by
  classical
  tauto

theorem initial8983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5273)) ∨ (meaning t m 5276) := by
  exact rule8983 (meaning t m 4037) (meaning t m 4190) (meaning t m 5274) (meaning t m 5275) (meaning t m 5276)

theorem rule8985 (p3323 p4367 p4421 p5278 p5279 : Prop) : (p4367) ∨ (¬ (p4367 ∧ p4421 ∧ p3323 ∧ p5278 ∧ p5279)) := by
  classical
  tauto

theorem initial8985 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4367) ∨ (¬ (meaning t m 5277)) := by
  exact rule8985 (meaning t m 3323) (meaning t m 4367) (meaning t m 4421) (meaning t m 5278) (meaning t m 5279)

theorem rule8986 (p3323 p4367 p4421 p5278 p5279 : Prop) : (p4421) ∨ (¬ (p4367 ∧ p4421 ∧ p3323 ∧ p5278 ∧ p5279)) := by
  classical
  tauto

theorem initial8986 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4421) ∨ (¬ (meaning t m 5277)) := by
  exact rule8986 (meaning t m 3323) (meaning t m 4367) (meaning t m 4421) (meaning t m 5278) (meaning t m 5279)

theorem rule8987 (p3323 p4367 p4421 p5278 p5279 : Prop) : (p3323) ∨ (¬ (p4367 ∧ p4421 ∧ p3323 ∧ p5278 ∧ p5279)) := by
  classical
  tauto

theorem initial8987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3323) ∨ (¬ (meaning t m 5277)) := by
  exact rule8987 (meaning t m 3323) (meaning t m 4367) (meaning t m 4421) (meaning t m 5278) (meaning t m 5279)

theorem rule8989 (p3323 p4367 p4421 p5278 p5279 : Prop) : (¬ (p4367 ∧ p4421 ∧ p3323 ∧ p5278 ∧ p5279)) ∨ (p5279) := by
  classical
  tauto

theorem initial8989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5277)) ∨ (meaning t m 5279) := by
  exact rule8989 (meaning t m 3323) (meaning t m 4367) (meaning t m 4421) (meaning t m 5278) (meaning t m 5279)

theorem rule8993 (p5273 p5277 : Prop) : (¬ (p5273 ∨ p5277)) ∨ (p5273) ∨ (p5277) := by
  classical
  tauto

theorem initial8993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5272)) ∨ (meaning t m 5273) ∨ (meaning t m 5277) := by
  exact rule8993 (meaning t m 5273) (meaning t m 5277)

theorem rule8994 (p3489 p5272 : Prop) (h : (p3489 ↔ p5272)) : (¬ p3489) ∨ (p5272) := by
  classical
  tauto

theorem initial8994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3489)) ∨ (meaning t m 5272) := by
  have source := ElevenTheory.theory1293 t (m.theta 3 6) (m.theta 3 9) (m.theta 6 9)
  exact rule8994 (meaning t m 3489) (meaning t m 5272) source

theorem rule8998 (p2027 p2210 p3452 p3684 p4210 p5217 : Prop) (h : (¬ p2210) ∨ (¬ p4210) ∨ (¬ p3452) ∨ (¬ p5217) ∨ p2027 ∨ (¬ p3684)) : (p2027) ∨ (¬ p2210) ∨ (¬ p3452) ∨ (¬ p3684) ∨ (¬ p4210) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial8998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory1296 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5)
  exact rule8998 (meaning t m 2027) (meaning t m 2210) (meaning t m 3452) (meaning t m 3684) (meaning t m 4210) (meaning t m 5217) source

theorem rule8999 (p3367 p3585 : Prop) (h : (¬ p3585) ∨ (¬ p3367)) : (¬ p3367) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial8999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory1297 (m.theta 1 2) (m.theta 2 4)
  exact rule8999 (meaning t m 3367) (meaning t m 3585) source

theorem rule9000 (p5282 p5283 p5284 p5285 p5286 : Prop) : (¬ (p5282 ∧ p5283 ∧ p5284 ∧ p5285 ∧ p5286)) ∨ (p5282) := by
  classical
  tauto

theorem initial9000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5281)) ∨ (meaning t m 5282) := by
  exact rule9000 (meaning t m 5282) (meaning t m 5283) (meaning t m 5284) (meaning t m 5285) (meaning t m 5286)

theorem rule9001 (p5282 p5283 p5284 p5285 p5286 : Prop) : (¬ (p5282 ∧ p5283 ∧ p5284 ∧ p5285 ∧ p5286)) ∨ (p5283) := by
  classical
  tauto

theorem initial9001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5281)) ∨ (meaning t m 5283) := by
  exact rule9001 (meaning t m 5282) (meaning t m 5283) (meaning t m 5284) (meaning t m 5285) (meaning t m 5286)

theorem rule9002 (p5282 p5283 p5284 p5285 p5286 : Prop) : (¬ (p5282 ∧ p5283 ∧ p5284 ∧ p5285 ∧ p5286)) ∨ (p5284) := by
  classical
  tauto

theorem initial9002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5281)) ∨ (meaning t m 5284) := by
  exact rule9002 (meaning t m 5282) (meaning t m 5283) (meaning t m 5284) (meaning t m 5285) (meaning t m 5286)

theorem rule9006 (p3506 p5288 p5289 p5290 p5291 : Prop) : (¬ (p5288 ∧ p5289 ∧ p3506 ∧ p5290 ∧ p5291)) ∨ (p5288) := by
  classical
  tauto

theorem initial9006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5287)) ∨ (meaning t m 5288) := by
  exact rule9006 (meaning t m 3506) (meaning t m 5288) (meaning t m 5289) (meaning t m 5290) (meaning t m 5291)

theorem rule9007 (p3506 p5288 p5289 p5290 p5291 : Prop) : (¬ (p5288 ∧ p5289 ∧ p3506 ∧ p5290 ∧ p5291)) ∨ (p5289) := by
  classical
  tauto

theorem initial9007 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5287)) ∨ (meaning t m 5289) := by
  exact rule9007 (meaning t m 3506) (meaning t m 5288) (meaning t m 5289) (meaning t m 5290) (meaning t m 5291)

theorem rule9008 (p3506 p5288 p5289 p5290 p5291 : Prop) : (p3506) ∨ (¬ (p5288 ∧ p5289 ∧ p3506 ∧ p5290 ∧ p5291)) := by
  classical
  tauto

theorem initial9008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3506) ∨ (¬ (meaning t m 5287)) := by
  exact rule9008 (meaning t m 3506) (meaning t m 5288) (meaning t m 5289) (meaning t m 5290) (meaning t m 5291)

theorem rule9014 (p5281 p5287 : Prop) : (¬ (p5281 ∨ p5287)) ∨ (p5281) ∨ (p5287) := by
  classical
  tauto

theorem initial9014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5280)) ∨ (meaning t m 5281) ∨ (meaning t m 5287) := by
  exact rule9014 (meaning t m 5281) (meaning t m 5287)

theorem rule9015 (p3500 p5280 : Prop) (h : (p3500 ↔ p5280)) : (¬ p3500) ∨ (p5280) := by
  classical
  tauto

theorem initial9015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3500)) ∨ (meaning t m 5280) := by
  have source := ElevenTheory.theory1298 t (m.theta 3 10) (m.theta 3 9) (m.theta 9 10)
  exact rule9015 (meaning t m 3500) (meaning t m 5280) source

theorem rule9017 (p3821 p5294 p5295 p5296 p5297 : Prop) : (¬ (p5294 ∧ p5295 ∧ p3821 ∧ p5296 ∧ p5297)) ∨ (p5294) := by
  classical
  tauto

theorem initial9017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5293)) ∨ (meaning t m 5294) := by
  exact rule9017 (meaning t m 3821) (meaning t m 5294) (meaning t m 5295) (meaning t m 5296) (meaning t m 5297)

theorem rule9018 (p3821 p5294 p5295 p5296 p5297 : Prop) : (¬ (p5294 ∧ p5295 ∧ p3821 ∧ p5296 ∧ p5297)) ∨ (p5295) := by
  classical
  tauto

theorem initial9018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5293)) ∨ (meaning t m 5295) := by
  exact rule9018 (meaning t m 3821) (meaning t m 5294) (meaning t m 5295) (meaning t m 5296) (meaning t m 5297)

theorem rule9019 (p3821 p5294 p5295 p5296 p5297 : Prop) : (p3821) ∨ (¬ (p5294 ∧ p5295 ∧ p3821 ∧ p5296 ∧ p5297)) := by
  classical
  tauto

theorem initial9019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3821) ∨ (¬ (meaning t m 5293)) := by
  exact rule9019 (meaning t m 3821) (meaning t m 5294) (meaning t m 5295) (meaning t m 5296) (meaning t m 5297)

theorem rule9023 (p3516 p5299 p5300 p5301 p5302 : Prop) : (¬ (p5299 ∧ p5300 ∧ p3516 ∧ p5301 ∧ p5302)) ∨ (p5299) := by
  classical
  tauto

theorem initial9023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5298)) ∨ (meaning t m 5299) := by
  exact rule9023 (meaning t m 3516) (meaning t m 5299) (meaning t m 5300) (meaning t m 5301) (meaning t m 5302)

theorem rule9025 (p3516 p5299 p5300 p5301 p5302 : Prop) : (p3516) ∨ (¬ (p5299 ∧ p5300 ∧ p3516 ∧ p5301 ∧ p5302)) := by
  classical
  tauto

theorem initial9025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3516) ∨ (¬ (meaning t m 5298)) := by
  exact rule9025 (meaning t m 3516) (meaning t m 5299) (meaning t m 5300) (meaning t m 5301) (meaning t m 5302)

theorem rule9031 (p5293 p5298 : Prop) : (¬ (p5293 ∨ p5298)) ∨ (p5293) ∨ (p5298) := by
  classical
  tauto

theorem initial9031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5292)) ∨ (meaning t m 5293) ∨ (meaning t m 5298) := by
  exact rule9031 (meaning t m 5293) (meaning t m 5298)

theorem rule9032 (p3510 p5292 : Prop) (h : (p3510 ↔ p5292)) : (¬ p3510) ∨ (p5292) := by
  classical
  tauto

theorem initial9032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3510)) ∨ (meaning t m 5292) := by
  have source := ElevenTheory.theory1299 t (m.theta 0 7) (m.theta 0 9) (m.theta 7 9)
  exact rule9032 (meaning t m 3510) (meaning t m 5292) source

theorem rule9034 (p2027 p2122 p2341 p3575 p4138 p4358 p4712 : Prop) (h : (¬ p3575) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p4358) ∨ (¬ p4712) ∨ (¬ p4138) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2341) ∨ (¬ p3575) ∨ (¬ p4138) ∨ (¬ p4358) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial9034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory1300 t (m.theta 0 7) (m.theta 2 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule9034 (meaning t m 2027) (meaning t m 2122) (meaning t m 2341) (meaning t m 3575) (meaning t m 4138) (meaning t m 4358) (meaning t m 4712) source

theorem rule9035 (p2177 p2299 : Prop) (h : (¬ p2299) ∨ (¬ p2177)) : (¬ p2177) ∨ (¬ p2299) := by
  classical
  tauto

theorem initial9035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2299)) := by
  have source := ElevenTheory.theory1301 (m.theta 6 7) (m.theta 7 8)
  exact rule9035 (meaning t m 2177) (meaning t m 2299) source

theorem rule9036 (p3542 p3544 p3548 p4832 p5305 : Prop) : (p3544) ∨ (¬ (p3544 ∧ p3542 ∧ p3548 ∧ p5305 ∧ p4832)) := by
  classical
  tauto

theorem initial9036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3544) ∨ (¬ (meaning t m 5304)) := by
  exact rule9036 (meaning t m 3542) (meaning t m 3544) (meaning t m 3548) (meaning t m 4832) (meaning t m 5305)

theorem rule9037 (p3542 p3544 p3548 p4832 p5305 : Prop) : (p3542) ∨ (¬ (p3544 ∧ p3542 ∧ p3548 ∧ p5305 ∧ p4832)) := by
  classical
  tauto

theorem initial9037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3542) ∨ (¬ (meaning t m 5304)) := by
  exact rule9037 (meaning t m 3542) (meaning t m 3544) (meaning t m 3548) (meaning t m 4832) (meaning t m 5305)

theorem rule9038 (p3542 p3544 p3548 p4832 p5305 : Prop) : (p3548) ∨ (¬ (p3544 ∧ p3542 ∧ p3548 ∧ p5305 ∧ p4832)) := by
  classical
  tauto

theorem initial9038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3548) ∨ (¬ (meaning t m 5304)) := by
  exact rule9038 (meaning t m 3542) (meaning t m 3544) (meaning t m 3548) (meaning t m 4832) (meaning t m 5305)

theorem rule9040 (p3542 p3544 p3548 p4832 p5305 : Prop) : (p4832) ∨ (¬ (p3544 ∧ p3542 ∧ p3548 ∧ p5305 ∧ p4832)) := by
  classical
  tauto

theorem initial9040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4832) ∨ (¬ (meaning t m 5304)) := by
  exact rule9040 (meaning t m 3542) (meaning t m 3544) (meaning t m 3548) (meaning t m 4832) (meaning t m 5305)

theorem rule9042 (p3527 p4189 p5307 p5308 p5309 : Prop) : (¬ (p5307 ∧ p4189 ∧ p3527 ∧ p5308 ∧ p5309)) ∨ (p5307) := by
  classical
  tauto

theorem initial9042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5306)) ∨ (meaning t m 5307) := by
  exact rule9042 (meaning t m 3527) (meaning t m 4189) (meaning t m 5307) (meaning t m 5308) (meaning t m 5309)

theorem rule9043 (p3527 p4189 p5307 p5308 p5309 : Prop) : (p4189) ∨ (¬ (p5307 ∧ p4189 ∧ p3527 ∧ p5308 ∧ p5309)) := by
  classical
  tauto

theorem initial9043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4189) ∨ (¬ (meaning t m 5306)) := by
  exact rule9043 (meaning t m 3527) (meaning t m 4189) (meaning t m 5307) (meaning t m 5308) (meaning t m 5309)

theorem rule9044 (p3527 p4189 p5307 p5308 p5309 : Prop) : (p3527) ∨ (¬ (p5307 ∧ p4189 ∧ p3527 ∧ p5308 ∧ p5309)) := by
  classical
  tauto

theorem initial9044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3527) ∨ (¬ (meaning t m 5306)) := by
  exact rule9044 (meaning t m 3527) (meaning t m 4189) (meaning t m 5307) (meaning t m 5308) (meaning t m 5309)

theorem rule9046 (p3527 p4189 p5307 p5308 p5309 : Prop) : (¬ (p5307 ∧ p4189 ∧ p3527 ∧ p5308 ∧ p5309)) ∨ (p5309) := by
  classical
  tauto

theorem initial9046 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5306)) ∨ (meaning t m 5309) := by
  exact rule9046 (meaning t m 3527) (meaning t m 4189) (meaning t m 5307) (meaning t m 5308) (meaning t m 5309)

theorem rule9050 (p5304 p5306 : Prop) : (¬ (p5304 ∨ p5306)) ∨ (p5304) ∨ (p5306) := by
  classical
  tauto

theorem initial9050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5303)) ∨ (meaning t m 5304) ∨ (meaning t m 5306) := by
  exact rule9050 (meaning t m 5304) (meaning t m 5306)

theorem rule9051 (p3521 p5303 : Prop) (h : (p3521 ↔ p5303)) : (¬ p3521) ∨ (p5303) := by
  classical
  tauto

theorem initial9051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3521)) ∨ (meaning t m 5303) := by
  have source := ElevenTheory.theory1302 t (m.theta 1 7) (m.theta 1 8) (m.theta 7 8)
  exact rule9051 (meaning t m 3521) (meaning t m 5303) source

theorem rule9053 (p3527 p3548 : Prop) (h : (¬ p3548) ∨ (¬ p3527)) : (¬ p3527) ∨ (¬ p3548) := by
  classical
  tauto

theorem initial9053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3548)) := by
  have source := ElevenTheory.theory1303 (m.theta 1 7) (m.theta 7 8)
  exact rule9053 (meaning t m 3527) (meaning t m 3548) source

end SunPrize.SMT
