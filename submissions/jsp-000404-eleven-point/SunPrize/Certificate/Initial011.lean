import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory004
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule7959 (p4840 p4844 : Prop) : (¬ (p4840 ∨ p4844)) ∨ (p4840) ∨ (p4844) := by
  classical
  tauto

theorem initial7959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4839)) ∨ (meaning t m 4840) ∨ (meaning t m 4844) := by
  exact rule7959 (meaning t m 4840) (meaning t m 4844)

theorem rule7960 (p2791 p4839 : Prop) (h : (p2791 ↔ p4839)) : (¬ p2791) ∨ (p4839) := by
  classical
  tauto

theorem initial7960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2791)) ∨ (meaning t m 4839) := by
  have source := ElevenTheory.theory1177 t (m.theta 2 3) (m.theta 2 6) (m.theta 3 6)
  exact rule7960 (meaning t m 2791) (meaning t m 4839) source

theorem rule7962 (p2027 p2253 p2750 p2807 p3954 p4111 p4112 : Prop) (h : (¬ p4112) ∨ (¬ p2253) ∨ (¬ p3954) ∨ (¬ p2750) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p4111)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2750) ∨ (¬ p2807) ∨ (¬ p3954) ∨ (¬ p4111) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial7962 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory1178 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7)
  exact rule7962 (meaning t m 2027) (meaning t m 2253) (meaning t m 2750) (meaning t m 2807) (meaning t m 3954) (meaning t m 4111) (meaning t m 4112) source

theorem rule7963 (p3414 p4066 p4849 p4850 p4851 : Prop) : (¬ (p4849 ∧ p4066 ∧ p3414 ∧ p4850 ∧ p4851)) ∨ (p4849) := by
  classical
  tauto

theorem initial7963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4848)) ∨ (meaning t m 4849) := by
  exact rule7963 (meaning t m 3414) (meaning t m 4066) (meaning t m 4849) (meaning t m 4850) (meaning t m 4851)

theorem rule7964 (p3414 p4066 p4849 p4850 p4851 : Prop) : (p4066) ∨ (¬ (p4849 ∧ p4066 ∧ p3414 ∧ p4850 ∧ p4851)) := by
  classical
  tauto

theorem initial7964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4066) ∨ (¬ (meaning t m 4848)) := by
  exact rule7964 (meaning t m 3414) (meaning t m 4066) (meaning t m 4849) (meaning t m 4850) (meaning t m 4851)

theorem rule7965 (p3414 p4066 p4849 p4850 p4851 : Prop) : (p3414) ∨ (¬ (p4849 ∧ p4066 ∧ p3414 ∧ p4850 ∧ p4851)) := by
  classical
  tauto

theorem initial7965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3414) ∨ (¬ (meaning t m 4848)) := by
  exact rule7965 (meaning t m 3414) (meaning t m 4066) (meaning t m 4849) (meaning t m 4850) (meaning t m 4851)

theorem rule7966 (p3414 p4066 p4849 p4850 p4851 : Prop) : (¬ (p4849 ∧ p4066 ∧ p3414 ∧ p4850 ∧ p4851)) ∨ (p4850) := by
  classical
  tauto

theorem initial7966 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4848)) ∨ (meaning t m 4850) := by
  exact rule7966 (meaning t m 3414) (meaning t m 4066) (meaning t m 4849) (meaning t m 4850) (meaning t m 4851)

theorem rule7967 (p3414 p4066 p4849 p4850 p4851 : Prop) : (¬ (p4849 ∧ p4066 ∧ p3414 ∧ p4850 ∧ p4851)) ∨ (p4851) := by
  classical
  tauto

theorem initial7967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4848)) ∨ (meaning t m 4851) := by
  exact rule7967 (meaning t m 3414) (meaning t m 4066) (meaning t m 4849) (meaning t m 4850) (meaning t m 4851)

theorem rule7969 (p2807 p4104 p4155 p4853 p4854 : Prop) : (p4155) ∨ (¬ (p4155 ∧ p4104 ∧ p2807 ∧ p4853 ∧ p4854)) := by
  classical
  tauto

theorem initial7969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4155) ∨ (¬ (meaning t m 4852)) := by
  exact rule7969 (meaning t m 2807) (meaning t m 4104) (meaning t m 4155) (meaning t m 4853) (meaning t m 4854)

theorem rule7970 (p2807 p4104 p4155 p4853 p4854 : Prop) : (p4104) ∨ (¬ (p4155 ∧ p4104 ∧ p2807 ∧ p4853 ∧ p4854)) := by
  classical
  tauto

theorem initial7970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4104) ∨ (¬ (meaning t m 4852)) := by
  exact rule7970 (meaning t m 2807) (meaning t m 4104) (meaning t m 4155) (meaning t m 4853) (meaning t m 4854)

theorem rule7971 (p2807 p4104 p4155 p4853 p4854 : Prop) : (p2807) ∨ (¬ (p4155 ∧ p4104 ∧ p2807 ∧ p4853 ∧ p4854)) := by
  classical
  tauto

theorem initial7971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2807) ∨ (¬ (meaning t m 4852)) := by
  exact rule7971 (meaning t m 2807) (meaning t m 4104) (meaning t m 4155) (meaning t m 4853) (meaning t m 4854)

theorem rule7973 (p2807 p4104 p4155 p4853 p4854 : Prop) : (¬ (p4155 ∧ p4104 ∧ p2807 ∧ p4853 ∧ p4854)) ∨ (p4854) := by
  classical
  tauto

theorem initial7973 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4852)) ∨ (meaning t m 4854) := by
  exact rule7973 (meaning t m 2807) (meaning t m 4104) (meaning t m 4155) (meaning t m 4853) (meaning t m 4854)

theorem rule7977 (p4848 p4852 : Prop) : (¬ (p4848 ∨ p4852)) ∨ (p4848) ∨ (p4852) := by
  classical
  tauto

theorem initial7977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4847)) ∨ (meaning t m 4848) ∨ (meaning t m 4852) := by
  exact rule7977 (meaning t m 4848) (meaning t m 4852)

theorem rule7978 (p2801 p4847 : Prop) (h : (p2801 ↔ p4847)) : (¬ p2801) ∨ (p4847) := by
  classical
  tauto

theorem initial7978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2801)) ∨ (meaning t m 4847) := by
  have source := ElevenTheory.theory1179 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 7)
  exact rule7978 (meaning t m 2801) (meaning t m 4847) source

theorem rule7980 (p2027 p2598 p3365 p3572 p3683 p4650 : Prop) (h : (¬ p3683) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p4650) ∨ (¬ p2598) ∨ p2027) : (p2027) ∨ (¬ p2598) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3683) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial7980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory1180 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 7)
  exact rule7980 (meaning t m 2027) (meaning t m 2598) (meaning t m 3365) (meaning t m 3572) (meaning t m 3683) (meaning t m 4650) source

theorem rule7981 (p4078 p4358 p4857 p4858 p4859 : Prop) : (p4078) ∨ (¬ (p4078 ∧ p4857 ∧ p4358 ∧ p4858 ∧ p4859)) := by
  classical
  tauto

theorem initial7981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4078) ∨ (¬ (meaning t m 4856)) := by
  exact rule7981 (meaning t m 4078) (meaning t m 4358) (meaning t m 4857) (meaning t m 4858) (meaning t m 4859)

theorem rule7982 (p4078 p4358 p4857 p4858 p4859 : Prop) : (¬ (p4078 ∧ p4857 ∧ p4358 ∧ p4858 ∧ p4859)) ∨ (p4857) := by
  classical
  tauto

theorem initial7982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4856)) ∨ (meaning t m 4857) := by
  exact rule7982 (meaning t m 4078) (meaning t m 4358) (meaning t m 4857) (meaning t m 4858) (meaning t m 4859)

theorem rule7983 (p4078 p4358 p4857 p4858 p4859 : Prop) : (p4358) ∨ (¬ (p4078 ∧ p4857 ∧ p4358 ∧ p4858 ∧ p4859)) := by
  classical
  tauto

theorem initial7983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4358) ∨ (¬ (meaning t m 4856)) := by
  exact rule7983 (meaning t m 4078) (meaning t m 4358) (meaning t m 4857) (meaning t m 4858) (meaning t m 4859)

theorem rule7985 (p4078 p4358 p4857 p4858 p4859 : Prop) : (¬ (p4078 ∧ p4857 ∧ p4358 ∧ p4858 ∧ p4859)) ∨ (p4859) := by
  classical
  tauto

theorem initial7985 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4856)) ∨ (meaning t m 4859) := by
  exact rule7985 (meaning t m 4078) (meaning t m 4358) (meaning t m 4857) (meaning t m 4858) (meaning t m 4859)

theorem rule7987 (p2819 p4326 p4861 p4862 p4863 : Prop) : (p4326) ∨ (¬ (p4326 ∧ p4861 ∧ p2819 ∧ p4862 ∧ p4863)) := by
  classical
  tauto

theorem initial7987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4326) ∨ (¬ (meaning t m 4860)) := by
  exact rule7987 (meaning t m 2819) (meaning t m 4326) (meaning t m 4861) (meaning t m 4862) (meaning t m 4863)

theorem rule7988 (p2819 p4326 p4861 p4862 p4863 : Prop) : (¬ (p4326 ∧ p4861 ∧ p2819 ∧ p4862 ∧ p4863)) ∨ (p4861) := by
  classical
  tauto

theorem initial7988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4860)) ∨ (meaning t m 4861) := by
  exact rule7988 (meaning t m 2819) (meaning t m 4326) (meaning t m 4861) (meaning t m 4862) (meaning t m 4863)

theorem rule7989 (p2819 p4326 p4861 p4862 p4863 : Prop) : (p2819) ∨ (¬ (p4326 ∧ p4861 ∧ p2819 ∧ p4862 ∧ p4863)) := by
  classical
  tauto

theorem initial7989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2819) ∨ (¬ (meaning t m 4860)) := by
  exact rule7989 (meaning t m 2819) (meaning t m 4326) (meaning t m 4861) (meaning t m 4862) (meaning t m 4863)

theorem rule7991 (p2819 p4326 p4861 p4862 p4863 : Prop) : (¬ (p4326 ∧ p4861 ∧ p2819 ∧ p4862 ∧ p4863)) ∨ (p4863) := by
  classical
  tauto

theorem initial7991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4860)) ∨ (meaning t m 4863) := by
  exact rule7991 (meaning t m 2819) (meaning t m 4326) (meaning t m 4861) (meaning t m 4862) (meaning t m 4863)

theorem rule7995 (p4856 p4860 : Prop) : (¬ (p4856 ∨ p4860)) ∨ (p4856) ∨ (p4860) := by
  classical
  tauto

theorem initial7995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4855)) ∨ (meaning t m 4856) ∨ (meaning t m 4860) := by
  exact rule7995 (meaning t m 4856) (meaning t m 4860)

theorem rule7996 (p2813 p4855 : Prop) (h : (p2813 ↔ p4855)) : (¬ p2813) ∨ (p4855) := by
  classical
  tauto

theorem initial7996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2813)) ∨ (meaning t m 4855) := by
  have source := ElevenTheory.theory1181 t (m.theta 2 6) (m.theta 2 8) (m.theta 6 8)
  exact rule7996 (meaning t m 2813) (meaning t m 4855) source

theorem rule7998 (p3688 p3918 p3953 p4866 p4867 : Prop) : (p3953) ∨ (¬ (p3953 ∧ p3918 ∧ p3688 ∧ p4866 ∧ p4867)) := by
  classical
  tauto

theorem initial7998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3953) ∨ (¬ (meaning t m 4865)) := by
  exact rule7998 (meaning t m 3688) (meaning t m 3918) (meaning t m 3953) (meaning t m 4866) (meaning t m 4867)

theorem rule7999 (p3688 p3918 p3953 p4866 p4867 : Prop) : (p3918) ∨ (¬ (p3953 ∧ p3918 ∧ p3688 ∧ p4866 ∧ p4867)) := by
  classical
  tauto

theorem initial7999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3918) ∨ (¬ (meaning t m 4865)) := by
  exact rule7999 (meaning t m 3688) (meaning t m 3918) (meaning t m 3953) (meaning t m 4866) (meaning t m 4867)

theorem rule8000 (p3688 p3918 p3953 p4866 p4867 : Prop) : (p3688) ∨ (¬ (p3953 ∧ p3918 ∧ p3688 ∧ p4866 ∧ p4867)) := by
  classical
  tauto

theorem initial8000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3688) ∨ (¬ (meaning t m 4865)) := by
  exact rule8000 (meaning t m 3688) (meaning t m 3918) (meaning t m 3953) (meaning t m 4866) (meaning t m 4867)

theorem rule8001 (p3688 p3918 p3953 p4866 p4867 : Prop) : (¬ (p3953 ∧ p3918 ∧ p3688 ∧ p4866 ∧ p4867)) ∨ (p4866) := by
  classical
  tauto

theorem initial8001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4865)) ∨ (meaning t m 4866) := by
  exact rule8001 (meaning t m 3688) (meaning t m 3918) (meaning t m 3953) (meaning t m 4866) (meaning t m 4867)

theorem rule8002 (p3688 p3918 p3953 p4866 p4867 : Prop) : (¬ (p3953 ∧ p3918 ∧ p3688 ∧ p4866 ∧ p4867)) ∨ (p4867) := by
  classical
  tauto

theorem initial8002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4865)) ∨ (meaning t m 4867) := by
  exact rule8002 (meaning t m 3688) (meaning t m 3918) (meaning t m 3953) (meaning t m 4866) (meaning t m 4867)

theorem rule8004 (p2829 p4024 p4869 p4870 p4871 : Prop) : (p4024) ∨ (¬ (p4024 ∧ p4869 ∧ p2829 ∧ p4870 ∧ p4871)) := by
  classical
  tauto

theorem initial8004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4024) ∨ (¬ (meaning t m 4868)) := by
  exact rule8004 (meaning t m 2829) (meaning t m 4024) (meaning t m 4869) (meaning t m 4870) (meaning t m 4871)

theorem rule8005 (p2829 p4024 p4869 p4870 p4871 : Prop) : (¬ (p4024 ∧ p4869 ∧ p2829 ∧ p4870 ∧ p4871)) ∨ (p4869) := by
  classical
  tauto

theorem initial8005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4868)) ∨ (meaning t m 4869) := by
  exact rule8005 (meaning t m 2829) (meaning t m 4024) (meaning t m 4869) (meaning t m 4870) (meaning t m 4871)

theorem rule8006 (p2829 p4024 p4869 p4870 p4871 : Prop) : (p2829) ∨ (¬ (p4024 ∧ p4869 ∧ p2829 ∧ p4870 ∧ p4871)) := by
  classical
  tauto

theorem initial8006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2829) ∨ (¬ (meaning t m 4868)) := by
  exact rule8006 (meaning t m 2829) (meaning t m 4024) (meaning t m 4869) (meaning t m 4870) (meaning t m 4871)

theorem rule8007 (p2829 p4024 p4869 p4870 p4871 : Prop) : (¬ (p4024 ∧ p4869 ∧ p2829 ∧ p4870 ∧ p4871)) ∨ (p4870) := by
  classical
  tauto

theorem initial8007 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4868)) ∨ (meaning t m 4870) := by
  exact rule8007 (meaning t m 2829) (meaning t m 4024) (meaning t m 4869) (meaning t m 4870) (meaning t m 4871)

theorem rule8008 (p2829 p4024 p4869 p4870 p4871 : Prop) : (¬ (p4024 ∧ p4869 ∧ p2829 ∧ p4870 ∧ p4871)) ∨ (p4871) := by
  classical
  tauto

theorem initial8008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4868)) ∨ (meaning t m 4871) := by
  exact rule8008 (meaning t m 2829) (meaning t m 4024) (meaning t m 4869) (meaning t m 4870) (meaning t m 4871)

theorem rule8012 (p4865 p4868 : Prop) : (¬ (p4865 ∨ p4868)) ∨ (p4865) ∨ (p4868) := by
  classical
  tauto

theorem initial8012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4864)) ∨ (meaning t m 4865) ∨ (meaning t m 4868) := by
  exact rule8012 (meaning t m 4865) (meaning t m 4868)

theorem rule8013 (p2823 p4864 : Prop) (h : (p2823 ↔ p4864)) : (¬ p2823) ∨ (p4864) := by
  classical
  tauto

theorem initial8013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2823)) ∨ (meaning t m 4864) := by
  have source := ElevenTheory.theory1182 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 6)
  exact rule8013 (meaning t m 2823) (meaning t m 4864) source

theorem rule8015 (p3583 p4377 p4418 p4874 p4875 : Prop) : (¬ (p4874 ∧ p4418 ∧ p3583 ∧ p4377 ∧ p4875)) ∨ (p4874) := by
  classical
  tauto

theorem initial8015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4873)) ∨ (meaning t m 4874) := by
  exact rule8015 (meaning t m 3583) (meaning t m 4377) (meaning t m 4418) (meaning t m 4874) (meaning t m 4875)

theorem rule8016 (p3583 p4377 p4418 p4874 p4875 : Prop) : (p4418) ∨ (¬ (p4874 ∧ p4418 ∧ p3583 ∧ p4377 ∧ p4875)) := by
  classical
  tauto

theorem initial8016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4418) ∨ (¬ (meaning t m 4873)) := by
  exact rule8016 (meaning t m 3583) (meaning t m 4377) (meaning t m 4418) (meaning t m 4874) (meaning t m 4875)

theorem rule8017 (p3583 p4377 p4418 p4874 p4875 : Prop) : (p3583) ∨ (¬ (p4874 ∧ p4418 ∧ p3583 ∧ p4377 ∧ p4875)) := by
  classical
  tauto

theorem initial8017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3583) ∨ (¬ (meaning t m 4873)) := by
  exact rule8017 (meaning t m 3583) (meaning t m 4377) (meaning t m 4418) (meaning t m 4874) (meaning t m 4875)

theorem rule8018 (p3583 p4377 p4418 p4874 p4875 : Prop) : (p4377) ∨ (¬ (p4874 ∧ p4418 ∧ p3583 ∧ p4377 ∧ p4875)) := by
  classical
  tauto

theorem initial8018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4377) ∨ (¬ (meaning t m 4873)) := by
  exact rule8018 (meaning t m 3583) (meaning t m 4377) (meaning t m 4418) (meaning t m 4874) (meaning t m 4875)

theorem rule8019 (p3583 p4377 p4418 p4874 p4875 : Prop) : (¬ (p4874 ∧ p4418 ∧ p3583 ∧ p4377 ∧ p4875)) ∨ (p4875) := by
  classical
  tauto

theorem initial8019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4873)) ∨ (meaning t m 4875) := by
  exact rule8019 (meaning t m 3583) (meaning t m 4377) (meaning t m 4418) (meaning t m 4874) (meaning t m 4875)

theorem rule8021 (p2839 p3371 p4243 p4877 p4878 : Prop) : (p4243) ∨ (¬ (p4243 ∧ p3371 ∧ p2839 ∧ p4877 ∧ p4878)) := by
  classical
  tauto

theorem initial8021 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4243) ∨ (¬ (meaning t m 4876)) := by
  exact rule8021 (meaning t m 2839) (meaning t m 3371) (meaning t m 4243) (meaning t m 4877) (meaning t m 4878)

theorem rule8022 (p2839 p3371 p4243 p4877 p4878 : Prop) : (p3371) ∨ (¬ (p4243 ∧ p3371 ∧ p2839 ∧ p4877 ∧ p4878)) := by
  classical
  tauto

theorem initial8022 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3371) ∨ (¬ (meaning t m 4876)) := by
  exact rule8022 (meaning t m 2839) (meaning t m 3371) (meaning t m 4243) (meaning t m 4877) (meaning t m 4878)

theorem rule8023 (p2839 p3371 p4243 p4877 p4878 : Prop) : (p2839) ∨ (¬ (p4243 ∧ p3371 ∧ p2839 ∧ p4877 ∧ p4878)) := by
  classical
  tauto

theorem initial8023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2839) ∨ (¬ (meaning t m 4876)) := by
  exact rule8023 (meaning t m 2839) (meaning t m 3371) (meaning t m 4243) (meaning t m 4877) (meaning t m 4878)

theorem rule8024 (p2839 p3371 p4243 p4877 p4878 : Prop) : (¬ (p4243 ∧ p3371 ∧ p2839 ∧ p4877 ∧ p4878)) ∨ (p4877) := by
  classical
  tauto

theorem initial8024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4876)) ∨ (meaning t m 4877) := by
  exact rule8024 (meaning t m 2839) (meaning t m 3371) (meaning t m 4243) (meaning t m 4877) (meaning t m 4878)

theorem rule8025 (p2839 p3371 p4243 p4877 p4878 : Prop) : (¬ (p4243 ∧ p3371 ∧ p2839 ∧ p4877 ∧ p4878)) ∨ (p4878) := by
  classical
  tauto

theorem initial8025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4876)) ∨ (meaning t m 4878) := by
  exact rule8025 (meaning t m 2839) (meaning t m 3371) (meaning t m 4243) (meaning t m 4877) (meaning t m 4878)

theorem rule8029 (p4873 p4876 : Prop) : (¬ (p4873 ∨ p4876)) ∨ (p4873) ∨ (p4876) := by
  classical
  tauto

theorem initial8029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4872)) ∨ (meaning t m 4873) ∨ (meaning t m 4876) := by
  exact rule8029 (meaning t m 4873) (meaning t m 4876)

theorem rule8030 (p2833 p4872 : Prop) (h : (p2833 ↔ p4872)) : (¬ p2833) ∨ (p4872) := by
  classical
  tauto

theorem initial8030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2833)) ∨ (meaning t m 4872) := by
  have source := ElevenTheory.theory1183 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 5)
  exact rule8030 (meaning t m 2833) (meaning t m 4872) source

theorem rule8032 (p3054 p3684 p3698 p4881 p4882 : Prop) : (p3054) ∨ (¬ (p3054 ∧ p3698 ∧ p3684 ∧ p4881 ∧ p4882)) := by
  classical
  tauto

theorem initial8032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3054) ∨ (¬ (meaning t m 4880)) := by
  exact rule8032 (meaning t m 3054) (meaning t m 3684) (meaning t m 3698) (meaning t m 4881) (meaning t m 4882)

theorem rule8033 (p3054 p3684 p3698 p4881 p4882 : Prop) : (p3698) ∨ (¬ (p3054 ∧ p3698 ∧ p3684 ∧ p4881 ∧ p4882)) := by
  classical
  tauto

theorem initial8033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3698) ∨ (¬ (meaning t m 4880)) := by
  exact rule8033 (meaning t m 3054) (meaning t m 3684) (meaning t m 3698) (meaning t m 4881) (meaning t m 4882)

theorem rule8034 (p3054 p3684 p3698 p4881 p4882 : Prop) : (p3684) ∨ (¬ (p3054 ∧ p3698 ∧ p3684 ∧ p4881 ∧ p4882)) := by
  classical
  tauto

theorem initial8034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3684) ∨ (¬ (meaning t m 4880)) := by
  exact rule8034 (meaning t m 3054) (meaning t m 3684) (meaning t m 3698) (meaning t m 4881) (meaning t m 4882)

theorem rule8035 (p3054 p3684 p3698 p4881 p4882 : Prop) : (¬ (p3054 ∧ p3698 ∧ p3684 ∧ p4881 ∧ p4882)) ∨ (p4881) := by
  classical
  tauto

theorem initial8035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4880)) ∨ (meaning t m 4881) := by
  exact rule8035 (meaning t m 3054) (meaning t m 3684) (meaning t m 3698) (meaning t m 4881) (meaning t m 4882)

theorem rule8036 (p3054 p3684 p3698 p4881 p4882 : Prop) : (¬ (p3054 ∧ p3698 ∧ p3684 ∧ p4881 ∧ p4882)) ∨ (p4882) := by
  classical
  tauto

theorem initial8036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4880)) ∨ (meaning t m 4882) := by
  exact rule8036 (meaning t m 3054) (meaning t m 3684) (meaning t m 3698) (meaning t m 4881) (meaning t m 4882)

theorem rule8038 (p2850 p3582 p3695 p4884 p4885 : Prop) : (p3695) ∨ (¬ (p3695 ∧ p3582 ∧ p2850 ∧ p4884 ∧ p4885)) := by
  classical
  tauto

theorem initial8038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3695) ∨ (¬ (meaning t m 4883)) := by
  exact rule8038 (meaning t m 2850) (meaning t m 3582) (meaning t m 3695) (meaning t m 4884) (meaning t m 4885)

theorem rule8039 (p2850 p3582 p3695 p4884 p4885 : Prop) : (p3582) ∨ (¬ (p3695 ∧ p3582 ∧ p2850 ∧ p4884 ∧ p4885)) := by
  classical
  tauto

theorem initial8039 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3582) ∨ (¬ (meaning t m 4883)) := by
  exact rule8039 (meaning t m 2850) (meaning t m 3582) (meaning t m 3695) (meaning t m 4884) (meaning t m 4885)

theorem rule8040 (p2850 p3582 p3695 p4884 p4885 : Prop) : (p2850) ∨ (¬ (p3695 ∧ p3582 ∧ p2850 ∧ p4884 ∧ p4885)) := by
  classical
  tauto

theorem initial8040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2850) ∨ (¬ (meaning t m 4883)) := by
  exact rule8040 (meaning t m 2850) (meaning t m 3582) (meaning t m 3695) (meaning t m 4884) (meaning t m 4885)

theorem rule8041 (p2850 p3582 p3695 p4884 p4885 : Prop) : (¬ (p3695 ∧ p3582 ∧ p2850 ∧ p4884 ∧ p4885)) ∨ (p4884) := by
  classical
  tauto

theorem initial8041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4883)) ∨ (meaning t m 4884) := by
  exact rule8041 (meaning t m 2850) (meaning t m 3582) (meaning t m 3695) (meaning t m 4884) (meaning t m 4885)

theorem rule8042 (p2850 p3582 p3695 p4884 p4885 : Prop) : (¬ (p3695 ∧ p3582 ∧ p2850 ∧ p4884 ∧ p4885)) ∨ (p4885) := by
  classical
  tauto

theorem initial8042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4883)) ∨ (meaning t m 4885) := by
  exact rule8042 (meaning t m 2850) (meaning t m 3582) (meaning t m 3695) (meaning t m 4884) (meaning t m 4885)

theorem rule8046 (p4880 p4883 : Prop) : (¬ (p4880 ∨ p4883)) ∨ (p4880) ∨ (p4883) := by
  classical
  tauto

theorem initial8046 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4879)) ∨ (meaning t m 4880) ∨ (meaning t m 4883) := by
  exact rule8046 (meaning t m 4880) (meaning t m 4883)

theorem rule8047 (p2844 p4879 : Prop) (h : (p2844 ↔ p4879)) : (¬ p2844) ∨ (p4879) := by
  classical
  tauto

theorem initial8047 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2844)) ∨ (meaning t m 4879) := by
  have source := ElevenTheory.theory1184 t (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule8047 (meaning t m 2844) (meaning t m 4879) source

theorem rule8049 (p3758 p4193 p4428 p4888 p4889 : Prop) : (p4193) ∨ (¬ (p4193 ∧ p4428 ∧ p3758 ∧ p4888 ∧ p4889)) := by
  classical
  tauto

theorem initial8049 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4193) ∨ (¬ (meaning t m 4887)) := by
  exact rule8049 (meaning t m 3758) (meaning t m 4193) (meaning t m 4428) (meaning t m 4888) (meaning t m 4889)

theorem rule8050 (p3758 p4193 p4428 p4888 p4889 : Prop) : (p4428) ∨ (¬ (p4193 ∧ p4428 ∧ p3758 ∧ p4888 ∧ p4889)) := by
  classical
  tauto

theorem initial8050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4428) ∨ (¬ (meaning t m 4887)) := by
  exact rule8050 (meaning t m 3758) (meaning t m 4193) (meaning t m 4428) (meaning t m 4888) (meaning t m 4889)

theorem rule8051 (p3758 p4193 p4428 p4888 p4889 : Prop) : (p3758) ∨ (¬ (p4193 ∧ p4428 ∧ p3758 ∧ p4888 ∧ p4889)) := by
  classical
  tauto

theorem initial8051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3758) ∨ (¬ (meaning t m 4887)) := by
  exact rule8051 (meaning t m 3758) (meaning t m 4193) (meaning t m 4428) (meaning t m 4888) (meaning t m 4889)

theorem rule8053 (p3758 p4193 p4428 p4888 p4889 : Prop) : (¬ (p4193 ∧ p4428 ∧ p3758 ∧ p4888 ∧ p4889)) ∨ (p4889) := by
  classical
  tauto

theorem initial8053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4887)) ∨ (meaning t m 4889) := by
  exact rule8053 (meaning t m 3758) (meaning t m 4193) (meaning t m 4428) (meaning t m 4888) (meaning t m 4889)

theorem rule8055 (p2860 p3985 p4185 p4401 p4891 : Prop) : (p4185) ∨ (¬ (p4185 ∧ p3985 ∧ p2860 ∧ p4891 ∧ p4401)) := by
  classical
  tauto

theorem initial8055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4185) ∨ (¬ (meaning t m 4890)) := by
  exact rule8055 (meaning t m 2860) (meaning t m 3985) (meaning t m 4185) (meaning t m 4401) (meaning t m 4891)

theorem rule8056 (p2860 p3985 p4185 p4401 p4891 : Prop) : (p3985) ∨ (¬ (p4185 ∧ p3985 ∧ p2860 ∧ p4891 ∧ p4401)) := by
  classical
  tauto

theorem initial8056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3985) ∨ (¬ (meaning t m 4890)) := by
  exact rule8056 (meaning t m 2860) (meaning t m 3985) (meaning t m 4185) (meaning t m 4401) (meaning t m 4891)

theorem rule8057 (p2860 p3985 p4185 p4401 p4891 : Prop) : (p2860) ∨ (¬ (p4185 ∧ p3985 ∧ p2860 ∧ p4891 ∧ p4401)) := by
  classical
  tauto

theorem initial8057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2860) ∨ (¬ (meaning t m 4890)) := by
  exact rule8057 (meaning t m 2860) (meaning t m 3985) (meaning t m 4185) (meaning t m 4401) (meaning t m 4891)

theorem rule8059 (p2860 p3985 p4185 p4401 p4891 : Prop) : (p4401) ∨ (¬ (p4185 ∧ p3985 ∧ p2860 ∧ p4891 ∧ p4401)) := by
  classical
  tauto

theorem initial8059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4401) ∨ (¬ (meaning t m 4890)) := by
  exact rule8059 (meaning t m 2860) (meaning t m 3985) (meaning t m 4185) (meaning t m 4401) (meaning t m 4891)

theorem rule8063 (p4887 p4890 : Prop) : (¬ (p4887 ∨ p4890)) ∨ (p4887) ∨ (p4890) := by
  classical
  tauto

theorem initial8063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4886)) ∨ (meaning t m 4887) ∨ (meaning t m 4890) := by
  exact rule8063 (meaning t m 4887) (meaning t m 4890)

theorem rule8064 (p2854 p4886 : Prop) (h : (p2854 ↔ p4886)) : (¬ p2854) ∨ (p4886) := by
  classical
  tauto

theorem initial8064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2854)) ∨ (meaning t m 4886) := by
  have source := ElevenTheory.theory1185 t (m.theta 2 5) (m.theta 2 6) (m.theta 5 6)
  exact rule8064 (meaning t m 2854) (meaning t m 4886) source

theorem rule8066 (p4136 p4169 p4244 p4894 p4895 : Prop) : (p4136) ∨ (¬ (p4136 ∧ p4169 ∧ p4244 ∧ p4894 ∧ p4895)) := by
  classical
  tauto

theorem initial8066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4136) ∨ (¬ (meaning t m 4893)) := by
  exact rule8066 (meaning t m 4136) (meaning t m 4169) (meaning t m 4244) (meaning t m 4894) (meaning t m 4895)

theorem rule8067 (p4136 p4169 p4244 p4894 p4895 : Prop) : (p4169) ∨ (¬ (p4136 ∧ p4169 ∧ p4244 ∧ p4894 ∧ p4895)) := by
  classical
  tauto

theorem initial8067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4169) ∨ (¬ (meaning t m 4893)) := by
  exact rule8067 (meaning t m 4136) (meaning t m 4169) (meaning t m 4244) (meaning t m 4894) (meaning t m 4895)

theorem rule8068 (p4136 p4169 p4244 p4894 p4895 : Prop) : (p4244) ∨ (¬ (p4136 ∧ p4169 ∧ p4244 ∧ p4894 ∧ p4895)) := by
  classical
  tauto

theorem initial8068 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4244) ∨ (¬ (meaning t m 4893)) := by
  exact rule8068 (meaning t m 4136) (meaning t m 4169) (meaning t m 4244) (meaning t m 4894) (meaning t m 4895)

theorem rule8070 (p4136 p4169 p4244 p4894 p4895 : Prop) : (¬ (p4136 ∧ p4169 ∧ p4244 ∧ p4894 ∧ p4895)) ∨ (p4895) := by
  classical
  tauto

theorem initial8070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4893)) ∨ (meaning t m 4895) := by
  exact rule8070 (meaning t m 4136) (meaning t m 4169) (meaning t m 4244) (meaning t m 4894) (meaning t m 4895)

theorem rule8072 (p2870 p3587 p4344 p4897 p4898 : Prop) : (p4344) ∨ (¬ (p4344 ∧ p3587 ∧ p2870 ∧ p4897 ∧ p4898)) := by
  classical
  tauto

theorem initial8072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4344) ∨ (¬ (meaning t m 4896)) := by
  exact rule8072 (meaning t m 2870) (meaning t m 3587) (meaning t m 4344) (meaning t m 4897) (meaning t m 4898)

theorem rule8073 (p2870 p3587 p4344 p4897 p4898 : Prop) : (p3587) ∨ (¬ (p4344 ∧ p3587 ∧ p2870 ∧ p4897 ∧ p4898)) := by
  classical
  tauto

theorem initial8073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3587) ∨ (¬ (meaning t m 4896)) := by
  exact rule8073 (meaning t m 2870) (meaning t m 3587) (meaning t m 4344) (meaning t m 4897) (meaning t m 4898)

theorem rule8074 (p2870 p3587 p4344 p4897 p4898 : Prop) : (p2870) ∨ (¬ (p4344 ∧ p3587 ∧ p2870 ∧ p4897 ∧ p4898)) := by
  classical
  tauto

theorem initial8074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2870) ∨ (¬ (meaning t m 4896)) := by
  exact rule8074 (meaning t m 2870) (meaning t m 3587) (meaning t m 4344) (meaning t m 4897) (meaning t m 4898)

theorem rule8075 (p2870 p3587 p4344 p4897 p4898 : Prop) : (¬ (p4344 ∧ p3587 ∧ p2870 ∧ p4897 ∧ p4898)) ∨ (p4897) := by
  classical
  tauto

theorem initial8075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4896)) ∨ (meaning t m 4897) := by
  exact rule8075 (meaning t m 2870) (meaning t m 3587) (meaning t m 4344) (meaning t m 4897) (meaning t m 4898)

theorem rule8076 (p2870 p3587 p4344 p4897 p4898 : Prop) : (¬ (p4344 ∧ p3587 ∧ p2870 ∧ p4897 ∧ p4898)) ∨ (p4898) := by
  classical
  tauto

theorem initial8076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4896)) ∨ (meaning t m 4898) := by
  exact rule8076 (meaning t m 2870) (meaning t m 3587) (meaning t m 4344) (meaning t m 4897) (meaning t m 4898)

theorem rule8080 (p4893 p4896 : Prop) : (¬ (p4893 ∨ p4896)) ∨ (p4893) ∨ (p4896) := by
  classical
  tauto

theorem initial8080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4892)) ∨ (meaning t m 4893) ∨ (meaning t m 4896) := by
  exact rule8080 (meaning t m 4893) (meaning t m 4896)

theorem rule8081 (p2864 p4892 : Prop) (h : (p2864 ↔ p4892)) : (¬ p2864) ∨ (p4892) := by
  classical
  tauto

theorem initial8081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2864)) ∨ (meaning t m 4892) := by
  have source := ElevenTheory.theory1186 t (m.theta 2 5) (m.theta 2 7) (m.theta 5 7)
  exact rule8081 (meaning t m 2864) (meaning t m 4892) source

theorem rule8083 (p2027 p2146 p2839 p3051 p3588 p4169 : Prop) (h : p2027 ∨ (¬ p3051) ∨ (¬ p4169) ∨ (¬ p2839) ∨ (¬ p3588) ∨ (¬ p2146)) : (p2027) ∨ (¬ p2146) ∨ (¬ p2839) ∨ (¬ p3051) ∨ (¬ p3588) ∨ (¬ p4169) := by
  classical
  tauto

theorem initial8083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2146)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4169)) := by
  have source := ElevenTheory.theory1187 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7)
  exact rule8083 (meaning t m 2027) (meaning t m 2146) (meaning t m 2839) (meaning t m 3051) (meaning t m 3588) (meaning t m 4169) source

theorem rule8084 (p3570 p4119 p4132 p4901 p4902 : Prop) : (p4119) ∨ (¬ (p4119 ∧ p4132 ∧ p3570 ∧ p4901 ∧ p4902)) := by
  classical
  tauto

theorem initial8084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4119) ∨ (¬ (meaning t m 4900)) := by
  exact rule8084 (meaning t m 3570) (meaning t m 4119) (meaning t m 4132) (meaning t m 4901) (meaning t m 4902)

theorem rule8085 (p3570 p4119 p4132 p4901 p4902 : Prop) : (p4132) ∨ (¬ (p4119 ∧ p4132 ∧ p3570 ∧ p4901 ∧ p4902)) := by
  classical
  tauto

theorem initial8085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4132) ∨ (¬ (meaning t m 4900)) := by
  exact rule8085 (meaning t m 3570) (meaning t m 4119) (meaning t m 4132) (meaning t m 4901) (meaning t m 4902)

theorem rule8086 (p3570 p4119 p4132 p4901 p4902 : Prop) : (p3570) ∨ (¬ (p4119 ∧ p4132 ∧ p3570 ∧ p4901 ∧ p4902)) := by
  classical
  tauto

theorem initial8086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3570) ∨ (¬ (meaning t m 4900)) := by
  exact rule8086 (meaning t m 3570) (meaning t m 4119) (meaning t m 4132) (meaning t m 4901) (meaning t m 4902)

theorem rule8087 (p3570 p4119 p4132 p4901 p4902 : Prop) : (¬ (p4119 ∧ p4132 ∧ p3570 ∧ p4901 ∧ p4902)) ∨ (p4901) := by
  classical
  tauto

theorem initial8087 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4900)) ∨ (meaning t m 4901) := by
  exact rule8087 (meaning t m 3570) (meaning t m 4119) (meaning t m 4132) (meaning t m 4901) (meaning t m 4902)

theorem rule8088 (p3570 p4119 p4132 p4901 p4902 : Prop) : (¬ (p4119 ∧ p4132 ∧ p3570 ∧ p4901 ∧ p4902)) ∨ (p4902) := by
  classical
  tauto

theorem initial8088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4900)) ∨ (meaning t m 4902) := by
  exact rule8088 (meaning t m 3570) (meaning t m 4119) (meaning t m 4132) (meaning t m 4901) (meaning t m 4902)

theorem rule8090 (p2881 p3747 p4042 p4904 p4905 : Prop) : (p4042) ∨ (¬ (p4042 ∧ p3747 ∧ p2881 ∧ p4904 ∧ p4905)) := by
  classical
  tauto

theorem initial8090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4042) ∨ (¬ (meaning t m 4903)) := by
  exact rule8090 (meaning t m 2881) (meaning t m 3747) (meaning t m 4042) (meaning t m 4904) (meaning t m 4905)

theorem rule8091 (p2881 p3747 p4042 p4904 p4905 : Prop) : (p3747) ∨ (¬ (p4042 ∧ p3747 ∧ p2881 ∧ p4904 ∧ p4905)) := by
  classical
  tauto

theorem initial8091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3747) ∨ (¬ (meaning t m 4903)) := by
  exact rule8091 (meaning t m 2881) (meaning t m 3747) (meaning t m 4042) (meaning t m 4904) (meaning t m 4905)

theorem rule8092 (p2881 p3747 p4042 p4904 p4905 : Prop) : (p2881) ∨ (¬ (p4042 ∧ p3747 ∧ p2881 ∧ p4904 ∧ p4905)) := by
  classical
  tauto

theorem initial8092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2881) ∨ (¬ (meaning t m 4903)) := by
  exact rule8092 (meaning t m 2881) (meaning t m 3747) (meaning t m 4042) (meaning t m 4904) (meaning t m 4905)

theorem rule8093 (p2881 p3747 p4042 p4904 p4905 : Prop) : (¬ (p4042 ∧ p3747 ∧ p2881 ∧ p4904 ∧ p4905)) ∨ (p4904) := by
  classical
  tauto

theorem initial8093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4903)) ∨ (meaning t m 4904) := by
  exact rule8093 (meaning t m 2881) (meaning t m 3747) (meaning t m 4042) (meaning t m 4904) (meaning t m 4905)

theorem rule8094 (p2881 p3747 p4042 p4904 p4905 : Prop) : (¬ (p4042 ∧ p3747 ∧ p2881 ∧ p4904 ∧ p4905)) ∨ (p4905) := by
  classical
  tauto

theorem initial8094 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4903)) ∨ (meaning t m 4905) := by
  exact rule8094 (meaning t m 2881) (meaning t m 3747) (meaning t m 4042) (meaning t m 4904) (meaning t m 4905)

theorem rule8098 (p4900 p4903 : Prop) : (¬ (p4900 ∨ p4903)) ∨ (p4900) ∨ (p4903) := by
  classical
  tauto

theorem initial8098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4899)) ∨ (meaning t m 4900) ∨ (meaning t m 4903) := by
  exact rule8098 (meaning t m 4900) (meaning t m 4903)

theorem rule8099 (p2875 p4899 : Prop) (h : (p2875 ↔ p4899)) : (¬ p2875) ∨ (p4899) := by
  classical
  tauto

theorem initial8099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2875)) ∨ (meaning t m 4899) := by
  have source := ElevenTheory.theory1188 t (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule8099 (meaning t m 2875) (meaning t m 4899) source

theorem rule8102 (p3486 p3554 p4909 p4910 p4911 : Prop) : (p3554) ∨ (¬ (p3554 ∧ p4909 ∧ p3486 ∧ p4910 ∧ p4911)) := by
  classical
  tauto

theorem initial8102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3554) ∨ (¬ (meaning t m 4908)) := by
  exact rule8102 (meaning t m 3486) (meaning t m 3554) (meaning t m 4909) (meaning t m 4910) (meaning t m 4911)

theorem rule8103 (p3486 p3554 p4909 p4910 p4911 : Prop) : (¬ (p3554 ∧ p4909 ∧ p3486 ∧ p4910 ∧ p4911)) ∨ (p4909) := by
  classical
  tauto

theorem initial8103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4908)) ∨ (meaning t m 4909) := by
  exact rule8103 (meaning t m 3486) (meaning t m 3554) (meaning t m 4909) (meaning t m 4910) (meaning t m 4911)

theorem rule8104 (p3486 p3554 p4909 p4910 p4911 : Prop) : (p3486) ∨ (¬ (p3554 ∧ p4909 ∧ p3486 ∧ p4910 ∧ p4911)) := by
  classical
  tauto

theorem initial8104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3486) ∨ (¬ (meaning t m 4908)) := by
  exact rule8104 (meaning t m 3486) (meaning t m 3554) (meaning t m 4909) (meaning t m 4910) (meaning t m 4911)

theorem rule8106 (p3486 p3554 p4909 p4910 p4911 : Prop) : (¬ (p3554 ∧ p4909 ∧ p3486 ∧ p4910 ∧ p4911)) ∨ (p4911) := by
  classical
  tauto

theorem initial8106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4908)) ∨ (meaning t m 4911) := by
  exact rule8106 (meaning t m 3486) (meaning t m 3554) (meaning t m 4909) (meaning t m 4910) (meaning t m 4911)

theorem rule8108 (p2891 p3571 p4431 p4913 p4914 : Prop) : (p3571) ∨ (¬ (p3571 ∧ p4431 ∧ p2891 ∧ p4913 ∧ p4914)) := by
  classical
  tauto

theorem initial8108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3571) ∨ (¬ (meaning t m 4912)) := by
  exact rule8108 (meaning t m 2891) (meaning t m 3571) (meaning t m 4431) (meaning t m 4913) (meaning t m 4914)

theorem rule8109 (p2891 p3571 p4431 p4913 p4914 : Prop) : (p4431) ∨ (¬ (p3571 ∧ p4431 ∧ p2891 ∧ p4913 ∧ p4914)) := by
  classical
  tauto

theorem initial8109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4431) ∨ (¬ (meaning t m 4912)) := by
  exact rule8109 (meaning t m 2891) (meaning t m 3571) (meaning t m 4431) (meaning t m 4913) (meaning t m 4914)

theorem rule8110 (p2891 p3571 p4431 p4913 p4914 : Prop) : (p2891) ∨ (¬ (p3571 ∧ p4431 ∧ p2891 ∧ p4913 ∧ p4914)) := by
  classical
  tauto

theorem initial8110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2891) ∨ (¬ (meaning t m 4912)) := by
  exact rule8110 (meaning t m 2891) (meaning t m 3571) (meaning t m 4431) (meaning t m 4913) (meaning t m 4914)

theorem rule8116 (p4908 p4912 : Prop) : (¬ (p4908 ∨ p4912)) ∨ (p4908) ∨ (p4912) := by
  classical
  tauto

theorem initial8116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4907)) ∨ (meaning t m 4908) ∨ (meaning t m 4912) := by
  exact rule8116 (meaning t m 4908) (meaning t m 4912)

theorem rule8117 (p2885 p4907 : Prop) (h : (p2885 ↔ p4907)) : (¬ p2885) ∨ (p4907) := by
  classical
  tauto

theorem initial8117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2885)) ∨ (meaning t m 4907) := by
  have source := ElevenTheory.theory1190 t (m.theta 1 5) (m.theta 1 7) (m.theta 5 7)
  exact rule8117 (meaning t m 2885) (meaning t m 4907) source

theorem rule8119 (p3699 p4280 p4320 p4386 p4917 : Prop) : (p4386) ∨ (¬ (p4386 ∧ p3699 ∧ p4320 ∧ p4917 ∧ p4280)) := by
  classical
  tauto

theorem initial8119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4386) ∨ (¬ (meaning t m 4916)) := by
  exact rule8119 (meaning t m 3699) (meaning t m 4280) (meaning t m 4320) (meaning t m 4386) (meaning t m 4917)

theorem rule8120 (p3699 p4280 p4320 p4386 p4917 : Prop) : (p3699) ∨ (¬ (p4386 ∧ p3699 ∧ p4320 ∧ p4917 ∧ p4280)) := by
  classical
  tauto

theorem initial8120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3699) ∨ (¬ (meaning t m 4916)) := by
  exact rule8120 (meaning t m 3699) (meaning t m 4280) (meaning t m 4320) (meaning t m 4386) (meaning t m 4917)

theorem rule8121 (p3699 p4280 p4320 p4386 p4917 : Prop) : (p4320) ∨ (¬ (p4386 ∧ p3699 ∧ p4320 ∧ p4917 ∧ p4280)) := by
  classical
  tauto

theorem initial8121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4320) ∨ (¬ (meaning t m 4916)) := by
  exact rule8121 (meaning t m 3699) (meaning t m 4280) (meaning t m 4320) (meaning t m 4386) (meaning t m 4917)

theorem rule8122 (p3699 p4280 p4320 p4386 p4917 : Prop) : (¬ (p4386 ∧ p3699 ∧ p4320 ∧ p4917 ∧ p4280)) ∨ (p4917) := by
  classical
  tauto

theorem initial8122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4916)) ∨ (meaning t m 4917) := by
  exact rule8122 (meaning t m 3699) (meaning t m 4280) (meaning t m 4320) (meaning t m 4386) (meaning t m 4917)

theorem rule8123 (p3699 p4280 p4320 p4386 p4917 : Prop) : (p4280) ∨ (¬ (p4386 ∧ p3699 ∧ p4320 ∧ p4917 ∧ p4280)) := by
  classical
  tauto

theorem initial8123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4280) ∨ (¬ (meaning t m 4916)) := by
  exact rule8123 (meaning t m 3699) (meaning t m 4280) (meaning t m 4320) (meaning t m 4386) (meaning t m 4917)

theorem rule8125 (p2901 p2995 p4333 p4362 p4919 : Prop) : (p4333) ∨ (¬ (p4333 ∧ p2995 ∧ p2901 ∧ p4919 ∧ p4362)) := by
  classical
  tauto

theorem initial8125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4333) ∨ (¬ (meaning t m 4918)) := by
  exact rule8125 (meaning t m 2901) (meaning t m 2995) (meaning t m 4333) (meaning t m 4362) (meaning t m 4919)

theorem rule8126 (p2901 p2995 p4333 p4362 p4919 : Prop) : (p2995) ∨ (¬ (p4333 ∧ p2995 ∧ p2901 ∧ p4919 ∧ p4362)) := by
  classical
  tauto

theorem initial8126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2995) ∨ (¬ (meaning t m 4918)) := by
  exact rule8126 (meaning t m 2901) (meaning t m 2995) (meaning t m 4333) (meaning t m 4362) (meaning t m 4919)

theorem rule8127 (p2901 p2995 p4333 p4362 p4919 : Prop) : (p2901) ∨ (¬ (p4333 ∧ p2995 ∧ p2901 ∧ p4919 ∧ p4362)) := by
  classical
  tauto

theorem initial8127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2901) ∨ (¬ (meaning t m 4918)) := by
  exact rule8127 (meaning t m 2901) (meaning t m 2995) (meaning t m 4333) (meaning t m 4362) (meaning t m 4919)

theorem rule8128 (p2901 p2995 p4333 p4362 p4919 : Prop) : (¬ (p4333 ∧ p2995 ∧ p2901 ∧ p4919 ∧ p4362)) ∨ (p4919) := by
  classical
  tauto

theorem initial8128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4918)) ∨ (meaning t m 4919) := by
  exact rule8128 (meaning t m 2901) (meaning t m 2995) (meaning t m 4333) (meaning t m 4362) (meaning t m 4919)

theorem rule8129 (p2901 p2995 p4333 p4362 p4919 : Prop) : (p4362) ∨ (¬ (p4333 ∧ p2995 ∧ p2901 ∧ p4919 ∧ p4362)) := by
  classical
  tauto

theorem initial8129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4362) ∨ (¬ (meaning t m 4918)) := by
  exact rule8129 (meaning t m 2901) (meaning t m 2995) (meaning t m 4333) (meaning t m 4362) (meaning t m 4919)

theorem rule8133 (p4916 p4918 : Prop) : (¬ (p4916 ∨ p4918)) ∨ (p4916) ∨ (p4918) := by
  classical
  tauto

theorem initial8133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4915)) ∨ (meaning t m 4916) ∨ (meaning t m 4918) := by
  exact rule8133 (meaning t m 4916) (meaning t m 4918)

theorem rule8134 (p2895 p4915 : Prop) (h : (p2895 ↔ p4915)) : (¬ p2895) ∨ (p4915) := by
  classical
  tauto

theorem initial8134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2895)) ∨ (meaning t m 4915) := by
  have source := ElevenTheory.theory1191 t (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule8134 (meaning t m 2895) (meaning t m 4915) source

theorem rule8136 (p3644 p4186 p4383 p4420 p4922 : Prop) : (p4186) ∨ (¬ (p4186 ∧ p4383 ∧ p3644 ∧ p4922 ∧ p4420)) := by
  classical
  tauto

theorem initial8136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4186) ∨ (¬ (meaning t m 4921)) := by
  exact rule8136 (meaning t m 3644) (meaning t m 4186) (meaning t m 4383) (meaning t m 4420) (meaning t m 4922)

theorem rule8137 (p3644 p4186 p4383 p4420 p4922 : Prop) : (p4383) ∨ (¬ (p4186 ∧ p4383 ∧ p3644 ∧ p4922 ∧ p4420)) := by
  classical
  tauto

theorem initial8137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4383) ∨ (¬ (meaning t m 4921)) := by
  exact rule8137 (meaning t m 3644) (meaning t m 4186) (meaning t m 4383) (meaning t m 4420) (meaning t m 4922)

theorem rule8138 (p3644 p4186 p4383 p4420 p4922 : Prop) : (p3644) ∨ (¬ (p4186 ∧ p4383 ∧ p3644 ∧ p4922 ∧ p4420)) := by
  classical
  tauto

theorem initial8138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3644) ∨ (¬ (meaning t m 4921)) := by
  exact rule8138 (meaning t m 3644) (meaning t m 4186) (meaning t m 4383) (meaning t m 4420) (meaning t m 4922)

theorem rule8139 (p3644 p4186 p4383 p4420 p4922 : Prop) : (¬ (p4186 ∧ p4383 ∧ p3644 ∧ p4922 ∧ p4420)) ∨ (p4922) := by
  classical
  tauto

theorem initial8139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4921)) ∨ (meaning t m 4922) := by
  exact rule8139 (meaning t m 3644) (meaning t m 4186) (meaning t m 4383) (meaning t m 4420) (meaning t m 4922)

theorem rule8140 (p3644 p4186 p4383 p4420 p4922 : Prop) : (p4420) ∨ (¬ (p4186 ∧ p4383 ∧ p3644 ∧ p4922 ∧ p4420)) := by
  classical
  tauto

theorem initial8140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4420) ∨ (¬ (meaning t m 4921)) := by
  exact rule8140 (meaning t m 3644) (meaning t m 4186) (meaning t m 4383) (meaning t m 4420) (meaning t m 4922)

theorem rule8142 (p2911 p3875 p4404 p4438 p4924 : Prop) : (p4404) ∨ (¬ (p4404 ∧ p3875 ∧ p2911 ∧ p4924 ∧ p4438)) := by
  classical
  tauto

theorem initial8142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4404) ∨ (¬ (meaning t m 4923)) := by
  exact rule8142 (meaning t m 2911) (meaning t m 3875) (meaning t m 4404) (meaning t m 4438) (meaning t m 4924)

theorem rule8143 (p2911 p3875 p4404 p4438 p4924 : Prop) : (p3875) ∨ (¬ (p4404 ∧ p3875 ∧ p2911 ∧ p4924 ∧ p4438)) := by
  classical
  tauto

theorem initial8143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3875) ∨ (¬ (meaning t m 4923)) := by
  exact rule8143 (meaning t m 2911) (meaning t m 3875) (meaning t m 4404) (meaning t m 4438) (meaning t m 4924)

theorem rule8144 (p2911 p3875 p4404 p4438 p4924 : Prop) : (p2911) ∨ (¬ (p4404 ∧ p3875 ∧ p2911 ∧ p4924 ∧ p4438)) := by
  classical
  tauto

theorem initial8144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2911) ∨ (¬ (meaning t m 4923)) := by
  exact rule8144 (meaning t m 2911) (meaning t m 3875) (meaning t m 4404) (meaning t m 4438) (meaning t m 4924)

theorem rule8146 (p2911 p3875 p4404 p4438 p4924 : Prop) : (p4438) ∨ (¬ (p4404 ∧ p3875 ∧ p2911 ∧ p4924 ∧ p4438)) := by
  classical
  tauto

theorem initial8146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4438) ∨ (¬ (meaning t m 4923)) := by
  exact rule8146 (meaning t m 2911) (meaning t m 3875) (meaning t m 4404) (meaning t m 4438) (meaning t m 4924)

theorem rule8150 (p4921 p4923 : Prop) : (¬ (p4921 ∨ p4923)) ∨ (p4921) ∨ (p4923) := by
  classical
  tauto

theorem initial8150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4920)) ∨ (meaning t m 4921) ∨ (meaning t m 4923) := by
  exact rule8150 (meaning t m 4921) (meaning t m 4923)

theorem rule8151 (p2905 p4920 : Prop) (h : (p2905 ↔ p4920)) : (¬ p2905) ∨ (p4920) := by
  classical
  tauto

theorem initial8151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2905)) ∨ (meaning t m 4920) := by
  have source := ElevenTheory.theory1192 t (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule8151 (meaning t m 2905) (meaning t m 4920) source

theorem rule8155 (p2925 p2932 : Prop) : (p2925) ∨ (p2932) ∨ (¬ (p2925 ∨ p2932)) := by
  classical
  tauto

theorem initial8155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2925) ∨ (meaning t m 2932) ∨ (¬ (meaning t m 4925)) := by
  exact rule8155 (meaning t m 2925) (meaning t m 2932)

theorem rule8156 (p2916 p4925 : Prop) (h : (p2916 ↔ p4925)) : (¬ p2916) ∨ (p4925) := by
  classical
  tauto

theorem initial8156 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2916)) ∨ (meaning t m 4925) := by
  have source := ElevenTheory.theory1193 t (m.theta 1 4) (m.theta 1 7) (m.theta 4 7)
  exact rule8156 (meaning t m 2916) (meaning t m 4925) source

theorem rule8182 (p2949 p2956 : Prop) : (p2949) ∨ (p2956) ∨ (¬ (p2949 ∨ p2956)) := by
  classical
  tauto

theorem initial8182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2949) ∨ (meaning t m 2956) ∨ (¬ (meaning t m 4931)) := by
  exact rule8182 (meaning t m 2949) (meaning t m 2956)

theorem rule8183 (p2940 p4931 : Prop) (h : (p2940 ↔ p4931)) : (¬ p2940) ∨ (p4931) := by
  classical
  tauto

theorem initial8183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2940)) ∨ (meaning t m 4931) := by
  have source := ElevenTheory.theory1197 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 5)
  exact rule8183 (meaning t m 2940) (meaning t m 4931) source

theorem rule8201 (p2284 p3952 : Prop) (h : (¬ p3952) ∨ (¬ p2284)) : (¬ p2284) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial8201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory1200 (m.theta 3 5) (m.theta 5 6)
  exact rule8201 (meaning t m 2284) (meaning t m 3952) source

theorem rule8202 (p2946 p2952 : Prop) (h : (¬ p2952) ∨ (¬ p2946)) : (¬ p2946) ∨ (¬ p2952) := by
  classical
  tauto

theorem initial8202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2952)) := by
  have source := ElevenTheory.theory1201 (m.theta 0 3) (m.theta 3 5)
  exact rule8202 (meaning t m 2946) (meaning t m 2952) source

theorem rule8203 (p2027 p2563 p2946 p2963 p3745 p4702 : Prop) (h : (¬ p4702) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p2963) ∨ (¬ p3745) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3745) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial8203 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory1202 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6)
  exact rule8203 (meaning t m 2027) (meaning t m 2563) (meaning t m 2946) (meaning t m 2963) (meaning t m 3745) (meaning t m 4702) source

theorem rule8204 (p4363 p4388 p4938 p4939 p4940 : Prop) : (¬ (p4938 ∧ p4388 ∧ p4363 ∧ p4939 ∧ p4940)) ∨ (p4938) := by
  classical
  tauto

theorem initial8204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4937)) ∨ (meaning t m 4938) := by
  exact rule8204 (meaning t m 4363) (meaning t m 4388) (meaning t m 4938) (meaning t m 4939) (meaning t m 4940)

theorem rule8205 (p4363 p4388 p4938 p4939 p4940 : Prop) : (p4388) ∨ (¬ (p4938 ∧ p4388 ∧ p4363 ∧ p4939 ∧ p4940)) := by
  classical
  tauto

theorem initial8205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4388) ∨ (¬ (meaning t m 4937)) := by
  exact rule8205 (meaning t m 4363) (meaning t m 4388) (meaning t m 4938) (meaning t m 4939) (meaning t m 4940)

theorem rule8206 (p4363 p4388 p4938 p4939 p4940 : Prop) : (p4363) ∨ (¬ (p4938 ∧ p4388 ∧ p4363 ∧ p4939 ∧ p4940)) := by
  classical
  tauto

theorem initial8206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4363) ∨ (¬ (meaning t m 4937)) := by
  exact rule8206 (meaning t m 4363) (meaning t m 4388) (meaning t m 4938) (meaning t m 4939) (meaning t m 4940)

theorem rule8210 (p2972 p4387 p4942 p4943 p4944 : Prop) : (p4387) ∨ (¬ (p4387 ∧ p4942 ∧ p2972 ∧ p4943 ∧ p4944)) := by
  classical
  tauto

theorem initial8210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4387) ∨ (¬ (meaning t m 4941)) := by
  exact rule8210 (meaning t m 2972) (meaning t m 4387) (meaning t m 4942) (meaning t m 4943) (meaning t m 4944)

theorem rule8211 (p2972 p4387 p4942 p4943 p4944 : Prop) : (¬ (p4387 ∧ p4942 ∧ p2972 ∧ p4943 ∧ p4944)) ∨ (p4942) := by
  classical
  tauto

theorem initial8211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4941)) ∨ (meaning t m 4942) := by
  exact rule8211 (meaning t m 2972) (meaning t m 4387) (meaning t m 4942) (meaning t m 4943) (meaning t m 4944)

theorem rule8212 (p2972 p4387 p4942 p4943 p4944 : Prop) : (p2972) ∨ (¬ (p4387 ∧ p4942 ∧ p2972 ∧ p4943 ∧ p4944)) := by
  classical
  tauto

theorem initial8212 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2972) ∨ (¬ (meaning t m 4941)) := by
  exact rule8212 (meaning t m 2972) (meaning t m 4387) (meaning t m 4942) (meaning t m 4943) (meaning t m 4944)

theorem rule8218 (p4937 p4941 : Prop) : (¬ (p4937 ∨ p4941)) ∨ (p4937) ∨ (p4941) := by
  classical
  tauto

theorem initial8218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4936)) ∨ (meaning t m 4937) ∨ (meaning t m 4941) := by
  exact rule8218 (meaning t m 4937) (meaning t m 4941)

theorem rule8219 (p2966 p4936 : Prop) (h : (p2966 ↔ p4936)) : (¬ p2966) ∨ (p4936) := by
  classical
  tauto

theorem initial8219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2966)) ∨ (meaning t m 4936) := by
  have source := ElevenTheory.theory1203 t (m.theta 1 5) (m.theta 1 9) (m.theta 5 9)
  exact rule8219 (meaning t m 2966) (meaning t m 4936) source

theorem rule8221 (p3237 p4947 p4948 p4949 p4950 : Prop) : (p3237) ∨ (¬ (p3237 ∧ p4947 ∧ p4948 ∧ p4949 ∧ p4950)) := by
  classical
  tauto

theorem initial8221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3237) ∨ (¬ (meaning t m 4946)) := by
  exact rule8221 (meaning t m 3237) (meaning t m 4947) (meaning t m 4948) (meaning t m 4949) (meaning t m 4950)

theorem rule8222 (p3237 p4947 p4948 p4949 p4950 : Prop) : (¬ (p3237 ∧ p4947 ∧ p4948 ∧ p4949 ∧ p4950)) ∨ (p4947) := by
  classical
  tauto

theorem initial8222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4946)) ∨ (meaning t m 4947) := by
  exact rule8222 (meaning t m 3237) (meaning t m 4947) (meaning t m 4948) (meaning t m 4949) (meaning t m 4950)

theorem rule8223 (p3237 p4947 p4948 p4949 p4950 : Prop) : (¬ (p3237 ∧ p4947 ∧ p4948 ∧ p4949 ∧ p4950)) ∨ (p4948) := by
  classical
  tauto

theorem initial8223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4946)) ∨ (meaning t m 4948) := by
  exact rule8223 (meaning t m 3237) (meaning t m 4947) (meaning t m 4948) (meaning t m 4949) (meaning t m 4950)

theorem rule8224 (p3237 p4947 p4948 p4949 p4950 : Prop) : (¬ (p3237 ∧ p4947 ∧ p4948 ∧ p4949 ∧ p4950)) ∨ (p4949) := by
  classical
  tauto

theorem initial8224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4946)) ∨ (meaning t m 4949) := by
  exact rule8224 (meaning t m 3237) (meaning t m 4947) (meaning t m 4948) (meaning t m 4949) (meaning t m 4950)

theorem rule8227 (p2982 p4449 p4952 p4953 p4954 : Prop) : (¬ (p4952 ∧ p4449 ∧ p2982 ∧ p4953 ∧ p4954)) ∨ (p4952) := by
  classical
  tauto

theorem initial8227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4951)) ∨ (meaning t m 4952) := by
  exact rule8227 (meaning t m 2982) (meaning t m 4449) (meaning t m 4952) (meaning t m 4953) (meaning t m 4954)

theorem rule8228 (p2982 p4449 p4952 p4953 p4954 : Prop) : (p4449) ∨ (¬ (p4952 ∧ p4449 ∧ p2982 ∧ p4953 ∧ p4954)) := by
  classical
  tauto

theorem initial8228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4449) ∨ (¬ (meaning t m 4951)) := by
  exact rule8228 (meaning t m 2982) (meaning t m 4449) (meaning t m 4952) (meaning t m 4953) (meaning t m 4954)

theorem rule8229 (p2982 p4449 p4952 p4953 p4954 : Prop) : (p2982) ∨ (¬ (p4952 ∧ p4449 ∧ p2982 ∧ p4953 ∧ p4954)) := by
  classical
  tauto

theorem initial8229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2982) ∨ (¬ (meaning t m 4951)) := by
  exact rule8229 (meaning t m 2982) (meaning t m 4449) (meaning t m 4952) (meaning t m 4953) (meaning t m 4954)

theorem rule8230 (p2982 p4449 p4952 p4953 p4954 : Prop) : (¬ (p4952 ∧ p4449 ∧ p2982 ∧ p4953 ∧ p4954)) ∨ (p4953) := by
  classical
  tauto

theorem initial8230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4951)) ∨ (meaning t m 4953) := by
  exact rule8230 (meaning t m 2982) (meaning t m 4449) (meaning t m 4952) (meaning t m 4953) (meaning t m 4954)

theorem rule8231 (p2982 p4449 p4952 p4953 p4954 : Prop) : (¬ (p4952 ∧ p4449 ∧ p2982 ∧ p4953 ∧ p4954)) ∨ (p4954) := by
  classical
  tauto

theorem initial8231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4951)) ∨ (meaning t m 4954) := by
  exact rule8231 (meaning t m 2982) (meaning t m 4449) (meaning t m 4952) (meaning t m 4953) (meaning t m 4954)

theorem rule8235 (p4946 p4951 : Prop) : (¬ (p4946 ∨ p4951)) ∨ (p4946) ∨ (p4951) := by
  classical
  tauto

theorem initial8235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4945)) ∨ (meaning t m 4946) ∨ (meaning t m 4951) := by
  exact rule8235 (meaning t m 4946) (meaning t m 4951)

theorem rule8236 (p2976 p4945 : Prop) (h : (p2976 ↔ p4945)) : (¬ p2976) ∨ (p4945) := by
  classical
  tauto

theorem initial8236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2976)) ∨ (meaning t m 4945) := by
  have source := ElevenTheory.theory1204 t (m.theta 4 5) (m.theta 4 9) (m.theta 5 9)
  exact rule8236 (meaning t m 2976) (meaning t m 4945) source

theorem rule8238 (p3368 p3412 p3662 p4448 p4957 : Prop) : (p3368) ∨ (¬ (p3368 ∧ p3412 ∧ p3662 ∧ p4448 ∧ p4957)) := by
  classical
  tauto

theorem initial8238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3368) ∨ (¬ (meaning t m 4956)) := by
  exact rule8238 (meaning t m 3368) (meaning t m 3412) (meaning t m 3662) (meaning t m 4448) (meaning t m 4957)

theorem rule8239 (p3368 p3412 p3662 p4448 p4957 : Prop) : (p3412) ∨ (¬ (p3368 ∧ p3412 ∧ p3662 ∧ p4448 ∧ p4957)) := by
  classical
  tauto

theorem initial8239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3412) ∨ (¬ (meaning t m 4956)) := by
  exact rule8239 (meaning t m 3368) (meaning t m 3412) (meaning t m 3662) (meaning t m 4448) (meaning t m 4957)

theorem rule8240 (p3368 p3412 p3662 p4448 p4957 : Prop) : (p3662) ∨ (¬ (p3368 ∧ p3412 ∧ p3662 ∧ p4448 ∧ p4957)) := by
  classical
  tauto

theorem initial8240 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3662) ∨ (¬ (meaning t m 4956)) := by
  exact rule8240 (meaning t m 3368) (meaning t m 3412) (meaning t m 3662) (meaning t m 4448) (meaning t m 4957)

theorem rule8241 (p3368 p3412 p3662 p4448 p4957 : Prop) : (p4448) ∨ (¬ (p3368 ∧ p3412 ∧ p3662 ∧ p4448 ∧ p4957)) := by
  classical
  tauto

theorem initial8241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4448) ∨ (¬ (meaning t m 4956)) := by
  exact rule8241 (meaning t m 3368) (meaning t m 3412) (meaning t m 3662) (meaning t m 4448) (meaning t m 4957)

theorem rule8242 (p3368 p3412 p3662 p4448 p4957 : Prop) : (¬ (p3368 ∧ p3412 ∧ p3662 ∧ p4448 ∧ p4957)) ∨ (p4957) := by
  classical
  tauto

theorem initial8242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4956)) ∨ (meaning t m 4957) := by
  exact rule8242 (meaning t m 3368) (meaning t m 3412) (meaning t m 3662) (meaning t m 4448) (meaning t m 4957)

theorem rule8244 (p2992 p4282 p4365 p4959 p4960 : Prop) : (p4282) ∨ (¬ (p4282 ∧ p4365 ∧ p2992 ∧ p4959 ∧ p4960)) := by
  classical
  tauto

theorem initial8244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4282) ∨ (¬ (meaning t m 4958)) := by
  exact rule8244 (meaning t m 2992) (meaning t m 4282) (meaning t m 4365) (meaning t m 4959) (meaning t m 4960)

theorem rule8245 (p2992 p4282 p4365 p4959 p4960 : Prop) : (p4365) ∨ (¬ (p4282 ∧ p4365 ∧ p2992 ∧ p4959 ∧ p4960)) := by
  classical
  tauto

theorem initial8245 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4365) ∨ (¬ (meaning t m 4958)) := by
  exact rule8245 (meaning t m 2992) (meaning t m 4282) (meaning t m 4365) (meaning t m 4959) (meaning t m 4960)

theorem rule8246 (p2992 p4282 p4365 p4959 p4960 : Prop) : (p2992) ∨ (¬ (p4282 ∧ p4365 ∧ p2992 ∧ p4959 ∧ p4960)) := by
  classical
  tauto

theorem initial8246 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2992) ∨ (¬ (meaning t m 4958)) := by
  exact rule8246 (meaning t m 2992) (meaning t m 4282) (meaning t m 4365) (meaning t m 4959) (meaning t m 4960)

theorem rule8247 (p2992 p4282 p4365 p4959 p4960 : Prop) : (¬ (p4282 ∧ p4365 ∧ p2992 ∧ p4959 ∧ p4960)) ∨ (p4959) := by
  classical
  tauto

theorem initial8247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4958)) ∨ (meaning t m 4959) := by
  exact rule8247 (meaning t m 2992) (meaning t m 4282) (meaning t m 4365) (meaning t m 4959) (meaning t m 4960)

theorem rule8248 (p2992 p4282 p4365 p4959 p4960 : Prop) : (¬ (p4282 ∧ p4365 ∧ p2992 ∧ p4959 ∧ p4960)) ∨ (p4960) := by
  classical
  tauto

theorem initial8248 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4958)) ∨ (meaning t m 4960) := by
  exact rule8248 (meaning t m 2992) (meaning t m 4282) (meaning t m 4365) (meaning t m 4959) (meaning t m 4960)

theorem rule8252 (p4956 p4958 : Prop) : (¬ (p4956 ∨ p4958)) ∨ (p4956) ∨ (p4958) := by
  classical
  tauto

theorem initial8252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4955)) ∨ (meaning t m 4956) ∨ (meaning t m 4958) := by
  exact rule8252 (meaning t m 4956) (meaning t m 4958)

theorem rule8253 (p2986 p4955 : Prop) (h : (p2986 ↔ p4955)) : (¬ p2986) ∨ (p4955) := by
  classical
  tauto

theorem initial8253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2986)) ∨ (meaning t m 4955) := by
  have source := ElevenTheory.theory1205 t (m.theta 1 3) (m.theta 1 5) (m.theta 3 5)
  exact rule8253 (meaning t m 2986) (meaning t m 4955) source

theorem rule8255 (p3877 p4364 p4963 p4964 p4965 : Prop) : (p4364) ∨ (¬ (p4364 ∧ p4963 ∧ p3877 ∧ p4964 ∧ p4965)) := by
  classical
  tauto

theorem initial8255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4364) ∨ (¬ (meaning t m 4962)) := by
  exact rule8255 (meaning t m 3877) (meaning t m 4364) (meaning t m 4963) (meaning t m 4964) (meaning t m 4965)

theorem rule8256 (p3877 p4364 p4963 p4964 p4965 : Prop) : (¬ (p4364 ∧ p4963 ∧ p3877 ∧ p4964 ∧ p4965)) ∨ (p4963) := by
  classical
  tauto

theorem initial8256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4962)) ∨ (meaning t m 4963) := by
  exact rule8256 (meaning t m 3877) (meaning t m 4364) (meaning t m 4963) (meaning t m 4964) (meaning t m 4965)

theorem rule8257 (p3877 p4364 p4963 p4964 p4965 : Prop) : (p3877) ∨ (¬ (p4364 ∧ p4963 ∧ p3877 ∧ p4964 ∧ p4965)) := by
  classical
  tauto

theorem initial8257 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3877) ∨ (¬ (meaning t m 4962)) := by
  exact rule8257 (meaning t m 3877) (meaning t m 4364) (meaning t m 4963) (meaning t m 4964) (meaning t m 4965)

theorem rule8258 (p3877 p4364 p4963 p4964 p4965 : Prop) : (¬ (p4364 ∧ p4963 ∧ p3877 ∧ p4964 ∧ p4965)) ∨ (p4964) := by
  classical
  tauto

theorem initial8258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4962)) ∨ (meaning t m 4964) := by
  exact rule8258 (meaning t m 3877) (meaning t m 4364) (meaning t m 4963) (meaning t m 4964) (meaning t m 4965)

theorem rule8261 (p3005 p4373 p4967 p4968 p4969 : Prop) : (¬ (p4967 ∧ p4373 ∧ p3005 ∧ p4968 ∧ p4969)) ∨ (p4967) := by
  classical
  tauto

theorem initial8261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4966)) ∨ (meaning t m 4967) := by
  exact rule8261 (meaning t m 3005) (meaning t m 4373) (meaning t m 4967) (meaning t m 4968) (meaning t m 4969)

theorem rule8262 (p3005 p4373 p4967 p4968 p4969 : Prop) : (p4373) ∨ (¬ (p4967 ∧ p4373 ∧ p3005 ∧ p4968 ∧ p4969)) := by
  classical
  tauto

theorem initial8262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4373) ∨ (¬ (meaning t m 4966)) := by
  exact rule8262 (meaning t m 3005) (meaning t m 4373) (meaning t m 4967) (meaning t m 4968) (meaning t m 4969)

theorem rule8263 (p3005 p4373 p4967 p4968 p4969 : Prop) : (p3005) ∨ (¬ (p4967 ∧ p4373 ∧ p3005 ∧ p4968 ∧ p4969)) := by
  classical
  tauto

theorem initial8263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3005) ∨ (¬ (meaning t m 4966)) := by
  exact rule8263 (meaning t m 3005) (meaning t m 4373) (meaning t m 4967) (meaning t m 4968) (meaning t m 4969)

theorem rule8269 (p4962 p4966 : Prop) : (¬ (p4962 ∨ p4966)) ∨ (p4962) ∨ (p4966) := by
  classical
  tauto

theorem initial8269 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4961)) ∨ (meaning t m 4962) ∨ (meaning t m 4966) := by
  exact rule8269 (meaning t m 4962) (meaning t m 4966)

theorem rule8270 (p2999 p4961 : Prop) (h : (p2999 ↔ p4961)) : (¬ p2999) ∨ (p4961) := by
  classical
  tauto

theorem initial8270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2999)) ∨ (meaning t m 4961) := by
  have source := ElevenTheory.theory1206 t (m.theta 2 3) (m.theta 2 8) (m.theta 3 8)
  exact rule8270 (meaning t m 2999) (meaning t m 4961) source

theorem rule8272 (p3574 p4194 p4389 p4972 p4973 : Prop) : (p4194) ∨ (¬ (p4194 ∧ p4389 ∧ p3574 ∧ p4972 ∧ p4973)) := by
  classical
  tauto

theorem initial8272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4194) ∨ (¬ (meaning t m 4971)) := by
  exact rule8272 (meaning t m 3574) (meaning t m 4194) (meaning t m 4389) (meaning t m 4972) (meaning t m 4973)

theorem rule8273 (p3574 p4194 p4389 p4972 p4973 : Prop) : (p4389) ∨ (¬ (p4194 ∧ p4389 ∧ p3574 ∧ p4972 ∧ p4973)) := by
  classical
  tauto

theorem initial8273 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4389) ∨ (¬ (meaning t m 4971)) := by
  exact rule8273 (meaning t m 3574) (meaning t m 4194) (meaning t m 4389) (meaning t m 4972) (meaning t m 4973)

theorem rule8274 (p3574 p4194 p4389 p4972 p4973 : Prop) : (p3574) ∨ (¬ (p4194 ∧ p4389 ∧ p3574 ∧ p4972 ∧ p4973)) := by
  classical
  tauto

theorem initial8274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3574) ∨ (¬ (meaning t m 4971)) := by
  exact rule8274 (meaning t m 3574) (meaning t m 4194) (meaning t m 4389) (meaning t m 4972) (meaning t m 4973)

theorem rule8275 (p3574 p4194 p4389 p4972 p4973 : Prop) : (¬ (p4194 ∧ p4389 ∧ p3574 ∧ p4972 ∧ p4973)) ∨ (p4972) := by
  classical
  tauto

theorem initial8275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4971)) ∨ (meaning t m 4972) := by
  exact rule8275 (meaning t m 3574) (meaning t m 4194) (meaning t m 4389) (meaning t m 4972) (meaning t m 4973)

theorem rule8276 (p3574 p4194 p4389 p4972 p4973 : Prop) : (¬ (p4194 ∧ p4389 ∧ p3574 ∧ p4972 ∧ p4973)) ∨ (p4973) := by
  classical
  tauto

theorem initial8276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4971)) ∨ (meaning t m 4973) := by
  exact rule8276 (meaning t m 3574) (meaning t m 4194) (meaning t m 4389) (meaning t m 4972) (meaning t m 4973)

theorem rule8278 (p3016 p3019 p3984 p4975 p4976 : Prop) : (p3984) ∨ (¬ (p3984 ∧ p3019 ∧ p3016 ∧ p4975 ∧ p4976)) := by
  classical
  tauto

theorem initial8278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3984) ∨ (¬ (meaning t m 4974)) := by
  exact rule8278 (meaning t m 3016) (meaning t m 3019) (meaning t m 3984) (meaning t m 4975) (meaning t m 4976)

theorem rule8279 (p3016 p3019 p3984 p4975 p4976 : Prop) : (p3019) ∨ (¬ (p3984 ∧ p3019 ∧ p3016 ∧ p4975 ∧ p4976)) := by
  classical
  tauto

theorem initial8279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3019) ∨ (¬ (meaning t m 4974)) := by
  exact rule8279 (meaning t m 3016) (meaning t m 3019) (meaning t m 3984) (meaning t m 4975) (meaning t m 4976)

theorem rule8280 (p3016 p3019 p3984 p4975 p4976 : Prop) : (p3016) ∨ (¬ (p3984 ∧ p3019 ∧ p3016 ∧ p4975 ∧ p4976)) := by
  classical
  tauto

theorem initial8280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3016) ∨ (¬ (meaning t m 4974)) := by
  exact rule8280 (meaning t m 3016) (meaning t m 3019) (meaning t m 3984) (meaning t m 4975) (meaning t m 4976)

theorem rule8281 (p3016 p3019 p3984 p4975 p4976 : Prop) : (¬ (p3984 ∧ p3019 ∧ p3016 ∧ p4975 ∧ p4976)) ∨ (p4975) := by
  classical
  tauto

theorem initial8281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4974)) ∨ (meaning t m 4975) := by
  exact rule8281 (meaning t m 3016) (meaning t m 3019) (meaning t m 3984) (meaning t m 4975) (meaning t m 4976)

theorem rule8282 (p3016 p3019 p3984 p4975 p4976 : Prop) : (¬ (p3984 ∧ p3019 ∧ p3016 ∧ p4975 ∧ p4976)) ∨ (p4976) := by
  classical
  tauto

theorem initial8282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4974)) ∨ (meaning t m 4976) := by
  exact rule8282 (meaning t m 3016) (meaning t m 3019) (meaning t m 3984) (meaning t m 4975) (meaning t m 4976)

theorem rule8286 (p4971 p4974 : Prop) : (¬ (p4971 ∨ p4974)) ∨ (p4971) ∨ (p4974) := by
  classical
  tauto

theorem initial8286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4970)) ∨ (meaning t m 4971) ∨ (meaning t m 4974) := by
  exact rule8286 (meaning t m 4971) (meaning t m 4974)

theorem rule8287 (p3010 p4970 : Prop) (h : (p3010 ↔ p4970)) : (¬ p3010) ∨ (p4970) := by
  classical
  tauto

theorem initial8287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3010)) ∨ (meaning t m 4970) := by
  have source := ElevenTheory.theory1207 t (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule8287 (meaning t m 3010) (meaning t m 4970) source

theorem rule8291 (p3030 p3036 : Prop) : (p3030) ∨ (p3036) ∨ (¬ (p3030 ∨ p3036)) := by
  classical
  tauto

theorem initial8291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3030) ∨ (meaning t m 3036) ∨ (¬ (meaning t m 4977)) := by
  exact rule8291 (meaning t m 3030) (meaning t m 3036)

theorem rule8292 (p3021 p4977 : Prop) (h : (p3021 ↔ p4977)) : (¬ p3021) ∨ (p4977) := by
  classical
  tauto

theorem initial8292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3021)) ∨ (meaning t m 4977) := by
  have source := ElevenTheory.theory1208 t (m.theta 1 3) (m.theta 1 7) (m.theta 3 7)
  exact rule8292 (meaning t m 3021) (meaning t m 4977) source

theorem rule8310 (p2027 p3027 p3574 p3579 p4111 p4711 : Prop) (h : (¬ p4711) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p3027) ∨ (¬ p3574) ∨ (¬ p3579)) : (p2027) ∨ (¬ p3027) ∨ (¬ p3574) ∨ (¬ p3579) ∨ (¬ p4111) ∨ (¬ p4711) := by
  classical
  tauto

theorem initial8310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4711)) := by
  have source := ElevenTheory.theory1211 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7)
  exact rule8310 (meaning t m 2027) (meaning t m 3027) (meaning t m 3574) (meaning t m 3579) (meaning t m 4111) (meaning t m 4711) source

theorem rule8311 (p2331 p2963 : Prop) (h : (¬ p2963) ∨ (¬ p2331)) : (¬ p2331) ∨ (¬ p2963) := by
  classical
  tauto

theorem initial8311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2963)) := by
  have source := ElevenTheory.theory1212 (m.theta 0 3) (m.theta 3 6)
  exact rule8311 (meaning t m 2331) (meaning t m 2963) source

theorem rule8312 (p2027 p2745 p2870 p2957 p3556 p3662 p4313 : Prop) (h : (¬ p2870) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p2745) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p4313)) : (p2027) ∨ (¬ p2745) ∨ (¬ p2870) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p4313) := by
  classical
  tauto

theorem initial8312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4313)) := by
  have source := ElevenTheory.theory1213 t (m.theta 0 5) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule8312 (meaning t m 2027) (meaning t m 2745) (meaning t m 2870) (meaning t m 2957) (meaning t m 3556) (meaning t m 3662) (meaning t m 4313) source

theorem rule8313 (p3556 p3691 p4984 p4985 p4986 : Prop) : (¬ (p4984 ∧ p3691 ∧ p3556 ∧ p4985 ∧ p4986)) ∨ (p4984) := by
  classical
  tauto

theorem initial8313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4983)) ∨ (meaning t m 4984) := by
  exact rule8313 (meaning t m 3556) (meaning t m 3691) (meaning t m 4984) (meaning t m 4985) (meaning t m 4986)

theorem rule8314 (p3556 p3691 p4984 p4985 p4986 : Prop) : (p3691) ∨ (¬ (p4984 ∧ p3691 ∧ p3556 ∧ p4985 ∧ p4986)) := by
  classical
  tauto

theorem initial8314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3691) ∨ (¬ (meaning t m 4983)) := by
  exact rule8314 (meaning t m 3556) (meaning t m 3691) (meaning t m 4984) (meaning t m 4985) (meaning t m 4986)

theorem rule8315 (p3556 p3691 p4984 p4985 p4986 : Prop) : (p3556) ∨ (¬ (p4984 ∧ p3691 ∧ p3556 ∧ p4985 ∧ p4986)) := by
  classical
  tauto

theorem initial8315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3556) ∨ (¬ (meaning t m 4983)) := by
  exact rule8315 (meaning t m 3556) (meaning t m 3691) (meaning t m 4984) (meaning t m 4985) (meaning t m 4986)

theorem rule8316 (p3556 p3691 p4984 p4985 p4986 : Prop) : (¬ (p4984 ∧ p3691 ∧ p3556 ∧ p4985 ∧ p4986)) ∨ (p4985) := by
  classical
  tauto

theorem initial8316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4983)) ∨ (meaning t m 4985) := by
  exact rule8316 (meaning t m 3556) (meaning t m 3691) (meaning t m 4984) (meaning t m 4985) (meaning t m 4986)

theorem rule8317 (p3556 p3691 p4984 p4985 p4986 : Prop) : (¬ (p4984 ∧ p3691 ∧ p3556 ∧ p4985 ∧ p4986)) ∨ (p4986) := by
  classical
  tauto

theorem initial8317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4983)) ∨ (meaning t m 4986) := by
  exact rule8317 (meaning t m 3556) (meaning t m 3691) (meaning t m 4984) (meaning t m 4985) (meaning t m 4986)

theorem rule8319 (p3051 p4283 p4988 p4989 p4990 : Prop) : (p4283) ∨ (¬ (p4283 ∧ p4988 ∧ p3051 ∧ p4989 ∧ p4990)) := by
  classical
  tauto

theorem initial8319 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4283) ∨ (¬ (meaning t m 4987)) := by
  exact rule8319 (meaning t m 3051) (meaning t m 4283) (meaning t m 4988) (meaning t m 4989) (meaning t m 4990)

theorem rule8320 (p3051 p4283 p4988 p4989 p4990 : Prop) : (¬ (p4283 ∧ p4988 ∧ p3051 ∧ p4989 ∧ p4990)) ∨ (p4988) := by
  classical
  tauto

theorem initial8320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4987)) ∨ (meaning t m 4988) := by
  exact rule8320 (meaning t m 3051) (meaning t m 4283) (meaning t m 4988) (meaning t m 4989) (meaning t m 4990)

theorem rule8321 (p3051 p4283 p4988 p4989 p4990 : Prop) : (p3051) ∨ (¬ (p4283 ∧ p4988 ∧ p3051 ∧ p4989 ∧ p4990)) := by
  classical
  tauto

theorem initial8321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3051) ∨ (¬ (meaning t m 4987)) := by
  exact rule8321 (meaning t m 3051) (meaning t m 4283) (meaning t m 4988) (meaning t m 4989) (meaning t m 4990)

theorem rule8327 (p4983 p4987 : Prop) : (¬ (p4983 ∨ p4987)) ∨ (p4983) ∨ (p4987) := by
  classical
  tauto

theorem initial8327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4982)) ∨ (meaning t m 4983) ∨ (meaning t m 4987) := by
  exact rule8327 (meaning t m 4983) (meaning t m 4987)

end SunPrize.SMT
