import SunPrize.Certificate.Initial087
import SunPrize.Certificate.Inputs
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace SunPrize.SMT
open ElevenLogic

theorem inputBlock544_valid (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) (i : Nat) :
    inputBlock544 (meaning t m) i := by
  unfold inputBlock544
  exact (choose_proof (i < 40734) (choose_proof (i < 40719) (choose_proof (i < 40706) (choose_proof (i < 40703) (choose_proof (i < 40701) (initial40693 t m ht) (initial40701 t m ht)) (choose_proof (i < 40705) (initial40703 t m ht) (initial40705 t m ht))) (choose_proof (i < 40711) (choose_proof (i < 40709) (initial40706 t m ht) (initial40709 t m ht)) (choose_proof (i < 40715) (initial40711 t m ht) (initial40715 t m ht)))) (choose_proof (i < 40728) (choose_proof (i < 40723) (choose_proof (i < 40722) (initial40719 t m ht) (initial40722 t m ht)) (choose_proof (i < 40726) (initial40723 t m ht) (initial40726 t m ht))) (choose_proof (i < 40730) (choose_proof (i < 40729) (initial40728 t m ht) (initial40729 t m ht)) (choose_proof (i < 40731) (initial40730 t m ht) (initial40731 t m ht))))) (choose_proof (i < 40748) (choose_proof (i < 40744) (choose_proof (i < 40739) (choose_proof (i < 40738) (initial40734 t m ht) (initial40738 t m ht)) (choose_proof (i < 40742) (initial40739 t m ht) (initial40742 t m ht))) (choose_proof (i < 40746) (choose_proof (i < 40745) (initial40744 t m ht) (initial40745 t m ht)) (choose_proof (i < 40747) (initial40746 t m ht) (initial40747 t m ht)))) (choose_proof (i < 40753) (choose_proof (i < 40751) (choose_proof (i < 40750) (initial40748 t m ht) (initial40750 t m ht)) (choose_proof (i < 40752) (initial40751 t m ht) (initial40752 t m ht))) (choose_proof (i < 40758) (choose_proof (i < 40757) (initial40753 t m ht) (initial40757 t m ht)) (choose_proof (i < 40760) (initial40758 t m ht) (initial40760 t m ht))))))

theorem inputBlock545_valid (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) (i : Nat) :
    inputBlock545 (meaning t m) i := by
  unfold inputBlock545
  exact (choose_proof (i < 40784) (choose_proof (i < 40769) (choose_proof (i < 40766) (choose_proof (i < 40763) (initial40762 t m ht) (choose_proof (i < 40764) (initial40763 t m ht) (initial40764 t m ht))) (choose_proof (i < 40767) (initial40766 t m ht) (choose_proof (i < 40768) (initial40767 t m ht) (initial40768 t m ht)))) (choose_proof (i < 40777) (choose_proof (i < 40774) (initial40769 t m ht) (choose_proof (i < 40776) (initial40774 t m ht) (initial40776 t m ht))) (choose_proof (i < 40782) (choose_proof (i < 40781) (initial40777 t m ht) (initial40781 t m ht)) (choose_proof (i < 40783) (initial40782 t m ht) (initial40783 t m ht))))) (choose_proof (i < 40795) (choose_proof (i < 40790) (choose_proof (i < 40787) (initial40784 t m ht) (choose_proof (i < 40788) (initial40787 t m ht) (initial40788 t m ht))) (choose_proof (i < 40792) (choose_proof (i < 40791) (initial40790 t m ht) (initial40791 t m ht)) (choose_proof (i < 40794) (initial40792 t m ht) (initial40794 t m ht)))) (choose_proof (i < 40803) (choose_proof (i < 40799) (initial40795 t m ht) (choose_proof (i < 40800) (initial40799 t m ht) (initial40800 t m ht))) (choose_proof (i < 40806) (choose_proof (i < 40804) (initial40803 t m ht) (initial40804 t m ht)) (choose_proof (i < 40808) (initial40806 t m ht) (initial40808 t m ht))))))

theorem inputGroup034_valid (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) (i : Nat) :
    inputGroup034 (meaning t m) i := by
  unfold inputGroup034
  exact (choose_proof (i < 40762) (inputBlock544_valid t m ht i) (inputBlock545_valid t m ht i))

end SunPrize.SMT
