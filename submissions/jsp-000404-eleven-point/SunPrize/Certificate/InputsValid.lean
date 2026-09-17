import SunPrize.Certificate.InputsValid000
import SunPrize.Certificate.InputsValid001
import SunPrize.Certificate.InputsValid002
import SunPrize.Certificate.InputsValid003
import SunPrize.Certificate.InputsValid004
import SunPrize.Certificate.InputsValid005
import SunPrize.Certificate.InputsValid006
import SunPrize.Certificate.InputsValid007
import SunPrize.Certificate.InputsValid008
import SunPrize.Certificate.InputsValid009
import SunPrize.Certificate.InputsValid010
import SunPrize.Certificate.InputsValid011
import SunPrize.Certificate.InputsValid012
import SunPrize.Certificate.InputsValid013
import SunPrize.Certificate.InputsValid014
import SunPrize.Certificate.InputsValid015
import SunPrize.Certificate.InputsValid016
import SunPrize.Certificate.InputsValid017
import SunPrize.Certificate.InputsValid018
import SunPrize.Certificate.InputsValid019
import SunPrize.Certificate.InputsValid020
import SunPrize.Certificate.InputsValid021
import SunPrize.Certificate.InputsValid022
import SunPrize.Certificate.InputsValid023
import SunPrize.Certificate.InputsValid024
import SunPrize.Certificate.InputsValid025
import SunPrize.Certificate.InputsValid026
import SunPrize.Certificate.InputsValid027
import SunPrize.Certificate.InputsValid028
import SunPrize.Certificate.InputsValid029
import SunPrize.Certificate.InputsValid030
import SunPrize.Certificate.InputsValid031
import SunPrize.Certificate.InputsValid032
import SunPrize.Certificate.InputsValid033
import SunPrize.Certificate.InputsValid034
namespace SunPrize.SMT
open ElevenLogic

theorem inputs_valid (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) : Inputs (meaning t m) := by
  intro i
  unfold inputRow
  exact (choose_proof (i < 19702) (choose_proof (i < 11165) (choose_proof (i < 7664) (choose_proof (i < 5303) (choose_proof (i < 3142) (inputGroup000_valid t m ht i) (inputGroup001_valid t m ht i)) (choose_proof (i < 6730) (inputGroup002_valid t m ht i) (inputGroup003_valid t m ht i))) (choose_proof (i < 9537) (choose_proof (i < 8624) (inputGroup004_valid t m ht i) (inputGroup005_valid t m ht i)) (choose_proof (i < 10372) (inputGroup006_valid t m ht i) (inputGroup007_valid t m ht i)))) (choose_proof (i < 14804) (choose_proof (i < 12810) (choose_proof (i < 11954) (inputGroup008_valid t m ht i) (inputGroup009_valid t m ht i)) (choose_proof (i < 13748) (inputGroup010_valid t m ht i) (inputGroup011_valid t m ht i))) (choose_proof (i < 16835) (choose_proof (i < 15764) (inputGroup012_valid t m ht i) (inputGroup013_valid t m ht i)) (choose_proof (i < 17756) (inputGroup014_valid t m ht i) (choose_proof (i < 18697) (inputGroup015_valid t m ht i) (inputGroup016_valid t m ht i)))))) (choose_proof (i < 29104) (choose_proof (i < 23483) (choose_proof (i < 21659) (choose_proof (i < 20748) (inputGroup017_valid t m ht i) (inputGroup018_valid t m ht i)) (choose_proof (i < 22548) (inputGroup019_valid t m ht i) (inputGroup020_valid t m ht i))) (choose_proof (i < 25377) (choose_proof (i < 24371) (inputGroup021_valid t m ht i) (inputGroup022_valid t m ht i)) (choose_proof (i < 26529) (inputGroup023_valid t m ht i) (choose_proof (i < 27760) (inputGroup024_valid t m ht i) (inputGroup025_valid t m ht i))))) (choose_proof (i < 35189) (choose_proof (i < 31928) (choose_proof (i < 30502) (inputGroup026_valid t m ht i) (inputGroup027_valid t m ht i)) (choose_proof (i < 33501) (inputGroup028_valid t m ht i) (inputGroup029_valid t m ht i))) (choose_proof (i < 38229) (choose_proof (i < 36832) (inputGroup030_valid t m ht i) (inputGroup031_valid t m ht i)) (choose_proof (i < 39535) (inputGroup032_valid t m ht i) (choose_proof (i < 40693) (inputGroup033_valid t m ht i) (inputGroup034_valid t m ht i)))))))

#print axioms inputs_valid
end SunPrize.SMT
