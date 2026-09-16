/-
Licensed under Apache-2.0; see LICENSE and NOTICE.
Adapted from Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz,
Arthur742Ramos/hadamard-668-lean at 78fbae8d69b6fdb66705b662469692d60e346ef0.
Modification: certify the distinct order-716 matrix with fresh certificate data.
Matrix discovery belongs to the original Alpoge/Voinov/Reynolds-Haertle team.
-/
import Hadamard716.ListCompactCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hadamard716

theorem corePairList_0_1 : corePairCheckList 0 1 = true := by
  decide +kernel

theorem corePairList_0_0 : corePairCheckList 0 0 = true := by
  decide +kernel

theorem corePairList_0_2 : corePairCheckList 0 2 = true := by
  decide +kernel

theorem corePairList_0_3 : corePairCheckList 0 3 = true := by
  decide +kernel

theorem corePairList_1_1 : corePairCheckList 1 1 = true := by
  decide +kernel

theorem corePairList_1_2 : corePairCheckList 1 2 = true := by
  decide +kernel

theorem corePairList_1_3 : corePairCheckList 1 3 = true := by
  decide +kernel

theorem corePairList_2_2 : corePairCheckList 2 2 = true := by
  decide +kernel

theorem corePairList_2_3 : corePairCheckList 2 3 = true := by
  decide +kernel

theorem corePairList_3_3 : corePairCheckList 3 3 = true := by
  decide +kernel

theorem topCoreList_check : topCoreCheckList = true := by
  decide +kernel

theorem topTopList_check : topTopCheckList = true := by
  decide +kernel

end Hadamard716
