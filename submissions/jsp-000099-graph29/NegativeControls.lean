import CheckpointCertificate
namespace Erdos82Finite

-- A false smallness claim on all 29 vertices must be rejected.
example : fcheck 7 0 0 full .small = false := by decide +kernel

-- A forged state checkpoint cannot discard all possible vertices.
example : fcheck 7 0 0 full (.checkpoint 0 0 .small) = false := by decide +kernel

-- Relabeling the initial selected set is also rejected.
example : fcheck 7 0 0 full (.checkpoint 1 full .small) = false := by decide +kernel

end Erdos82Finite
