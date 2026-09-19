import CheckpointCertificate
namespace Graph20Proof

-- A forged small-cardinality leaf at the full root must be rejected.
example : fcheck 6 0 0 full .small = false := by decide +kernel

-- A degree contradiction cannot be attached to a vertex not selected.
example : fcheck 6 19 0 full (.bad 0) = false := by decide +kernel

-- Checkpoint labels are checked; they do not replace the actual state unchecked.
example : fcheck 6 0 0 full (.checkpoint 0 0 .small) = false := by decide +kernel

-- With an actually empty upper set, the same checkpoint and child are valid.
example : fcheck 6 0 0 0 (.checkpoint 0 0 .small) = true := by decide +kernel

end Graph20Proof
