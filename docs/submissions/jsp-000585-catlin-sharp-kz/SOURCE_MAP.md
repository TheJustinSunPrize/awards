# Relationship to the tested source

The thirteen proof, build and checking files below are byte-for-byte copies of
`projects/catlin-research` at the tested commit
[019467ead20f2d6b87e672a1dfef7d5b8886febf](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/019467ead20f2d6b87e672a1dfef7d5b8886febf/projects/catlin-research).
Their Git blob identities were checked before preparing this PR.

| File | Git blob SHA-1 |
| --- | --- |
| Certificate.lean | `26f4bb85dcf3efc43c4cd7942575d84bc9b42b92` |
| GraphCore.lean | `78992e310bfd387e88575d2195ea28ba52aa904e` |
| Profile.lean | `d8ccd5e01318e8df691b58690f6b2998655fe156` |
| Subdivision.lean | `b04c1d2656e762e9faa3a2761e3ec033b73fcd38` |
| Colouring.lean | `796c6402f7ee95adedfa1474961d56a51d0ca583` |
| Catlin.lean | `f040e6601f8cf50fb683524be7ac97d2ffaf8de9` |
| Sharp.lean | `a669fd5416060fa85fb13891472256cc3d61a3cd` |
| Audit.lean | `21e6bf42e4716622f545347a0e6d9c48bf780cb6` |
| lakefile.lean | `9780864738bf032a67006a3314a99f3d34b28f7a` |
| lake-manifest.json | `aa131e019f0e2af49887796377cdf857c4bab810` |
| lean-toolchain | `12359f928f18e4a89ebd1444a0310b025931b17d` |
| scripts/verify.sh | `75258c58912c2d7c83352829dce839ac030ef833` |
| scripts/verify_nanoda.sh | `7c471f52df0f1e1baaa41b0ac0447c50c1bd62ee` |

[RECEIPT.md](RECEIPT.md) records the successful cloud run and artifact identity.
The proof was not changed after that run. This PR relocates the same standalone
project into the awards repository and supplies review documentation. The
absolute location of the project is not a proof premise.

The documents incorporate the later receipt snapshot
`f22d9c0c5989678c4a449ab2a7635f67bb173f03`. README, SUBMISSION and VERIFICATION are
updated to associate this PR with the now-existing Issue #417 and remove stale
pending-run wording. PROVENANCE is added to supply the previously missing
attribution reference. SOURCE_MAP and SHA256SUMS are PR packaging additions.

Reproduction from this directory:

    lake exe cache get
    bash scripts/verify.sh
    bash scripts/verify_nanoda.sh

The root awards-repository CI validates repository records and links; it does
not execute this Lean proof. The separate successful proof workflow remains
linked in the receipt. The contribution remains scoped to the finite Catlin
graph; this PR does not create or change any official candidate, award, payment
or problem-catalog record.
