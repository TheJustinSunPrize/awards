/- Local 20-vertex adaptation of PR #190, commit 4022d2df0f941a12f497d5045b75995e0cf8f883.
   Upstream formalization: jinkaizhang236-sketch / Justin Sun Prize contributors.
   Original mathematical construction: Paul W. Dyson and Brendan D. McKay.
   See THIRD_PARTY_NOTICES.md for exact reuse and changes. -/
import CheckpointCertificate
namespace Graph20Proof

theorem accept_drop {k d S U : Nat} {v : Fin 20} {c : FastCert}
    (hb : mincompatible d S U v = true)
    (hc : fcheck k d S (U &&& (full ^^^ (2^v.val))) c = true) :
    fcheck k d S U (.drop v c) = true := by
  simpa only [fcheck, Bool.and_eq_true] using And.intro hb hc

theorem accept_fill {k d S U : Nat} {v : Fin 20} {c : FastCert}
    (hb : (S.testBit v.val && decide (mdegree U v = d)) = true)
    (hc : fcheck k d (S ||| (adjBits v &&& U)) U c = true) :
    fcheck k d S U (.fill v c) = true := by
  simpa only [fcheck, Bool.and_eq_true] using And.intro hb hc

theorem accept_empty {k d S U : Nat} {v : Fin 20} {c : FastCert}
    (hb : (S.testBit v.val && decide (mdegree S v = d)) = true)
    (hc : fcheck k d S (U &&& (full ^^^ (adjBits v &&& (full ^^^ S)))) c = true) :
    fcheck k d S U (.empty v c) = true := by
  simpa only [fcheck, Bool.and_eq_true] using And.intro hb hc

theorem accept_split {k d S U : Nat} {v : Fin 20} {yes no : FastCert}
    (hy : fcheck k d (S ||| 2^v.val) U yes = true)
    (hn : fcheck k d S (U &&& (full ^^^ (2^v.val))) no = true) :
    fcheck k d S U (.split v yes no) = true := by
  simpa only [fcheck, Bool.and_eq_true] using And.intro hy hn

theorem accept_checkpoint {k d S U selected possible : Nat} {c : FastCert}
    (hb : (S == selected && U == possible) = true)
    (hc : fcheck k d selected possible c = true) :
    fcheck k d S U (.checkpoint selected possible c) = true := by
  simpa only [fcheck, Bool.and_eq_true] using And.intro hb hc

end Graph20Proof
