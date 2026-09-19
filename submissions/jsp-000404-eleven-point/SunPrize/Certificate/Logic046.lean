import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step91335 (p2501 p3093 p3564 p3830 p3834 p5148 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h42194 : (¬ p2501) ∨ (¬ p3093) ∨ (¬ p3564) ∨ (¬ p3834) ∨ (¬ p5148))
    : (¬ p5148) ∨ p3830 ∨ (¬ p3564) ∨ (¬ p2501) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5148 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42194 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step91337 (p2761 p3093 p3707 p3830 p3834 p4321 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73474 : p3834 ∨ p3830)
    (h62800 : (¬ p2761) ∨ (¬ p3093) ∨ (¬ p3834) ∨ (¬ p4321))
    : p3707 ∨ p3830 ∨ (¬ p2761) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62800 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91338 (p3093 p3276 p3707 p3830 p3834 p4321 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73474 : p3834 ∨ p3830)
    (h46885 : (¬ p3093) ∨ (¬ p3276) ∨ (¬ p3834) ∨ (¬ p4321))
    : p3707 ∨ p3830 ∨ (¬ p3093) ∨ (¬ p3276) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46885 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91340 (p3093 p3309 p3323 p3830 p3834 p5148 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h52094 : (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3323) ∨ (¬ p3834) ∨ (¬ p5148))
    : p3830 ∨ (¬ p3323) ∨ (¬ p3093) ∨ (¬ p5148) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5148 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h52094 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91341 (p3093 p3483 p3830 p3834 p4867 p5148 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h41988 : (¬ p3093) ∨ (¬ p3483) ∨ (¬ p3834) ∨ (¬ p4867) ∨ (¬ p5148))
    : p3830 ∨ (¬ p3483) ∨ (¬ p5148) ∨ (¬ p4867) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5148 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4867 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41988 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91343 (p3449 p3830 p3834 p4351 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h30255 : (¬ p3449) ∨ (¬ p3834) ∨ (¬ p4351))
    : p3830 ∨ (¬ p4351) ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p4351 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h30255 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step91347 (p2241 p3830 p3833 p3834 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h5657 : (¬ p2241) ∨ (¬ p3833) ∨ (¬ p3834))
    : p3830 ∨ (¬ p3833) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3833 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h5657 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step91349 (p3438 p3449 p3830 p3834 p4181 p5122 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h42510 : (¬ p3438) ∨ (¬ p3449) ∨ (¬ p3834) ∨ (¬ p4181) ∨ (¬ p5122))
    : (¬ p4181) ∨ p3830 ∨ (¬ p5122) ∨ (¬ p3438) ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42510 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91350 (p2459 p3438 p3449 p3830 p3834 p4832 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h53459 : (¬ p2459) ∨ (¬ p3438) ∨ (¬ p3449) ∨ (¬ p3834) ∨ (¬ p4832))
    : p3830 ∨ (¬ p3438) ∨ (¬ p3449) ∨ (¬ p4832) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4832 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53459 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91351 (p2363 p3438 p3449 p3830 p3834 p4995 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h42145 : (¬ p2363) ∨ (¬ p3438) ∨ (¬ p3449) ∨ (¬ p3834) ∨ (¬ p4995))
    : p3830 ∨ (¬ p3438) ∨ (¬ p4995) ∨ (¬ p2363) ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42145 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91352 (p3146 p3438 p3449 p3830 p3834 p4494 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h42638 : (¬ p3146) ∨ (¬ p3438) ∨ (¬ p3449) ∨ (¬ p3834) ∨ (¬ p4494))
    : p3830 ∨ (¬ p3438) ∨ (¬ p3146) ∨ (¬ p3449) ∨ (¬ p4494) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4494 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42638 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91355 (p3227 p3343 p3379 p3830 p3834 p4811 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h42260 : (¬ p3227) ∨ (¬ p3343) ∨ (¬ p3379) ∨ (¬ p3834) ∨ (¬ p4811))
    : p3830 ∨ (¬ p3343) ∨ (¬ p4811) ∨ (¬ p3379) ∨ (¬ p3227) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3227 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42260 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91358 (p2753 p2881 p3093 p3362 p3389 p3707 p3830 p3834 p3868 p4321 p4870 p5660 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73474 : p3834 ∨ p3830)
    (h47880 : (¬ p2753) ∨ (¬ p2881) ∨ (¬ p3093) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3834) ∨ (¬ p3868) ∨ (¬ p4321) ∨ (¬ p4870) ∨ (¬ p5660))
    : (¬ p5660) ∨ p3707 ∨ (¬ p3868) ∨ (¬ p2881) ∨ (¬ p4870) ∨ (¬ p3362) ∨ (¬ p2753) ∨ p3830 ∨ (¬ p3389) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5660 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h47880 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step91359 (p2246 p2608 p2744 p2946 p3156 p3707 p3830 p3834 p3969 p4321 p5119 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73474 : p3834 ∨ p3830)
    (h61451 : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3834) ∨ (¬ p3969) ∨ (¬ p4321) ∨ (¬ p5119))
    : (¬ p3969) ∨ p3707 ∨ p3830 ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p2946) ∨ (¬ p5119) ∨ (¬ p2608) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61451 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step91364 (p2246 p2437 p2608 p2651 p2744 p3707 p3830 p3834 p3868 p4321 p4826 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73474 : p3834 ∨ p3830)
    (h56684 : (¬ p2246) ∨ (¬ p2437) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3834) ∨ (¬ p3868) ∨ (¬ p4321) ∨ (¬ p4826))
    : (¬ p3868) ∨ (¬ p4826) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2246) ∨ p3707 ∨ (¬ p2608) ∨ (¬ p2744) ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3868 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h56684 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step91371 (p2246 p2608 p2744 p2901 p2946 p3707 p3830 p3834 p4129 p4321 p4826 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73474 : p3834 ∨ p3830)
    (h62151 : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3834) ∨ (¬ p4129) ∨ (¬ p4321) ∨ (¬ p4826))
    : (¬ p4129) ∨ (¬ p2608) ∨ (¬ p4826) ∨ (¬ p2246) ∨ (¬ p2744) ∨ p3707 ∨ (¬ p2901) ∨ (¬ p2946) ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4129 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h62151 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step91376 (p2427 p2982 p3379 p3830 p3834 p4235 p4388 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h73536 : p4235 ∨ p2427)
    (h47513 : (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3834) ∨ (¬ p4235) ∨ (¬ p4388))
    : p3830 ∨ (¬ p4388) ∨ (¬ p3379) ∨ p2427 ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p4388 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47513 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step91378 (p2122 p2241 p2750 p2753 p2774 p3707 p3791 p3830 p3834 p4321 p4826 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73474 : p3834 ∨ p3830)
    (h51528 : (¬ p2122) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3791) ∨ (¬ p3834) ∨ (¬ p4321) ∨ (¬ p4826))
    : p3707 ∨ (¬ p4826) ∨ (¬ p2774) ∨ (¬ p2750) ∨ (¬ p2753) ∨ p3830 ∨ (¬ p2241) ∨ (¬ p3791) ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51528 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step91382 (p2553 p2573 p2608 p3519 p3791 p3830 p3834 p3847 p4376 p4826 p5284 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h52729 : (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3791) ∨ (¬ p3834) ∨ (¬ p3847) ∨ (¬ p4376) ∨ (¬ p4826) ∨ (¬ p5284))
    : p3830 ∨ (¬ p3847) ∨ (¬ p4376) ∨ (¬ p4826) ∨ (¬ p5284) ∨ (¬ p2573) ∨ (¬ p3519) ∨ (¬ p3791) ∨ (¬ p2608) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3847 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h52729 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step91385 (p2122 p2753 p2774 p3227 p3276 p3379 p3791 p3830 p3834 p4425 p4826 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73474 : p3834 ∨ p3830)
    (h71924 : (¬ p3834) ∨ (¬ p3379) ∨ (¬ p3791) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3227) ∨ (¬ p4826) ∨ (¬ p2122) ∨ (¬ p4425))
    : p3276 ∨ (¬ p3791) ∨ (¬ p4826) ∨ (¬ p2122) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p2774) ∨ p3830 ∨ (¬ p3227) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3830) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3227 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71924 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step91388 (p3227 p3323 p3333 p3422 p3584 p4037 p4973 p5152 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73426 : p3584 ∨ p3422)
    (h42346 : (¬ p3227) ∨ (¬ p3333) ∨ (¬ p3584) ∨ (¬ p4037) ∨ (¬ p4973) ∨ (¬ p5152))
    : (¬ p5152) ∨ (¬ p3333) ∨ (¬ p4973) ∨ p3323 ∨ (¬ p3227) ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5152 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3227 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42346 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step91390 (p3227 p3333 p3379 p3830 p3834 p5214 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h42441 : (¬ p3227) ∨ (¬ p3333) ∨ (¬ p3379) ∨ (¬ p3834) ∨ (¬ p5214))
    : p3830 ∨ (¬ p3333) ∨ (¬ p3227) ∨ (¬ p3379) ∨ (¬ p5214) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3227 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42441 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91392 (p2254 p2331 p2363 p2668 p2963 p3233 p3276 p3324 p3379 p3707 p4332 p4347 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73386 : p3324 ∨ p2668)
    (h73560 : p4347 ∨ p2363)
    (h73338 : p2963 ∨ p2331)
    (h50817 : (¬ p2254) ∨ (¬ p2963) ∨ (¬ p3233) ∨ (¬ p3324) ∨ (¬ p3379) ∨ (¬ p3707) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p4425))
    : (¬ p3707) ∨ p3276 ∨ (¬ p2254) ∨ (¬ p3379) ∨ p2668 ∨ (¬ p3233) ∨ p2363 ∨ (¬ p4332) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h50817 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step91393 (p2230 p2406 p3233 p3238 p3276 p3707 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73374 : p3238 ∨ p2406)
    (h42894 : (¬ p2230) ∨ (¬ p3233) ∨ (¬ p3238) ∨ (¬ p3707) ∨ (¬ p4425))
    : p3276 ∨ (¬ p3707) ∨ (¬ p2230) ∨ p2406 ∨ (¬ p3233) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42894 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91402 (p2440 p3237 p3343 p3359 : Prop)
    (h73387 : (¬ p3343) ∨ (¬ p3359))
    (h33427 : (¬ p2440) ∨ (¬ p3237) ∨ p3359)
    : (¬ p3343) ∨ (¬ p3237) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3359) := (Or.elim h73387 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    (Or.elim h33427 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step91403 (p2427 p3237 p3276 p3680 p4334 p4425 p4558 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h51514 : (¬ p2427) ∨ (¬ p3237) ∨ (¬ p3680) ∨ (¬ p4334) ∨ (¬ p4425) ∨ (¬ p4558))
    : p3276 ∨ (¬ p3680) ∨ (¬ p3237) ∨ (¬ p4334) ∨ (¬ p2427) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4334 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51514 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step91405 (p2901 p3237 p3276 p3680 p4192 p4425 p4705 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h41827 : (¬ p2901) ∨ (¬ p3237) ∨ (¬ p3680) ∨ (¬ p4192) ∨ (¬ p4425) ∨ (¬ p4705))
    : p3276 ∨ (¬ p3680) ∨ (¬ p3237) ∨ (¬ p4192) ∨ (¬ p2901) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41827 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step91407 (p2563 p3237 p3276 p3680 p4425 p5043 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h51068 : (¬ p2563) ∨ (¬ p3237) ∨ (¬ p3680) ∨ (¬ p4425) ∨ (¬ p5043))
    : (¬ p3237) ∨ p3276 ∨ (¬ p5043) ∨ (¬ p3680) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3237 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51068 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91409 (p2563 p2630 p2651 p2657 p3237 p3286 p5175 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h52823 : (¬ p2563) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3237) ∨ (¬ p3286) ∨ (¬ p5175))
    : (¬ p3237) ∨ (¬ p3286) ∨ (¬ p5175) ∨ (¬ p2630) ∨ (¬ p2563) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3237 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5175 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h52823 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step91413 (p2440 p2542 p2891 p3051 p3486 p4109 p4202 p4811 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73270 : p2542 ∨ p2440)
    (h48215 : (¬ p2542) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p4811))
    : (¬ p3051) ∨ p2891 ∨ (¬ p4811) ∨ (¬ p4202) ∨ p2440 ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48215 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step91414 (p2493 p2891 p3051 p3486 p4109 p4202 p4717 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h41985 : (¬ p2493) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p4717))
    : (¬ p3051) ∨ p2891 ∨ (¬ p4717) ∨ (¬ p2493) ∨ (¬ p4109) ∨ (¬ p4202) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41985 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step91415 (p2241 p2247 p2744 p2891 p3051 p3486 p4172 p4202 p4257 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73398 : p3486 ∨ p2891)
    (h52469 : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4172) ∨ (¬ p4202) ∨ (¬ p4257))
    : p2241 ∨ (¬ p2744) ∨ (¬ p4172) ∨ p2891 ∨ (¬ p4202) ∨ (¬ p3051) ∨ (¬ p4257) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52469 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step91416 (p2307 p2578 p3016 p3309 p3549 p4202 p4512 p4811 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h41892 : (¬ p2307) ∨ (¬ p2578) ∨ (¬ p3016) ∨ (¬ p3549) ∨ (¬ p4202) ∨ (¬ p4512) ∨ (¬ p4811))
    : (¬ p2307) ∨ (¬ p2578) ∨ (¬ p4202) ∨ (¬ p4811) ∨ (¬ p3016) ∨ p3309 ∨ (¬ p4512) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41892 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step91421 (p2850 p2891 p3051 p3486 p4109 p4202 p5214 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h41117 : (¬ p2850) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p5214))
    : (¬ p3051) ∨ p2891 ∨ (¬ p4109) ∨ (¬ p2850) ∨ (¬ p5214) ∨ (¬ p4202) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41117 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step91423 (p3389 p3575 p6040 : Prop)
    (h74377 : p3389 ∨ (¬ p6040))
    (h13237 : p3575 ∨ p6040)
    : p3575 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3575) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6040) := (Or.elim h74377 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13237 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step91427 (p2417 p2437 p2665 p3516 p3742 p4278 p5201 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73452 : p3742 ∨ p2437)
    (h50096 : (¬ p2665) ∨ (¬ p3516) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p5201))
    : p2417 ∨ (¬ p3516) ∨ (¬ p5201) ∨ (¬ p2665) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50096 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91429 (p2417 p2441 p2573 p2579 p3516 p4278 p4715 p5201 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73274 : p2579 ∨ p2573)
    (h61206 : (¬ p2441) ∨ (¬ p2579) ∨ (¬ p3516) ∨ (¬ p4278) ∨ (¬ p4715) ∨ (¬ p5201))
    : p2417 ∨ (¬ p3516) ∨ (¬ p2441) ∨ (¬ p5201) ∨ p2573 ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h61206 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step91433 (p2341 p2573 p2579 p2911 p3016 p3644 p5201 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73434 : p3644 ∨ p2911)
    (h52740 : (¬ p2341) ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3644) ∨ (¬ p5201))
    : (¬ p2341) ∨ p2573 ∨ p2911 ∨ (¬ p3016) ∨ (¬ p5201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52740 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91434 (p2230 p2341 p2589 p2911 p3644 p4646 p5201 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73284 : p2589 ∨ p2230)
    (h41685 : (¬ p2341) ∨ (¬ p2589) ∨ (¬ p3644) ∨ (¬ p4646) ∨ (¬ p5201))
    : (¬ p2341) ∨ p2911 ∨ (¬ p5201) ∨ (¬ p4646) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41685 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91440 (p2341 p2437 p2665 p2911 p3644 p3742 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73434 : p3644 ∨ p2911)
    (h69023 : (¬ p2341) ∨ (¬ p3644) ∨ (¬ p2665) ∨ (¬ p3742))
    : (¬ p2341) ∨ p2437 ∨ p2911 ∨ (¬ p2665) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69023 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91441 (p2230 p2341 p2437 p2589 p2911 p3644 p3742 p5201 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73434 : p3644 ∨ p2911)
    (h73284 : p2589 ∨ p2230)
    (h59253 : (¬ p2341) ∨ (¬ p2589) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p5201))
    : (¬ p2341) ∨ p2437 ∨ (¬ p5201) ∨ p2911 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59253 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91444 (p2341 p2911 p2922 p2928 p3644 p5194 p5201 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73434 : p3644 ∨ p2911)
    (h49249 : (¬ p2341) ∨ (¬ p2928) ∨ (¬ p3644) ∨ (¬ p5194) ∨ (¬ p5201))
    : (¬ p2341) ∨ p2922 ∨ (¬ p5201) ∨ p2911 ∨ (¬ p5194) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49249 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91445 (p2341 p2417 p2630 p2911 p3519 p3644 p4116 p5201 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h56749 : (¬ p2341) ∨ (¬ p2417) ∨ (¬ p2630) ∨ (¬ p3519) ∨ (¬ p3644) ∨ (¬ p4116) ∨ (¬ p5201))
    : (¬ p2341) ∨ (¬ p2417) ∨ (¬ p2630) ∨ (¬ p4116) ∨ (¬ p5201) ∨ p2911 ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56749 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step91449 (p2352 p2383 p2437 p2584 p2590 p2656 p3742 p3956 p4644 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73500 : p3956 ∨ p2352)
    (h53328 : (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2590) ∨ (¬ p2656) ∨ (¬ p3742) ∨ (¬ p3956) ∨ (¬ p4644))
    : p2437 ∨ (¬ p2383) ∨ (¬ p2656) ∨ (¬ p4644) ∨ (¬ p2590) ∨ p2352 ∨ (¬ p2584) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h53328 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step91450 (p2156 p2563 p3389 p3540 p4110 p4399 p4644 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73402 : p3540 ∨ p3389)
    (h51233 : (¬ p2156) ∨ (¬ p3540) ∨ (¬ p4110) ∨ (¬ p4399) ∨ (¬ p4644))
    : (¬ p2156) ∨ (¬ p4399) ∨ (¬ p4644) ∨ p2563 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51233 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91466 (p2651 p2657 p2850 p2946 p3412 p3684 p4210 p4750 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73442 : p3684 ∨ p2850)
    (h55175 : (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3684) ∨ (¬ p4210) ∨ (¬ p4750))
    : (¬ p4210) ∨ (¬ p3412) ∨ p2651 ∨ p2850 ∨ (¬ p2946) ∨ (¬ p4750) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55175 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step91502 (p3093 p3193 p3379 p3452 p4210 p4512 p4949 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h42149 : (¬ p3093) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4210) ∨ (¬ p4512) ∨ (¬ p4949))
    : (¬ p3193) ∨ (¬ p4210) ∨ (¬ p4512) ∨ p3379 ∨ (¬ p3093) ∨ (¬ p4949) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42149 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step91507 (p2122 p2563 p3051 p3556 p3645 p4210 p4275 p4401 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h60036 : (¬ p2122) ∨ (¬ p2563) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4210) ∨ (¬ p4275) ∨ (¬ p4401))
    : (¬ p4210) ∨ (¬ p2122) ∨ (¬ p3645) ∨ (¬ p4401) ∨ p3051 ∨ (¬ p4275) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60036 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step91509 (p2563 p2972 p3461 p3670 p4210 p4363 p5030 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73568 : p4363 ∨ p2972)
    (h63848 : (¬ p2563) ∨ (¬ p3461) ∨ (¬ p4210) ∨ (¬ p4363) ∨ (¬ p5030) ∨ (¬ p5387))
    : p3670 ∨ (¬ p5030) ∨ (¬ p2563) ∨ (¬ p3461) ∨ p2972 ∨ (¬ p4210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p5030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4363 := (Or.elim h73568 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63848 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step91518 (p3379 p3519 p6037 : Prop)
    (h74373 : p3379 ∨ (¬ p6037))
    (h13218 : p3519 ∨ p6037)
    : p3519 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3519) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6037) := (Or.elim h74373 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13218 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step91519 (p3379 p5191 p6037 : Prop)
    (h74373 : p3379 ∨ (¬ p6037))
    (h13220 : p5191 ∨ p6037)
    : p5191 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5191) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6037) := (Or.elim h74373 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13220 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step91521 (p3379 p4108 p6037 : Prop)
    (h74373 : p3379 ∨ (¬ p6037))
    (h13222 : p4108 ∨ p6037)
    : p4108 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4108) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6037) := (Or.elim h74373 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13222 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step91523 (p2253 p2651 p2727 p3093 p3591 p4111 p4756 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73432 : p3591 ∨ p3093)
    (h51673 : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p3591) ∨ (¬ p4111) ∨ (¬ p4756))
    : p2727 ∨ (¬ p2253) ∨ p3093 ∨ (¬ p4756) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4756 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51673 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91524 (p2241 p2383 p2387 p3063 p4756 p5015 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h55404 : (¬ p2241) ∨ (¬ p2387) ∨ (¬ p3063) ∨ (¬ p4756) ∨ (¬ p5015))
    : (¬ p3063) ∨ (¬ p5015) ∨ (¬ p4756) ∨ p2383 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4756 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55404 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step91525 (p2230 p2406 p3093 p3238 p3402 p3591 p4079 p4756 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73374 : p3238 ∨ p2406)
    (h41818 : (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p3591) ∨ (¬ p4079) ∨ (¬ p4756))
    : p3093 ∨ (¬ p3402) ∨ (¬ p4079) ∨ (¬ p2230) ∨ (¬ p4756) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4756 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41818 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step91526 (p2341 p2608 p3527 p3551 p4377 p4431 p5206 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h48752 : (¬ p2608) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4377) ∨ (¬ p4431) ∨ (¬ p5206))
    : (¬ p3527) ∨ p2341 ∨ (¬ p5206) ∨ (¬ p4431) ∨ (¬ p2608) ∨ (¬ p4377) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48752 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step91527 (p2341 p2608 p3527 p3551 p4793 p5206 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h50082 : (¬ p2608) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4793) ∨ (¬ p5206))
    : (¬ p3527) ∨ p2341 ∨ (¬ p4793) ∨ (¬ p5206) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4793 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50082 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91532 (p2210 p3038 p3516 p3631 p3821 p4959 p5206 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h52559 : (¬ p2210) ∨ (¬ p3038) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4959) ∨ (¬ p5206))
    : (¬ p3631) ∨ (¬ p5206) ∨ p3516 ∨ (¬ p3038) ∨ (¬ p4959) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5206 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52559 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step91539 (p2901 p4075 p4320 p4338 p4452 p4960 p5660 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h42552 : (¬ p4075) ∨ (¬ p4320) ∨ (¬ p4338) ∨ (¬ p4452) ∨ (¬ p4960) ∨ (¬ p5660))
    : (¬ p5660) ∨ (¬ p4075) ∨ (¬ p4338) ∨ p2901 ∨ (¬ p4960) ∨ (¬ p4452) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5660 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42552 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step91541 (p2891 p3051 p3125 p3319 p3486 p3744 p4172 p4338 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73454 : p3744 ∨ p3125)
    (h55916 : (¬ p3051) ∨ (¬ p3319) ∨ (¬ p3486) ∨ (¬ p3744) ∨ (¬ p4172) ∨ (¬ p4338))
    : (¬ p3319) ∨ (¬ p4338) ∨ p2891 ∨ (¬ p4172) ∨ (¬ p3051) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55916 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step91542 (p2187 p2891 p3063 p3486 p3989 p4338 p4555 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73502 : p3989 ∨ p2187)
    (h48930 : (¬ p3063) ∨ (¬ p3486) ∨ (¬ p3989) ∨ (¬ p4338) ∨ (¬ p4555))
    : (¬ p3063) ∨ p2891 ∨ p2187 ∨ (¬ p4555) ∨ (¬ p4338) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48930 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91548 (p2274 p3097 p3957 p4756 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h58471 : (¬ p3097) ∨ (¬ p3957) ∨ p4756)
    : p4756 ∨ p2274 ∨ (¬ p3957) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4756) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h58471 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u0 r1)))))))

theorem step91549 (p2156 p2427 p2891 p3957 p4235 p4512 p4539 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h50947 : (¬ p2156) ∨ (¬ p2891) ∨ (¬ p3957) ∨ (¬ p4235) ∨ (¬ p4512) ∨ (¬ p4539))
    : (¬ p3957) ∨ (¬ p4512) ∨ (¬ p4539) ∨ p2427 ∨ (¬ p2156) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50947 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step91550 (p2274 p3093 p3097 p3591 p3830 p3957 p4624 p5152 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73352 : p3097 ∨ p2274)
    (h51378 : (¬ p3097) ∨ (¬ p3591) ∨ (¬ p3830) ∨ (¬ p3957) ∨ (¬ p4624) ∨ (¬ p5152))
    : (¬ p3830) ∨ p3093 ∨ (¬ p3957) ∨ (¬ p4624) ∨ (¬ p5152) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5152 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51378 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step91553 (p2156 p3093 p3591 p3957 p4172 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h6236 : (¬ p2156) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4172))
    : p3093 ∨ (¬ p3957) ∨ (¬ p2156) ∨ (¬ p4172) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6236 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step91556 (p2156 p2220 p3309 p3957 p4120 p4506 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h71929 : (¬ p3957) ∨ (¬ p4120) ∨ (¬ p4506) ∨ (¬ p3309) ∨ (¬ p2156))
    : p2220 ∨ (¬ p3309) ∨ (¬ p4506) ∨ (¬ p3957) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h71929 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91559 (p2210 p3093 p3156 p3591 p3957 p4282 p4509 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h58560 : (¬ p2210) ∨ (¬ p3156) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4282) ∨ (¬ p4509))
    : p3093 ∨ (¬ p4282) ∨ (¬ p3156) ∨ (¬ p4509) ∨ (¬ p3957) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h58560 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step91560 (p2132 p2274 p2383 p2387 p2778 p3063 p3097 p3957 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73352 : p3097 ∨ p2274)
    (h52541 : (¬ p2132) ∨ (¬ p2387) ∨ (¬ p2778) ∨ (¬ p3063) ∨ (¬ p3097) ∨ (¬ p3957))
    : (¬ p3063) ∨ (¬ p3957) ∨ p2383 ∨ (¬ p2132) ∨ p2274 ∨ (¬ p2778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52541 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step91568 (p2187 p2210 p2246 p2264 p2363 p2651 p2911 p3093 p3580 p3591 p3644 p3957 p3989 p4347 p4959 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73560 : p4347 ∨ p2363)
    (h73502 : p3989 ∨ p2187)
    (h73432 : p3591 ∨ p3093)
    (h45595 : (¬ p2210) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2651) ∨ (¬ p3580) ∨ (¬ p3591) ∨ (¬ p3644) ∨ (¬ p3957) ∨ (¬ p3989) ∨ (¬ p4347) ∨ (¬ p4959))
    : p2911 ∨ (¬ p2264) ∨ p2363 ∨ (¬ p4959) ∨ p2187 ∨ (¬ p2210) ∨ (¬ p3580) ∨ p3093 ∨ (¬ p2651) ∨ (¬ p2246) ∨ (¬ p3957) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u13 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u14 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h45595 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u14))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (False.elim (r9 u3)))))))))))))))))))))))

theorem step91570 (p2307 p2313 p3399 p3547 p5015 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h35814 : (¬ p2313) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p5015))
    : (¬ p3547) ∨ (¬ p5015) ∨ p2307 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3547 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h35814 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step91571 (p2383 p2387 p2608 p3063 p4866 p5015 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h48555 : (¬ p2387) ∨ (¬ p2608) ∨ (¬ p3063) ∨ (¬ p4866) ∨ (¬ p5015))
    : (¬ p3063) ∨ (¬ p5015) ∨ (¬ p4866) ∨ p2383 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48555 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step91574 (p2210 p3319 p3654 p3946 p4869 p4877 p5015 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h50625 : (¬ p2210) ∨ (¬ p3319) ∨ (¬ p3946) ∨ (¬ p4869) ∨ (¬ p4877) ∨ (¬ p5015))
    : (¬ p3319) ∨ p3654 ∨ (¬ p2210) ∨ (¬ p4877) ∨ (¬ p4869) ∨ (¬ p5015) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50625 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step91576 (p2307 p2313 p2501 p2553 p3093 p5015 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h41417 : (¬ p2313) ∨ (¬ p2501) ∨ (¬ p2553) ∨ (¬ p3093) ∨ (¬ p5015))
    : (¬ p5015) ∨ p2307 ∨ (¬ p2501) ∨ (¬ p2553) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5015 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41417 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step91577 (p2363 p2774 p2819 p2901 p2946 p2952 p3246 p3690 p4320 p4669 p4789 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73552 : p4320 ∨ p2901)
    (h73330 : p2952 ∨ p2946)
    (h65255 : (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2952) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4669) ∨ (¬ p4789))
    : p3246 ∨ p2901 ∨ (¬ p4789) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p4669) ∨ (¬ p2363) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h65255 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step91578 (p2143 p2891 p3051 p3367 p3371 p3556 p3585 p4884 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73428 : p3585 ∨ p3367)
    (h50170 : (¬ p2143) ∨ (¬ p2891) ∨ (¬ p3371) ∨ (¬ p3556) ∨ (¬ p3585) ∨ (¬ p4884))
    : (¬ p3371) ∨ p3051 ∨ (¬ p4884) ∨ (¬ p2143) ∨ p3367 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3371 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4884 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50170 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step91583 (p2156 p2192 p2427 p3367 p3371 p3585 p3646 p4031 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73428 : p3585 ∨ p3367)
    (h55994 : (¬ p2192) ∨ (¬ p2427) ∨ (¬ p3371) ∨ (¬ p3585) ∨ (¬ p3646) ∨ (¬ p4031))
    : (¬ p2192) ∨ p2156 ∨ (¬ p3371) ∨ (¬ p2427) ∨ (¬ p4031) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55994 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step91585 (p2132 p2138 p2166 p2619 p3371 p3694 p4734 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h72735 : p4734)
    (h73450 : p3694 ∨ p2619)
    (h54512 : (¬ p2138) ∨ (¬ p2166) ∨ (¬ p3371) ∨ (¬ p3694) ∨ (¬ p4734))
    : (¬ p3371) ∨ p2132 ∨ (¬ p2166) ∨ p2619 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3371 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4734 := h72735;
    let u6 : p3694 := (Or.elim h73450 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54512 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91588 (p2132 p2138 p2192 p2860 p3371 p3758 p4734 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h72735 : p4734)
    (h73456 : p3758 ∨ p2860)
    (h63755 : (¬ p2138) ∨ (¬ p2192) ∨ (¬ p3371) ∨ (¬ p3758) ∨ (¬ p4734))
    : (¬ p3371) ∨ p2132 ∨ (¬ p2192) ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3371 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4734 := h72735;
    let u6 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63755 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91591 (p2132 p2138 p2870 p2891 p3371 p4244 p4734 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h72735 : p4734)
    (h50628 : (¬ p2138) ∨ (¬ p2891) ∨ (¬ p3371) ∨ (¬ p4244) ∨ (¬ p4734))
    : (¬ p3371) ∨ p2132 ∨ p2870 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3371 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4734 := h72735;
    (Or.elim h50628 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step91593 (p2156 p2252 p2528 p2534 p2651 p2657 p2750 p2860 p3083 p3105 p3370 p3371 p3758 p4256 p4450 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73456 : p3758 ∨ p2860)
    (h73288 : p2657 ∨ p2651)
    (h73542 : p4256 ∨ p3083)
    (h63176 : (¬ p2156) ∨ (¬ p2252) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3105) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3758) ∨ (¬ p4256) ∨ (¬ p4450))
    : p2528 ∨ p2860 ∨ p2651 ∨ p3083 ∨ (¬ p3370) ∨ (¬ p2750) ∨ (¬ p3371) ∨ (¬ p4450) ∨ (¬ p2252) ∨ (¬ p2156) ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u14 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63176 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u14))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step91594 (p2737 p2743 p2870 p2891 p3371 p4244 p5052 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73298 : p2743 ∨ p2737)
    (h58154 : (¬ p2743) ∨ (¬ p2891) ∨ (¬ p3371) ∨ (¬ p4244) ∨ (¬ p5052))
    : p2870 ∨ p2737 ∨ (¬ p5052) ∨ (¬ p3371) ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h58154 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91595 (p2192 p2737 p2743 p2860 p3371 p3758 p5052 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73456 : p3758 ∨ p2860)
    (h62035 : (¬ p2192) ∨ (¬ p2743) ∨ (¬ p3371) ∨ (¬ p3758) ∨ (¬ p5052))
    : p2737 ∨ (¬ p3371) ∨ p2860 ∨ (¬ p5052) ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62035 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91598 (p2241 p2750 p2891 p3051 p3369 p3371 p3556 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h42613 : (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2891) ∨ (¬ p3369) ∨ (¬ p3371) ∨ (¬ p3556))
    : (¬ p3369) ∨ (¬ p2241) ∨ (¬ p3371) ∨ (¬ p2750) ∨ p3051 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3369 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42613 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step91599 (p2891 p3051 p3369 p3371 p3379 p3556 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h71930 : (¬ p3379) ∨ (¬ p3556) ∨ (¬ p3369) ∨ (¬ p2891) ∨ (¬ p3371))
    : p3051 ∨ (¬ p3379) ∨ (¬ p3369) ∨ (¬ p2891) ∨ (¬ p3371) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h71930 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91600 (p2192 p2241 p2274 p2396 p2750 p3073 p3371 p3449 p3860 p3950 p4261 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73482 : p3860 ∨ p3449)
    (h48073 : (¬ p2192) ∨ (¬ p2241) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p3371) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261))
    : (¬ p3950) ∨ p3073 ∨ (¬ p2750) ∨ (¬ p3371) ∨ (¬ p2274) ∨ (¬ p2396) ∨ p3449 ∨ (¬ p2192) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3950 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h48073 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step91601 (p2192 p2860 p3105 p3266 p3276 p3346 p3347 p3371 p3758 p4425 p4450 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73456 : p3758 ∨ p2860)
    (h71931 : (¬ p4425) ∨ (¬ p3266) ∨ (¬ p2192) ∨ (¬ p3347) ∨ (¬ p3758) ∨ (¬ p4450) ∨ (¬ p3371) ∨ (¬ p3346) ∨ (¬ p3105))
    : p3276 ∨ (¬ p3266) ∨ (¬ p2192) ∨ (¬ p3347) ∨ p2860 ∨ (¬ p3105) ∨ (¬ p3371) ∨ (¬ p4450) ∨ (¬ p3346) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71931 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step91602 (p2156 p2264 p2807 p3125 p3366 p3370 p3371 p3414 p3461 p3553 p4789 p5123 p5558 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73392 : p3414 ∨ p2807)
    (h64517 : (¬ p2156) ∨ (¬ p3125) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3414) ∨ (¬ p3461) ∨ (¬ p3553) ∨ (¬ p4789) ∨ (¬ p5123) ∨ (¬ p5558))
    : (¬ p5558) ∨ (¬ p3370) ∨ (¬ p4789) ∨ (¬ p3371) ∨ p2264 ∨ (¬ p3125) ∨ (¬ p5123) ∨ (¬ p3461) ∨ (¬ p3366) ∨ p2807 ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h64517 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step91609 (p2341 p3961 p5830 : Prop)
    (h74117 : p2341 ∨ (¬ p5830))
    (h11974 : p3961 ∨ p5830)
    : p3961 ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3961) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5830) := (Or.elim h74117 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11974 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step91611 (p2891 p3073 p3486 p3609 p4078 p4185 p4340 p4496 p4555 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73558 : p4340 ∨ p3609)
    (h42118 : (¬ p3073) ∨ (¬ p3486) ∨ (¬ p4078) ∨ (¬ p4185) ∨ (¬ p4340) ∨ (¬ p4496) ∨ (¬ p4555))
    : (¬ p4496) ∨ (¬ p4185) ∨ (¬ p4555) ∨ p2891 ∨ (¬ p3073) ∨ p3609 ∨ (¬ p4078) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4496 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42118 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step91613 (p2241 p2459 p3073 p3399 p3544 p4261 p4366 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73544 : p4261 ∨ p3073)
    (h65172 : (¬ p2241) ∨ (¬ p2459) ∨ (¬ p3544) ∨ (¬ p4261) ∨ (¬ p4366))
    : p3399 ∨ p3073 ∨ (¬ p2459) ∨ (¬ p3544) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3544 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h65172 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91623 (p2363 p2911 p2930 p3073 p3544 p4138 p4261 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h61669 : (¬ p2363) ∨ (¬ p2911) ∨ (¬ p2930) ∨ (¬ p3544) ∨ (¬ p4138) ∨ (¬ p4261))
    : p3073 ∨ (¬ p3544) ∨ (¬ p4138) ∨ (¬ p2363) ∨ (¬ p2911) ∨ (¬ p2930) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3544 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2930 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h61669 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step91624 (p2459 p2717 p3073 p3544 p4261 p4794 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h59384 : (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3544) ∨ (¬ p4261) ∨ (¬ p4794))
    : (¬ p2717) ∨ p3073 ∨ (¬ p2459) ∨ (¬ p3544) ∨ (¬ p4794) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3544 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4794 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h59384 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91625 (p2255 p3031 p3073 p3166 p3256 p3544 p4261 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h60165 : (¬ p2255) ∨ (¬ p3031) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3544) ∨ (¬ p4261))
    : p3073 ∨ (¬ p3031) ∨ (¬ p2255) ∨ (¬ p3256) ∨ (¬ p3166) ∨ (¬ p3544) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3544 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h60165 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step91631 (p2608 p3449 p3860 p5316 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h20499 : (¬ p2608) ∨ (¬ p3860) ∨ (¬ p5316))
    : p3449 ∨ (¬ p5316) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p5316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20499 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step91635 (p2737 p2743 p3073 p3609 p4340 p4968 p5316 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73298 : p2743 ∨ p2737)
    (h41955 : (¬ p2743) ∨ (¬ p3073) ∨ (¬ p4340) ∨ (¬ p4968) ∨ (¬ p5316))
    : (¬ p3073) ∨ (¬ p5316) ∨ p3609 ∨ p2737 ∨ (¬ p4968) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4968 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41955 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step91636 (p3367 p3585 p3670 p3707 p4351 p4749 p5316 p5387 p5453 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73428 : p3585 ∨ p3367)
    (h56794 : (¬ p3585) ∨ (¬ p3707) ∨ (¬ p4351) ∨ (¬ p4749) ∨ (¬ p5316) ∨ (¬ p5387) ∨ (¬ p5453))
    : p3670 ∨ (¬ p3707) ∨ (¬ p5316) ∨ (¬ p5453) ∨ (¬ p4351) ∨ (¬ p4749) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4351 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h56794 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step91639 (p2088 p2241 p2750 p3073 p3857 p4416 p5316 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h42274 : (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3073) ∨ (¬ p3857) ∨ (¬ p4416) ∨ (¬ p5316))
    : (¬ p4416) ∨ (¬ p3073) ∨ (¬ p5316) ∨ p2088 ∨ (¬ p2241) ∨ (¬ p2750) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4416 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42274 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step91640 (p3073 p3367 p3585 p3609 p4340 p4364 p4749 p5316 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73428 : p3585 ∨ p3367)
    (h49024 : (¬ p3073) ∨ (¬ p3585) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p4749) ∨ (¬ p5316))
    : (¬ p3073) ∨ (¬ p4364) ∨ (¬ p4749) ∨ p3609 ∨ (¬ p5316) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49024 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step91642 (p2373 p2459 p2532 p2982 p3880 p4348 p4905 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73562 : p4348 ∨ p2459)
    (h41413 : (¬ p2532) ∨ (¬ p2982) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4905))
    : (¬ p2982) ∨ (¬ p4905) ∨ (¬ p2532) ∨ p2373 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41413 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step91649 (p2192 p2563 p2922 p2928 p3389 p3948 p4110 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73516 : p4110 ∨ p2563)
    (h45670 : (¬ p2192) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p3948) ∨ (¬ p4110))
    : (¬ p2192) ∨ (¬ p3948) ∨ p2922 ∨ (¬ p3389) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45670 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step91656 (p2307 p2313 p2641 p2651 p2667 p2745 p2811 p2972 p3680 p3948 p4116 p4154 p4260 p4831 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73238 : p2313 ∨ p2307)
    (h60387 : (¬ p2313) ∨ (¬ p2651) ∨ (¬ p2667) ∨ (¬ p2745) ∨ (¬ p2811) ∨ (¬ p2972) ∨ (¬ p3680) ∨ (¬ p3948) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p4260) ∨ (¬ p4831))
    : (¬ p2811) ∨ p2641 ∨ (¬ p3680) ∨ (¬ p4116) ∨ (¬ p2972) ∨ p2307 ∨ (¬ p2651) ∨ (¬ p2745) ∨ (¬ p2667) ∨ (¬ p4260) ∨ (¬ p4831) ∨ (¬ p3948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2811 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h60387 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step91663 (p2166 p2373 p2493 p2499 p3880 p3948 p4715 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73260 : p2499 ∨ p2493)
    (h50108 : (¬ p2166) ∨ (¬ p2499) ∨ (¬ p3880) ∨ (¬ p3948) ∨ (¬ p4715))
    : (¬ p2166) ∨ p2373 ∨ p2493 ∨ (¬ p4715) ∨ (¬ p3948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50108 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91664 (p2166 p2230 p2373 p2589 p3880 p3948 p5191 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73284 : p2589 ∨ p2230)
    (h41578 : (¬ p2166) ∨ (¬ p2589) ∨ (¬ p3880) ∨ (¬ p3948) ∨ (¬ p5191))
    : (¬ p3948) ∨ (¬ p2166) ∨ (¬ p5191) ∨ p2373 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3948 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41578 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91665 (p2192 p2230 p2563 p2589 p3948 p4110 p5191 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73284 : p2589 ∨ p2230)
    (h51766 : (¬ p2192) ∨ (¬ p2589) ∨ (¬ p3948) ∨ (¬ p4110) ∨ (¬ p5191))
    : (¬ p2192) ∨ (¬ p3948) ∨ (¬ p5191) ∨ p2563 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51766 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91666 (p2230 p2427 p2589 p2891 p3948 p4235 p5191 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73284 : p2589 ∨ p2230)
    (h41288 : (¬ p2589) ∨ (¬ p2891) ∨ (¬ p3948) ∨ (¬ p4235) ∨ (¬ p5191))
    : (¬ p2891) ∨ (¬ p3948) ∨ p2427 ∨ (¬ p5191) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41288 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91671 (p2156 p2192 p2922 p2928 p2957 p3646 p3948 p4241 p4644 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73436 : p3646 ∨ p2156)
    (h58339 : (¬ p2192) ∨ (¬ p2928) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3948) ∨ (¬ p4241) ∨ (¬ p4644))
    : (¬ p2192) ∨ (¬ p3948) ∨ (¬ p4241) ∨ p2922 ∨ (¬ p2957) ∨ (¬ p4644) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h58339 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step91674 (p2440 p2891 p3051 p3556 p3948 p4031 p4814 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h51082 : (¬ p2440) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3948) ∨ (¬ p4031) ∨ (¬ p4814))
    : (¬ p3948) ∨ (¬ p4031) ∨ (¬ p2440) ∨ (¬ p4814) ∨ p3051 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3948 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51082 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step91675 (p2177 p2299 p2881 p2891 p3379 p3948 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h43708 : (¬ p2299) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3379) ∨ (¬ p3948))
    : (¬ p2891) ∨ (¬ p3948) ∨ p2177 ∨ (¬ p3379) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43708 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step91677 (p2922 p2928 p2972 p2982 p3948 p4644 p4948 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73846 : p4948 ∨ p2982)
    (h51399 : (¬ p2928) ∨ (¬ p2972) ∨ (¬ p3948) ∨ (¬ p4644) ∨ (¬ p4948))
    : (¬ p3948) ∨ p2922 ∨ (¬ p4644) ∨ p2982 ∨ (¬ p2972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3948 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51399 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step91678 (p2427 p2493 p2499 p2891 p3948 p4235 p4715 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73260 : p2499 ∨ p2493)
    (h60760 : (¬ p2499) ∨ (¬ p2891) ∨ (¬ p3948) ∨ (¬ p4235) ∨ (¬ p4715))
    : (¬ p2891) ∨ p2427 ∨ (¬ p4715) ∨ p2493 ∨ (¬ p3948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60760 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91679 (p2493 p2499 p2972 p2982 p3948 p4715 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73260 : p2499 ∨ p2493)
    (h64451 : (¬ p2499) ∨ (¬ p2972) ∨ (¬ p3948) ∨ (¬ p4715) ∨ (¬ p4948))
    : (¬ p2972) ∨ (¬ p3948) ∨ (¬ p4715) ∨ p2982 ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h64451 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91680 (p2166 p2373 p2440 p3880 p3948 p4814 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h50094 : (¬ p2166) ∨ (¬ p2440) ∨ (¬ p3880) ∨ (¬ p3948) ∨ (¬ p4814))
    : (¬ p3948) ∨ (¬ p4814) ∨ p2373 ∨ (¬ p2166) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3948 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50094 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step91685 (p2192 p2553 p3125 p3564 p3948 p4137 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h55512 : (¬ p2192) ∨ (¬ p2553) ∨ (¬ p3125) ∨ (¬ p3948) ∨ (¬ p4137))
    : (¬ p3125) ∨ p3564 ∨ (¬ p2192) ∨ (¬ p2553) ∨ (¬ p3948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h55512 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91687 (p2166 p2220 p2922 p2928 p3948 p4031 p4120 p4644 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73522 : p4120 ∨ p2220)
    (h58270 : (¬ p2166) ∨ (¬ p2928) ∨ (¬ p3948) ∨ (¬ p4031) ∨ (¬ p4120) ∨ (¬ p4644))
    : (¬ p3948) ∨ p2922 ∨ (¬ p4031) ∨ (¬ p4644) ∨ p2220 ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3948 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58270 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step91688 (p2891 p3016 p3051 p3556 p3574 p3948 p4031 p4116 p4715 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73422 : p3574 ∨ p3016)
    (h54002 : (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3574) ∨ (¬ p3948) ∨ (¬ p4031) ∨ (¬ p4116) ∨ (¬ p4715))
    : (¬ p4031) ∨ (¬ p4116) ∨ (¬ p2891) ∨ (¬ p3948) ∨ (¬ p4715) ∨ p3051 ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4031 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u8 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h54002 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step91693 (p2230 p4109 p5812 : Prop)
    (h74093 : p2230 ∨ (¬ p5812))
    (h11870 : p4109 ∨ p5812)
    : p4109 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4109) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2230) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5812) := (Or.elim h74093 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11870 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step91697 (p2177 p3527 p3547 p3548 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h5166 : (¬ p2177) ∨ (¬ p3547) ∨ (¬ p3548))
    : p3527 ∨ (¬ p3547) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p3547 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h5166 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step91710 (p2396 p3547 p3631 p3817 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h19884 : (¬ p2396) ∨ (¬ p3547) ∨ (¬ p3817))
    : (¬ p3547) ∨ p3631 ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3547 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h19884 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step91720 (p2241 p2247 p2307 p2313 p2744 p2778 p3366 p3399 p3547 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73238 : p2313 ∨ p2307)
    (h56928 : (¬ p2247) ∨ (¬ p2313) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3547))
    : (¬ p3399) ∨ p2241 ∨ (¬ p2778) ∨ (¬ p2744) ∨ (¬ p3366) ∨ p2307 ∨ (¬ p3547) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3547 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56928 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step91721 (p2132 p2138 p2241 p2247 p2744 p2870 p2881 p3366 p3399 p3547 p3570 p3791 p4244 p5564 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73226 : p2247 ∨ p2241)
    (h73418 : p3570 ∨ p2881)
    (h73214 : p2138 ∨ p2132)
    (h52780 : (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3570) ∨ (¬ p3791) ∨ (¬ p4244) ∨ (¬ p5564))
    : (¬ p3791) ∨ (¬ p5564) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ p2870 ∨ p2241 ∨ p2881 ∨ (¬ p3547) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3547 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h52780 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step91726 (p2274 p2449 p3097 p3547 p3631 p3817 p4156 p4560 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h73352 : p3097 ∨ p2274)
    (h72955 : p4560)
    (h41248 : (¬ p2449) ∨ (¬ p3097) ∨ (¬ p3547) ∨ (¬ p3817) ∨ (¬ p4156) ∨ (¬ p4560))
    : (¬ p3547) ∨ (¬ p4156) ∨ (¬ p2449) ∨ p3631 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3547 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p4560 := h72955;
    (Or.elim h41248 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step91727 (p2319 p2341 p3527 p3547 p3548 p3654 p3946 p4620 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h73404 : p3548 ∨ p3527)
    (h41026 : (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3547) ∨ (¬ p3548) ∨ (¬ p3946) ∨ (¬ p4620))
    : (¬ p3547) ∨ (¬ p2341) ∨ (¬ p4620) ∨ (¬ p2319) ∨ p3654 ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3547 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41026 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step91735 (p2295 p2352 p3323 p3564 p3568 p4137 p4405 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73416 : p3568 ∨ p2295)
    (h53961 : (¬ p2352) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4137) ∨ (¬ p4405))
    : p3564 ∨ (¬ p3323) ∨ (¬ p4405) ∨ (¬ p2352) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53961 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91736 (p2177 p2295 p2299 p3125 p3323 p3568 p3744 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73234 : p2299 ∨ p2177)
    (h73416 : p3568 ∨ p2295)
    (h47988 : (¬ p2299) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p3744))
    : (¬ p3323) ∨ p3125 ∨ p2177 ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47988 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91738 (p2807 p3019 p3323 p3654 p3946 p3983 p4652 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h59590 : (¬ p2807) ∨ (¬ p3019) ∨ (¬ p3323) ∨ (¬ p3946) ∨ (¬ p3983) ∨ (¬ p4652))
    : (¬ p3323) ∨ (¬ p3983) ∨ p3654 ∨ (¬ p2807) ∨ (¬ p4652) ∨ (¬ p3019) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h59590 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step91742 (p2177 p2295 p2299 p3323 p3568 p3654 p3946 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h73416 : p3568 ∨ p2295)
    (h73234 : p2299 ∨ p2177)
    (h53719 : (¬ p2299) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p3946))
    : (¬ p3323) ∨ p3654 ∨ p2295 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53719 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91743 (p2668 p3322 p3323 p3324 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h4767 : (¬ p3322) ∨ (¬ p3323) ∨ (¬ p3324))
    : (¬ p3323) ∨ (¬ p3322) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h4767 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step91748 (p2295 p2573 p2579 p3323 p3564 p3568 p4137 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73416 : p3568 ∨ p2295)
    (h73274 : p2579 ∨ p2573)
    (h57586 : (¬ p2579) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4137))
    : (¬ p3323) ∨ p3564 ∨ p2295 ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57586 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91750 (p2383 p2417 p2598 p2668 p3055 p3201 p3323 p3324 p3876 p3987 p4278 p4621 p4786 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73350 : p3055 ∨ p2598)
    (h73546 : p4278 ∨ p2417)
    (h73386 : p3324 ∨ p2668)
    (h53878 : (¬ p2383) ∨ (¬ p3055) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3876) ∨ (¬ p3987) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4786))
    : (¬ p2383) ∨ p3201 ∨ (¬ p3987) ∨ (¬ p4786) ∨ p2598 ∨ p2417 ∨ (¬ p4621) ∨ p2668 ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h53878 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step91755 (p2459 p2668 p3323 p3324 p4345 p4348 p4503 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73386 : p3324 ∨ p2668)
    (h54257 : (¬ p3323) ∨ (¬ p3324) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4503))
    : (¬ p3323) ∨ (¬ p4503) ∨ p2459 ∨ (¬ p4345) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54257 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step91756 (p2295 p2459 p2493 p2499 p2927 p3323 p3389 p3527 p3564 p3568 p4137 p5194 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73416 : p3568 ∨ p2295)
    (h73260 : p2499 ∨ p2493)
    (h49437 : (¬ p2459) ∨ (¬ p2499) ∨ (¬ p2927) ∨ (¬ p3323) ∨ (¬ p3389) ∨ (¬ p3527) ∨ (¬ p3568) ∨ (¬ p4137) ∨ (¬ p5194))
    : (¬ p3323) ∨ (¬ p3527) ∨ (¬ p3389) ∨ p3564 ∨ p2295 ∨ p2493 ∨ (¬ p2927) ∨ (¬ p5194) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2927 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49437 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step91758 (p2331 p2493 p2499 p2553 p2588 p2946 p2952 p2992 p3323 p3379 p3452 p4624 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73394 : p3452 ∨ p3379)
    (h73282 : p2588 ∨ p2553)
    (h73330 : p2952 ∨ p2946)
    (h49814 : (¬ p2331) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3323) ∨ (¬ p3452) ∨ (¬ p4624))
    : p2493 ∨ p3379 ∨ (¬ p2992) ∨ (¬ p4624) ∨ p2553 ∨ (¬ p3323) ∨ p2946 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h49814 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step91759 (p2331 p3323 p3564 p3888 p4137 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h47316 : (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3888) ∨ (¬ p4137))
    : (¬ p3888) ∨ (¬ p3323) ∨ p3564 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47316 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91760 (p2311 p2341 p2667 p2911 p3323 p3551 p3921 p4624 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h49813 : (¬ p2311) ∨ (¬ p2667) ∨ (¬ p2911) ∨ (¬ p3323) ∨ (¬ p3551) ∨ (¬ p3921) ∨ (¬ p4624))
    : (¬ p2911) ∨ (¬ p2667) ∨ (¬ p3323) ∨ (¬ p3921) ∨ p2341 ∨ (¬ p2311) ∨ (¬ p4624) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49813 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step91761 (p2295 p3246 p3323 p3568 p3690 p4556 p5299 p5379 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73416 : p3568 ∨ p2295)
    (h53089 : (¬ p3323) ∨ (¬ p3568) ∨ (¬ p3690) ∨ (¬ p4556) ∨ (¬ p5299) ∨ (¬ p5379))
    : (¬ p3323) ∨ (¬ p5379) ∨ p3246 ∨ p2295 ∨ (¬ p4556) ∨ (¬ p5299) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53089 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step91764 (p2509 p2528 p2534 p2696 p2797 p3323 p3379 p3452 p4330 p4733 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73268 : p2534 ∨ p2528)
    (h51523 : (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3452) ∨ (¬ p4330) ∨ (¬ p4733))
    : (¬ p3323) ∨ p3379 ∨ (¬ p2797) ∨ (¬ p2509) ∨ (¬ p4733) ∨ p2528 ∨ (¬ p4330) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51523 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step91769 (p2509 p2528 p2534 p2641 p2761 p3323 p3379 p3452 p3461 p3950 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73394 : p3452 ∨ p3379)
    (h73268 : p2534 ∨ p2528)
    (h48936 : (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p3452) ∨ (¬ p3461) ∨ (¬ p3950) ∨ (¬ p4381))
    : (¬ p2641) ∨ p2761 ∨ p3379 ∨ p2528 ∨ (¬ p3461) ∨ (¬ p2509) ∨ (¬ p3323) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48936 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step91770 (p3125 p3323 p3744 p3745 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h5485 : (¬ p3323) ∨ (¬ p3744) ∨ (¬ p3745))
    : (¬ p3323) ∨ p3125 ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5485 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step91772 (p3323 p3564 p4137 p4389 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h20194 : (¬ p3323) ∨ (¬ p4137) ∨ (¬ p4389))
    : (¬ p3323) ∨ p3564 ∨ (¬ p4389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20194 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step91779 (p2253 p2331 p2553 p3323 p3564 p4137 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h43689 : (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2553) ∨ (¬ p3323) ∨ (¬ p4137))
    : (¬ p3323) ∨ p3564 ∨ (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43689 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91792 (p2295 p2383 p2668 p2737 p2743 p3324 p4869 p5016 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73298 : p2743 ∨ p2737)
    (h59333 : (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2743) ∨ (¬ p3324) ∨ (¬ p4869) ∨ (¬ p5016))
    : (¬ p5016) ∨ (¬ p2383) ∨ p2668 ∨ (¬ p4869) ∨ (¬ p2295) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h59333 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step91793 (p2307 p2313 p3309 p3549 p5016 : Prop)
    (h73237 : (¬ p2307) ∨ (¬ p2313))
    (h73406 : p3549 ∨ p3309)
    (h19100 : p2313 ∨ (¬ p3549) ∨ (¬ p5016))
    : (¬ p5016) ∨ (¬ p2307) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2313) := (Or.elim h73237 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h19100 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u0)))))))

theorem step91794 (p2373 p2563 p3309 p3549 p4110 p4356 p4405 p4441 p5016 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73406 : p3549 ∨ p3309)
    (h42130 : (¬ p2373) ∨ (¬ p3549) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4405) ∨ (¬ p4441) ∨ (¬ p5016))
    : (¬ p5016) ∨ (¬ p4441) ∨ (¬ p4405) ∨ p2563 ∨ (¬ p4356) ∨ (¬ p2373) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h42130 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step91806 (p2363 p2737 p2774 p2780 p3073 p3136 p3156 p4024 p4261 p4371 p4433 p4734 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h72735 : p4734)
    (h73544 : p4261 ∨ p3073)
    (h63789 : (¬ p2363) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p4024) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4433) ∨ (¬ p4734))
    : (¬ p4024) ∨ p2774 ∨ (¬ p2737) ∨ (¬ p3156) ∨ (¬ p2363) ∨ (¬ p4433) ∨ (¬ p4371) ∨ p3073 ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4024 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4734 := h72735;
    let u11 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h63789 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u10)))))))))))))))))))))

theorem step91808 (p2608 p2737 p2743 p3093 p3954 p4024 p4845 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73298 : p2743 ∨ p2737)
    (h41201 : (¬ p2743) ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p4024) ∨ (¬ p4845))
    : p2608 ∨ p2737 ∨ (¬ p4024) ∨ (¬ p3093) ∨ (¬ p4845) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41201 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91813 (p3204 p3654 p3917 p3946 p4024 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h32738 : (¬ p3204) ∨ p3917 ∨ (¬ p3946) ∨ (¬ p4024))
    : p3917 ∨ p3654 ∨ (¬ p4024) ∨ (¬ p3204) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3917) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h32738 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step91815 (p3319 p3483 p4024 p4026 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h26489 : (¬ p3483) ∨ (¬ p4024) ∨ (¬ p4026))
    : (¬ p3483) ∨ p3319 ∨ (¬ p4024) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h26489 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step91826 (p2088 p2295 p2312 p3073 p4261 p4371 p4590 p4757 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h50332 : (¬ p2088) ∨ (¬ p2295) ∨ (¬ p2312) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4590) ∨ (¬ p4757))
    : p3073 ∨ (¬ p4590) ∨ (¬ p4371) ∨ (¬ p4757) ∨ (¬ p2295) ∨ (¬ p2312) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4757 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50332 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step91828 (p2252 p2295 p2331 p2396 p2598 p2717 p2748 p2963 p3055 p3425 p3471 p3568 p4107 p4666 p4749 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73396 : p3471 ∨ p3425)
    (h73338 : p2963 ∨ p2331)
    (h73416 : p3568 ∨ p2295)
    (h73350 : p3055 ∨ p2598)
    (h51066 : (¬ p2252) ∨ (¬ p2717) ∨ (¬ p2748) ∨ (¬ p2963) ∨ (¬ p3055) ∨ (¬ p3471) ∨ (¬ p3568) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p4749))
    : (¬ p2748) ∨ p2396 ∨ p3425 ∨ (¬ p4749) ∨ (¬ p4666) ∨ p2331 ∨ p2295 ∨ (¬ p2717) ∨ (¬ p2252) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2748 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u14 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h51066 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u14))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step91829 (p2252 p2651 p2657 p3487 p4281 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h15387 : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p3487) ∨ (¬ p4281))
    : (¬ p4281) ∨ (¬ p2252) ∨ (¬ p3487) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4281 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h15387 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step91832 (p2252 p2331 p2963 p2992 p3323 p3461 p4037 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73508 : p4037 ∨ p3323)
    (h73338 : p2963 ∨ p2331)
    (h57611 : (¬ p2252) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (¬ p4037) ∨ (¬ p4191))
    : p3461 ∨ (¬ p2992) ∨ p3323 ∨ p2331 ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57611 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91838 (p2252 p2331 p2668 p2750 p2753 p2761 p2963 p3324 p3425 p3434 p3471 p5123 p5580 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73386 : p3324 ∨ p2668)
    (h73396 : p3471 ∨ p3425)
    (h64553 : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p2753) ∨ (¬ p2252) ∨ (¬ p2761) ∨ p2331 ∨ p2668 ∨ (¬ p3434) ∨ p3425 ∨ (¬ p2750) ∨ (¬ p5123) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64553 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step91840 (p2177 p2210 p2252 p2295 p2299 p2331 p2608 p2619 p2750 p2963 p3568 p3954 p4243 p4902 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73338 : p2963 ∨ p2331)
    (h73234 : p2299 ∨ p2177)
    (h73416 : p3568 ∨ p2295)
    (h51028 : (¬ p2210) ∨ (¬ p2252) ∨ (¬ p2299) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p3954) ∨ (¬ p4243) ∨ (¬ p4902))
    : (¬ p2619) ∨ p2608 ∨ p2331 ∨ (¬ p2210) ∨ p2177 ∨ (¬ p4902) ∨ p2295 ∨ (¬ p2750) ∨ (¬ p4243) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h51028 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step91841 (p2252 p2331 p2363 p2608 p2668 p2750 p2963 p3324 p3399 p3631 p3950 p3954 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73338 : p2963 ∨ p2331)
    (h73386 : p3324 ∨ p2668)
    (h73498 : p3954 ∨ p2608)
    (h41581 : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4347))
    : (¬ p3631) ∨ p2363 ∨ (¬ p2750) ∨ p2331 ∨ (¬ p3399) ∨ p2668 ∨ (¬ p2252) ∨ (¬ p3950) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h41581 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step91842 (p2252 p2608 p2750 p3266 p3286 p3292 p3399 p3631 p3950 p3954 p5284 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73378 : p3292 ∨ p3286)
    (h63406 : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p5284))
    : (¬ p5284) ∨ p2608 ∨ (¬ p3399) ∨ (¬ p3950) ∨ p3286 ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p3266) ∨ (¬ p3631) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63406 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step91846 (p2252 p2573 p2579 p2630 p2655 p2745 p3016 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h41840 : (¬ p2252) ∨ (¬ p2579) ∨ (¬ p2630) ∨ (¬ p2655) ∨ (¬ p2745) ∨ (¬ p3016))
    : (¬ p3016) ∨ (¬ p2252) ∨ p2573 ∨ (¬ p2745) ∨ (¬ p2655) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41840 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step91849 (p2252 p2946 p2952 p4282 p4365 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h13214 : (¬ p2252) ∨ (¬ p2952) ∨ (¬ p4282) ∨ (¬ p4365))
    : (¬ p4365) ∨ p2946 ∨ (¬ p2252) ∨ (¬ p4282) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h13214 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step91852 (p2177 p2252 p2274 p2299 p2331 p2963 p2992 p3097 p3745 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73352 : p3097 ∨ p2274)
    (h73338 : p2963 ∨ p2331)
    (h46496 : (¬ p2252) ∨ (¬ p2299) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (¬ p3097) ∨ (¬ p3745))
    : (¬ p3745) ∨ (¬ p2992) ∨ p2177 ∨ (¬ p2252) ∨ p2274 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3745 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46496 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step91862 (p2252 p2598 p2750 p2753 p2901 p2911 p2946 p2952 p3201 p3246 p3690 p4320 p4666 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73330 : p2952 ∨ p2946)
    (h73552 : p4320 ∨ p2901)
    (h64996 : (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2911) ∨ (¬ p2952) ∨ (¬ p3201) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4666))
    : (¬ p2911) ∨ p3246 ∨ p2946 ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2598) ∨ (¬ p4666) ∨ p2901 ∨ (¬ p2753) ∨ (¬ p3201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64996 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step91863 (p2252 p2264 p2598 p2748 p2807 p3055 p3276 p3414 p3553 p3619 p4749 p5123 p5164 p5558 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h73350 : p3055 ∨ p2598)
    (h73410 : p3553 ∨ p2264)
    (h59747 : (¬ p2252) ∨ (¬ p2748) ∨ (¬ p3055) ∨ (¬ p3276) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3619) ∨ (¬ p4749) ∨ (¬ p5123) ∨ (¬ p5164) ∨ (¬ p5558))
    : (¬ p5558) ∨ (¬ p5164) ∨ (¬ p4749) ∨ p2807 ∨ (¬ p3276) ∨ (¬ p2748) ∨ (¬ p5123) ∨ (¬ p3619) ∨ (¬ p2252) ∨ p2598 ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5164 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u13 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h59747 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step91864 (p2252 p2470 p2476 p2528 p2534 p2608 p2655 p2750 p3146 p3399 p3527 p3954 p4905 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h73498 : p3954 ∨ p2608)
    (h54698 : (¬ p2252) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3146) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p4905))
    : p2528 ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3527) ∨ (¬ p3146) ∨ (¬ p3399) ∨ (¬ p2252) ∨ p2470 ∨ p2608 ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h54698 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step91866 (p2252 p2608 p2651 p2657 p2750 p3016 p3399 p3564 p3574 p3631 p3954 p4137 p4625 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73288 : p2657 ∨ p2651)
    (h73524 : p4137 ∨ p3564)
    (h73498 : p3954 ∨ p2608)
    (h41610 : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3399) ∨ (¬ p3574) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p4137) ∨ (¬ p4625))
    : (¬ p3399) ∨ (¬ p3631) ∨ (¬ p2252) ∨ (¬ p4625) ∨ (¬ p2750) ∨ p3016 ∨ p2651 ∨ p3564 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h41610 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step91867 (p2210 p2252 p2264 p2307 p2313 p2459 p2608 p2750 p2972 p3552 p3553 p3954 p3983 p4348 p4450 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73238 : p2313 ∨ p2307)
    (h73410 : p3553 ∨ p2264)
    (h73562 : p4348 ∨ p2459)
    (h64962 : (¬ p2210) ∨ (¬ p2252) ∨ (¬ p2313) ∨ (¬ p2750) ∨ (¬ p2972) ∨ (¬ p3552) ∨ (¬ p3553) ∨ (¬ p3954) ∨ (¬ p3983) ∨ (¬ p4348) ∨ (¬ p4450))
    : (¬ p2972) ∨ p2608 ∨ (¬ p2210) ∨ p2307 ∨ (¬ p2252) ∨ (¬ p2750) ∨ p2264 ∨ (¬ p3983) ∨ p2459 ∨ (¬ p4450) ∨ (¬ p3552) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u14 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h64962 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u14))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step91869 (p2144 p2252 p2437 p2655 p2750 p3212 p3343 p3359 p3366 p3389 p3461 p3540 p3680 p4191 p5325 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73402 : p3540 ∨ p3389)
    (h73388 : p3359 ∨ p3343)
    (h64534 : (¬ p2144) ∨ (¬ p2252) ∨ (¬ p2437) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3212) ∨ (¬ p3359) ∨ p3366 ∨ (¬ p3540) ∨ (¬ p3680) ∨ (¬ p4191) ∨ (¬ p5325))
    : p3366 ∨ p3461 ∨ (¬ p3212) ∨ p3389 ∨ (¬ p2750) ∨ (¬ p2655) ∨ (¬ p2144) ∨ (¬ p2437) ∨ (¬ p5325) ∨ (¬ p3680) ∨ p3343 ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3366) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u14 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h64534 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u14))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u0 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u12))) (fun r10 => (False.elim (r10 u8)))))))))))))))))))))))))

theorem step91871 (p2252 p2459 p2528 p2534 p2608 p2655 p2750 p3093 p3319 p3322 p3389 p3540 p3954 p4133 p4186 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73402 : p3540 ∨ p3389)
    (h73498 : p3954 ∨ p2608)
    (h63138 : (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3322) ∨ (¬ p3540) ∨ (¬ p3954) ∨ (¬ p4133) ∨ (¬ p4186))
    : (¬ p3322) ∨ (¬ p3319) ∨ p2528 ∨ p3389 ∨ (¬ p2459) ∨ (¬ p4186) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p3093) ∨ (¬ p2655) ∨ p2608 ∨ (¬ p4133) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u13 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u14 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h63138 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u14))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (False.elim (r10 u5)))))))))))))))))))))))))

theorem step91872 (p2132 p2252 p2264 p2459 p2750 p2753 p2807 p2860 p3125 p3414 p3553 p4330 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73410 : p3553 ∨ p2264)
    (h73392 : p3414 ∨ p2807)
    (h64636 : (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4330) ∨ (¬ p4348))
    : (¬ p2132) ∨ (¬ p3125) ∨ p2459 ∨ (¬ p4330) ∨ (¬ p2252) ∨ p2264 ∨ p2807 ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64636 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u10)))))))))))))))))))))

theorem step91876 (p2210 p2252 p2437 p2651 p2657 p3399 p3527 p3555 p3742 p4448 p5503 p5559 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73288 : p2657 ∨ p2651)
    (h73412 : p3555 ∨ p2210)
    (h61053 : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3555) ∨ (¬ p3742) ∨ (¬ p4448) ∨ (¬ p5503) ∨ (¬ p5559))
    : (¬ p5503) ∨ (¬ p2252) ∨ (¬ p3527) ∨ (¬ p5559) ∨ (¬ p3399) ∨ p2437 ∨ (¬ p4448) ∨ p2651 ∨ p2210 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5503 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4448 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u11 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h61053 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step91877 (p2252 p2295 p2331 p2963 p2992 p3136 p3568 p4315 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73338 : p2963 ∨ p2331)
    (h73550 : p4315 ∨ p3136)
    (h46497 : (¬ p2252) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (¬ p3568) ∨ (¬ p4315))
    : (¬ p2992) ∨ p2295 ∨ p2331 ∨ p3136 ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46497 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step91881 (p2144 p2220 p2252 p2459 p2573 p2579 p2655 p2750 p2753 p3016 p3083 p3146 p4256 p4348 p4438 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73542 : p4256 ∨ p3083)
    (h73274 : p2579 ∨ p2573)
    (h64538 : (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2252) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3016) ∨ (¬ p3146) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4438))
    : (¬ p2753) ∨ p2459 ∨ (¬ p2750) ∨ (¬ p2655) ∨ (¬ p3146) ∨ (¬ p4438) ∨ (¬ p2252) ∨ (¬ p2220) ∨ (¬ p2144) ∨ p3083 ∨ p2573 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u14 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h64538 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u14))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u13))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u12))) (fun r10 => (False.elim (r10 u5)))))))))))))))))))))))))

theorem step91885 (p2459 p2727 p3189 p3256 p4111 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73518 : p4111 ∨ p2727)
    (h45002 : (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4111) ∨ (¬ p4348))
    : (¬ p3189) ∨ p2459 ∨ p2727 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45002 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91886 (p2459 p2992 p3189 p3256 p3662 p4348 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73562 : p4348 ∨ p2459)
    (h44650 : (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3662) ∨ (¬ p4348))
    : (¬ p3189) ∨ p2992 ∨ p2459 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44650 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step91888 (p2264 p2727 p2911 p3189 p3644 p4111 p4551 p4653 : Prop)
    (h73632 : p4551 ∨ (¬ p2264))
    (h73434 : p3644 ∨ p2911)
    (h73518 : p4111 ∨ p2727)
    (h66741 : (¬ p4551) ∨ (¬ p3189) ∨ (¬ p3644) ∨ (¬ p4653) ∨ (¬ p4111))
    : (¬ p2264) ∨ p2911 ∨ (¬ p4653) ∨ p2727 ∨ (¬ p3189) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4551 := (Or.elim h73632 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h66741 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step91889 (p2992 p3189 p3256 p3266 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h47361 : (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3662))
    : (¬ p3189) ∨ p2992 ∨ (¬ p3266) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47361 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91892 (p2528 p2651 p2727 p3189 p4111 p4346 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h48539 : (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3189) ∨ (¬ p4111) ∨ (¬ p4346))
    : (¬ p3189) ∨ (¬ p4346) ∨ (¬ p2651) ∨ (¬ p2528) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48539 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step91893 (p2177 p2299 p2651 p2727 p3189 p4111 p4378 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73234 : p2299 ∨ p2177)
    (h43769 : (¬ p2299) ∨ (¬ p2651) ∨ (¬ p3189) ∨ (¬ p4111) ∨ (¬ p4378))
    : p2727 ∨ (¬ p4378) ∨ p2177 ∨ (¬ p3189) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43769 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step91898 (p2156 p2177 p2253 p2274 p2299 p2651 p2727 p3097 p3189 p3646 p4111 p4524 p4550 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73436 : p3646 ∨ p2156)
    (h72962 : p4524)
    (h73234 : p2299 ∨ p2177)
    (h73352 : p3097 ∨ p2274)
    (h51719 : (¬ p2253) ∨ (¬ p2299) ∨ (¬ p2651) ∨ (¬ p3097) ∨ (¬ p3189) ∨ (¬ p3646) ∨ (¬ p4111) ∨ (¬ p4524) ∨ (¬ p4550))
    : p2727 ∨ (¬ p2253) ∨ p2156 ∨ (¬ p3189) ∨ (¬ p4550) ∨ p2177 ∨ (¬ p2651) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4524 := h72962;
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51719 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step91903 (p2440 p2727 p2807 p3189 p3414 p3919 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73392 : p3414 ∨ p2807)
    (h55022 : (¬ p2440) ∨ (¬ p3189) ∨ (¬ p3414) ∨ (¬ p3919) ∨ (¬ p4111))
    : (¬ p3189) ∨ p2727 ∨ (¬ p2440) ∨ p2807 ∨ (¬ p3919) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55022 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91908 (p2252 p3166 p3172 p3189 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h5347 : (¬ p2252) ∨ (¬ p3172) ∨ (¬ p3189))
    : p3166 ∨ (¬ p3189) ∨ (¬ p2252) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h5347 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step91910 (p2245 p2295 p2641 p3166 p3172 p3189 p3568 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73356 : p3172 ∨ p3166)
    (h73416 : p3568 ∨ p2295)
    (h50680 : (¬ p2245) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p3568) ∨ (¬ p4154))
    : p2641 ∨ (¬ p3189) ∨ (¬ p2245) ∨ p3166 ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50680 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91912 (p2651 p2992 p3166 p3172 p3189 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73356 : p3172 ∨ p3166)
    (h42732 : (¬ p2651) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p3662))
    : (¬ p3189) ∨ p2992 ∨ p3166 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42732 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91915 (p2241 p3146 p3189 p3256 p3692 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h47252 : (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3692))
    : (¬ p3189) ∨ (¬ p3256) ∨ (¬ p2241) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47252 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91917 (p2177 p2249 p2299 p2331 p2963 p3146 p3189 p3256 p3309 p3549 p3692 p3922 p4902 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73406 : p3549 ∨ p3309)
    (h73234 : p2299 ∨ p2177)
    (h73338 : p2963 ∨ p2331)
    (h64401 : (¬ p2249) ∨ (¬ p2299) ∨ (¬ p2963) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3549) ∨ (¬ p3692) ∨ (¬ p3922) ∨ (¬ p4902))
    : p3146 ∨ p3309 ∨ (¬ p4902) ∨ (¬ p3922) ∨ (¬ p2249) ∨ (¬ p3189) ∨ p2177 ∨ p2331 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64401 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step91919 (p2946 p2992 p3146 p3189 p3662 p4311 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h49700 : (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p4311))
    : (¬ p3189) ∨ (¬ p3146) ∨ p2992 ∨ (¬ p4311) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49700 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91923 (p2295 p2641 p3005 p3189 p3568 p3877 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73488 : p3877 ∨ p3005)
    (h73416 : p3568 ∨ p2295)
    (h46128 : (¬ p3189) ∨ (¬ p3568) ∨ (¬ p3877) ∨ (¬ p4154))
    : (¬ p3189) ∨ p2641 ∨ p3005 ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46128 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91925 (p2245 p2749 p3166 p3172 p3189 p3379 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h71933 : (¬ p3172) ∨ (¬ p3379) ∨ (¬ p3189) ∨ (¬ p2749) ∨ (¬ p2245))
    : (¬ p3189) ∨ p3166 ∨ (¬ p2749) ∨ (¬ p2245) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71933 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91927 (p2187 p2641 p3189 p3989 p4154 p4417 p4560 : Prop)
    (h72955 : p4560)
    (h73526 : p4154 ∨ p2641)
    (h73502 : p3989 ∨ p2187)
    (h50719 : (¬ p3189) ∨ (¬ p3989) ∨ (¬ p4154) ∨ (¬ p4417) ∨ (¬ p4560))
    : (¬ p4417) ∨ (¬ p3189) ∨ p2641 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4560 := h72955;
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50719 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91929 (p2307 p2313 p2641 p2667 p3189 p4154 p4405 p4417 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73238 : p2313 ∨ p2307)
    (h41341 : (¬ p2313) ∨ (¬ p2667) ∨ (¬ p3189) ∨ (¬ p4154) ∨ (¬ p4405) ∨ (¬ p4417))
    : (¬ p4417) ∨ (¬ p3189) ∨ p2641 ∨ (¬ p4405) ∨ p2307 ∨ (¬ p2667) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41341 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step91930 (p2253 p2331 p2598 p2641 p2911 p3055 p3189 p3201 p3644 p3876 p4133 p4154 p4417 p4736 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73350 : p3055 ∨ p2598)
    (h73526 : p4154 ∨ p2641)
    (h73434 : p3644 ∨ p2911)
    (h58263 : (¬ p2253) ∨ (¬ p2331) ∨ (¬ p3055) ∨ (¬ p3189) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4133) ∨ (¬ p4154) ∨ (¬ p4417) ∨ (¬ p4736))
    : p3201 ∨ (¬ p3189) ∨ (¬ p4133) ∨ (¬ p4736) ∨ p2598 ∨ (¬ p2331) ∨ (¬ p2253) ∨ (¬ p4417) ∨ p2641 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u13 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h58263 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step91932 (p2992 p3189 p3661 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h5346 : (¬ p3189) ∨ (¬ p3661) ∨ (¬ p3662))
    : (¬ p3189) ∨ p2992 ∨ (¬ p3661) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5346 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step91935 (p2373 p2992 p3189 p3662 p3880 p4311 p4705 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73490 : p3880 ∨ p2373)
    (h58241 : (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3880) ∨ (¬ p4311) ∨ (¬ p4705))
    : (¬ p3189) ∨ p2992 ∨ (¬ p4705) ∨ p2373 ∨ (¬ p4311) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58241 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91936 (p2241 p2630 p3005 p3189 p3877 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h42975 : (¬ p2241) ∨ (¬ p2630) ∨ (¬ p3189) ∨ (¬ p3877))
    : (¬ p3189) ∨ p3005 ∨ (¬ p2630) ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42975 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91940 (p2177 p2299 p2307 p2313 p2641 p2667 p3189 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73234 : p2299 ∨ p2177)
    (h73238 : p2313 ∨ p2307)
    (h60162 : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (¬ p3189) ∨ (¬ p4154))
    : p2641 ∨ (¬ p3189) ∨ p2177 ∨ p2307 ∨ (¬ p2667) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60162 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91941 (p2641 p2819 p3171 p3189 p4113 p4154 p4358 p4843 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73564 : p4358 ∨ p2819)
    (h51521 : (¬ p3171) ∨ (¬ p3189) ∨ (¬ p4113) ∨ (¬ p4154) ∨ (¬ p4358) ∨ (¬ p4843))
    : p2641 ∨ (¬ p3189) ∨ p2819 ∨ (¬ p3171) ∨ (¬ p4113) ∨ (¬ p4843) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4843 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51521 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step91942 (p2531 p2901 p2992 p3189 p3662 p3988 p4320 p4346 p4555 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73552 : p4320 ∨ p2901)
    (h42037 : (¬ p2531) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3988) ∨ (¬ p4320) ∨ (¬ p4346) ∨ (¬ p4555))
    : (¬ p3189) ∨ p2992 ∨ (¬ p4346) ∨ p2901 ∨ (¬ p3988) ∨ (¬ p2531) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42037 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step91944 (p2440 p2727 p3166 p3172 p3189 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73356 : p3172 ∨ p3166)
    (h53755 : (¬ p2440) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p4111))
    : (¬ p3189) ∨ p2727 ∨ p3166 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53755 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91947 (p2630 p2727 p3166 p3172 p3189 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73356 : p3172 ∨ p3166)
    (h71934 : (¬ p3189) ∨ (¬ p3172) ∨ (¬ p2630) ∨ (¬ p4111))
    : (¬ p3189) ∨ p2727 ∨ p3166 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71934 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91948 (p2427 p2992 p3189 p3662 p3919 p4066 p4235 p4283 p4705 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73536 : p4235 ∨ p2427)
    (h42041 : (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3919) ∨ (¬ p4066) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4705))
    : (¬ p3189) ∨ p2992 ∨ (¬ p4283) ∨ (¬ p3919) ∨ p2427 ∨ (¬ p4705) ∨ (¬ p4066) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42041 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step91950 (p2253 p2651 p2727 p3189 p3256 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h51697 : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4111))
    : (¬ p3189) ∨ p2727 ∨ (¬ p3256) ∨ (¬ p2253) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51697 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step91954 (p2727 p3016 p3189 p3574 p4111 p4346 p4598 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73422 : p3574 ∨ p3016)
    (h41390 : (¬ p3189) ∨ (¬ p3574) ∨ (¬ p4111) ∨ (¬ p4346) ∨ (¬ p4598))
    : (¬ p3189) ∨ (¬ p4346) ∨ p2727 ∨ (¬ p4598) ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41390 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91955 (p2659 p2727 p3189 p3389 p3540 p3579 p3919 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73402 : p3540 ∨ p3389)
    (h59140 : (¬ p2659) ∨ (¬ p3189) ∨ (¬ p3540) ∨ (¬ p3579) ∨ (¬ p3919) ∨ (¬ p4111))
    : (¬ p3189) ∨ p2727 ∨ (¬ p3579) ∨ (¬ p2659) ∨ (¬ p3919) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h59140 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step91957 (p2727 p3189 p3641 p3874 p4111 p4346 p4750 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73484 : p3874 ∨ p3641)
    (h49995 : (¬ p3189) ∨ (¬ p3874) ∨ (¬ p4111) ∨ (¬ p4346) ∨ (¬ p4750))
    : (¬ p3189) ∨ (¬ p4346) ∨ (¬ p4750) ∨ p2727 ∨ p3641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49995 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step91959 (p2230 p2241 p2427 p2589 p3189 p3246 p3256 p3690 p4235 p4669 p5193 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73284 : p2589 ∨ p2230)
    (h73446 : p3690 ∨ p3246)
    (h48090 : (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4669) ∨ (¬ p5193))
    : (¬ p3189) ∨ (¬ p3256) ∨ p2427 ∨ p2230 ∨ p3246 ∨ (¬ p5193) ∨ (¬ p2241) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48090 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step91960 (p2241 p2396 p2553 p2573 p2579 p2588 p3189 p3256 p4107 p4669 p5193 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73514 : p4107 ∨ p2396)
    (h73274 : p2579 ∨ p2573)
    (h52230 : (¬ p2241) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p5193))
    : (¬ p3189) ∨ (¬ p3256) ∨ p2553 ∨ p2396 ∨ (¬ p2241) ∨ p2573 ∨ (¬ p4669) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h52230 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step91963 (p2177 p2299 p2996 p3171 p3189 p4361 p4403 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h62448 : (¬ p2299) ∨ (¬ p2996) ∨ (¬ p3171) ∨ (¬ p3189) ∨ (¬ p4361) ∨ (¬ p4403))
    : (¬ p2996) ∨ (¬ p3189) ∨ (¬ p3171) ∨ (¬ p4403) ∨ p2177 ∨ (¬ p4361) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62448 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step91966 (p2911 p2996 p3189 p3644 p4378 p4653 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h48739 : (¬ p2996) ∨ (¬ p3189) ∨ (¬ p3644) ∨ (¬ p4378) ∨ (¬ p4653))
    : (¬ p4378) ∨ (¬ p3189) ∨ p2911 ∨ (¬ p2996) ∨ (¬ p4653) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4378 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48739 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step91968 (p2881 p2996 p3189 p3570 p4362 p4804 p4963 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h42035 : (¬ p2996) ∨ (¬ p3189) ∨ (¬ p3570) ∨ (¬ p4362) ∨ (¬ p4804) ∨ (¬ p4963))
    : (¬ p3189) ∨ (¬ p2996) ∨ (¬ p4804) ∨ (¬ p4963) ∨ (¬ p4362) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4804 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42035 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step91974 (p2122 p2241 p2396 p2573 p2579 p3189 p3256 p3822 p4107 p4390 p4669 p5193 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73472 : p3822 ∨ p2122)
    (h73514 : p4107 ∨ p2396)
    (h63588 : (¬ p2241) ∨ (¬ p2579) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4390) ∨ (¬ p4669) ∨ (¬ p5193))
    : (¬ p3189) ∨ (¬ p3256) ∨ p2573 ∨ (¬ p4390) ∨ (¬ p4669) ∨ (¬ p2241) ∨ p2122 ∨ p2396 ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h63588 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step91978 (p2230 p2470 p2476 p2727 p3189 p4111 p4346 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h73518 : p4111 ∨ p2727)
    (h50684 : (¬ p2230) ∨ (¬ p2476) ∨ (¬ p3189) ∨ (¬ p4111) ∨ (¬ p4346))
    : (¬ p3189) ∨ (¬ p4346) ∨ (¬ p2230) ∨ p2470 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50684 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step91979 (p2220 p2241 p2459 p2608 p3146 p3189 p3645 p3692 p3954 p4120 p4550 p4877 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73522 : p4120 ∨ p2220)
    (h73498 : p3954 ∨ p2608)
    (h63047 : (¬ p2241) ∨ (¬ p2459) ∨ (¬ p3189) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p3954) ∨ (¬ p4120) ∨ (¬ p4550) ∨ (¬ p4877))
    : (¬ p3189) ∨ p3146 ∨ (¬ p2459) ∨ p2220 ∨ (¬ p3645) ∨ (¬ p4877) ∨ (¬ p4550) ∨ p2608 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h63047 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step91980 (p2284 p2992 p3189 p3662 p3952 p4311 p4509 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73496 : p3952 ∨ p2284)
    (h49306 : (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3952) ∨ (¬ p4311) ∨ (¬ p4509))
    : (¬ p3189) ∨ (¬ p4311) ∨ p2992 ∨ (¬ p4509) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49306 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91986 (p2156 p2241 p3125 p3189 p3461 p3646 p3744 p4009 p4191 p4524 p5119 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73454 : p3744 ∨ p3125)
    (h72962 : p4524)
    (h73530 : p4191 ∨ p3461)
    (h55065 : (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4009) ∨ (¬ p4191) ∨ (¬ p4524) ∨ (¬ p5119))
    : (¬ p4009) ∨ (¬ p3189) ∨ p2156 ∨ p3125 ∨ (¬ p5119) ∨ p3461 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4524 := h72962;
    let u10 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55065 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step91987 (p2295 p2331 p3166 p3172 p3189 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h44126 : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3172) ∨ (¬ p3189))
    : p3166 ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3189) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h44126 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step91988 (p2295 p2641 p3189 p3568 p4154 p4405 p4417 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73416 : p3568 ∨ p2295)
    (h57415 : (¬ p3189) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4405) ∨ (¬ p4417))
    : p2641 ∨ (¬ p3189) ∨ p2295 ∨ (¬ p4417) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57415 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step91992 (p2727 p2911 p3189 p3527 p3644 p4111 p4652 p4653 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73434 : p3644 ∨ p2911)
    (h66742 : (¬ p3189) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p4653) ∨ (¬ p4652) ∨ (¬ p4111))
    : (¬ p3189) ∨ p2727 ∨ p2911 ∨ (¬ p4652) ∨ (¬ p4653) ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h66742 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step91994 (p2253 p2459 p2651 p2727 p3051 p3146 p3189 p3556 p3692 p4111 p4119 p4524 p4550 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73518 : p4111 ∨ p2727)
    (h73414 : p3556 ∨ p3051)
    (h72962 : p4524)
    (h51700 : (¬ p2253) ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p3189) ∨ (¬ p3556) ∨ (¬ p3692) ∨ (¬ p4111) ∨ (¬ p4119) ∨ (¬ p4524) ∨ (¬ p4550))
    : p3146 ∨ (¬ p3189) ∨ p2727 ∨ (¬ p4550) ∨ (¬ p2253) ∨ p3051 ∨ (¬ p2651) ∨ (¬ p2459) ∨ (¬ p4119) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4524 := h72962;
    (Or.elim h51700 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step91996 (p2331 p2641 p3189 p3256 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h59641 : (¬ p2331) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4154))
    : p2641 ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h59641 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step91998 (p2331 p2641 p2811 p3189 p3256 p4154 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h59695 : (¬ p2331) ∨ (¬ p2811) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4154))
    : p2641 ∨ (¬ p3189) ∨ (¬ p2331) ∨ (¬ p3256) ∨ (¬ p2811) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h59695 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92005 (p2177 p2253 p2299 p2331 p2641 p3189 p4154 p4378 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73234 : p2299 ∨ p2177)
    (h64120 : (¬ p2253) ∨ (¬ p2299) ∨ (¬ p2331) ∨ (¬ p3189) ∨ (¬ p4154) ∨ (¬ p4378))
    : (¬ p4378) ∨ p2641 ∨ (¬ p2331) ∨ p2177 ∨ (¬ p2253) ∨ (¬ p3189) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4378 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64120 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step92007 (p2493 p2499 p3016 p3189 p3402 p5011 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h48661 : (¬ p2499) ∨ (¬ p3016) ∨ (¬ p3189) ∨ (¬ p3402) ∨ (¬ p5011))
    : (¬ p3189) ∨ (¬ p3402) ∨ (¬ p3016) ∨ (¬ p5011) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5011 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48661 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92011 (p2696 p2742 p3189 p3276 p3346 p3363 p3367 p3585 p4009 p4425 p5119 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73428 : p3585 ∨ p3367)
    (h71936 : (¬ p4009) ∨ (¬ p2742) ∨ (¬ p3585) ∨ (¬ p2696) ∨ (¬ p4425) ∨ (¬ p3189) ∨ (¬ p3363) ∨ (¬ p3346) ∨ (¬ p5119))
    : p3276 ∨ (¬ p3189) ∨ p3367 ∨ (¬ p4009) ∨ (¬ p5119) ∨ (¬ p3363) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3346) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71936 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step92012 (p2241 p2363 p3189 p3256 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h45340 : (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4347))
    : (¬ p3189) ∨ (¬ p3256) ∨ p2363 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45340 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92027 (p3125 p4033 p5989 : Prop)
    (h74321 : p3125 ∨ (¬ p5989))
    (h12922 : p4033 ∨ p5989)
    : p4033 ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4033) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5989) := (Or.elim h74321 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12922 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step92028 (p2737 p2743 p2774 p2780 p2819 p3063 p3873 p4358 p4869 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73308 : p2780 ∨ p2774)
    (h73298 : p2743 ∨ p2737)
    (h60950 : (¬ p2743) ∨ (¬ p2780) ∨ (¬ p3063) ∨ (¬ p3873) ∨ (¬ p4358) ∨ (¬ p4869))
    : (¬ p4869) ∨ (¬ p3063) ∨ (¬ p3873) ∨ p2819 ∨ p2774 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4869 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h60950 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step92030 (p2122 p2132 p2138 p3309 p3822 p4193 p4734 p4869 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h72735 : p4734)
    (h73472 : p3822 ∨ p2122)
    (h50130 : (¬ p2138) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p4193) ∨ (¬ p4734) ∨ (¬ p4869))
    : (¬ p4869) ∨ p2132 ∨ p2122 ∨ (¬ p4193) ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4869 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4734 := h72735;
    let u7 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50130 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step92031 (p3319 p3367 p3585 p3917 p4869 p5224 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h49743 : (¬ p3319) ∨ (¬ p3585) ∨ (¬ p3917) ∨ (¬ p4869) ∨ (¬ p5224))
    : (¬ p3319) ∨ (¬ p4869) ∨ (¬ p3917) ∨ p3367 ∨ (¬ p5224) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5224 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49743 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92032 (p2383 p2387 p2737 p2743 p2785 p3063 p4845 p4869 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73246 : p2387 ∨ p2383)
    (h61843 : (¬ p2387) ∨ (¬ p2743) ∨ (¬ p2785) ∨ (¬ p3063) ∨ (¬ p4845) ∨ (¬ p4869))
    : (¬ p3063) ∨ p2737 ∨ (¬ p4869) ∨ (¬ p4845) ∨ p2383 ∨ (¬ p2785) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h61843 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step92033 (p2608 p3093 p3591 p4869 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h20328 : (¬ p2608) ∨ (¬ p3591) ∨ (¬ p4869))
    : p3093 ∨ (¬ p4869) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20328 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step92039 (p2122 p2307 p2737 p2743 p3822 p4845 p4869 p5016 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73298 : p2743 ∨ p2737)
    (h61853 : (¬ p2307) ∨ (¬ p2743) ∨ (¬ p3822) ∨ (¬ p4845) ∨ (¬ p4869) ∨ (¬ p5016))
    : (¬ p5016) ∨ (¬ p2307) ∨ p2122 ∨ p2737 ∨ (¬ p4845) ∨ (¬ p4869) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61853 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step92041 (p2122 p2230 p2440 p2542 p2589 p2608 p3016 p3309 p3574 p3822 p4869 p5193 p5222 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73284 : p2589 ∨ p2230)
    (h73270 : p2542 ∨ p2440)
    (h73422 : p3574 ∨ p3016)
    (h57879 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p3822) ∨ (¬ p4869) ∨ (¬ p5193) ∨ (¬ p5222))
    : p2122 ∨ (¬ p3309) ∨ (¬ p4869) ∨ p2230 ∨ (¬ p5193) ∨ (¬ p2608) ∨ p2440 ∨ p3016 ∨ (¬ p5222) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4869 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h57879 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step92042 (p2982 p4948 p5104 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h43045 : (¬ p4948) ∨ p5104)
    : p2982 ∨ p5104 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5104) := (fun h => hn (Or.inr h));
    let u2 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43045 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step92044 (p2563 p2946 p2982 p3115 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h44909 : (¬ p2563) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p4948))
    : (¬ p3115) ∨ p2982 ∨ (¬ p2946) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44909 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92045 (p2274 p2563 p2982 p3115 p3413 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h46272 : (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3115) ∨ (¬ p3413) ∨ (¬ p4948))
    : p2982 ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3413) ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46272 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92047 (p2220 p2373 p2608 p2982 p3347 p3399 p3631 p3904 p3951 p3954 p4120 p4948 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73846 : p4948 ∨ p2982)
    (h73498 : p3954 ∨ p2608)
    (h71938 : (¬ p3399) ∨ (¬ p3347) ∨ (¬ p4948) ∨ (¬ p3954) ∨ (¬ p3904) ∨ (¬ p3951) ∨ (¬ p4120) ∨ (¬ p3631) ∨ (¬ p2373))
    : (¬ p3631) ∨ p2220 ∨ (¬ p3904) ∨ (¬ p2373) ∨ p2982 ∨ p2608 ∨ (¬ p3951) ∨ (¬ p3399) ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h71938 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step92048 (p2210 p2373 p2972 p2982 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h45242 : (¬ p2210) ∨ (¬ p2373) ∨ (¬ p2972) ∨ (¬ p4948))
    : p2982 ∨ (¬ p2972) ∨ (¬ p2373) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45242 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92049 (p2427 p2982 p3434 p4382 p4898 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h50697 : (¬ p2427) ∨ (¬ p3434) ∨ (¬ p4382) ∨ (¬ p4898) ∨ (¬ p4948))
    : (¬ p4382) ∨ (¬ p3434) ∨ (¬ p2427) ∨ p2982 ∨ (¬ p4898) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4382 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4898 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50697 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92051 (p2427 p2449 p2982 p4362 p4382 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h56460 : (¬ p2427) ∨ (¬ p2449) ∨ (¬ p4362) ∨ (¬ p4382) ∨ (¬ p4948))
    : (¬ p4382) ∨ (¬ p2449) ∨ (¬ p2427) ∨ p2982 ∨ (¬ p4362) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4382 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56460 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92053 (p2132 p2138 p2427 p2870 p2982 p4244 p4948 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73214 : p2138 ∨ p2132)
    (h73846 : p4948 ∨ p2982)
    (h42683 : (¬ p2138) ∨ (¬ p2427) ∨ (¬ p4244) ∨ (¬ p4948))
    : p2870 ∨ p2132 ∨ p2982 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42683 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step92055 (p2427 p2982 p3051 p3369 p3379 p3556 p4948 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73846 : p4948 ∨ p2982)
    (h44801 : (¬ p2427) ∨ (¬ p3369) ∨ (¬ p3379) ∨ (¬ p3556) ∨ (¬ p4948))
    : p3051 ∨ p2982 ∨ (¬ p3379) ∨ (¬ p2427) ∨ (¬ p3369) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44801 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92059 (p2373 p2982 p3256 p4043 p4209 p4456 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h57328 : (¬ p2373) ∨ (¬ p3256) ∨ (¬ p4043) ∨ (¬ p4209) ∨ (¬ p4456) ∨ (¬ p4948))
    : (¬ p4209) ∨ (¬ p4456) ∨ (¬ p2373) ∨ (¬ p3256) ∨ (¬ p4043) ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4209 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4456 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h57328 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step92060 (p2563 p2982 p4334 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h20002 : (¬ p2563) ∨ (¬ p4334) ∨ (¬ p4948))
    : p2982 ∨ (¬ p4334) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p4334 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20002 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step92063 (p2563 p2839 p2982 p3105 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h43907 : (¬ p2563) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p4948))
    : p2982 ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43907 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92068 (p2396 p2427 p2982 p4382 p4556 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h50235 : (¬ p2396) ∨ (¬ p2427) ∨ (¬ p4382) ∨ (¬ p4556) ∨ (¬ p4948))
    : (¬ p4382) ∨ (¬ p2396) ∨ p2982 ∨ (¬ p4556) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4382 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50235 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92072 (p2563 p2630 p2810 p2982 p3755 p4039 p4948 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73846 : p4948 ∨ p2982)
    (h62684 : (¬ p2563) ∨ (¬ p2810) ∨ (¬ p3755) ∨ (¬ p4039) ∨ (¬ p4948))
    : (¬ p4039) ∨ (¬ p3755) ∨ p2630 ∨ (¬ p2563) ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4039 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62684 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92073 (p2563 p2651 p2657 p2958 p2982 p3212 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73288 : p2657 ∨ p2651)
    (h45186 : (¬ p2563) ∨ (¬ p2657) ∨ (¬ p2958) ∨ (¬ p3212) ∨ (¬ p4948))
    : p2982 ∨ (¬ p2958) ∨ (¬ p3212) ∨ (¬ p2563) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45186 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92074 (p2363 p2427 p2533 p2982 p3051 p3166 p3256 p3556 p3904 p4117 p4134 p4347 p4729 p4948 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73414 : p3556 ∨ p3051)
    (h73846 : p4948 ∨ p2982)
    (h50777 : (¬ p2427) ∨ (¬ p2533) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p4117) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4729) ∨ (¬ p4948))
    : p2363 ∨ p3051 ∨ p2982 ∨ (¬ p3904) ∨ (¬ p3256) ∨ (¬ p2427) ∨ (¬ p3166) ∨ (¬ p4134) ∨ (¬ p4117) ∨ (¬ p4729) ∨ (¬ p2533) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50777 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u13)))))))))))))))))))))))

theorem step92080 (p2144 p2427 p2598 p2982 p3055 p3212 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73350 : p3055 ∨ p2598)
    (h57765 : (¬ p2144) ∨ (¬ p2427) ∨ (¬ p3055) ∨ (¬ p3212) ∨ (¬ p4948))
    : (¬ p3212) ∨ p2982 ∨ (¬ p2144) ∨ (¬ p2427) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57765 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92081 (p2881 p2891 p2972 p2982 p3486 p3570 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73418 : p3570 ∨ p2881)
    (h73398 : p3486 ∨ p2891)
    (h43717 : (¬ p2972) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4948))
    : (¬ p2972) ∨ p2982 ∨ p2881 ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43717 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92082 (p2982 p3115 p3879 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h39552 : (¬ p3115) ∨ (¬ p3879) ∨ (¬ p4948))
    : (¬ p3115) ∨ p2982 ∨ (¬ p3879) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h39552 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step92085 (p2396 p2761 p2982 p4322 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h45111 : (¬ p2396) ∨ (¬ p2761) ∨ (¬ p4322) ∨ (¬ p4948))
    : (¬ p4322) ∨ (¬ p2761) ∨ (¬ p2396) ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45111 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92086 (p2982 p4032 p4109 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h26676 : p4032 ∨ (¬ p4109) ∨ (¬ p4948))
    : p4032 ∨ p2982 ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4032) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h26676 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step92090 (p2440 p2982 p3016 p4203 p4948 p5043 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h50229 : (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4203) ∨ (¬ p4948) ∨ (¬ p5043))
    : p2982 ∨ (¬ p5043) ∨ (¬ p4203) ∨ (¬ p2440) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50229 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92092 (p2850 p2982 p3212 p3684 p4399 p4730 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73442 : p3684 ∨ p2850)
    (h41065 : (¬ p3212) ∨ (¬ p3684) ∨ (¬ p4399) ∨ (¬ p4730) ∨ (¬ p4948))
    : (¬ p3212) ∨ p2982 ∨ p2850 ∨ (¬ p4730) ∨ (¬ p4399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41065 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92093 (p2982 p3212 p4109 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h29819 : (¬ p3212) ∨ (¬ p4109) ∨ (¬ p4948))
    : (¬ p3212) ∨ p2982 ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h29819 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step92094 (p2230 p2437 p2589 p2982 p3115 p3413 p3742 p4948 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73846 : p4948 ∨ p2982)
    (h73284 : p2589 ∨ p2230)
    (h44777 : (¬ p2589) ∨ (¬ p3115) ∨ (¬ p3413) ∨ (¬ p3742) ∨ (¬ p4948))
    : (¬ p3115) ∨ (¬ p3413) ∨ p2437 ∨ p2982 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44777 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92095 (p2363 p2373 p2982 p3949 p4433 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h41211 : (¬ p2363) ∨ (¬ p2373) ∨ (¬ p3949) ∨ (¬ p4433) ∨ (¬ p4948))
    : p2982 ∨ (¬ p3949) ∨ (¬ p4433) ∨ (¬ p2363) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p3949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41211 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92097 (p2177 p2299 p2341 p2396 p2406 p2982 p3238 p3379 p3452 p3951 p4948 p5207 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73846 : p4948 ∨ p2982)
    (h73374 : p3238 ∨ p2406)
    (h73234 : p2299 ∨ p2177)
    (h51670 : (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3951) ∨ (¬ p4948) ∨ (¬ p5207))
    : p3379 ∨ p2982 ∨ (¬ p2396) ∨ p2406 ∨ p2177 ∨ (¬ p3951) ∨ (¬ p5207) ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5207 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51670 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step92099 (p2230 p2589 p2630 p2662 p2810 p2982 p4322 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73316 : p2810 ∨ p2630)
    (h73284 : p2589 ∨ p2230)
    (h60859 : (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p4322) ∨ (¬ p4948))
    : (¬ p4322) ∨ p2982 ∨ p2630 ∨ p2230 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60859 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92102 (p2573 p2579 p2982 p3212 p4399 p4715 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73274 : p2579 ∨ p2573)
    (h50321 : (¬ p2579) ∨ (¬ p3212) ∨ (¬ p4399) ∨ (¬ p4715) ∨ (¬ p4948))
    : (¬ p3212) ∨ (¬ p4399) ∨ (¬ p4715) ∨ p2982 ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50321 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92104 (p2651 p2657 p2946 p2982 p3115 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73288 : p2657 ∨ p2651)
    (h45007 : (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p4948))
    : (¬ p3115) ∨ p2982 ∨ (¬ p2946) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45007 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92105 (p2230 p2589 p2662 p2727 p2982 p4111 p4322 p4948 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73846 : p4948 ∨ p2982)
    (h73284 : p2589 ∨ p2230)
    (h55652 : (¬ p2589) ∨ (¬ p2662) ∨ (¬ p4111) ∨ (¬ p4322) ∨ (¬ p4948))
    : p2727 ∨ p2982 ∨ (¬ p4322) ∨ p2230 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55652 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92110 (p2210 p2427 p2459 p2717 p2972 p2982 p3425 p3659 p4348 p4736 p4948 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73846 : p4948 ∨ p2982)
    (h73562 : p4348 ∨ p2459)
    (h49515 : (¬ p2210) ∨ (¬ p2427) ∨ (¬ p2972) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4736) ∨ (¬ p4948))
    : (¬ p2427) ∨ p2717 ∨ p2982 ∨ (¬ p4736) ∨ (¬ p3425) ∨ (¬ p2210) ∨ p2459 ∨ (¬ p2972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h49515 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step92122 (p2177 p2307 p2440 p2459 p2651 p2657 p2781 p2982 p4236 p4948 p5059 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73288 : p2657 ∨ p2651)
    (h55116 : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2440) ∨ (¬ p2459) ∨ (¬ p2657) ∨ (¬ p2781) ∨ (¬ p4236) ∨ (¬ p4948) ∨ (¬ p5059))
    : (¬ p2307) ∨ (¬ p4236) ∨ (¬ p2459) ∨ (¬ p5059) ∨ (¬ p2440) ∨ (¬ p2177) ∨ p2982 ∨ (¬ p2781) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h55116 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step92126 (p2246 p2331 p2363 p2598 p2668 p2744 p2850 p2982 p3055 p3366 p3684 p4948 p5059 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73350 : p3055 ∨ p2598)
    (h73442 : p3684 ∨ p2850)
    (h52787 : (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3684) ∨ (¬ p4948) ∨ (¬ p5059))
    : (¬ p2668) ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p5059) ∨ p2982 ∨ (¬ p2744) ∨ (¬ p2331) ∨ p2598 ∨ (¬ p2363) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h52787 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step92127 (p2274 p2284 p2982 p3097 p3115 p3952 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73352 : p3097 ∨ p2274)
    (h73496 : p3952 ∨ p2284)
    (h45305 : (¬ p3097) ∨ (¬ p3115) ∨ (¬ p3952) ∨ (¬ p4948))
    : (¬ p3115) ∨ p2982 ∨ p2274 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45305 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92128 (p2427 p2982 p3516 p3543 p4382 p4914 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h42067 : (¬ p2427) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p4382) ∨ (¬ p4914) ∨ (¬ p4948))
    : (¬ p4382) ∨ (¬ p3516) ∨ p2982 ∨ (¬ p3543) ∨ (¬ p2427) ∨ (¬ p4914) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4382 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42067 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step92132 (p2440 p2651 p2657 p2761 p2786 p2982 p3461 p3654 p3951 p4381 p4789 p4948 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73288 : p2657 ∨ p2651)
    (h73846 : p4948 ∨ p2982)
    (h49050 : (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2786) ∨ (¬ p3461) ∨ (¬ p3654) ∨ (¬ p3951) ∨ (¬ p4381) ∨ (¬ p4789) ∨ (¬ p4948))
    : p2761 ∨ (¬ p3461) ∨ (¬ p3951) ∨ (¬ p2440) ∨ (¬ p2786) ∨ (¬ p4789) ∨ p2651 ∨ p2982 ∨ (¬ p3654) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49050 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u11)))))))))))))))))))

theorem step92135 (p2177 p2386 p2553 p2630 p2797 p2810 p3567 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h56000 : (¬ p2177) ∨ (¬ p2386) ∨ (¬ p2553) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3567))
    : (¬ p3567) ∨ (¬ p2553) ∨ (¬ p2386) ∨ (¬ p2797) ∨ (¬ p2177) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56000 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step92138 (p2573 p2579 p2651 p2654 p2797 p3016 p3984 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73286 : p2654 ∨ p2651)
    (h71941 : (¬ p3016) ∨ (¬ p2797) ∨ (¬ p2654) ∨ (¬ p3984) ∨ (¬ p2579))
    : (¬ p2797) ∨ (¬ p3984) ∨ p2573 ∨ p2651 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2654 := (Or.elim h73286 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71941 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92139 (p2295 p2553 p2588 p2590 p2696 p2797 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h43329 : (¬ p2295) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p2696) ∨ (¬ p2797))
    : (¬ p2295) ∨ p2553 ∨ (¬ p2590) ∨ (¬ p2696) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43329 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92140 (p2295 p2553 p2588 p2630 p2797 p2810 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73316 : p2810 ∨ p2630)
    (h47962 : (¬ p2295) ∨ (¬ p2588) ∨ (¬ p2797) ∨ (¬ p2810))
    : (¬ p2295) ∨ p2553 ∨ (¬ p2797) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47962 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92141 (p2274 p2295 p2696 p2797 p3097 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h43791 : (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3097))
    : (¬ p2295) ∨ p2274 ∨ (¬ p2696) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43791 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92142 (p2630 p2797 p2810 p3125 p3323 p3744 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73316 : p2810 ∨ p2630)
    (h59723 : (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3323) ∨ (¬ p3744))
    : (¬ p3323) ∨ p3125 ∨ (¬ p2797) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59723 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92143 (p2406 p2590 p2630 p2797 p2810 p3238 p3984 p4811 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73374 : p3238 ∨ p2406)
    (h54987 : (¬ p2590) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3238) ∨ (¬ p3984) ∨ (¬ p4811))
    : (¬ p2797) ∨ (¬ p4811) ∨ p2630 ∨ (¬ p3984) ∨ (¬ p2590) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h54987 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step92148 (p2192 p2210 p2274 p2668 p2696 p2797 p3097 p3555 p4173 p4405 p4733 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73528 : p4173 ∨ p2192)
    (h73412 : p3555 ∨ p2210)
    (h54321 : (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3097) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p4405) ∨ (¬ p4733))
    : (¬ p2668) ∨ (¬ p2797) ∨ (¬ p2696) ∨ (¬ p4733) ∨ p2274 ∨ p2192 ∨ (¬ p4405) ∨ p2210 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h54321 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step92150 (p2307 p2797 p3136 p3309 p3549 p3567 p4315 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h73550 : p4315 ∨ p3136)
    (h47111 : (¬ p2307) ∨ (¬ p2797) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p4315))
    : (¬ p2307) ∨ (¬ p3567) ∨ p3309 ∨ p3136 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47111 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92151 (p2493 p2499 p2553 p2588 p2668 p2696 p2797 p3379 p3452 p4405 p4733 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73394 : p3452 ∨ p3379)
    (h73260 : p2499 ∨ p2493)
    (h49909 : (¬ p2499) ∨ (¬ p2588) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3452) ∨ (¬ p4405) ∨ (¬ p4733))
    : (¬ p2668) ∨ p2553 ∨ p3379 ∨ (¬ p2696) ∨ (¬ p2797) ∨ p2493 ∨ (¬ p4733) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49909 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step92153 (p2331 p2440 p2630 p2797 p2810 p2963 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73316 : p2810 ∨ p2630)
    (h45758 : (¬ p2440) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p2963))
    : p2331 ∨ (¬ p2797) ∨ p2630 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45758 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92156 (p2241 p2630 p2727 p2797 p2810 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h44901 : (¬ p2241) ∨ (¬ p2727) ∨ (¬ p2797) ∨ (¬ p2810))
    : (¬ p2727) ∨ (¬ p2241) ∨ p2630 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44901 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92159 (p2177 p2264 p2299 p2630 p2797 p2810 p4156 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73316 : p2810 ∨ p2630)
    (h47959 : (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p4156))
    : (¬ p2264) ∨ (¬ p4156) ∨ p2177 ∨ p2630 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47959 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92160 (p2295 p2630 p2651 p2797 p2810 p4117 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h46478 : (¬ p2295) ∨ (¬ p2651) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p4117))
    : (¬ p2295) ∨ (¬ p2797) ∨ (¬ p2651) ∨ (¬ p4117) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46478 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92162 (p2331 p2630 p2797 p2807 p2810 p2963 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73316 : p2810 ∨ p2630)
    (h47113 : (¬ p2797) ∨ (¬ p2807) ∨ (¬ p2810) ∨ (¬ p2963))
    : p2331 ∨ (¬ p2797) ∨ (¬ p2807) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47113 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92165 (p2331 p2598 p2797 p2963 p4752 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h67105 : (¬ p2797) ∨ (¬ p2598) ∨ (¬ p4752) ∨ (¬ p2963))
    : p2331 ∨ (¬ p2797) ∨ (¬ p4752) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h67105 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92166 (p2630 p2668 p2797 p2810 p3923 p4245 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h43475 : (¬ p2668) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3923) ∨ (¬ p4245))
    : (¬ p2668) ∨ (¬ p2797) ∨ (¬ p3923) ∨ p2630 ∨ (¬ p4245) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43475 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92168 (p2493 p2499 p2630 p2797 p2810 p3984 p4811 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73316 : p2810 ∨ p2630)
    (h43141 : (¬ p2499) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3984) ∨ (¬ p4811))
    : (¬ p2797) ∨ (¬ p4811) ∨ p2493 ∨ p2630 ∨ (¬ p3984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43141 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92170 (p2668 p2696 p2753 p2797 p3093 p3309 p3379 p3549 p3591 p4405 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73406 : p3549 ∨ p3309)
    (h71942 : (¬ p3549) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p2696) ∨ (¬ p4405) ∨ (¬ p2668) ∨ (¬ p2797) ∨ (¬ p2753))
    : p3093 ∨ (¬ p2797) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p4405) ∨ p3309 ∨ (¬ p2668) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h71942 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step92172 (p2696 p2753 p2761 p2797 p3051 p3246 p3556 p3645 p3690 p4228 p4381 p4877 p5250 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73414 : p3556 ∨ p3051)
    (h73446 : p3690 ∨ p3246)
    (h50768 : (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3690) ∨ (¬ p4228) ∨ (¬ p4381) ∨ (¬ p4877) ∨ (¬ p5250))
    : (¬ p4228) ∨ p2761 ∨ p3051 ∨ (¬ p5250) ∨ (¬ p2696) ∨ (¬ p3645) ∨ p3246 ∨ (¬ p2753) ∨ (¬ p4877) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h50768 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step92176 (p2341 p2417 p2696 p2753 p2797 p2911 p3323 p3546 p3551 p4278 p4621 p4796 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73408 : p3551 ∨ p2341)
    (h50620 : (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p2911) ∨ (¬ p3323) ∨ (¬ p3546) ∨ (¬ p3551) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4796))
    : (¬ p2911) ∨ p2417 ∨ (¬ p2696) ∨ (¬ p3323) ∨ (¬ p3546) ∨ (¬ p4796) ∨ p2341 ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p4621) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3546 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4796 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h50620 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step92177 (p2459 p2696 p2797 p3323 p3399 p3527 p3548 p4330 p4348 p4366 p4733 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73562 : p4348 ∨ p2459)
    (h73404 : p3548 ∨ p3527)
    (h50766 : (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3548) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4733))
    : (¬ p2797) ∨ p3399 ∨ (¬ p3323) ∨ p2459 ∨ (¬ p4733) ∨ (¬ p4330) ∨ (¬ p2696) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50766 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step92179 (p2417 p2696 p2753 p2761 p2797 p3347 p3389 p3540 p4228 p4278 p4381 p5250 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73574 : p4381 ∨ p2761)
    (h73402 : p3540 ∨ p3389)
    (h71945 : (¬ p4228) ∨ (¬ p5250) ∨ (¬ p2797) ∨ (¬ p3347) ∨ (¬ p4278) ∨ (¬ p2696) ∨ (¬ p4381) ∨ (¬ p3540) ∨ (¬ p2753))
    : (¬ p4228) ∨ (¬ p2753) ∨ (¬ p5250) ∨ (¬ p2797) ∨ p2417 ∨ p2761 ∨ (¬ p3347) ∨ p3389 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71945 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step92181 (p2145 p2220 p2696 p2797 p3146 p3266 p3692 p4120 p4228 p4444 p5250 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73522 : p4120 ∨ p2220)
    (h73448 : p3692 ∨ p3146)
    (h62203 : (¬ p2145) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4228) ∨ (¬ p4444) ∨ (¬ p5250))
    : (¬ p4228) ∨ p3266 ∨ p2220 ∨ (¬ p2145) ∨ (¬ p2797) ∨ (¬ p5250) ∨ p3146 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h62203 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step92183 (p2284 p2331 p2797 p2963 p3136 p3952 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73338 : p2963 ∨ p2331)
    (h73496 : p3952 ∨ p2284)
    (h57683 : (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3952) ∨ (¬ p4315))
    : p3136 ∨ (¬ p2797) ∨ p2331 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57683 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92184 (p2331 p2797 p2963 p3136 p3156 p3497 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73400 : p3497 ∨ p3156)
    (h73338 : p2963 ∨ p2331)
    (h45293 : (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3497) ∨ (¬ p4315))
    : p3136 ∨ (¬ p2797) ∨ p3156 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45293 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92187 (p2797 p3136 p3319 p3323 p4026 p4315 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h73550 : p4315 ∨ p3136)
    (h59910 : (¬ p2797) ∨ (¬ p3323) ∨ (¬ p4026) ∨ (¬ p4315))
    : (¬ p3323) ∨ p3319 ∨ p3136 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h59910 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92190 (p2363 p2383 p2797 p3136 p3567 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h47112 : (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p4315))
    : (¬ p3567) ∨ (¬ p2383) ∨ p3136 ∨ (¬ p2797) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47112 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92191 (p2274 p2307 p2797 p3097 p3136 p3567 p4315 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73550 : p4315 ∨ p3136)
    (h47106 : (¬ p2307) ∨ (¬ p2797) ∨ (¬ p3097) ∨ (¬ p3567) ∨ (¬ p4315))
    : (¬ p3567) ∨ (¬ p2307) ∨ (¬ p2797) ∨ p2274 ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47106 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92195 (p2797 p3115 p3136 p3986 p4208 p4315 p5043 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73550 : p4315 ∨ p3136)
    (h54894 : (¬ p2797) ∨ (¬ p3986) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p5043))
    : p3115 ∨ (¬ p5043) ∨ (¬ p3986) ∨ (¬ p2797) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54894 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92197 (p2651 p2657 p2685 p2797 p2807 p3572 p4975 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h73288 : p2657 ∨ p2651)
    (h50140 : (¬ p2657) ∨ (¬ p2797) ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p4975))
    : (¬ p4975) ∨ (¬ p2797) ∨ p2685 ∨ (¬ p2807) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4975 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50140 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step92198 (p2132 p2138 p2696 p2797 p4316 p4566 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h62478 : (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p4316) ∨ (¬ p4566))
    : (¬ p4316) ∨ p2132 ∨ (¬ p2797) ∨ (¬ p4566) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4316 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4566 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62478 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92202 (p2630 p2651 p2668 p2797 p2810 p4117 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h46484 : (¬ p2651) ∨ (¬ p2668) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p4117))
    : (¬ p2668) ∨ (¬ p2797) ∨ p2630 ∨ (¬ p2651) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46484 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92204 (p2459 p2470 p2476 p2528 p2534 p2668 p2696 p2797 p4133 p4729 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h50588 : (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p4133) ∨ (¬ p4729))
    : (¬ p2668) ∨ p2528 ∨ (¬ p4729) ∨ (¬ p2696) ∨ (¬ p2797) ∨ p2470 ∨ (¬ p2459) ∨ (¬ p4133) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50588 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step92205 (p2166 p2641 p2797 p3156 p3497 p4154 p4365 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73400 : p3497 ∨ p3156)
    (h45694 : (¬ p2166) ∨ (¬ p2797) ∨ (¬ p3497) ∨ (¬ p4154) ∨ (¬ p4365))
    : p2641 ∨ (¬ p4365) ∨ (¬ p2797) ∨ p3156 ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45694 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92206 (p2459 p2696 p2753 p2797 p2881 p3051 p3323 p3556 p3570 p3645 p4330 p4348 p4877 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73418 : p3570 ∨ p2881)
    (h73414 : p3556 ∨ p3051)
    (h50622 : (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3645) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4877))
    : p2459 ∨ p2881 ∨ p3051 ∨ (¬ p2696) ∨ (¬ p4877) ∨ (¬ p2753) ∨ (¬ p3323) ∨ (¬ p3645) ∨ (¬ p4330) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50622 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step92207 (p2177 p2264 p2299 p2737 p2797 p4156 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h42731 : (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p4156))
    : (¬ p2264) ∨ p2177 ∨ (¬ p4156) ∨ (¬ p2797) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42731 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92211 (p2331 p2651 p2727 p2745 p2797 p2963 p4111 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73518 : p4111 ∨ p2727)
    (h60069 : (¬ p2651) ∨ (¬ p2745) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p4111))
    : (¬ p2651) ∨ p2331 ∨ (¬ p2797) ∨ (¬ p2745) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60069 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92214 (p2386 p2493 p2499 p2630 p2797 p2810 p3567 p4811 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73316 : p2810 ∨ p2630)
    (h41249 : (¬ p2386) ∨ (¬ p2499) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3567) ∨ (¬ p4811))
    : (¬ p3567) ∨ (¬ p2797) ∨ (¬ p4811) ∨ (¬ p2386) ∨ p2493 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41249 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step92217 (p2363 p2383 p2630 p2797 p2810 p3567 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h49086 : (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3567))
    : (¬ p2383) ∨ (¬ p2363) ∨ (¬ p2797) ∨ (¬ p3567) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49086 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92219 (p2737 p2797 p2829 p3323 p3688 : Prop)
    (h73444 : p3688 ∨ p2829)
    (h44698 : (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3688))
    : (¬ p3323) ∨ p2829 ∨ (¬ p2797) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44698 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92221 (p2230 p2373 p2589 p2696 p2797 p3146 p3323 p3692 p3880 p4330 p4729 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73490 : p3880 ∨ p2373)
    (h73284 : p2589 ∨ p2230)
    (h53779 : (¬ p2589) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4330) ∨ (¬ p4729))
    : (¬ p3323) ∨ p3146 ∨ p2373 ∨ (¬ p2696) ∨ p2230 ∨ (¬ p4729) ∨ (¬ p2797) ∨ (¬ p4330) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53779 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step92223 (p2331 p2737 p2797 p2963 p4236 p4734 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h72735 : p4734)
    (h62070 : (¬ p2737) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p4236) ∨ (¬ p4734))
    : (¬ p4236) ∨ (¬ p2737) ∨ (¬ p2797) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u5 : p4734 := h72735;
    (Or.elim h62070 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92228 (p2331 p2797 p2901 p2963 p3136 p4236 p4315 p4320 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73338 : p2963 ∨ p2331)
    (h73552 : p4320 ∨ p2901)
    (h60061 : (¬ p2797) ∨ (¬ p2963) ∨ (¬ p4236) ∨ (¬ p4315) ∨ (¬ p4320))
    : p3136 ∨ (¬ p2797) ∨ (¬ p4236) ∨ p2331 ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60061 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step92231 (p2241 p2247 p2630 p2641 p2797 p2810 p4154 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73526 : p4154 ∨ p2641)
    (h73316 : p2810 ∨ p2630)
    (h54753 : (¬ p2247) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p4154))
    : p2241 ∨ p2641 ∨ p2630 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54753 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92232 (p2641 p2741 p2797 p3367 p4154 p4752 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h51599 : (¬ p2741) ∨ (¬ p2797) ∨ (¬ p3367) ∨ (¬ p4154) ∨ (¬ p4752))
    : (¬ p2741) ∨ p2641 ∨ (¬ p2797) ∨ (¬ p4752) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2741 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51599 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92235 (p2166 p2191 p2210 p2696 p2797 p3146 p3323 p3555 p3692 p4330 p4733 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73222 : p2191 ∨ p2166)
    (h73412 : p3555 ∨ p2210)
    (h50369 : (¬ p2191) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p4330) ∨ (¬ p4733))
    : (¬ p3323) ∨ p3146 ∨ (¬ p2696) ∨ p2166 ∨ (¬ p4733) ∨ (¬ p2797) ∨ (¬ p4330) ∨ p2210 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50369 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step92236 (p2295 p2696 p2797 p2911 p3399 p3527 p3548 p4366 p4712 p4733 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73404 : p3548 ∨ p3527)
    (h51522 : (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p2911) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4712) ∨ (¬ p4733))
    : (¬ p2295) ∨ (¬ p2797) ∨ (¬ p2911) ∨ (¬ p4733) ∨ p3399 ∨ (¬ p2696) ∨ p3527 ∨ (¬ p4712) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h51522 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step92237 (p2156 p2797 p2954 p3136 p3646 p3986 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73436 : p3646 ∨ p2156)
    (h59540 : (¬ p2797) ∨ (¬ p2954) ∨ (¬ p3646) ∨ (¬ p3986) ∨ (¬ p4315))
    : (¬ p3986) ∨ (¬ p2797) ∨ (¬ p2954) ∨ p3136 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3986 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59540 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92238 (p2363 p2737 p2797 p3256 p4341 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h48925 : (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3256) ∨ (¬ p4341) ∨ (¬ p4347))
    : (¬ p4341) ∨ p2363 ∨ (¬ p3256) ∨ (¬ p2737) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48925 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92242 (p2668 p2685 p2797 p2807 p3572 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h47422 : (¬ p2668) ∨ (¬ p2797) ∨ (¬ p2807) ∨ (¬ p3572))
    : (¬ p2668) ∨ (¬ p2797) ∨ p2685 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47422 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92245 (p2295 p2797 p3005 p3166 p3877 p4117 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h43296 : (¬ p2295) ∨ (¬ p2797) ∨ (¬ p3166) ∨ (¬ p3877) ∨ (¬ p4117))
    : p3005 ∨ (¬ p2295) ∨ (¬ p4117) ∨ (¬ p2797) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43296 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92246 (p2797 p3005 p3166 p3323 p3877 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h58402 : (¬ p2797) ∨ (¬ p3166) ∨ (¬ p3323) ∨ (¬ p3877))
    : p3005 ∨ (¬ p3323) ∨ (¬ p2797) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h58402 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92249 (p2298 p2383 p2685 p2797 p3567 p3572 p4405 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h48260 : (¬ p2298) ∨ (¬ p2383) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3572) ∨ (¬ p4405))
    : (¬ p2298) ∨ p2685 ∨ (¬ p2383) ∨ (¬ p4405) ∨ (¬ p2797) ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2298 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48260 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step92252 (p2797 p3323 p3654 p3946 p3983 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h71948 : (¬ p3946) ∨ (¬ p3323) ∨ (¬ p3983) ∨ (¬ p2797))
    : (¬ p3323) ∨ (¬ p3983) ∨ p3654 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71948 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step92254 (p2210 p2254 p2331 p2797 p2881 p2891 p2963 p3005 p3877 p4041 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73488 : p3877 ∨ p3005)
    (h49212 : (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2797) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p2963) ∨ (¬ p3877) ∨ (¬ p4041))
    : (¬ p2891) ∨ p2331 ∨ (¬ p2210) ∨ (¬ p4041) ∨ (¬ p2881) ∨ (¬ p2797) ∨ (¬ p2254) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49212 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step92255 (p2295 p2797 p3286 p3755 p4035 p4117 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h46108 : (¬ p2295) ∨ (¬ p2797) ∨ (¬ p3286) ∨ (¬ p4035) ∨ (¬ p4117))
    : p3755 ∨ (¬ p3286) ∨ (¬ p4117) ∨ (¬ p2797) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46108 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92256 (p2797 p3125 p3136 p3567 p3654 p3744 p4315 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73550 : p4315 ∨ p3136)
    (h59852 : (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p4315))
    : (¬ p3567) ∨ (¬ p3654) ∨ p3125 ∨ (¬ p2797) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59852 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92257 (p2298 p2685 p2797 p3567 p3572 p3654 p4624 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h63628 : (¬ p2298) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3572) ∨ (¬ p3654) ∨ (¬ p4624))
    : (¬ p3654) ∨ (¬ p2797) ∨ p2685 ∨ (¬ p2298) ∨ (¬ p3567) ∨ (¬ p4624) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h63628 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step92258 (p2497 p2797 p2922 p3319 p3567 p3654 p4026 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h60773 : (¬ p2497) ∨ (¬ p2797) ∨ (¬ p2922) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p4026))
    : (¬ p3654) ∨ (¬ p3567) ∨ (¬ p2497) ∨ (¬ p2922) ∨ p3319 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60773 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step92259 (p2352 p2797 p3564 p3567 p3654 p4137 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h46309 : (¬ p2352) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p4137))
    : (¬ p3567) ∨ (¬ p3654) ∨ (¬ p2352) ∨ p3564 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46309 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92260 (p2264 p2685 p2797 p2881 p3553 p3572 p4153 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73420 : p3572 ∨ p2685)
    (h59019 : (¬ p2797) ∨ (¬ p2881) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4153))
    : (¬ p2797) ∨ (¬ p2881) ∨ p2264 ∨ (¬ p4153) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59019 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92262 (p2088 p2363 p2630 p2797 p2810 p3567 p4114 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73316 : p2810 ∨ p2630)
    (h46967 : (¬ p2088) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3567) ∨ (¬ p4114) ∨ (¬ p4347))
    : p2363 ∨ (¬ p2088) ∨ p2630 ∨ (¬ p3567) ∨ (¬ p4114) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46967 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step92263 (p2088 p2745 p2797 p3073 p3567 p4114 p4261 p4262 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h42168 : (¬ p2088) ∨ (¬ p2745) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p4114) ∨ (¬ p4261) ∨ (¬ p4262))
    : (¬ p4114) ∨ p3073 ∨ (¬ p2088) ∨ (¬ p3567) ∨ (¬ p2745) ∨ (¬ p4262) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4114 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4262 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42168 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step92268 (p2177 p2299 p2319 p2341 p2396 p2797 p3567 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h49586 : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p2797) ∨ (¬ p3567))
    : (¬ p2396) ∨ (¬ p2341) ∨ p2177 ∨ (¬ p3567) ∨ (¬ p2319) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49586 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step92271 (p2298 p2553 p2685 p2797 p3572 p4973 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h41424 : (¬ p2298) ∨ (¬ p2553) ∨ (¬ p2797) ∨ (¬ p3572) ∨ (¬ p4973))
    : (¬ p2298) ∨ (¬ p2797) ∨ (¬ p4973) ∨ (¬ p2553) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2298 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41424 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92272 (p2264 p2331 p2797 p2807 p2963 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h45695 : (¬ p2264) ∨ (¬ p2797) ∨ (¬ p2807) ∨ (¬ p2963))
    : p2331 ∨ (¬ p2797) ∨ (¬ p2807) ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45695 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92276 (p2331 p2363 p2797 p2963 p3166 p4417 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h46537 : (¬ p2363) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p4417))
    : (¬ p4417) ∨ p2331 ∨ (¬ p3166) ∨ (¬ p2363) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46537 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step92277 (p2331 p2449 p2797 p2807 p2963 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h45403 : (¬ p2449) ∨ (¬ p2797) ∨ (¬ p2807) ∨ (¬ p2963))
    : p2331 ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45403 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92278 (p2331 p2797 p2963 p3286 p3461 p4367 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h46544 : (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3286) ∨ (¬ p3461) ∨ (¬ p4367))
    : (¬ p3286) ∨ (¬ p4367) ∨ p2331 ∨ (¬ p2797) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46544 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92281 (p2331 p2630 p2797 p2810 p2963 p3286 p5177 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73338 : p2963 ∨ p2331)
    (h54366 : (¬ p2797) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3286) ∨ (¬ p5177))
    : (¬ p3286) ∨ (¬ p5177) ∨ p2630 ∨ p2331 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54366 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92283 (p2797 p3125 p3297 p3755 p4035 p4564 p5379 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h52029 : (¬ p2797) ∨ (¬ p3125) ∨ (¬ p3297) ∨ (¬ p4035) ∨ (¬ p4564) ∨ (¬ p5379))
    : p3755 ∨ (¬ p3297) ∨ (¬ p5379) ∨ (¬ p4564) ∨ (¬ p3125) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p3297 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h52029 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step92293 (p2177 p2319 p2797 p2946 p2952 p3115 p3567 p4063 p4208 p4260 p4322 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73534 : p4208 ∨ p3115)
    (h71949 : (¬ p4063) ∨ (¬ p4260) ∨ (¬ p2797) ∨ (¬ p2952) ∨ (¬ p2177) ∨ (¬ p2319) ∨ (¬ p4322) ∨ (¬ p4208) ∨ (¬ p3567))
    : (¬ p4260) ∨ (¬ p4063) ∨ (¬ p2797) ∨ p2946 ∨ (¬ p2177) ∨ (¬ p2319) ∨ (¬ p4322) ∨ p3115 ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4260 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71949 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step92294 (p2685 p2797 p3572 p4075 p4391 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h47415 : (¬ p2797) ∨ (¬ p3572) ∨ (¬ p4075) ∨ (¬ p4391))
    : (¬ p4075) ∨ (¬ p4391) ∨ p2685 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4075 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47415 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step92295 (p2608 p2685 p2797 p3037 p3399 p3572 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73420 : p3572 ∨ p2685)
    (h44473 : (¬ p2797) ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p3572) ∨ (¬ p3954))
    : (¬ p3037) ∨ p2608 ∨ p2685 ∨ (¬ p3399) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3037 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44473 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92296 (p2241 p2685 p2797 p2996 p3027 p3572 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73420 : p3572 ∨ p2685)
    (h54991 : (¬ p2241) ∨ (¬ p2797) ∨ (¬ p3027) ∨ (¬ p3572))
    : p2996 ∨ (¬ p2241) ∨ (¬ p2797) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2996) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54991 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92300 (p2797 p3297 p3319 p3755 p4035 p4761 p5379 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h62655 : (¬ p2797) ∨ (¬ p3297) ∨ (¬ p3319) ∨ (¬ p4035) ∨ (¬ p4761) ∨ (¬ p5379))
    : p3755 ∨ (¬ p3319) ∨ (¬ p3297) ∨ (¬ p5379) ∨ (¬ p4761) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3297 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h62655 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step92302 (p2608 p2797 p3755 p3830 p3853 p3954 p4035 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h73498 : p3954 ∨ p2608)
    (h47488 : (¬ p2797) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p3954) ∨ (¬ p4035))
    : (¬ p3830) ∨ (¬ p3853) ∨ p3755 ∨ p2608 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47488 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92304 (p2737 p2797 p3367 p3585 p4343 p4975 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h48071 : (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4975))
    : (¬ p2797) ∨ (¬ p2737) ∨ p3367 ∨ (¬ p4975) ∨ (¬ p4343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48071 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92309 (p2373 p2427 p2608 p3051 p3093 p3370 p3591 p3923 p4235 p4377 p4433 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73536 : p4235 ∨ p2427)
    (h42100 : (¬ p2373) ∨ (¬ p2608) ∨ (¬ p3051) ∨ (¬ p3370) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4235) ∨ (¬ p4377) ∨ (¬ p4433))
    : (¬ p3051) ∨ p3093 ∨ (¬ p3370) ∨ p2427 ∨ (¬ p2608) ∨ (¬ p3923) ∨ (¬ p4377) ∨ (¬ p2373) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42100 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step92313 (p2459 p2630 p2696 p2810 p2881 p3051 p3343 p3359 p3365 p3366 p3370 p4377 p4697 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73388 : p3359 ∨ p3343)
    (h73390 : p3365 ∨ p2696)
    (h42414 : (¬ p2459) ∨ (¬ p2810) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3359) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p4377) ∨ (¬ p4697))
    : (¬ p2881) ∨ (¬ p3051) ∨ p2630 ∨ (¬ p2459) ∨ (¬ p3370) ∨ (¬ p3366) ∨ (¬ p4697) ∨ (¬ p4377) ∨ p3343 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u12 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h42414 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step92314 (p2187 p2383 p2417 p2598 p2962 p3055 p3125 p3201 p3366 p3370 p3876 p3989 p4278 p4377 p4621 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73350 : p3055 ∨ p2598)
    (h73502 : p3989 ∨ p2187)
    (h73486 : p3876 ∨ p3201)
    (h63548 : (¬ p2383) ∨ (¬ p2962) ∨ (¬ p3055) ∨ (¬ p3125) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3876) ∨ (¬ p3989) ∨ (¬ p4278) ∨ (¬ p4377) ∨ (¬ p4621))
    : p2417 ∨ (¬ p3125) ∨ (¬ p4377) ∨ (¬ p2962) ∨ (¬ p3366) ∨ p2598 ∨ p2187 ∨ (¬ p3370) ∨ p3201 ∨ (¬ p4621) ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u14 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h63548 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u14))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step92316 (p2156 p2187 p2363 p2630 p2696 p2810 p3276 p3343 p3359 p3365 p3366 p3370 p4377 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73316 : p2810 ∨ p2630)
    (h73390 : p3365 ∨ p2696)
    (h73388 : p3359 ∨ p3343)
    (h47110 : (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2810) ∨ (¬ p3359) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p4377) ∨ (¬ p4425))
    : p3276 ∨ (¬ p3370) ∨ p2630 ∨ p2696 ∨ (¬ p4377) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3366) ∨ (¬ p2156) ∨ p3343 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h47110 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u10)))))))))))))))))))))

theorem step92318 (p2156 p2563 p2696 p2982 p3005 p3256 p3365 p3366 p3370 p3877 p4110 p4118 p4330 p4377 p5045 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73390 : p3365 ∨ p2696)
    (h73516 : p4110 ∨ p2563)
    (h73488 : p3877 ∨ p3005)
    (h64698 : (¬ p2156) ∨ (¬ p2982) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3877) ∨ (¬ p4110) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4377) ∨ (¬ p5045))
    : p3256 ∨ (¬ p3370) ∨ (¬ p3366) ∨ (¬ p4377) ∨ (¬ p5045) ∨ (¬ p2982) ∨ (¬ p4330) ∨ p2696 ∨ (¬ p2156) ∨ p2563 ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u14 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h64698 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u14))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (False.elim (r9 u4)))))))))))))))))))))))

theorem step92319 (p2891 p3051 p3370 p3486 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h5055 : (¬ p3051) ∨ (¬ p3370) ∨ (¬ p3486))
    : (¬ p3051) ∨ (¬ p3370) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h5055 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step92320 (p2459 p2696 p2797 p2881 p3051 p3323 p3365 p3366 p3370 p4037 p4195 p4377 p4604 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73390 : p3365 ∨ p2696)
    (h73508 : p4037 ∨ p3323)
    (h63547 : (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4377) ∨ (¬ p4604))
    : (¬ p3051) ∨ (¬ p2881) ∨ (¬ p4604) ∨ (¬ p3366) ∨ (¬ p4377) ∨ p2797 ∨ p2696 ∨ (¬ p2459) ∨ p3323 ∨ (¬ p3370) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h63547 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step92323 (p2901 p3051 p3370 p3412 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h40597 : (¬ p3051) ∨ (¬ p3370) ∨ (¬ p3412) ∨ (¬ p4320))
    : (¬ p3370) ∨ (¬ p3412) ∨ p2901 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3370 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h40597 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92327 (p2156 p2187 p2352 p2590 p3370 p3956 p4632 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h62917 : (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2590) ∨ (¬ p3370) ∨ (¬ p3956) ∨ (¬ p4632))
    : (¬ p3370) ∨ (¬ p2187) ∨ (¬ p2156) ∨ p2352 ∨ (¬ p2590) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3370 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62917 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step92330 (p3461 p3707 p3923 p4025 p4191 p5153 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h71950 : (¬ p4191) ∨ (¬ p3707) ∨ (¬ p4025) ∨ (¬ p5153) ∨ (¬ p3923))
    : (¬ p3707) ∨ p3461 ∨ (¬ p3923) ∨ (¬ p5153) ∨ (¬ p4025) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71950 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92337 (p2132 p2138 p2727 p2946 p4111 p4117 p4243 p4365 p4704 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73214 : p2138 ∨ p2132)
    (h73046 : p4704)
    (h48125 : (¬ p2138) ∨ (¬ p2946) ∨ (¬ p4111) ∨ (¬ p4117) ∨ (¬ p4243) ∨ (¬ p4365) ∨ (¬ p4704))
    : p2727 ∨ (¬ p4243) ∨ p2132 ∨ (¬ p4117) ∨ (¬ p2946) ∨ (¬ p4365) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4704 := h73046;
    (Or.elim h48125 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u8)))))))))))))))

theorem step92341 (p2210 p2248 p2807 p2996 p3555 p4365 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h48546 : (¬ p2248) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p3555) ∨ (¬ p4365))
    : (¬ p2996) ∨ p2210 ∨ (¬ p2807) ∨ (¬ p4365) ∨ (¬ p2248) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48546 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92342 (p2284 p2901 p3125 p3319 p3744 p3952 p4338 p4365 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73496 : p3952 ∨ p2284)
    (h44509 : (¬ p2901) ∨ (¬ p3319) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4338) ∨ (¬ p4365))
    : (¬ p3319) ∨ p3125 ∨ (¬ p4338) ∨ (¬ p2901) ∨ (¬ p4365) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h44509 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step92344 (p2166 p2241 p3016 p3156 p3497 p4365 p4700 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h44926 : (¬ p2166) ∨ (¬ p2241) ∨ (¬ p3016) ∨ (¬ p3497) ∨ (¬ p4365) ∨ (¬ p4700))
    : (¬ p4365) ∨ p3156 ∨ (¬ p4700) ∨ (¬ p3016) ∨ (¬ p2241) ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4365 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44926 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step92347 (p2573 p2579 p2744 p2761 p3212 p3347 p3370 p3422 p3680 p4257 p4365 p4381 p4641 p5160 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73574 : p4381 ∨ p2761)
    (h53476 : (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3212) ∨ (¬ p3347) ∨ (¬ p3370) ∨ (¬ p3422) ∨ (¬ p3680) ∨ (¬ p4257) ∨ (¬ p4365) ∨ (¬ p4381) ∨ (¬ p4641) ∨ (¬ p5160))
    : (¬ p5160) ∨ (¬ p4641) ∨ (¬ p4365) ∨ (¬ p2744) ∨ (¬ p3370) ∨ p2573 ∨ (¬ p3422) ∨ (¬ p3347) ∨ (¬ p4257) ∨ (¬ p3680) ∨ (¬ p3212) ∨ p2761 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5160 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u11 r0))));
    (Or.elim h53476 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u13))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u1))) (fun r10 => (False.elim (r10 u0)))))))))))))))))))))))))

theorem step92350 (p2156 p2192 p2901 p3051 p3646 p4320 p4365 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73552 : p4320 ∨ p2901)
    (h57723 : (¬ p2192) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4320) ∨ (¬ p4365))
    : (¬ p2192) ∨ (¬ p4365) ∨ p2156 ∨ p2901 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57723 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92355 (p2187 p2331 p2963 p3166 p3989 p4318 p4560 p5074 : Prop)
    (h72955 : p4560)
    (h73338 : p2963 ∨ p2331)
    (h73502 : p3989 ∨ p2187)
    (h41306 : (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3989) ∨ (¬ p4318) ∨ (¬ p4560) ∨ (¬ p5074))
    : (¬ p4318) ∨ (¬ p5074) ∨ p2331 ∨ p2187 ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5074 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4560 := h72955;
    let u6 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41306 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step92358 (p2819 p3093 p3449 p3591 p4318 p4358 p4871 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73564 : p4358 ∨ p2819)
    (h42275 : (¬ p3449) ∨ (¬ p3591) ∨ (¬ p4318) ∨ (¬ p4358) ∨ (¬ p4871))
    : p3093 ∨ (¬ p3449) ∨ p2819 ∨ (¬ p4871) ∨ (¬ p4318) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4871 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42275 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92366 (p2668 p3093 p3324 p3449 p3591 p4318 p4761 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73386 : p3324 ∨ p2668)
    (h42555 : (¬ p3324) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p4318) ∨ (¬ p4761))
    : (¬ p4318) ∨ p3093 ∨ (¬ p4761) ∨ p2668 ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42555 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92372 (p2210 p2528 p2534 p2651 p2657 p3083 p3366 p3449 p3555 p3979 p4236 p4256 p4318 p4377 p5122 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73268 : p2534 ∨ p2528)
    (h73542 : p4256 ∨ p3083)
    (h73288 : p2657 ∨ p2651)
    (h51163 : (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p3979) ∨ (¬ p4236) ∨ (¬ p4256) ∨ (¬ p4318) ∨ (¬ p4377) ∨ (¬ p5122))
    : p2210 ∨ (¬ p4377) ∨ (¬ p4236) ∨ (¬ p3366) ∨ (¬ p3979) ∨ (¬ p3449) ∨ p2528 ∨ (¬ p4318) ∨ (¬ p5122) ∨ p3083 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u14 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h51163 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u1))) (fun r9 => (False.elim (r9 u8)))))))))))))))))))))))

theorem step92373 (p2352 p2507 p3093 p3449 p3591 p3956 p4318 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73500 : p3956 ∨ p2352)
    (h42538 : (¬ p2507) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p3956) ∨ (¬ p4318))
    : (¬ p4318) ∨ p3093 ∨ p2352 ∨ (¬ p2507) ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42538 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step92375 (p2363 p3093 p3266 p3449 p3591 p4318 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h54872 : (¬ p2363) ∨ (¬ p3266) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p4318))
    : p3093 ∨ (¬ p3449) ∨ (¬ p3266) ∨ (¬ p4318) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h54872 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92376 (p2363 p2598 p2850 p2982 p3055 p3093 p3366 p3449 p3591 p3684 p4318 p4866 p4948 p5059 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73442 : p3684 ∨ p2850)
    (h73350 : p3055 ∨ p2598)
    (h73846 : p4948 ∨ p2982)
    (h63416 : (¬ p2363) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p3684) ∨ (¬ p4318) ∨ (¬ p4866) ∨ (¬ p4948) ∨ (¬ p5059))
    : (¬ p4318) ∨ p3093 ∨ (¬ p3449) ∨ (¬ p5059) ∨ (¬ p3366) ∨ p2850 ∨ (¬ p4866) ∨ p2598 ∨ (¬ p2363) ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h63416 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step92378 (p2284 p3156 p3497 p3952 p3988 : Prop)
    (h73399 : (¬ p3156) ∨ (¬ p3497))
    (h73496 : p3952 ∨ p2284)
    (h38879 : p3497 ∨ (¬ p3952) ∨ (¬ p3988))
    : (¬ p3156) ∨ p2284 ∨ (¬ p3988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3497) := (Or.elim h73399 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h38879 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u2)))))))

theorem step92379 (p2156 p2957 p3156 p3497 p3646 p3988 : Prop)
    (h73399 : (¬ p3156) ∨ (¬ p3497))
    (h73436 : p3646 ∨ p2156)
    (h27893 : (¬ p2957) ∨ p3497 ∨ (¬ p3646) ∨ (¬ p3988))
    : (¬ p3156) ∨ (¬ p2957) ∨ (¬ p3988) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3497) := (Or.elim h73399 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h27893 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step92383 (p2156 p2220 p3646 p3988 p4120 : Prop)
    (h73521 : (¬ p2220) ∨ (¬ p4120))
    (h73436 : p3646 ∨ p2156)
    (h6524 : (¬ p3646) ∨ (¬ p3988) ∨ p4120)
    : (¬ p2220) ∨ p2156 ∨ (¬ p3988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4120) := (Or.elim h73521 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h6524 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u3 r1)))))))

theorem step92389 (p2274 p2363 p3146 p3692 p3988 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h71951 : (¬ p3988) ∨ (¬ p3692) ∨ (¬ p2363) ∨ (¬ p2274))
    : (¬ p2274) ∨ p3146 ∨ (¬ p2363) ∨ (¬ p3988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71951 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step92390 (p2284 p2363 p2946 p2952 p3146 p3692 p3952 p3988 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73330 : p2952 ∨ p2946)
    (h73496 : p3952 ∨ p2284)
    (h46499 : (¬ p2363) ∨ (¬ p2952) ∨ (¬ p3692) ∨ (¬ p3952) ∨ (¬ p3988))
    : p3146 ∨ p2946 ∨ (¬ p3988) ∨ (¬ p2363) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46499 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92391 (p2427 p2528 p3146 p3692 p3988 p4235 p4355 p4555 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73536 : p4235 ∨ p2427)
    (h63828 : (¬ p2528) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4235) ∨ (¬ p4355) ∨ (¬ p4555))
    : (¬ p4355) ∨ p3146 ∨ (¬ p2528) ∨ (¬ p4555) ∨ p2427 ∨ (¬ p3988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63828 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step92392 (p2373 p2563 p3988 p4110 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h6535 : (¬ p2373) ∨ (¬ p3988) ∨ (¬ p4110))
    : (¬ p2373) ∨ p2563 ∨ (¬ p3988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h6535 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step92398 (p2156 p2528 p3146 p3646 p3692 p3741 p3875 p3988 p4533 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73436 : p3646 ∨ p2156)
    (h55413 : (¬ p2528) ∨ (¬ p3646) ∨ (¬ p3692) ∨ (¬ p3741) ∨ (¬ p3875) ∨ (¬ p3988) ∨ (¬ p4533))
    : (¬ p2528) ∨ p3146 ∨ (¬ p3875) ∨ p2156 ∨ (¬ p3988) ∨ (¬ p4533) ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55413 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step92401 (p2363 p2563 p3979 p3988 p4110 p4347 p5568 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73516 : p4110 ∨ p2563)
    (h55866 : (¬ p3979) ∨ (¬ p3988) ∨ (¬ p4110) ∨ (¬ p4347) ∨ (¬ p5568))
    : (¬ p3979) ∨ (¬ p5568) ∨ p2363 ∨ (¬ p3988) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55866 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92404 (p2187 p2352 p2528 p3146 p3692 p3988 p3989 p4597 p4718 : Prop)
    (h73658 : p4597 ∨ (¬ p2352))
    (h73448 : p3692 ∨ p3146)
    (h73502 : p3989 ∨ p2187)
    (h67123 : (¬ p4597) ∨ (¬ p3692) ∨ (¬ p2528) ∨ (¬ p4718) ∨ (¬ p3988) ∨ (¬ p3989))
    : (¬ p2528) ∨ (¬ p2352) ∨ p3146 ∨ (¬ p3988) ∨ (¬ p4718) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4597 := (Or.elim h73658 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u7 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h67123 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u8)))))))))))))

theorem step92414 (p2187 p4505 p4506 : Prop)
    (h73606 : p4505 ∨ p2187)
    (h7072 : (¬ p4505) ∨ p4506)
    : p2187 ∨ p4506 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2187) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4506) := (fun h => hn (Or.inr h));
    let u2 : p4505 := (Or.elim h73606 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7072 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step92415 (p2187 p4506 p5800 : Prop)
    (h74077 : p2187 ∨ (¬ p5800))
    (h11800 : p4506 ∨ p5800)
    : p4506 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4506) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2187) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5800) := (Or.elim h74077 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11800 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step92417 (p2459 p3945 p5864 : Prop)
    (h74163 : (¬ p2459) ∨ (¬ p5864))
    (h12175 : p3945 ∨ p5864)
    : p3945 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3945) := (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5864) := (Or.elim h74163 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12175 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step92424 (p2156 p2440 p2542 p2860 p3054 p3758 p4109 p4750 : Prop)
    (h73456 : p3758 ∨ p2860)
    (h73270 : p2542 ∨ p2440)
    (h62528 : (¬ p2156) ∨ (¬ p2542) ∨ (¬ p3054) ∨ (¬ p3758) ∨ (¬ p4109) ∨ (¬ p4750))
    : p2860 ∨ p2440 ∨ (¬ p2156) ∨ (¬ p4750) ∨ (¬ p4109) ∨ (¬ p3054) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2860) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3054 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62528 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step92429 (p2210 p2608 p2972 p3266 p3276 p3346 p3347 p3954 p4425 p4450 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73498 : p3954 ∨ p2608)
    (h71955 : (¬ p4425) ∨ (¬ p3266) ∨ (¬ p4450) ∨ (¬ p3346) ∨ (¬ p3954) ∨ (¬ p2972) ∨ (¬ p2210) ∨ (¬ p3347))
    : p3276 ∨ p2608 ∨ (¬ p4450) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p2972) ∨ (¬ p2210) ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71955 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step92432 (p2230 p2246 p2373 p2589 p2685 p2749 p2807 p3005 p3146 p3347 p3572 p3692 p3880 p4009 p5122 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73490 : p3880 ∨ p2373)
    (h73284 : p2589 ∨ p2230)
    (h73420 : p3572 ∨ p2685)
    (h71958 : (¬ p3005) ∨ (¬ p4009) ∨ (¬ p2246) ∨ (¬ p3880) ∨ (¬ p5122) ∨ (¬ p2589) ∨ (¬ p3347) ∨ (¬ p2807) ∨ (¬ p2749) ∨ (¬ p3572) ∨ (¬ p3692))
    : (¬ p4009) ∨ (¬ p3005) ∨ (¬ p2246) ∨ p3146 ∨ p2373 ∨ p2230 ∨ (¬ p3347) ∨ (¬ p2807) ∨ (¬ p5122) ∨ (¬ p2749) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u14 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h71958 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u14))) (fun r9 => (False.elim (r9 u11)))))))))))))))))))))))

theorem step92444 (p2156 p2220 p2284 p3146 p3692 p3952 p4120 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73496 : p3952 ∨ p2284)
    (h73448 : p3692 ∨ p3146)
    (h54654 : (¬ p2156) ∨ (¬ p3692) ∨ (¬ p3952) ∨ (¬ p4120))
    : p2220 ∨ p2284 ∨ p3146 ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54654 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92445 (p2166 p2220 p2274 p2307 p2962 p3097 p4120 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73522 : p4120 ∨ p2220)
    (h56964 : (¬ p2166) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p4120))
    : (¬ p2307) ∨ p2274 ∨ (¬ p2962) ∨ (¬ p2166) ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56964 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92446 (p2156 p2220 p2363 p2563 p4110 p4120 p4347 p4506 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73516 : p4110 ∨ p2563)
    (h73522 : p4120 ∨ p2220)
    (h45259 : (¬ p2156) ∨ (¬ p4110) ∨ (¬ p4120) ∨ (¬ p4347) ∨ (¬ p4506))
    : (¬ p2156) ∨ p2363 ∨ (¬ p4506) ∨ p2563 ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45259 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92447 (p2156 p2220 p2274 p2619 p4120 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h43634 : (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2619) ∨ (¬ p4120))
    : p2220 ∨ (¬ p2274) ∨ (¬ p2619) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43634 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92448 (p2177 p2220 p2459 p3146 p3692 p4120 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73522 : p4120 ∨ p2220)
    (h42779 : (¬ p2177) ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4120))
    : (¬ p2177) ∨ p3146 ∨ (¬ p2459) ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42779 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92449 (p2220 p2373 p2427 p3246 p3690 p3904 p4120 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73446 : p3690 ∨ p3246)
    (h73522 : p4120 ∨ p2220)
    (h44632 : (¬ p2373) ∨ (¬ p3690) ∨ (¬ p3904) ∨ (¬ p4120) ∨ (¬ p4235))
    : (¬ p2373) ∨ p2427 ∨ p3246 ∨ (¬ p3904) ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44632 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92451 (p2156 p2220 p2363 p3146 p3692 p4120 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73448 : p3692 ∨ p3146)
    (h47448 : (¬ p2156) ∨ (¬ p2363) ∨ (¬ p3692) ∨ (¬ p4120))
    : p2220 ∨ p3146 ∨ (¬ p2156) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47448 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92452 (p2192 p2220 p2459 p3146 p3645 p3692 p4120 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73448 : p3692 ∨ p3146)
    (h46098 : (¬ p2192) ∨ (¬ p2459) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p4120))
    : p2220 ∨ (¬ p3645) ∨ p3146 ∨ (¬ p2192) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46098 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92453 (p2156 p2220 p2459 p3146 p3692 p4120 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73448 : p3692 ∨ p3146)
    (h62775 : (¬ p2156) ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4120))
    : p2220 ∨ p3146 ∨ (¬ p2156) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62775 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92454 (p2177 p2220 p3051 p4120 p4132 p4556 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h53698 : (¬ p2177) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4132) ∨ (¬ p4556))
    : (¬ p3051) ∨ (¬ p4556) ∨ (¬ p4132) ∨ p2220 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53698 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92456 (p2220 p2911 p3051 p4120 p4132 p4647 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h49732 : (¬ p2911) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4132) ∨ (¬ p4647))
    : (¬ p3051) ∨ (¬ p2911) ∨ (¬ p4132) ∨ p2220 ∨ (¬ p4647) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49732 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92458 (p2220 p2954 p3146 p3256 p3692 p4120 p4237 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73522 : p4120 ∨ p2220)
    (h42085 : (¬ p2954) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4237))
    : (¬ p4237) ∨ (¬ p3256) ∨ p3146 ∨ p2220 ∨ (¬ p2954) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4237 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42085 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step92460 (p2156 p2166 p2220 p2274 p4120 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h47084 : (¬ p2156) ∨ (¬ p2166) ∨ (¬ p2274) ∨ (¬ p4120))
    : p2220 ∨ (¬ p2274) ∨ (¬ p2156) ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47084 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92463 (p2220 p2891 p3051 p3156 p3486 p4120 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73398 : p3486 ∨ p2891)
    (h47195 : (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3486) ∨ (¬ p4120))
    : (¬ p3051) ∨ p2220 ∨ (¬ p3156) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47195 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92465 (p2156 p2220 p2284 p2363 p3952 p4120 p4347 p4506 p4700 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73496 : p3952 ∨ p2284)
    (h73522 : p4120 ∨ p2220)
    (h47481 : (¬ p2156) ∨ (¬ p3952) ∨ (¬ p4120) ∨ (¬ p4347) ∨ (¬ p4506) ∨ (¬ p4700))
    : p2363 ∨ p2284 ∨ p2220 ∨ (¬ p4506) ∨ (¬ p2156) ∨ (¬ p4700) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47481 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step92466 (p2220 p2363 p2532 p3212 p4120 p4134 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73522 : p4120 ∨ p2220)
    (h63207 : (¬ p2532) ∨ (¬ p3212) ∨ (¬ p4120) ∨ (¬ p4134) ∨ (¬ p4347))
    : p2363 ∨ (¬ p3212) ∨ p2220 ∨ (¬ p4134) ∨ (¬ p2532) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h63207 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92473 (p2220 p2528 p2532 p2534 p3212 p4120 p4158 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73522 : p4120 ∨ p2220)
    (h55197 : (¬ p2532) ∨ (¬ p2534) ∨ (¬ p3212) ∨ (¬ p4120) ∨ (¬ p4158))
    : (¬ p3212) ∨ p2528 ∨ (¬ p4158) ∨ (¬ p2532) ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55197 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92478 (p2143 p2220 p2284 p2839 p3156 p3583 p3952 p4120 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73522 : p4120 ∨ p2220)
    (h73424 : p3583 ∨ p2839)
    (h42879 : (¬ p2143) ∨ (¬ p3156) ∨ (¬ p3583) ∨ (¬ p3952) ∨ (¬ p4120))
    : (¬ p3156) ∨ p2284 ∨ p2220 ∨ p2839 ∨ (¬ p2143) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42879 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92480 (p2220 p2459 p2532 p3212 p4120 p4348 p4905 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73522 : p4120 ∨ p2220)
    (h41132 : (¬ p2532) ∨ (¬ p3212) ∨ (¬ p4120) ∨ (¬ p4348) ∨ (¬ p4905))
    : (¬ p3212) ∨ (¬ p4905) ∨ p2459 ∨ p2220 ∨ (¬ p2532) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41132 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92481 (p2220 p2449 p3516 p3947 p3986 p4067 p4120 p4988 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73522 : p4120 ∨ p2220)
    (h69530 : (¬ p3947) ∨ (¬ p4120) ∨ (¬ p4067) ∨ (¬ p4988) ∨ (¬ p3516) ∨ (¬ p3986))
    : (¬ p3516) ∨ p2449 ∨ (¬ p4988) ∨ (¬ p4067) ∨ p2220 ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h69530 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step92483 (p2145 p2220 p2295 p2331 p2373 p2396 p2982 p3951 p4117 p4120 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73522 : p4120 ∨ p2220)
    (h42553 : (¬ p2145) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2373) ∨ (¬ p2396) ∨ (¬ p3951) ∨ (¬ p4117) ∨ (¬ p4120) ∨ (¬ p4948))
    : (¬ p2295) ∨ (¬ p2396) ∨ (¬ p2373) ∨ p2982 ∨ p2220 ∨ (¬ p4117) ∨ (¬ p2145) ∨ (¬ p2331) ∨ (¬ p3951) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42553 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step92487 (p2220 p2850 p3156 p3413 p3684 p4031 p4120 p4750 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73442 : p3684 ∨ p2850)
    (h50137 : (¬ p3156) ∨ (¬ p3413) ∨ (¬ p3684) ∨ (¬ p4031) ∨ (¬ p4120) ∨ (¬ p4750))
    : (¬ p3156) ∨ (¬ p4031) ∨ (¬ p3413) ∨ p2220 ∨ p2850 ∨ (¬ p4750) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50137 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step92488 (p2220 p2573 p3156 p3879 p3904 p4120 p4717 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h65080 : (¬ p2573) ∨ (¬ p3156) ∨ (¬ p3879) ∨ (¬ p3904) ∨ (¬ p4120) ∨ (¬ p4717))
    : (¬ p3156) ∨ p2220 ∨ (¬ p4717) ∨ (¬ p3904) ∨ (¬ p3879) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h65080 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step92489 (p2220 p2440 p3016 p4031 p4120 p4203 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h69532 : (¬ p4120) ∨ (¬ p4031) ∨ (¬ p3016) ∨ (¬ p2440) ∨ (¬ p4203))
    : (¬ p4031) ∨ p2220 ∨ (¬ p3016) ∨ (¬ p4203) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4031 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h69532 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92490 (p2220 p2284 p2901 p3051 p4120 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73522 : p4120 ∨ p2220)
    (h44225 : (¬ p2284) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4320))
    : (¬ p3051) ∨ p2901 ∨ (¬ p2284) ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44225 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92491 (p2220 p2373 p2563 p3212 p4110 p4120 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73516 : p4110 ∨ p2563)
    (h46035 : (¬ p2373) ∨ (¬ p3212) ∨ (¬ p4110) ∨ (¬ p4120))
    : (¬ p3212) ∨ p2220 ∨ p2563 ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46035 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92494 (p2220 p3212 p4120 p4335 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h20663 : (¬ p3212) ∨ (¬ p4120) ∨ (¬ p4335))
    : (¬ p3212) ∨ (¬ p4335) ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4335 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20663 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step92497 (p2220 p2532 p3212 p3609 p4120 p4340 p4742 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73522 : p4120 ∨ p2220)
    (h42540 : (¬ p2532) ∨ (¬ p3212) ∨ (¬ p4120) ∨ (¬ p4340) ∨ (¬ p4742))
    : (¬ p3212) ∨ p3609 ∨ p2220 ∨ (¬ p4742) ∨ (¬ p2532) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42540 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92498 (p2220 p2373 p2440 p2542 p2659 p3904 p4120 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73522 : p4120 ∨ p2220)
    (h40922 : (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2659) ∨ (¬ p3904) ∨ (¬ p4120))
    : p2440 ∨ p2220 ∨ (¬ p2373) ∨ (¬ p3904) ∨ (¬ p2659) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h40922 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92501 (p2220 p2373 p2957 p3880 p4120 p4241 : Prop)
    (h73489 : (¬ p2373) ∨ (¬ p3880))
    (h73522 : p4120 ∨ p2220)
    (h24502 : (¬ p2957) ∨ p3880 ∨ (¬ p4120) ∨ (¬ p4241))
    : (¬ p4241) ∨ (¬ p2957) ∨ (¬ p2373) ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3880) := (Or.elim h73489 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h24502 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step92508 (p2220 p2608 p2707 p3115 p3156 p3434 p3951 p4120 p4208 p4524 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h72962 : p4524)
    (h73522 : p4120 ∨ p2220)
    (h51884 : (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3156) ∨ (¬ p3434) ∨ (¬ p3951) ∨ (¬ p4120) ∨ (¬ p4208) ∨ (¬ p4524))
    : p3115 ∨ (¬ p3156) ∨ (¬ p2707) ∨ (¬ p2608) ∨ p2220 ∨ (¬ p3434) ∨ (¬ p3951) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4524 := h72962;
    let u9 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51884 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step92511 (p2145 p2220 p2573 p3115 p3156 p3333 p3362 p3422 p3584 p4120 p4208 p4950 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73522 : p4120 ∨ p2220)
    (h73426 : p3584 ∨ p3422)
    (h64881 : (¬ p2145) ∨ (¬ p2573) ∨ (¬ p3156) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3584) ∨ (¬ p4120) ∨ (¬ p4208) ∨ (¬ p4950))
    : (¬ p3156) ∨ p3115 ∨ (¬ p3333) ∨ p2220 ∨ (¬ p2145) ∨ (¬ p3362) ∨ p3422 ∨ (¬ p4950) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64881 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step92512 (p2220 p2252 p2598 p2750 p2753 p2950 p3115 p3156 p3422 p3564 p4120 p4208 p4368 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73534 : p4208 ∨ p3115)
    (h64812 : (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2950) ∨ (¬ p3156) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p4120) ∨ (¬ p4208) ∨ (¬ p4368))
    : (¬ p4368) ∨ (¬ p2753) ∨ p2220 ∨ (¬ p3564) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p2950) ∨ p3115 ∨ (¬ p2598) ∨ (¬ p3156) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4368 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64812 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step92520 (p2220 p2608 p3146 p3266 p3399 p3645 p3692 p3954 p4075 p4120 p4444 p4826 p4877 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73522 : p4120 ∨ p2220)
    (h73448 : p3692 ∨ p3146)
    (h73580 : p4444 ∨ p3266)
    (h49979 : (¬ p3399) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p3954) ∨ (¬ p4075) ∨ (¬ p4120) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p4877))
    : (¬ p4075) ∨ p2608 ∨ (¬ p4877) ∨ p2220 ∨ (¬ p3399) ∨ p3146 ∨ p3266 ∨ (¬ p3645) ∨ (¬ p4826) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4075 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h49979 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step92521 (p2220 p2241 p2641 p3146 p3266 p3692 p4120 p4228 p4444 p4524 p5250 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73522 : p4120 ∨ p2220)
    (h72962 : p4524)
    (h73448 : p3692 ∨ p3146)
    (h56874 : (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4228) ∨ (¬ p4444) ∨ (¬ p4524) ∨ (¬ p5250))
    : (¬ p4228) ∨ p3266 ∨ (¬ p5250) ∨ p2220 ∨ (¬ p2241) ∨ (¬ p2641) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4524 := h72962;
    let u10 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h56874 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step92523 (p2220 p2459 p2957 p2992 p3146 p3662 p3692 p4120 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73440 : p3662 ∨ p2992)
    (h73522 : p4120 ∨ p2220)
    (h43671 : (¬ p2459) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p4120))
    : p3146 ∨ p2992 ∨ (¬ p2957) ∨ p2220 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43671 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step92527 (p2220 p2255 p2331 p2957 p2992 p3319 p3461 p3662 p4120 p4319 p5123 p5568 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73440 : p3662 ∨ p2992)
    (h48501 : (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2957) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3662) ∨ (¬ p4120) ∨ (¬ p4319) ∨ (¬ p5123) ∨ (¬ p5568))
    : (¬ p5568) ∨ (¬ p5123) ∨ p2220 ∨ (¬ p2255) ∨ (¬ p4319) ∨ (¬ p3319) ∨ (¬ p2957) ∨ (¬ p2331) ∨ (¬ p3461) ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h48501 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step92530 (p2122 p2145 p2220 p2528 p2531 p2534 p2774 p3266 p3791 p4120 p4444 p4826 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73522 : p4120 ∨ p2220)
    (h73268 : p2534 ∨ p2528)
    (h55663 : (¬ p2122) ∨ (¬ p2145) ∨ (¬ p2531) ∨ (¬ p2534) ∨ (¬ p2774) ∨ (¬ p3791) ∨ (¬ p4120) ∨ (¬ p4444) ∨ (¬ p4826))
    : (¬ p3791) ∨ p3266 ∨ (¬ p2122) ∨ p2220 ∨ (¬ p4826) ∨ p2528 ∨ (¬ p2145) ∨ (¬ p2774) ∨ (¬ p2531) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55663 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step92535 (p2220 p2950 p3136 p3156 p4120 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h71960 : (¬ p4120) ∨ (¬ p2950) ∨ (¬ p3136) ∨ (¬ p3156))
    : (¬ p3156) ∨ (¬ p3136) ∨ p2220 ∨ (¬ p2950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71960 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step92536 (p2220 p2655 p3136 p3156 p3904 p4120 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h71961 : (¬ p4120) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3904) ∨ (¬ p2655))
    : (¬ p3156) ∨ (¬ p3136) ∨ (¬ p2655) ∨ p2220 ∨ (¬ p3904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71961 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92538 (p2220 p2373 p2563 p3369 p3379 p4110 p4120 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73516 : p4110 ∨ p2563)
    (h56321 : (¬ p2373) ∨ (¬ p3369) ∨ (¬ p3379) ∨ (¬ p4110) ∨ (¬ p4120))
    : (¬ p3369) ∨ p2220 ∨ (¬ p2373) ∨ p2563 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3369 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56321 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92541 (p2220 p2741 p2957 p2992 p3146 p3266 p3662 p3692 p4120 p4444 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73580 : p4444 ∨ p3266)
    (h73522 : p4120 ∨ p2220)
    (h73440 : p3662 ∨ p2992)
    (h45611 : (¬ p2741) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4444))
    : p3146 ∨ p3266 ∨ p2220 ∨ (¬ p2957) ∨ (¬ p2741) ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h45611 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step92543 (p2220 p2254 p2922 p2950 p3256 p3266 p3379 p3868 p4118 p4120 p4311 p4444 p4826 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73580 : p4444 ∨ p3266)
    (h73522 : p4120 ∨ p2220)
    (h50814 : (¬ p2254) ∨ (¬ p2922) ∨ (¬ p2950) ∨ (¬ p3379) ∨ (¬ p3868) ∨ (¬ p4118) ∨ (¬ p4120) ∨ (¬ p4311) ∨ (¬ p4444) ∨ (¬ p4826))
    : p3256 ∨ (¬ p2950) ∨ (¬ p2254) ∨ (¬ p4311) ∨ (¬ p2922) ∨ p3266 ∨ (¬ p4826) ∨ p2220 ∨ (¬ p3868) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50814 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step92544 (p2220 p2274 p2373 p2553 p2588 p2590 p4120 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73522 : p4120 ∨ p2220)
    (h53323 : (¬ p2274) ∨ (¬ p2373) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p4120))
    : (¬ p2373) ∨ (¬ p2590) ∨ p2553 ∨ p2220 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53323 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92546 (p2881 p3527 p3548 p3571 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h9577 : (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3571))
    : (¬ p3571) ∨ p3527 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3571 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h9577 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step92550 (p3246 p3571 p3631 p3690 p3817 : Prop)
    (h73445 : (¬ p3246) ∨ (¬ p3690))
    (h73468 : p3817 ∨ p3631)
    (h36323 : (¬ p3571) ∨ p3690 ∨ (¬ p3817))
    : (¬ p3246) ∨ p3631 ∨ (¬ p3571) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3631) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3690) := (Or.elim h73445 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h36323 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step92554 (p2132 p2138 p2901 p3425 p3471 p3571 p4320 p4424 p5053 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73396 : p3471 ∨ p3425)
    (h73552 : p4320 ∨ p2901)
    (h63413 : (¬ p2138) ∨ (¬ p3471) ∨ (¬ p3571) ∨ (¬ p4320) ∨ (¬ p4424) ∨ (¬ p5053))
    : p2132 ∨ (¬ p4424) ∨ p3425 ∨ (¬ p3571) ∨ p2901 ∨ (¬ p5053) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63413 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step92558 (p2156 p2341 p3527 p3548 p3571 p3646 p4558 p4988 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73436 : p3646 ∨ p2156)
    (h49332 : (¬ p2341) ∨ (¬ p3548) ∨ (¬ p3571) ∨ (¬ p3646) ∨ (¬ p4558) ∨ (¬ p4988))
    : p3527 ∨ (¬ p4558) ∨ p2156 ∨ (¬ p3571) ∨ (¬ p4988) ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49332 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step92563 (p2608 p2717 p3399 p3527 p3548 p3587 p4366 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73404 : p3548 ∨ p3527)
    (h47130 : (¬ p2608) ∨ (¬ p2717) ∨ (¬ p3548) ∨ (¬ p3587) ∨ (¬ p4366))
    : p3399 ∨ (¬ p2608) ∨ (¬ p2717) ∨ p3527 ∨ (¬ p3587) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3587 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47130 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92579 (p2264 p2911 p2922 p2928 p3580 p3644 p4811 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73320 : p2928 ∨ p2922)
    (h51784 : (¬ p2264) ∨ (¬ p2928) ∨ (¬ p3580) ∨ (¬ p3644) ∨ (¬ p4811))
    : p2911 ∨ (¬ p3580) ∨ (¬ p4811) ∨ (¬ p2264) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51784 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92581 (p2088 p2481 p2509 p3256 p3580 p3857 p4044 p4811 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h41127 : (¬ p2481) ∨ (¬ p2509) ∨ (¬ p3256) ∨ (¬ p3580) ∨ (¬ p3857) ∨ (¬ p4044) ∨ (¬ p4811))
    : (¬ p3256) ∨ p2088 ∨ (¬ p2509) ∨ (¬ p3580) ∨ (¬ p2481) ∨ (¬ p4044) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2481 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41127 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step92584 (p2264 p2911 p3016 p3574 p3580 p3644 p4711 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73422 : p3574 ∨ p3016)
    (h40986 : (¬ p2264) ∨ (¬ p3574) ∨ (¬ p3580) ∨ (¬ p3644) ∨ (¬ p4711))
    : p2911 ∨ (¬ p2264) ∨ (¬ p4711) ∨ p3016 ∨ (¬ p3580) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4711 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h40986 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92586 (p2417 p2449 p2651 p2911 p3580 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h53236 : (¬ p2449) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3580) ∨ (¬ p4278))
    : p2417 ∨ (¬ p2449) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3580) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53236 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92591 (p2911 p3019 p3319 p3323 p3527 p3644 p4026 p4452 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73504 : p4026 ∨ p3319)
    (h52086 : (¬ p3019) ∨ (¬ p3323) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p4026) ∨ (¬ p4452))
    : (¬ p3527) ∨ (¬ p4452) ∨ p2911 ∨ (¬ p3019) ∨ (¬ p3323) ∨ p3319 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h52086 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step92594 (p3093 p3399 p4366 p4452 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h20307 : (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4452))
    : p3399 ∨ (¬ p4452) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20307 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step92598 (p2177 p2299 p2911 p2922 p2933 p3093 p4452 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h65917 : (¬ p2299) ∨ (¬ p2933) ∨ (¬ p2922) ∨ (¬ p4452) ∨ (¬ p3093) ∨ (¬ p2911))
    : (¬ p2911) ∨ (¬ p4452) ∨ (¬ p2922) ∨ (¬ p3093) ∨ p2177 ∨ (¬ p2933) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h65917 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step92603 (p2177 p2254 p2299 p2685 p2946 p2952 p3093 p3136 p3527 p3572 p4361 p4452 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73420 : p3572 ∨ p2685)
    (h73234 : p2299 ∨ p2177)
    (h57593 : (¬ p2254) ∨ (¬ p2299) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3136) ∨ (¬ p3527) ∨ (¬ p3572) ∨ (¬ p4361) ∨ (¬ p4452))
    : (¬ p3527) ∨ (¬ p4452) ∨ (¬ p4361) ∨ (¬ p3093) ∨ p2946 ∨ p2685 ∨ p2177 ∨ (¬ p3136) ∨ (¬ p2254) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h57593 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step92606 (p2177 p2299 p2608 p3093 p3527 p3954 p4452 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73498 : p3954 ∨ p2608)
    (h60034 : (¬ p2299) ∨ (¬ p3093) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p4452))
    : (¬ p3527) ∨ (¬ p4452) ∨ p2177 ∨ p2608 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60034 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92610 (p2254 p2685 p2911 p3005 p3093 p3166 p3172 p3527 p3572 p3644 p4452 p4653 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73356 : p3172 ∨ p3166)
    (h73420 : p3572 ∨ p2685)
    (h59796 : (¬ p2254) ∨ (¬ p3005) ∨ (¬ p3093) ∨ (¬ p3172) ∨ (¬ p3527) ∨ (¬ p3572) ∨ (¬ p3644) ∨ (¬ p4452) ∨ (¬ p4653))
    : (¬ p4452) ∨ (¬ p3527) ∨ (¬ p3005) ∨ p2911 ∨ p3166 ∨ (¬ p2254) ∨ p2685 ∨ (¬ p3093) ∨ (¬ p4653) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4452 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h59796 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step92611 (p2177 p2299 p2331 p2946 p2952 p3527 p4319 p4452 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73234 : p2299 ∨ p2177)
    (h60169 : (¬ p2299) ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3527) ∨ (¬ p4319) ∨ (¬ p4452))
    : (¬ p2331) ∨ p2946 ∨ p2177 ∨ (¬ p3527) ∨ (¬ p4452) ∨ (¬ p4319) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60169 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step92613 (p2177 p2299 p2962 p3319 p3527 p3654 p4026 p4452 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73504 : p4026 ∨ p3319)
    (h43525 : (¬ p2299) ∨ (¬ p2962) ∨ (¬ p3527) ∨ (¬ p3654) ∨ (¬ p4026) ∨ (¬ p4452))
    : (¬ p4452) ∨ (¬ p3654) ∨ (¬ p2962) ∨ p2177 ∨ (¬ p3527) ∨ p3319 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4452 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h43525 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step92614 (p2177 p2299 p2427 p2598 p2850 p3055 p3093 p3527 p3684 p4235 p4452 p4559 p4736 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73350 : p3055 ∨ p2598)
    (h73536 : p4235 ∨ p2427)
    (h73442 : p3684 ∨ p2850)
    (h49580 : (¬ p2299) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3527) ∨ (¬ p3684) ∨ (¬ p4235) ∨ (¬ p4452) ∨ (¬ p4559) ∨ (¬ p4736))
    : (¬ p3527) ∨ (¬ p4452) ∨ (¬ p4736) ∨ p2177 ∨ (¬ p4559) ∨ p2598 ∨ p2427 ∨ (¬ p3093) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h49580 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step92619 (p2177 p2299 p3319 p3527 p3654 p3987 p4026 p4452 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73504 : p4026 ∨ p3319)
    (h43690 : (¬ p2299) ∨ (¬ p3527) ∨ (¬ p3654) ∨ (¬ p3987) ∨ (¬ p4026) ∨ (¬ p4452))
    : (¬ p4452) ∨ (¬ p3654) ∨ p2177 ∨ (¬ p3527) ∨ p3319 ∨ (¬ p3987) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4452 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43690 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step92624 (p2891 p4908 p4911 : Prop)
    (h73822 : p4908 ∨ p2891)
    (h8106 : (¬ p4908) ∨ p4911)
    : p2891 ∨ p4911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4911) := (fun h => hn (Or.inr h));
    let u2 : p4908 := (Or.elim h73822 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8106 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step92629 (p3093 p3323 p3591 p3830 p4037 p4761 p5152 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73508 : p4037 ∨ p3323)
    (h53937 : (¬ p3591) ∨ (¬ p3830) ∨ (¬ p4037) ∨ (¬ p4761) ∨ (¬ p5152))
    : (¬ p3830) ∨ (¬ p5152) ∨ p3093 ∨ p3323 ∨ (¬ p4761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5152 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53937 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92634 (p3093 p3591 p3830 p3917 p4871 p5152 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h42269 : (¬ p3591) ∨ (¬ p3830) ∨ (¬ p3917) ∨ (¬ p4871) ∨ (¬ p5152))
    : (¬ p3830) ∨ p3093 ∨ (¬ p3917) ∨ (¬ p5152) ∨ (¬ p4871) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5152 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4871 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42269 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92635 (p2459 p3449 p3542 p3830 p3860 p4330 p4348 p5152 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73562 : p4348 ∨ p2459)
    (h64174 : (¬ p3542) ∨ (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p5152))
    : p3449 ∨ (¬ p5152) ∨ (¬ p3542) ∨ p2459 ∨ (¬ p3830) ∨ (¬ p4330) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p5152 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64174 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step92636 (p3461 p3707 p4321 p5152 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h19927 : (¬ p3461) ∨ (¬ p4321) ∨ (¬ p5152))
    : p3707 ∨ (¬ p5152) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p5152 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h19927 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step92638 (p2241 p2247 p2553 p3564 p3830 p4137 p5152 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73524 : p4137 ∨ p3564)
    (h64385 : (¬ p2247) ∨ (¬ p2553) ∨ (¬ p3830) ∨ (¬ p4137) ∨ (¬ p5152))
    : (¬ p5152) ∨ p2241 ∨ (¬ p2553) ∨ p3564 ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5152 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64385 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step92640 (p2498 p2553 p2588 p3093 p3591 p3830 p4624 p5152 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73282 : p2588 ∨ p2553)
    (h52923 : (¬ p2498) ∨ (¬ p2588) ∨ (¬ p3591) ∨ (¬ p3830) ∨ (¬ p4624) ∨ (¬ p5152))
    : (¬ p3830) ∨ p3093 ∨ (¬ p5152) ∨ p2553 ∨ (¬ p2498) ∨ (¬ p4624) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5152 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52923 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step92643 (p2210 p2427 p2891 p3379 p3486 p3555 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73412 : p3555 ∨ p2210)
    (h52741 : (¬ p2427) ∨ (¬ p3379) ∨ (¬ p3486) ∨ (¬ p3555))
    : p2891 ∨ (¬ p2427) ∨ (¬ p3379) ∨ p2210 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52741 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92646 (p2192 p2563 p2891 p3051 p3486 p4110 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73516 : p4110 ∨ p2563)
    (h46648 : (¬ p2192) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4110))
    : (¬ p3051) ∨ p2891 ∨ p2563 ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46648 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92647 (p2187 p2192 p2891 p3486 p4275 p4405 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h42006 : (¬ p2187) ∨ (¬ p2192) ∨ (¬ p3486) ∨ (¬ p4275) ∨ (¬ p4405))
    : p2891 ∨ (¬ p2192) ∨ (¬ p4405) ∨ (¬ p4275) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42006 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92649 (p2156 p2192 p2891 p3246 p3486 p3646 p3690 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73446 : p3690 ∨ p3246)
    (h73436 : p3646 ∨ p2156)
    (h47410 : (¬ p2192) ∨ (¬ p3486) ∨ (¬ p3646) ∨ (¬ p3690))
    : (¬ p2192) ∨ p2891 ∨ p3246 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47410 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92650 (p2156 p2192 p2881 p2891 p3486 p3570 p3646 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73436 : p3646 ∨ p2156)
    (h73418 : p3570 ∨ p2881)
    (h53686 : (¬ p2192) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p3646))
    : (¬ p2192) ∨ p2891 ∨ p2156 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53686 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92653 (p2192 p2891 p3486 p3872 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h5731 : (¬ p2192) ∨ (¬ p3486) ∨ (¬ p3872))
    : (¬ p2192) ∨ p2891 ∨ (¬ p3872) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5731 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step92658 (p2192 p2459 p2881 p2891 p3486 p3570 p4348 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73418 : p3570 ∨ p2881)
    (h73562 : p4348 ∨ p2459)
    (h63239 : (¬ p2192) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4348))
    : (¬ p2192) ∨ p2891 ∨ p2881 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63239 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step92659 (p2210 p2241 p2881 p2891 p3486 p3555 p3570 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73398 : p3486 ∨ p2891)
    (h73418 : p3570 ∨ p2881)
    (h64832 : (¬ p2241) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570))
    : (¬ p2241) ∨ p2210 ∨ p2891 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64832 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step92664 (p2166 p2427 p2891 p3146 p3486 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h47711 : (¬ p2166) ∨ (¬ p2427) ∨ (¬ p3146) ∨ (¬ p3486))
    : (¬ p2166) ∨ p2891 ∨ (¬ p3146) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47711 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92666 (p2192 p2891 p3125 p3486 p4275 p4624 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h49744 : (¬ p2192) ∨ (¬ p3125) ∨ (¬ p3486) ∨ (¬ p4275) ∨ (¬ p4624))
    : (¬ p3125) ∨ (¬ p2192) ∨ (¬ p4275) ∨ (¬ p4624) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49744 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92669 (p2192 p2563 p2891 p2901 p3486 p4110 p4705 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73516 : p4110 ∨ p2563)
    (h54536 : (¬ p2192) ∨ (¬ p2901) ∨ (¬ p3486) ∨ (¬ p4110) ∨ (¬ p4705))
    : (¬ p2901) ∨ p2891 ∨ p2563 ∨ (¬ p4705) ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54536 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92673 (p2156 p2192 p2891 p3486 p3569 p3646 p3741 p4533 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73398 : p3486 ∨ p2891)
    (h58144 : (¬ p2192) ∨ (¬ p3486) ∨ (¬ p3569) ∨ (¬ p3646) ∨ (¬ p3741) ∨ (¬ p4533))
    : (¬ p2192) ∨ p2156 ∨ (¬ p3569) ∨ p2891 ∨ (¬ p3741) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58144 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step92675 (p2156 p2166 p2220 p2891 p3486 p4120 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h73398 : p3486 ∨ p2891)
    (h57266 : (¬ p2156) ∨ (¬ p2166) ∨ (¬ p3486) ∨ (¬ p4120))
    : p2220 ∨ (¬ p2166) ∨ (¬ p2156) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57266 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92677 (p2166 p2220 p2427 p2891 p3486 p4120 p4533 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73522 : p4120 ∨ p2220)
    (h50741 : (¬ p2166) ∨ (¬ p2427) ∨ (¬ p3486) ∨ (¬ p4120) ∨ (¬ p4533))
    : p2891 ∨ (¬ p2166) ∨ (¬ p2427) ∨ p2220 ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50741 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92680 (p2177 p2192 p2881 p2891 p3486 p3570 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73418 : p3570 ∨ p2881)
    (h59959 : (¬ p2177) ∨ (¬ p2192) ∨ (¬ p3486) ∨ (¬ p3570))
    : (¬ p2192) ∨ p2891 ∨ (¬ p2177) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59959 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92681 (p2192 p2307 p2891 p3486 p4275 p4489 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h49593 : (¬ p2192) ∨ (¬ p2307) ∨ (¬ p3486) ∨ (¬ p4275) ∨ (¬ p4489))
    : p2891 ∨ (¬ p2307) ∨ (¬ p2192) ∨ (¬ p4489) ∨ (¬ p4275) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4489 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49593 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92686 (p2230 p2427 p2891 p3486 p4202 p5194 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h49416 : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3486) ∨ (¬ p4202) ∨ (¬ p5194))
    : (¬ p2427) ∨ p2891 ∨ (¬ p2230) ∨ (¬ p5194) ∨ (¬ p4202) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49416 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92690 (p2881 p2891 p2972 p3486 p3570 p4135 p4668 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73418 : p3570 ∨ p2881)
    (h52955 : (¬ p2972) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4135) ∨ (¬ p4668))
    : (¬ p4135) ∨ (¬ p2972) ∨ p2891 ∨ p2881 ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4135 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52955 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92703 (p2137 p2737 p2891 p3051 p3486 p4874 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h67287 : (¬ p3486) ∨ (¬ p2737) ∨ (¬ p4874) ∨ (¬ p3051) ∨ (¬ p2137))
    : (¬ p3051) ∨ p2891 ∨ (¬ p4874) ∨ (¬ p2137) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h67287 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92707 (p2891 p2972 p3486 p4402 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h20250 : (¬ p2972) ∨ (¬ p3486) ∨ (¬ p4402))
    : (¬ p4402) ∨ (¬ p2972) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4402 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20250 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step92708 (p2137 p2891 p3051 p3367 p3486 p4874 p4881 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h52576 : (¬ p2137) ∨ (¬ p3051) ∨ (¬ p3367) ∨ (¬ p3486) ∨ (¬ p4874) ∨ (¬ p4881))
    : (¬ p3051) ∨ (¬ p2137) ∨ (¬ p4874) ∨ p2891 ∨ (¬ p3367) ∨ (¬ p4881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52576 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step92709 (p2608 p2891 p3051 p3486 p3954 p4172 p4877 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73498 : p3954 ∨ p2608)
    (h49922 : (¬ p3051) ∨ (¬ p3486) ∨ (¬ p3954) ∨ (¬ p4172) ∨ (¬ p4877))
    : p2891 ∨ (¬ p3051) ∨ (¬ p4172) ∨ p2608 ∨ (¬ p4877) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49922 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92712 (p2166 p2891 p3486 p4042 p5559 p5660 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h49918 : (¬ p2166) ∨ (¬ p3486) ∨ (¬ p4042) ∨ (¬ p5559) ∨ (¬ p5660))
    : p2891 ∨ (¬ p2166) ∨ (¬ p5660) ∨ (¬ p5559) ∨ (¬ p4042) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49918 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92716 (p2166 p2177 p2299 p2891 p3486 p4042 p4559 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73234 : p2299 ∨ p2177)
    (h64080 : (¬ p2166) ∨ (¬ p2299) ∨ (¬ p3486) ∨ (¬ p4042) ∨ (¬ p4559))
    : p2891 ∨ (¬ p2166) ∨ p2177 ∨ (¬ p4559) ∨ (¬ p4042) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64080 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92717 (p2459 p2651 p2753 p2881 p2891 p3016 p3486 p3564 p3570 p4117 p4330 p4348 p4877 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73398 : p3486 ∨ p2891)
    (h73562 : p4348 ∨ p2459)
    (h50556 : (¬ p2651) ∨ (¬ p2753) ∨ (¬ p3016) ∨ (¬ p3486) ∨ (¬ p3564) ∨ (¬ p3570) ∨ (¬ p4117) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4877))
    : p2881 ∨ (¬ p3564) ∨ (¬ p4330) ∨ p2891 ∨ (¬ p4117) ∨ (¬ p3016) ∨ (¬ p2753) ∨ (¬ p2651) ∨ (¬ p4877) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h50556 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step92720 (p2192 p2891 p2901 p2946 p3486 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h42945 : (¬ p2192) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3486))
    : (¬ p2901) ∨ (¬ p2946) ∨ p2891 ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42945 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92723 (p2437 p2440 p2891 p3486 p3569 p4629 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h63238 : (¬ p2437) ∨ (¬ p2440) ∨ (¬ p3486) ∨ (¬ p3569) ∨ (¬ p4629))
    : (¬ p2437) ∨ (¬ p2440) ∨ (¬ p4629) ∨ p2891 ∨ (¬ p3569) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63238 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92724 (p2210 p2608 p2881 p2891 p3486 p3555 p3570 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73418 : p3570 ∨ p2881)
    (h73398 : p3486 ∨ p2891)
    (h47266 : (¬ p2608) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570))
    : (¬ p2608) ∨ p2210 ∨ p2881 ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47266 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92725 (p2210 p2427 p2608 p2891 p3486 p3555 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73412 : p3555 ∨ p2210)
    (h48832 : (¬ p2427) ∨ (¬ p2608) ∨ (¬ p3486) ∨ (¬ p3555))
    : p2891 ∨ (¬ p2427) ∨ p2210 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48832 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92728 (p2166 p2352 p2598 p2891 p3051 p3055 p3422 p3486 p3584 p3956 p4172 p4433 p4736 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73426 : p3584 ∨ p3422)
    (h73350 : p3055 ∨ p2598)
    (h73500 : p3956 ∨ p2352)
    (h59839 : (¬ p2166) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p3486) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4172) ∨ (¬ p4433) ∨ (¬ p4736))
    : (¬ p2166) ∨ p2891 ∨ p3422 ∨ (¬ p4736) ∨ p2598 ∨ (¬ p4172) ∨ (¬ p3051) ∨ (¬ p4433) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h59839 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step92731 (p2210 p2891 p3093 p3486 p3555 p4516 p4555 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73412 : p3555 ∨ p2210)
    (h42446 : (¬ p3093) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p4516) ∨ (¬ p4555))
    : (¬ p4516) ∨ (¬ p3093) ∨ p2891 ∨ (¬ p4555) ∨ p2210 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42446 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92735 (p2210 p2891 p2901 p3093 p3486 p3555 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73412 : p3555 ∨ p2210)
    (h58859 : (¬ p2901) ∨ (¬ p3093) ∨ (¬ p3486) ∨ (¬ p3555))
    : p2891 ∨ (¬ p2901) ∨ (¬ p3093) ∨ p2210 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58859 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92738 (p2210 p2264 p2685 p2696 p2891 p3246 p3486 p3555 p3690 p4666 p4733 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73412 : p3555 ∨ p2210)
    (h73398 : p3486 ∨ p2891)
    (h50755 : (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3690) ∨ (¬ p4666) ∨ (¬ p4733))
    : p3246 ∨ p2210 ∨ (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p4733) ∨ p2891 ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h50755 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step92739 (p2630 p2810 p2811 p2891 p2958 p3051 p3486 p4282 p4704 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73316 : p2810 ∨ p2630)
    (h73046 : p4704)
    (h52059 : (¬ p2810) ∨ (¬ p2811) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4282) ∨ (¬ p4704))
    : (¬ p3051) ∨ (¬ p2958) ∨ (¬ p2811) ∨ p2891 ∨ p2630 ∨ (¬ p4282) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p4704 := h73046;
    (Or.elim h52059 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u8)))))))))))))))

theorem step92740 (p2249 p2641 p2891 p2946 p2952 p3323 p3461 p3486 p4282 p4831 p5660 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73398 : p3486 ∨ p2891)
    (h56793 : (¬ p2249) ∨ (¬ p2641) ∨ (¬ p2952) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3486) ∨ (¬ p4282) ∨ (¬ p4831) ∨ (¬ p5660))
    : (¬ p5660) ∨ (¬ p3323) ∨ (¬ p4831) ∨ (¬ p3461) ∨ p2946 ∨ (¬ p4282) ∨ (¬ p2249) ∨ (¬ p2641) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5660 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4831 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h56793 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step92742 (p2132 p2138 p2417 p2881 p2891 p3367 p3389 p3486 p3570 p3759 p4243 p4668 p4734 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73418 : p3570 ∨ p2881)
    (h72735 : p4734)
    (h73398 : p3486 ∨ p2891)
    (h50116 : (¬ p2138) ∨ (¬ p2417) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p3759) ∨ (¬ p4243) ∨ (¬ p4668) ∨ (¬ p4734))
    : p2132 ∨ (¬ p2417) ∨ p2881 ∨ (¬ p4668) ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p4243) ∨ p2891 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4734 := h72735;
    let u12 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50116 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u11)))))))))))))))))))))

theorem step92746 (p2891 p3051 p3379 p3452 p3486 p4172 p4376 p4874 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73394 : p3452 ∨ p3379)
    (h50886 : (¬ p3051) ∨ (¬ p3452) ∨ (¬ p3486) ∨ (¬ p4172) ∨ (¬ p4376) ∨ (¬ p4874))
    : (¬ p3051) ∨ p2891 ∨ (¬ p4172) ∨ (¬ p4874) ∨ p3379 ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50886 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step92747 (p2761 p2891 p3246 p3399 p3486 p3631 p3690 p3817 p4366 p4381 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h73574 : p4381 ∨ p2761)
    (h73446 : p3690 ∨ p3246)
    (h73398 : p3486 ∨ p2891)
    (h73570 : p4366 ∨ p3399)
    (h66938 : (¬ p4381) ∨ (¬ p3817) ∨ (¬ p3486) ∨ (¬ p4366) ∨ (¬ p3690))
    : p3631 ∨ p2761 ∨ p3246 ∨ p2891 ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h66938 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step92755 (p2177 p2210 p2299 p2608 p2891 p2911 p3389 p3486 p3519 p3555 p4376 p4559 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73234 : p2299 ∨ p2177)
    (h73398 : p3486 ∨ p2891)
    (h62442 : (¬ p2299) ∨ (¬ p2608) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3486) ∨ (¬ p3519) ∨ (¬ p3555) ∨ (¬ p4376) ∨ (¬ p4559))
    : (¬ p2911) ∨ p2210 ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p4559) ∨ (¬ p3519) ∨ (¬ p3389) ∨ p2177 ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u11 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h62442 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step92758 (p2156 p2284 p2891 p3051 p3556 p3952 p4960 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73414 : p3556 ∨ p3051)
    (h53450 : (¬ p2156) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3952) ∨ (¬ p4960))
    : p2284 ∨ p3051 ∨ (¬ p2156) ∨ (¬ p2891) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53450 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92759 (p2156 p2630 p2810 p2870 p3051 p3556 p4313 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73316 : p2810 ∨ p2630)
    (h63048 : (¬ p2156) ∨ (¬ p2810) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p4313))
    : (¬ p2870) ∨ p3051 ∨ (¬ p4313) ∨ (¬ p2156) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63048 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92761 (p2156 p2427 p2440 p2542 p3051 p3556 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73270 : p2542 ∨ p2440)
    (h44425 : (¬ p2156) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (¬ p3556))
    : p3051 ∨ p2440 ∨ (¬ p2427) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44425 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92762 (p2156 p2307 p2317 p3051 p3556 p3646 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73242 : p2317 ∨ (¬ p2307))
    (h73435 : (¬ p2156) ∨ (¬ p3646))
    (h65949 : p3646 ∨ (¬ p2317) ∨ (¬ p3556))
    : p3051 ∨ (¬ p2307) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p2317 := (Or.elim h73242 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u5 : (¬ p3646) := (Or.elim h73435 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h65949 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u3)))))))

theorem step92763 (p2156 p2396 p3051 p3246 p3556 p3690 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73414 : p3556 ∨ p3051)
    (h57841 : (¬ p2156) ∨ (¬ p2396) ∨ (¬ p3556) ∨ (¬ p3690))
    : p3246 ∨ (¬ p2396) ∨ (¬ p2156) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57841 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92766 (p2156 p2553 p3051 p3556 p4275 p4718 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h57162 : (¬ p2156) ∨ (¬ p2553) ∨ (¬ p3556) ∨ (¬ p4275) ∨ (¬ p4718))
    : p3051 ∨ (¬ p2553) ∨ (¬ p4275) ∨ (¬ p4718) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h57162 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92768 (p2220 p2717 p3051 p3556 p3659 p4042 p4895 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73414 : p3556 ∨ p3051)
    (h41048 : (¬ p2220) ∨ (¬ p3556) ∨ (¬ p3659) ∨ (¬ p4042) ∨ (¬ p4895))
    : (¬ p4042) ∨ (¬ p2220) ∨ p2717 ∨ p3051 ∨ (¬ p4895) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4042 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4895 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41048 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

end ElevenRUP
