import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step92770 (p2417 p3051 p3246 p3556 p3690 p3741 p4533 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73414 : p3556 ∨ p3051)
    (h61400 : (¬ p2417) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p3741) ∨ (¬ p4533))
    : (¬ p2417) ∨ p3246 ∨ p3051 ∨ (¬ p4533) ∨ (¬ p3741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61400 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92773 (p2255 p2528 p2651 p2957 p2992 p3051 p3083 p3246 p3556 p3662 p3690 p4669 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73414 : p3556 ∨ p3051)
    (h73440 : p3662 ∨ p2992)
    (h60206 : (¬ p2255) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2957) ∨ (¬ p3083) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p3690) ∨ (¬ p4669))
    : p3246 ∨ (¬ p3083) ∨ p3051 ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2255) ∨ (¬ p2957) ∨ (¬ p4669) ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h60206 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step92775 (p2459 p2630 p2696 p2753 p3051 p3083 p3146 p3556 p3645 p3692 p4119 p4420 p4877 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73414 : p3556 ∨ p3051)
    (h50793 : (¬ p2459) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3083) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4420) ∨ (¬ p4877))
    : (¬ p3083) ∨ p3146 ∨ (¬ p2630) ∨ (¬ p4420) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3645) ∨ (¬ p4877) ∨ (¬ p2459) ∨ (¬ p4119) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h50793 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step92782 (p2156 p2177 p2264 p3051 p3553 p3556 p4333 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73410 : p3553 ∨ p2264)
    (h65165 : (¬ p2156) ∨ (¬ p2177) ∨ (¬ p3553) ∨ (¬ p3556) ∨ (¬ p4333))
    : p3051 ∨ (¬ p2156) ∨ p2264 ∨ (¬ p2177) ∨ (¬ p4333) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h65165 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92783 (p2427 p2761 p2972 p3051 p3556 p3645 p4135 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h47840 : (¬ p2427) ∨ (¬ p2761) ∨ (¬ p2972) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4135))
    : (¬ p2972) ∨ p3051 ∨ (¬ p2761) ∨ (¬ p4135) ∨ (¬ p3645) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4135 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47840 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step92784 (p2651 p2753 p2761 p3016 p3051 p3246 p3556 p3645 p3690 p3888 p4117 p4381 p4877 p5250 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73414 : p3556 ∨ p3051)
    (h73574 : p4381 ∨ p2761)
    (h62270 : (¬ p2651) ∨ (¬ p2753) ∨ (¬ p3016) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3690) ∨ (¬ p3888) ∨ (¬ p4117) ∨ (¬ p4381) ∨ (¬ p4877) ∨ (¬ p5250))
    : (¬ p3888) ∨ (¬ p2753) ∨ p3246 ∨ (¬ p4877) ∨ (¬ p3645) ∨ (¬ p2651) ∨ (¬ p4117) ∨ (¬ p3016) ∨ p3051 ∨ p2761 ∨ (¬ p5250) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u13 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h62270 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (False.elim (r9 u10)))))))))))))))))))))))

theorem step92785 (p2962 p3051 p3125 p3556 p3654 p3744 p4555 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73414 : p3556 ∨ p3051)
    (h42322 : (¬ p2962) ∨ (¬ p3556) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p4555))
    : (¬ p3654) ∨ p3125 ∨ (¬ p4555) ∨ (¬ p2962) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42322 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92787 (p2187 p2383 p2427 p2962 p3051 p3556 p3989 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73502 : p3989 ∨ p2187)
    (h45365 : (¬ p2383) ∨ (¬ p2427) ∨ (¬ p2962) ∨ (¬ p3556) ∨ (¬ p3989))
    : p3051 ∨ (¬ p2383) ∨ (¬ p2962) ∨ (¬ p2427) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45365 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92797 (p2156 p2396 p2860 p3051 p3556 p3758 p4107 p4275 : Prop)
    (h73456 : p3758 ∨ p2860)
    (h73514 : p4107 ∨ p2396)
    (h73414 : p3556 ∨ p3051)
    (h56896 : (¬ p2156) ∨ (¬ p3556) ∨ (¬ p3758) ∨ (¬ p4107) ∨ (¬ p4275))
    : p2860 ∨ (¬ p4275) ∨ (¬ p2156) ∨ p2396 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2860) := (fun h => hn (Or.inl h));
    let u1 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56896 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92801 (p2156 p2187 p2427 p3051 p3556 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h45366 : (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2427) ∨ (¬ p3556))
    : p3051 ∨ (¬ p2187) ∨ (¬ p2156) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45366 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92803 (p2156 p2187 p2901 p3051 p3556 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h48660 : (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2901) ∨ (¬ p3556))
    : p3051 ∨ (¬ p2187) ∨ (¬ p2156) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48660 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92805 (p2156 p2563 p3051 p3246 p3556 p3690 p4110 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73446 : p3690 ∨ p3246)
    (h73516 : p4110 ∨ p2563)
    (h42823 : (¬ p2156) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p4110))
    : p3051 ∨ p3246 ∨ p2563 ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42823 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step92806 (p2156 p2563 p2901 p3051 p3556 p4110 p4705 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73516 : p4110 ∨ p2563)
    (h54202 : (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p4110) ∨ (¬ p4705))
    : p3051 ∨ (¬ p2901) ∨ (¬ p4705) ∨ (¬ p2156) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54202 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92807 (p2156 p2563 p2870 p3051 p3556 p4110 p4885 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73516 : p4110 ∨ p2563)
    (h51298 : (¬ p2156) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p4110) ∨ (¬ p4885))
    : (¬ p2870) ∨ p3051 ∨ p2563 ∨ (¬ p4885) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51298 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92808 (p2156 p2177 p2299 p2563 p3051 p3556 p4110 p4275 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73516 : p4110 ∨ p2563)
    (h73234 : p2299 ∨ p2177)
    (h43850 : (¬ p2156) ∨ (¬ p2299) ∨ (¬ p3556) ∨ (¬ p4110) ∨ (¬ p4275))
    : p3051 ∨ (¬ p4275) ∨ (¬ p2156) ∨ p2563 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43850 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92810 (p2396 p2563 p3051 p3246 p3556 p3645 p3690 p4210 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73414 : p3556 ∨ p3051)
    (h63307 : (¬ p2396) ∨ (¬ p2563) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3690) ∨ (¬ p4210))
    : p3246 ∨ (¬ p2396) ∨ (¬ p3645) ∨ p3051 ∨ (¬ p4210) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63307 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step92811 (p3051 p3246 p3556 p3631 p3690 p4431 p4522 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73414 : p3556 ∨ p3051)
    (h48756 : (¬ p3556) ∨ (¬ p3631) ∨ (¬ p3690) ∨ (¬ p4431) ∨ (¬ p4522))
    : (¬ p3631) ∨ p3246 ∨ (¬ p4431) ∨ p3051 ∨ (¬ p4522) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4522 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48756 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92814 (p2881 p3051 p3212 p3556 p3570 p4135 p4668 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73418 : p3570 ∨ p2881)
    (h49642 : (¬ p3212) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4135) ∨ (¬ p4668))
    : (¬ p4135) ∨ (¬ p3212) ∨ (¬ p4668) ∨ p3051 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4135 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49642 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92817 (p2406 p2761 p3051 p3238 p3246 p3556 p3690 p4031 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73446 : p3690 ∨ p3246)
    (h73414 : p3556 ∨ p3051)
    (h73374 : p3238 ∨ p2406)
    (h52980 : (¬ p3238) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p4031) ∨ (¬ p4381))
    : p2761 ∨ (¬ p4031) ∨ p3246 ∨ p3051 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52980 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92824 (p2373 p2891 p3051 p3146 p3556 p4031 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h47921 : (¬ p2373) ∨ (¬ p2891) ∨ (¬ p3146) ∨ (¬ p3556) ∨ (¬ p4031))
    : (¬ p3146) ∨ p3051 ∨ (¬ p2373) ∨ (¬ p2891) ∨ (¬ p4031) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47921 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92825 (p2220 p2427 p2563 p3051 p3556 p4110 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73516 : p4110 ∨ p2563)
    (h45334 : (¬ p2220) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p4110))
    : p3051 ∨ (¬ p2220) ∨ (¬ p2427) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45334 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92827 (p2459 p2493 p2881 p3051 p3379 p3556 p3564 p3570 p4330 p4348 p4524 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73562 : p4348 ∨ p2459)
    (h73418 : p3570 ∨ p2881)
    (h72962 : p4524)
    (h60313 : (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3556) ∨ (¬ p3564) ∨ (¬ p3570) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4524))
    : (¬ p3564) ∨ p3051 ∨ (¬ p2493) ∨ p2459 ∨ (¬ p4330) ∨ (¬ p3379) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p4524 := h72962;
    (Or.elim h60313 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step92828 (p2386 p2493 p2499 p2901 p2962 p3051 p3413 p3556 p4811 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73260 : p2499 ∨ p2493)
    (h52358 : (¬ p2386) ∨ (¬ p2499) ∨ (¬ p2901) ∨ (¬ p2962) ∨ (¬ p3413) ∨ (¬ p3556) ∨ (¬ p4811))
    : (¬ p2901) ∨ p3051 ∨ (¬ p2962) ∨ (¬ p4811) ∨ (¬ p3413) ∨ p2493 ∨ (¬ p2386) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h52358 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step92829 (p2220 p2427 p2459 p3051 p3556 p4042 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h43787 : (¬ p2220) ∨ (¬ p2427) ∨ (¬ p2459) ∨ (¬ p3556) ∨ (¬ p4042))
    : p3051 ∨ (¬ p2220) ∨ (¬ p2427) ∨ (¬ p2459) ∨ (¬ p4042) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43787 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92830 (p2220 p2911 p3051 p3556 p3644 p4042 p4277 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73434 : p3644 ∨ p2911)
    (h61190 : (¬ p2220) ∨ (¬ p3556) ∨ (¬ p3644) ∨ (¬ p4042) ∨ (¬ p4277))
    : (¬ p4042) ∨ (¬ p2220) ∨ (¬ p4277) ∨ p3051 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4042 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h61190 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92834 (p2761 p2957 p2992 p3051 p3246 p3556 p3662 p3690 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73440 : p3662 ∨ p2992)
    (h73446 : p3690 ∨ p3246)
    (h73414 : p3556 ∨ p3051)
    (h45248 : (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p3690) ∨ (¬ p4381))
    : p2761 ∨ p2992 ∨ (¬ p2957) ∨ p3246 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45248 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92836 (p2427 p2573 p3051 p3556 p3904 p4717 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h41064 : (¬ p2427) ∨ (¬ p2573) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p4717))
    : p3051 ∨ (¬ p2573) ∨ (¬ p3904) ∨ (¬ p4717) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41064 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92837 (p2241 p2459 p2727 p3051 p3146 p3343 p3556 p3692 p4045 p4119 p4420 p4524 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h72962 : p4524)
    (h73448 : p3692 ∨ p3146)
    (h51643 : (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2727) ∨ (¬ p3343) ∨ (¬ p3556) ∨ (¬ p3692) ∨ (¬ p4045) ∨ (¬ p4119) ∨ (¬ p4420) ∨ (¬ p4524))
    : (¬ p3343) ∨ p3051 ∨ (¬ p4045) ∨ (¬ p4420) ∨ (¬ p4119) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2727) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4524 := h72962;
    let u11 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h51643 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u10)))))))))))))))))))))

theorem step92838 (p2459 p2881 p2957 p2992 p3051 p3556 p3570 p3662 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73418 : p3570 ∨ p2881)
    (h73440 : p3662 ∨ p2992)
    (h73414 : p3556 ∨ p3051)
    (h43664 : (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (¬ p4348))
    : p2459 ∨ p2881 ∨ (¬ p2957) ∨ p2992 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2992) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43664 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92841 (p2284 p2396 p2957 p3051 p3246 p3556 p3690 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73414 : p3556 ∨ p3051)
    (h45082 : (¬ p2284) ∨ (¬ p2396) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3690))
    : p3246 ∨ (¬ p2396) ∨ p3051 ∨ (¬ p2957) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45082 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92843 (p2177 p2284 p2881 p2957 p3051 p3556 p3570 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73418 : p3570 ∨ p2881)
    (h44898 : (¬ p2177) ∨ (¬ p2284) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570))
    : (¬ p2284) ∨ p3051 ∨ (¬ p2957) ∨ p2881 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44898 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92844 (p2901 p2957 p3051 p3556 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h5172 : (¬ p2901) ∨ (¬ p2957) ∨ (¬ p3556))
    : (¬ p2901) ∨ p3051 ∨ (¬ p2957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5172 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step92846 (p2608 p2901 p3051 p3156 p3333 p3367 p3497 p3556 p4045 p4158 p4524 : Prop)
    (h72962 : p4524)
    (h73414 : p3556 ∨ p3051)
    (h73400 : p3497 ∨ p3156)
    (h62938 : (¬ p2608) ∨ (¬ p2901) ∨ (¬ p3333) ∨ (¬ p3367) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p4045) ∨ (¬ p4158) ∨ (¬ p4524))
    : (¬ p2901) ∨ (¬ p4045) ∨ (¬ p3333) ∨ p3051 ∨ (¬ p3367) ∨ p3156 ∨ (¬ p2608) ∨ (¬ p4158) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4524 := h72962;
    let u9 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h62938 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step92851 (p2284 p2957 p3051 p3556 p3872 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h30502 : (¬ p2284) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3872))
    : (¬ p3872) ∨ (¬ p2957) ∨ p3051 ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3872 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h30502 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step92854 (p2761 p2870 p3051 p3212 p3556 p4135 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h53310 : (¬ p2761) ∨ (¬ p2870) ∨ (¬ p3212) ∨ (¬ p3556) ∨ (¬ p4135))
    : (¬ p2870) ∨ (¬ p3212) ∨ p3051 ∨ (¬ p2761) ∨ (¬ p4135) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4135 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53310 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92856 (p2427 p2957 p3051 p3556 p4241 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h20297 : (¬ p2427) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p4241))
    : p3051 ∨ (¬ p4241) ∨ (¬ p2957) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20297 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step92862 (p2440 p2459 p2881 p3051 p3556 p3570 p4031 p4348 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73562 : p4348 ∨ p2459)
    (h73414 : p3556 ∨ p3051)
    (h61753 : (¬ p2440) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4031) ∨ (¬ p4348))
    : p2881 ∨ p2459 ∨ p3051 ∨ (¬ p2440) ∨ (¬ p4031) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61753 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92863 (p2440 p2459 p3051 p3146 p3556 p3692 p4031 p4119 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73414 : p3556 ∨ p3051)
    (h54497 : (¬ p2440) ∨ (¬ p2459) ∨ (¬ p3556) ∨ (¬ p3692) ∨ (¬ p4031) ∨ (¬ p4119))
    : p3146 ∨ p3051 ∨ (¬ p2459) ∨ (¬ p2440) ∨ (¬ p4031) ∨ (¬ p4119) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54497 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step92865 (p2143 p2528 p2598 p2839 p3051 p3246 p3556 p3583 p3641 p3690 p4669 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73424 : p3583 ∨ p2839)
    (h73414 : p3556 ∨ p3051)
    (h71973 : (¬ p3641) ∨ (¬ p3690) ∨ (¬ p3556) ∨ (¬ p4669) ∨ (¬ p3583) ∨ (¬ p2143) ∨ (¬ p2528) ∨ (¬ p2598))
    : (¬ p3641) ∨ (¬ p2528) ∨ p3246 ∨ (¬ p4669) ∨ p2839 ∨ (¬ p2143) ∨ (¬ p2598) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71973 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step92868 (p2088 p2427 p3051 p3256 p3556 p4118 p4238 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73414 : p3556 ∨ p3051)
    (h45754 : (¬ p2088) ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p4118) ∨ (¬ p4238))
    : p3256 ∨ p3051 ∨ (¬ p2088) ∨ (¬ p2427) ∨ (¬ p4238) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45754 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92871 (p2427 p2440 p2870 p3051 p3556 p4753 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h71975 : (¬ p3556) ∨ (¬ p4753) ∨ (¬ p2870) ∨ (¬ p2440) ∨ p2427)
    : (¬ p2870) ∨ p3051 ∨ (¬ p4753) ∨ (¬ p2440) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71975 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (u4 r3)))))))))))

theorem step92872 (p2957 p3051 p3156 p3497 p3556 p4119 : Prop)
    (h73399 : (¬ p3156) ∨ (¬ p3497))
    (h73414 : p3556 ∨ p3051)
    (h37460 : (¬ p2957) ∨ p3497 ∨ (¬ p3556) ∨ (¬ p4119))
    : (¬ p3156) ∨ (¬ p2957) ∨ p3051 ∨ (¬ p4119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3497) := (Or.elim h73399 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h37460 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step92874 (p2177 p2440 p2881 p3051 p3556 p3570 p4031 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73414 : p3556 ∨ p3051)
    (h45128 : (¬ p2177) ∨ (¬ p2440) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4031))
    : p2881 ∨ (¬ p4031) ∨ p3051 ∨ (¬ p2177) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45128 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92875 (p2177 p2608 p2881 p2922 p3051 p3379 p3556 p3570 p3645 p3954 p4276 p4877 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73418 : p3570 ∨ p2881)
    (h73414 : p3556 ∨ p3051)
    (h50546 : (¬ p2177) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3645) ∨ (¬ p3954) ∨ (¬ p4276) ∨ (¬ p4877))
    : p2608 ∨ (¬ p4877) ∨ (¬ p2177) ∨ p2881 ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3645) ∨ p3051 ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50546 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step92876 (p2177 p2396 p2881 p3051 p3556 p3570 p4107 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73418 : p3570 ∨ p2881)
    (h73414 : p3556 ∨ p3051)
    (h43801 : (¬ p2177) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4107))
    : p2396 ∨ p2881 ∨ (¬ p2177) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2396) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43801 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92877 (p2177 p2881 p2957 p2992 p3051 p3556 p3570 p3662 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73440 : p3662 ∨ p2992)
    (h73414 : p3556 ∨ p3051)
    (h43836 : (¬ p2177) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662))
    : p2881 ∨ p2992 ∨ (¬ p2957) ∨ p3051 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43836 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92881 (p2651 p2901 p2950 p3051 p3556 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h69679 : (¬ p2901) ∨ (¬ p3556) ∨ (¬ p2950) ∨ (¬ p2651))
    : (¬ p2901) ∨ p3051 ∨ (¬ p2651) ∨ (¬ p2950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h69679 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step92883 (p2331 p2901 p2950 p3051 p3556 p4566 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h40995 : (¬ p2331) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3556) ∨ (¬ p4566))
    : (¬ p2901) ∨ p3051 ∨ (¬ p2331) ∨ (¬ p4566) ∨ (¬ p2950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4566 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h40995 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92884 (p2331 p2881 p3051 p3323 p3461 p3556 p3570 p3904 p4117 p4729 p5123 p5558 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73418 : p3570 ∨ p2881)
    (h58244 : (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3904) ∨ (¬ p4117) ∨ (¬ p4729) ∨ (¬ p5123) ∨ (¬ p5558))
    : (¬ p5558) ∨ (¬ p3461) ∨ (¬ p3323) ∨ p3051 ∨ (¬ p4729) ∨ (¬ p2331) ∨ (¬ p3904) ∨ p2881 ∨ (¬ p5123) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h58244 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step92890 (p2459 p2881 p2957 p3051 p3136 p3556 p3570 p4315 p4348 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73414 : p3556 ∨ p3051)
    (h73550 : p4315 ∨ p3136)
    (h73562 : p4348 ∨ p2459)
    (h63051 : (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4315) ∨ (¬ p4348))
    : p2881 ∨ p3051 ∨ (¬ p2957) ∨ p3136 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63051 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u8)))))))))))

theorem step92891 (p2177 p2315 p2881 p3051 p3556 p3570 p3961 p4238 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73414 : p3556 ∨ p3051)
    (h55778 : (¬ p2177) ∨ (¬ p2315) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3961) ∨ (¬ p4238))
    : (¬ p3961) ∨ p2881 ∨ (¬ p2177) ∨ (¬ p2315) ∨ (¬ p4238) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3961 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55778 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step92892 (p2177 p2241 p2437 p2727 p2881 p3051 p3556 p3570 p4276 p4524 : Prop)
    (h72962 : p4524)
    (h73418 : p3570 ∨ p2881)
    (h73414 : p3556 ∨ p3051)
    (h51873 : (¬ p2177) ∨ (¬ p2241) ∨ (¬ p2437) ∨ (¬ p2727) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4276) ∨ (¬ p4524))
    : (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2241) ∨ (¬ p4276) ∨ (¬ p2727) ∨ p2881 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4524 := h72962;
    let u8 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u9 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h51873 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step92896 (p2284 p2563 p2901 p3051 p3556 p3952 p4533 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73496 : p3952 ∨ p2284)
    (h63244 : (¬ p2563) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3952) ∨ (¬ p4533))
    : p3051 ∨ (¬ p2901) ∨ (¬ p4533) ∨ p2284 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63244 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step92897 (p2143 p2284 p2839 p2901 p3051 p3556 p3583 p3952 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73424 : p3583 ∨ p2839)
    (h73496 : p3952 ∨ p2284)
    (h42878 : (¬ p2143) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3583) ∨ (¬ p3952))
    : (¬ p2901) ∨ p3051 ∨ p2839 ∨ (¬ p2143) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42878 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step92900 (p2156 p2901 p3051 p3136 p3556 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h58517 : (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3136) ∨ (¬ p3556))
    : p3051 ∨ (¬ p2901) ∨ (¬ p3136) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h58517 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step92903 (p2901 p2950 p3051 p3136 p3556 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h71976 : (¬ p3556) ∨ (¬ p2950) ∨ (¬ p2901) ∨ (¬ p3136))
    : (¬ p2901) ∨ (¬ p3136) ∨ p3051 ∨ (¬ p2950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71976 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step92906 (p2598 p2901 p2950 p3051 p3115 p3422 p3556 p3564 p4208 p4368 p4789 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73414 : p3556 ∨ p3051)
    (h65149 : (¬ p2598) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3422) ∨ (¬ p3556) ∨ (¬ p3564) ∨ (¬ p4208) ∨ (¬ p4368) ∨ (¬ p4789))
    : (¬ p4368) ∨ p3115 ∨ p3051 ∨ (¬ p4789) ∨ (¬ p3564) ∨ (¬ p3422) ∨ (¬ p2598) ∨ (¬ p2901) ∨ (¬ p2950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4368 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h65149 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step92911 (p2249 p2655 p2901 p2992 p3051 p3556 p3904 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h51751 : (¬ p2249) ∨ (¬ p2655) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3556) ∨ (¬ p3904))
    : (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3904) ∨ p3051 ∨ (¬ p2655) ∨ (¬ p2249) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51751 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step92912 (p2901 p3016 p3051 p3413 p3556 p3574 p4031 p4715 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73414 : p3556 ∨ p3051)
    (h52754 : (¬ p2901) ∨ (¬ p3413) ∨ (¬ p3556) ∨ (¬ p3574) ∨ (¬ p4031) ∨ (¬ p4715))
    : (¬ p2901) ∨ (¬ p4031) ∨ p3016 ∨ p3051 ∨ (¬ p3413) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52754 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step92914 (p2427 p2563 p2651 p2950 p3051 p3556 p4110 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73516 : p4110 ∨ p2563)
    (h56639 : (¬ p2427) ∨ (¬ p2651) ∨ (¬ p2950) ∨ (¬ p3556) ∨ (¬ p4110))
    : p3051 ∨ (¬ p2950) ∨ (¬ p2427) ∨ p2563 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56639 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step92918 (p2727 p2881 p2957 p2992 p3051 p3556 p3570 p3662 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73418 : p3570 ∨ p2881)
    (h73414 : p3556 ∨ p3051)
    (h47658 : (¬ p2727) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662))
    : p2992 ∨ (¬ p2957) ∨ p2881 ∨ (¬ p2727) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47658 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92920 (p2459 p2573 p3016 p3051 p3083 p3146 p3519 p3556 p3574 p3645 p3692 p4119 p4376 p4420 p4874 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73414 : p3556 ∨ p3051)
    (h73422 : p3574 ∨ p3016)
    (h42457 : (¬ p2459) ∨ (¬ p2573) ∨ (¬ p3083) ∨ (¬ p3519) ∨ (¬ p3556) ∨ (¬ p3574) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4376) ∨ (¬ p4420) ∨ (¬ p4874))
    : p3146 ∨ p3051 ∨ (¬ p4420) ∨ (¬ p3083) ∨ (¬ p3519) ∨ (¬ p4874) ∨ (¬ p4119) ∨ (¬ p2459) ∨ p3016 ∨ (¬ p3645) ∨ (¬ p2573) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u13 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u14 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h42457 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u14))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u2))) (fun r10 => (False.elim (r10 u5)))))))))))))))))))))))))

theorem step92923 (p2143 p2761 p2839 p3051 p3246 p3556 p3583 p3690 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73414 : p3556 ∨ p3051)
    (h73446 : p3690 ∨ p3246)
    (h73424 : p3583 ∨ p2839)
    (h43777 : (¬ p2143) ∨ (¬ p3556) ∨ (¬ p3583) ∨ (¬ p3690) ∨ (¬ p4381))
    : p2761 ∨ p3051 ∨ p3246 ∨ p2839 ∨ (¬ p2143) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43777 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step92925 (p2881 p3051 p3556 p3570 p3979 p5558 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73414 : p3556 ∨ p3051)
    (h57275 : (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3979) ∨ (¬ p5558))
    : (¬ p5558) ∨ (¬ p3979) ∨ p2881 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57275 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step92926 (p2187 p2668 p2901 p2950 p3051 p3324 p3556 p4153 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73414 : p3556 ∨ p3051)
    (h46900 : (¬ p2187) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3324) ∨ (¬ p3556) ∨ (¬ p4153))
    : p2668 ∨ (¬ p2187) ∨ (¬ p2901) ∨ (¬ p4153) ∨ p3051 ∨ (¬ p2950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2668) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46900 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step92927 (p2274 p2284 p2901 p3051 p3097 p3556 p3952 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73496 : p3952 ∨ p2284)
    (h73352 : p3097 ∨ p2274)
    (h47958 : (¬ p2901) ∨ (¬ p3097) ∨ (¬ p3556) ∨ (¬ p3952))
    : (¬ p2901) ∨ p3051 ∨ p2284 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47958 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step92936 (p2911 p4404 p5951 : Prop)
    (h74275 : (¬ p2911) ∨ (¬ p5951))
    (h12687 : p4404 ∨ p5951)
    : p4404 ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4404) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5951) := (Or.elim h74275 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12687 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step92937 (p2911 p3875 p5951 : Prop)
    (h74275 : (¬ p2911) ∨ (¬ p5951))
    (h12688 : p3875 ∨ p5951)
    : p3875 ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3875) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5951) := (Or.elim h74275 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12688 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step92939 (p2911 p4438 p5951 : Prop)
    (h74275 : (¬ p2911) ∨ (¬ p5951))
    (h12691 : p4438 ∨ p5951)
    : p4438 ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4438) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5951) := (Or.elim h74275 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step92946 (p2132 p2138 p2192 p3425 p3471 p4173 p4243 p4344 p4558 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73528 : p4173 ∨ p2192)
    (h73396 : p3471 ∨ p3425)
    (h54755 : (¬ p2138) ∨ (¬ p3471) ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4344) ∨ (¬ p4558))
    : p2132 ∨ (¬ p4243) ∨ (¬ p4344) ∨ p2192 ∨ p3425 ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54755 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step92948 (p2210 p2608 p3367 p3585 p3954 p4243 p4884 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73428 : p3585 ∨ p3367)
    (h49692 : (¬ p2210) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p4243) ∨ (¬ p4884))
    : (¬ p4243) ∨ p2608 ∨ p3367 ∨ (¬ p4884) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4243 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4884 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49692 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step92953 (p2192 p2870 p4173 p4204 p4243 : Prop)
    (h73528 : p4173 ∨ p2192)
    (h20556 : (¬ p2870) ∨ (¬ p4173) ∨ (¬ p4204) ∨ (¬ p4243))
    : (¬ p2870) ∨ (¬ p4204) ∨ p2192 ∨ (¬ p4243) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20556 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step92971 (p2619 p3051 p3556 p3645 p3694 p4119 p4243 : Prop)
    (h73449 : (¬ p2619) ∨ (¬ p3694))
    (h73414 : p3556 ∨ p3051)
    (h6662 : (¬ p3556) ∨ (¬ p3645) ∨ p3694 ∨ (¬ p4119) ∨ (¬ p4243))
    : (¬ p4243) ∨ (¬ p2619) ∨ p3051 ∨ (¬ p3645) ∨ (¬ p4119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4243 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p3694) := (Or.elim h73449 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6662 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step92975 (p2132 p2138 p2696 p2881 p2891 p3486 p3570 p4243 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73418 : p3570 ∨ p2881)
    (h73398 : p3486 ∨ p2891)
    (h56283 : (¬ p2138) ∨ (¬ p2696) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4243))
    : p2132 ∨ (¬ p4243) ∨ p2881 ∨ (¬ p2696) ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56283 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step92976 (p2132 p2138 p2352 p2573 p2881 p2891 p3367 p3486 p3570 p3759 p4133 p4243 p4734 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73214 : p2138 ∨ p2132)
    (h73398 : p3486 ∨ p2891)
    (h72735 : p4734)
    (h60465 : (¬ p2138) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p3759) ∨ (¬ p4133) ∨ (¬ p4243) ∨ (¬ p4734))
    : (¬ p4243) ∨ (¬ p3367) ∨ p2881 ∨ (¬ p2573) ∨ p2132 ∨ p2891 ∨ (¬ p2352) ∨ (¬ p3759) ∨ (¬ p4133) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4243 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4734 := h72735;
    (Or.elim h60465 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u12)))))))))))))))))))))

theorem step92978 (p2230 p2589 p2891 p3389 p3486 p3569 p4243 p4882 : Prop)
    (h73398 : p3486 ∨ p2891)
    (h73284 : p2589 ∨ p2230)
    (h51026 : (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3486) ∨ (¬ p3569) ∨ (¬ p4243) ∨ (¬ p4882))
    : (¬ p4243) ∨ (¬ p4882) ∨ (¬ p3389) ∨ p2891 ∨ (¬ p3569) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4243 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51026 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step92980 (p2144 p2166 p2191 p2220 p2598 p2870 p3055 p4243 : Prop)
    (h73222 : p2191 ∨ p2166)
    (h73350 : p3055 ∨ p2598)
    (h46943 : (¬ p2144) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p2870) ∨ (¬ p3055) ∨ (¬ p4243))
    : (¬ p2870) ∨ (¬ p2144) ∨ (¬ p2220) ∨ p2166 ∨ p2598 ∨ (¬ p4243) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46943 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step92982 (p2210 p2608 p2737 p2743 p3954 p4243 p5052 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73498 : p3954 ∨ p2608)
    (h50872 : (¬ p2210) ∨ (¬ p2743) ∨ (¬ p3954) ∨ (¬ p4243) ∨ (¬ p5052))
    : p2737 ∨ p2608 ∨ (¬ p2210) ∨ (¬ p4243) ∨ (¬ p5052) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50872 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step92983 (p2972 p3105 p4243 p4363 p4385 : Prop)
    (h73575 : (¬ p3105) ∨ (¬ p4385))
    (h73568 : p4363 ∨ p2972)
    (h37157 : (¬ p4243) ∨ (¬ p4363) ∨ p4385)
    : (¬ p3105) ∨ (¬ p4243) ∨ p2972 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4385) := (Or.elim h73575 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p4363 := (Or.elim h73568 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h37157 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (u3 r1)))))))

theorem step92989 (p2132 p2138 p2187 p2192 p2911 p3367 p3389 p3759 p3989 p4173 p4243 p4503 p4734 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73502 : p3989 ∨ p2187)
    (h73528 : p4173 ∨ p2192)
    (h72735 : p4734)
    (h62071 : (¬ p2138) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4503) ∨ (¬ p4734))
    : p2132 ∨ (¬ p2911) ∨ p2187 ∨ p2192 ∨ (¬ p3389) ∨ (¬ p4503) ∨ (¬ p3759) ∨ (¬ p4243) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2132) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p4734 := h72735;
    (Or.elim h62071 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u12)))))))))))))))))))))

theorem step92990 (p2132 p2138 p2166 p2191 p2417 p3146 p3367 p3389 p3692 p3759 p3950 p4243 p4734 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73222 : p2191 ∨ p2166)
    (h73214 : p2138 ∨ p2132)
    (h72735 : p4734)
    (h50667 : (¬ p2138) ∨ (¬ p2191) ∨ (¬ p2417) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3692) ∨ (¬ p3759) ∨ (¬ p3950) ∨ (¬ p4243) ∨ (¬ p4734))
    : (¬ p4243) ∨ p3146 ∨ (¬ p3367) ∨ p2166 ∨ (¬ p2417) ∨ (¬ p3950) ∨ (¬ p3389) ∨ p2132 ∨ (¬ p3759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4243 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p4734 := h72735;
    (Or.elim h50667 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u12)))))))))))))))))))))

theorem step92993 (p2870 p3073 p3146 p4243 p4261 p4492 p4901 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h62130 : (¬ p2870) ∨ (¬ p3146) ∨ (¬ p4243) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4901))
    : p3073 ∨ (¬ p3146) ∨ (¬ p4901) ∨ (¬ p2870) ∨ (¬ p4243) ∨ (¬ p4492) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h62130 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step93009 (p2608 p3093 p3537 p3954 p4242 p4243 p4512 p4741 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h73498 : p3954 ∨ p2608)
    (h53159 : (¬ p3093) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4243) ∨ (¬ p4512) ∨ (¬ p4741))
    : p3537 ∨ p2608 ∨ (¬ p3093) ∨ (¬ p4243) ∨ (¬ p4741) ∨ (¬ p4512) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53159 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step93014 (p2427 p2901 p3115 p4208 p4235 p4322 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73536 : p4235 ∨ p2427)
    (h59034 : (¬ p2901) ∨ (¬ p4208) ∨ (¬ p4235) ∨ (¬ p4322))
    : (¬ p4322) ∨ p3115 ∨ (¬ p2901) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59034 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step93015 (p2901 p3115 p3276 p4208 p4322 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h44387 : (¬ p2901) ∨ (¬ p3276) ∨ (¬ p4208) ∨ (¬ p4322))
    : (¬ p4322) ∨ p3115 ∨ (¬ p3276) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44387 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step93016 (p2396 p2901 p3115 p4208 p4382 p4556 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h50105 : (¬ p2396) ∨ (¬ p2901) ∨ (¬ p4208) ∨ (¬ p4382) ∨ (¬ p4556))
    : p3115 ∨ (¬ p2396) ∨ (¬ p4382) ∨ (¬ p4556) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4382 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50105 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93019 (p2901 p2911 p2927 p3115 p3516 p3543 p3644 p4208 p4382 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73534 : p4208 ∨ p3115)
    (h60995 : (¬ p2901) ∨ (¬ p2927) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p3644) ∨ (¬ p4208) ∨ (¬ p4382))
    : (¬ p3516) ∨ (¬ p2927) ∨ (¬ p3543) ∨ p2911 ∨ (¬ p4382) ∨ (¬ p2901) ∨ p3115 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2927 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4382 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h60995 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step93022 (p2241 p2247 p2284 p3115 p3830 p4208 p4387 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73226 : p2247 ∨ p2241)
    (h63878 : (¬ p2247) ∨ (¬ p2284) ∨ (¬ p3830) ∨ (¬ p4208) ∨ (¬ p4387))
    : p3115 ∨ (¬ p4387) ∨ p2241 ∨ (¬ p3830) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p4387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h63878 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step93024 (p2210 p2284 p2972 p3115 p4208 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h45854 : (¬ p2210) ∨ (¬ p2284) ∨ (¬ p2972) ∨ (¬ p4208))
    : p3115 ∨ (¬ p2972) ∨ (¬ p2210) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45854 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step93025 (p2145 p2156 p2284 p2417 p2598 p3115 p3201 p3646 p3951 p4208 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73436 : p3646 ∨ p2156)
    (h65031 : (¬ p2145) ∨ (¬ p2284) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3646) ∨ (¬ p3951) ∨ (¬ p4208))
    : (¬ p2284) ∨ p3115 ∨ (¬ p2598) ∨ (¬ p3951) ∨ (¬ p3201) ∨ (¬ p2145) ∨ (¬ p2417) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h65031 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step93026 (p2156 p2284 p2417 p2598 p2950 p3115 p3201 p3646 p3951 p4208 p4789 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73436 : p3646 ∨ p2156)
    (h65263 : (¬ p2284) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2950) ∨ (¬ p3201) ∨ (¬ p3646) ∨ (¬ p3951) ∨ (¬ p4208) ∨ (¬ p4789))
    : p3115 ∨ (¬ p2284) ∨ p2156 ∨ (¬ p2417) ∨ (¬ p3951) ∨ (¬ p2598) ∨ (¬ p4789) ∨ (¬ p3201) ∨ (¬ p2950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h65263 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step93027 (p2284 p3115 p4208 p4334 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h6726 : (¬ p2284) ∨ (¬ p4208) ∨ (¬ p4334))
    : p3115 ∨ (¬ p4334) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p4334 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6726 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step93032 (p2427 p2982 p3115 p3136 p4208 p4235 p4315 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73536 : p4235 ∨ p2427)
    (h73550 : p4315 ∨ p3136)
    (h60068 : (¬ p2982) ∨ (¬ p4208) ∨ (¬ p4235) ∨ (¬ p4315))
    : p3115 ∨ (¬ p2982) ∨ p2427 ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60068 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step93035 (p2331 p2946 p2952 p3105 p3115 p4208 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73330 : p2952 ∨ p2946)
    (h61256 : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3105) ∨ (¬ p4208))
    : (¬ p2331) ∨ p3115 ∨ (¬ p3105) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61256 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step93037 (p2459 p3115 p3156 p3949 p4208 p4902 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h51116 : (¬ p2459) ∨ (¬ p3156) ∨ (¬ p3949) ∨ (¬ p4208) ∨ (¬ p4902))
    : p3115 ∨ (¬ p3949) ∨ (¬ p4902) ∨ (¬ p2459) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p3949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51116 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93039 (p2230 p2264 p2982 p2995 p3115 p4208 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h63851 : (¬ p2230) ∨ (¬ p2264) ∨ (¬ p2982) ∨ (¬ p2995) ∨ (¬ p4208))
    : p3115 ∨ (¬ p2982) ∨ (¬ p2264) ∨ (¬ p2230) ∨ (¬ p2995) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h63851 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step93041 (p2254 p2946 p2952 p3063 p3093 p3115 p3979 p4208 p4322 p5119 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73534 : p4208 ∨ p3115)
    (h48834 : (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3979) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p5119))
    : (¬ p4322) ∨ (¬ p3063) ∨ (¬ p2254) ∨ p2946 ∨ (¬ p5119) ∨ p3115 ∨ (¬ p3093) ∨ (¬ p3979) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48834 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step93043 (p2860 p2946 p2952 p3105 p3115 p3758 p4208 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73456 : p3758 ∨ p2860)
    (h73330 : p2952 ∨ p2946)
    (h56624 : (¬ p2952) ∨ (¬ p3105) ∨ (¬ p3758) ∨ (¬ p4208))
    : (¬ p3105) ∨ p3115 ∨ p2860 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56624 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step93045 (p2563 p2946 p2952 p2982 p3115 p4110 p4208 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73516 : p4110 ∨ p2563)
    (h73330 : p2952 ∨ p2946)
    (h55049 : (¬ p2952) ∨ (¬ p2982) ∨ (¬ p4110) ∨ (¬ p4208))
    : (¬ p2982) ∨ p3115 ∨ p2563 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55049 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step93046 (p2563 p2982 p3115 p3136 p4110 p4208 p4315 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73516 : p4110 ∨ p2563)
    (h73550 : p4315 ∨ p3136)
    (h60142 : (¬ p2982) ∨ (¬ p4110) ∨ (¬ p4208) ∨ (¬ p4315))
    : p3115 ∨ (¬ p2982) ∨ p2563 ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60142 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step93047 (p2210 p2284 p2459 p2911 p2972 p3115 p3389 p3540 p3644 p4208 p4348 p5193 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73402 : p3540 ∨ p3389)
    (h73434 : p3644 ∨ p2911)
    (h73562 : p4348 ∨ p2459)
    (h50502 : (¬ p2210) ∨ (¬ p2284) ∨ (¬ p2972) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4208) ∨ (¬ p4348) ∨ (¬ p5193))
    : p3115 ∨ p3389 ∨ (¬ p2284) ∨ p2911 ∨ p2459 ∨ (¬ p2210) ∨ (¬ p2972) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50502 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step93048 (p2230 p2437 p2663 p2982 p3115 p4208 p4700 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h47414 : (¬ p2230) ∨ (¬ p2437) ∨ (¬ p2663) ∨ (¬ p2982) ∨ (¬ p4208) ∨ (¬ p4700))
    : (¬ p4700) ∨ (¬ p2982) ∨ p3115 ∨ (¬ p2663) ∨ (¬ p2437) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4700 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47414 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step93050 (p2145 p2220 p3115 p3156 p3276 p3355 p3362 p3461 p4120 p4191 p4208 p4368 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73534 : p4208 ∨ p3115)
    (h73522 : p4120 ∨ p2220)
    (h64875 : (¬ p2145) ∨ (¬ p3156) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p4120) ∨ (¬ p4191) ∨ (¬ p4208) ∨ (¬ p4368))
    : (¬ p3276) ∨ p3461 ∨ p3115 ∨ (¬ p3156) ∨ (¬ p2145) ∨ p2220 ∨ (¬ p3362) ∨ (¬ p4368) ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h64875 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step93052 (p3115 p3136 p3276 p4208 p4315 p4322 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73550 : p4315 ∨ p3136)
    (h45627 : (¬ p3276) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4322))
    : (¬ p4322) ∨ (¬ p3276) ∨ p3115 ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45627 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step93054 (p2563 p3115 p3483 p4033 p4208 p4241 p4401 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h42175 : (¬ p2563) ∨ (¬ p3483) ∨ (¬ p4033) ∨ (¬ p4208) ∨ (¬ p4241) ∨ (¬ p4401))
    : (¬ p3483) ∨ p3115 ∨ (¬ p2563) ∨ (¬ p4033) ∨ (¬ p4401) ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4401 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42175 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step93055 (p2274 p2284 p3115 p4033 p4208 p4620 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h41514 : (¬ p2274) ∨ (¬ p2284) ∨ (¬ p4033) ∨ (¬ p4208) ∨ (¬ p4620))
    : p3115 ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p4620) ∨ (¬ p4033) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41514 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93057 (p2264 p2911 p2995 p3115 p3212 p3581 p3644 p4208 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73434 : p3644 ∨ p2911)
    (h45585 : (¬ p2264) ∨ (¬ p2995) ∨ (¬ p3212) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p4208))
    : p3115 ∨ (¬ p3212) ∨ (¬ p2995) ∨ (¬ p2264) ∨ (¬ p3581) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h45585 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step93059 (p2598 p2946 p2952 p3115 p3201 p3868 p4208 p4322 p4789 p4826 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73330 : p2952 ∨ p2946)
    (h51578 : (¬ p2598) ∨ (¬ p2952) ∨ (¬ p3201) ∨ (¬ p3868) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4789) ∨ (¬ p4826))
    : (¬ p4322) ∨ (¬ p3868) ∨ (¬ p3201) ∨ (¬ p2598) ∨ p3115 ∨ p2946 ∨ (¬ p4826) ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51578 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step93060 (p2254 p2922 p2946 p2952 p3115 p3379 p3868 p4208 p4322 p4826 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73534 : p4208 ∨ p3115)
    (h59761 : (¬ p2254) ∨ (¬ p2922) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3868) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4826))
    : (¬ p3868) ∨ (¬ p4322) ∨ (¬ p2254) ∨ (¬ p4826) ∨ p2946 ∨ p3115 ∨ (¬ p2922) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3868 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h59761 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step93064 (p2352 p2363 p2573 p2696 p3115 p3136 p3365 p3366 p3519 p4208 p4315 p4376 p5059 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73390 : p3365 ∨ p2696)
    (h73534 : p4208 ∨ p3115)
    (h63374 : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4376) ∨ (¬ p5059))
    : (¬ p2352) ∨ (¬ p3519) ∨ (¬ p3366) ∨ p3136 ∨ (¬ p4376) ∨ (¬ p2573) ∨ (¬ p2363) ∨ p2696 ∨ (¬ p5059) ∨ p3115 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h63374 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step93067 (p3115 p3276 p3707 p4208 p4321 p4387 p4449 p4702 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73534 : p4208 ∨ p3115)
    (h58012 : (¬ p3276) ∨ (¬ p4208) ∨ (¬ p4321) ∨ (¬ p4387) ∨ (¬ p4449) ∨ (¬ p4702))
    : p3707 ∨ (¬ p3276) ∨ p3115 ∨ (¬ p4387) ∨ (¬ p4702) ∨ (¬ p4449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58012 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step93070 (p3115 p3156 p3949 p3969 p4208 p5122 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h54376 : (¬ p3156) ∨ (¬ p3949) ∨ (¬ p3969) ∨ (¬ p4208) ∨ (¬ p5122))
    : (¬ p3969) ∨ p3115 ∨ (¬ p3949) ∨ (¬ p5122) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54376 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93072 (p2598 p2946 p2952 p3115 p3641 p4149 p4208 p4322 p4789 p5119 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73534 : p4208 ∨ p3115)
    (h65167 : (¬ p2598) ∨ (¬ p2952) ∨ (¬ p3641) ∨ (¬ p4149) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4789) ∨ (¬ p5119))
    : (¬ p4322) ∨ (¬ p3641) ∨ (¬ p4149) ∨ (¬ p5119) ∨ p2946 ∨ p3115 ∨ (¬ p2598) ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h65167 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step93079 (p2122 p2241 p2247 p2396 p2774 p3189 p3256 p3950 p4118 p4360 p4733 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73566 : p4360 ∨ p3189)
    (h73520 : p4118 ∨ p3256)
    (h50048 : (¬ p2122) ∨ (¬ p2247) ∨ (¬ p2396) ∨ (¬ p2774) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4733))
    : (¬ p2122) ∨ p2241 ∨ (¬ p4733) ∨ (¬ p3950) ∨ p3189 ∨ (¬ p2396) ∨ p3256 ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h50048 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step93086 (p2132 p2274 p2860 p2911 p3399 p3527 p3548 p4366 p4712 p4733 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73570 : p4366 ∨ p3399)
    (h63717 : (¬ p2132) ∨ (¬ p2274) ∨ (¬ p2860) ∨ (¬ p2911) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4712) ∨ (¬ p4733))
    : (¬ p4712) ∨ (¬ p2274) ∨ (¬ p2860) ∨ p3527 ∨ (¬ p2132) ∨ p3399 ∨ (¬ p4733) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4712 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63717 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step93087 (p2132 p2459 p2860 p3125 p3399 p3527 p3548 p4330 p4348 p4366 p4733 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73570 : p4366 ∨ p3399)
    (h73562 : p4348 ∨ p2459)
    (h50639 : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3548) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4733))
    : (¬ p2132) ∨ (¬ p2860) ∨ p3527 ∨ p3399 ∨ (¬ p3125) ∨ p2459 ∨ (¬ p4733) ∨ (¬ p4330) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50639 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step93097 (p2177 p2299 p2696 p3093 p3136 p3156 p3309 p3549 p3591 p4733 p4902 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73406 : p3549 ∨ p3309)
    (h73234 : p2299 ∨ p2177)
    (h51329 : (¬ p2299) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4733) ∨ (¬ p4902))
    : (¬ p3156) ∨ p3093 ∨ (¬ p4733) ∨ p3309 ∨ p2177 ∨ (¬ p4902) ∨ (¬ p2696) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51329 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step93098 (p2373 p2406 p2668 p2696 p2797 p3238 p3379 p3452 p3880 p4134 p4733 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73394 : p3452 ∨ p3379)
    (h73374 : p3238 ∨ p2406)
    (h54604 : (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4733))
    : (¬ p2668) ∨ p2373 ∨ (¬ p4733) ∨ p3379 ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p4134) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h54604 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step93100 (p3246 p4382 p5101 : Prop)
    (h73918 : p5101 ∨ p3246)
    (h8608 : p4382 ∨ (¬ p5101))
    : p4382 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4382) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr h));
    let u2 : p5101 := (Or.elim h73918 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h8608 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step93101 (p3246 p4382 p6010 : Prop)
    (h74345 : p3246 ∨ (¬ p6010))
    (h13053 : p4382 ∨ p6010)
    : p4382 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4382) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6010) := (Or.elim h74345 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13053 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93103 (p2156 p2417 p2608 p2707 p3461 p3588 p3680 p3954 p4106 p4191 p4278 p4334 p4521 p4621 : Prop)
    (h73430 : p3588 ∨ p2707)
    (h73530 : p4191 ∨ p3461)
    (h73546 : p4278 ∨ p2417)
    (h73498 : p3954 ∨ p2608)
    (h55811 : (¬ p2156) ∨ (¬ p3588) ∨ (¬ p3680) ∨ (¬ p3954) ∨ (¬ p4106) ∨ (¬ p4191) ∨ (¬ p4278) ∨ (¬ p4334) ∨ (¬ p4521) ∨ (¬ p4621))
    : (¬ p4334) ∨ (¬ p3680) ∨ (¬ p4106) ∨ p2707 ∨ (¬ p2156) ∨ (¬ p4621) ∨ p3461 ∨ p2417 ∨ (¬ p4521) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4334 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3588 := (Or.elim h73430 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h55811 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step93105 (p2230 p2589 p2655 p2761 p2786 p3146 p3156 p3461 p3497 p3654 p3692 p3950 p4241 p4381 p4789 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73448 : p3692 ∨ p3146)
    (h73284 : p2589 ∨ p2230)
    (h73400 : p3497 ∨ p3156)
    (h61966 : (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2786) ∨ (¬ p3461) ∨ (¬ p3497) ∨ (¬ p3654) ∨ (¬ p3692) ∨ (¬ p3950) ∨ (¬ p4241) ∨ (¬ p4381) ∨ (¬ p4789))
    : p2761 ∨ (¬ p3654) ∨ (¬ p2655) ∨ (¬ p4789) ∨ (¬ p2786) ∨ (¬ p3950) ∨ p3146 ∨ (¬ p4241) ∨ (¬ p3461) ∨ p2230 ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u14 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h61966 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u14))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (False.elim (r9 u3)))))))))))))))))))))))

theorem step93106 (p2122 p2774 p3166 p3172 p3256 p3266 p3791 p4118 p4444 p4789 p4826 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73580 : p4444 ∨ p3266)
    (h73520 : p4118 ∨ p3256)
    (h64911 : (¬ p2122) ∨ (¬ p2774) ∨ (¬ p3172) ∨ (¬ p3791) ∨ (¬ p4118) ∨ (¬ p4444) ∨ (¬ p4789) ∨ (¬ p4826))
    : (¬ p3791) ∨ p3166 ∨ p3266 ∨ (¬ p2774) ∨ (¬ p2122) ∨ (¬ p4789) ∨ (¬ p4826) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64911 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step93108 (p2088 p2819 p3073 p3857 p4113 p4317 p4358 p4871 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73480 : p3857 ∨ p2088)
    (h58028 : (¬ p3073) ∨ (¬ p3857) ∨ (¬ p4113) ∨ (¬ p4317) ∨ (¬ p4358) ∨ (¬ p4871))
    : (¬ p4317) ∨ (¬ p4113) ∨ (¬ p3073) ∨ p2819 ∨ p2088 ∨ (¬ p4871) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4317 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4871 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58028 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step93110 (p2363 p2819 p3256 p4341 p4347 p4358 p4843 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73564 : p4358 ∨ p2819)
    (h51999 : (¬ p3256) ∨ (¬ p4341) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4843))
    : p2363 ∨ (¬ p3256) ∨ (¬ p4843) ∨ (¬ p4341) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4843 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51999 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93111 (p2331 p2819 p2963 p3166 p4358 p4417 p4843 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73564 : p4358 ∨ p2819)
    (h50572 : (¬ p2963) ∨ (¬ p3166) ∨ (¬ p4358) ∨ (¬ p4417) ∨ (¬ p4843))
    : p2331 ∨ (¬ p3166) ∨ p2819 ∨ (¬ p4843) ∨ (¬ p4417) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4843 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50572 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93114 (p2295 p2307 p2313 p2383 p2819 p4358 p4843 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73564 : p4358 ∨ p2819)
    (h57257 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p4358) ∨ (¬ p4843))
    : (¬ p2383) ∨ p2307 ∨ (¬ p4843) ∨ (¬ p2295) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4843 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57257 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93117 (p2230 p2331 p2373 p2589 p3323 p3461 p3880 p4117 p4729 p5123 p5568 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73284 : p2589 ∨ p2230)
    (h53322 : (¬ p2331) ∨ (¬ p2589) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3880) ∨ (¬ p4117) ∨ (¬ p4729) ∨ (¬ p5123) ∨ (¬ p5568))
    : (¬ p5568) ∨ (¬ p5123) ∨ (¬ p4117) ∨ p2373 ∨ (¬ p3461) ∨ (¬ p4729) ∨ p2230 ∨ (¬ p3323) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h53322 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step93122 (p2819 p4857 p5923 : Prop)
    (h74237 : p2819 ∨ (¬ p5923))
    (h12524 : p4857 ∨ p5923)
    : p4857 ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4857) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2819) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5923) := (Or.elim h74237 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12524 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93123 (p2156 p2685 p2696 p2753 p3125 p3461 p3645 p3646 p3744 p3931 p4191 p4826 p4877 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73530 : p4191 ∨ p3461)
    (h73454 : p3744 ∨ p3125)
    (h63797 : (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3931) ∨ (¬ p4191) ∨ (¬ p4826) ∨ (¬ p4877))
    : (¬ p3931) ∨ (¬ p2753) ∨ (¬ p2696) ∨ p2156 ∨ (¬ p4877) ∨ (¬ p2685) ∨ p3461 ∨ (¬ p4826) ∨ p3125 ∨ (¬ p3645) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3931 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h63797 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step93124 (p2156 p2753 p2911 p3125 p3425 p3461 p3471 p3645 p3646 p3744 p4191 p4253 p4877 p5503 : Prop)
    (h73396 : p3471 ∨ p3425)
    (h73530 : p4191 ∨ p3461)
    (h73454 : p3744 ∨ p3125)
    (h73436 : p3646 ∨ p2156)
    (h51306 : (¬ p2753) ∨ (¬ p2911) ∨ (¬ p3471) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4191) ∨ (¬ p4253) ∨ (¬ p4877) ∨ (¬ p5503))
    : (¬ p4253) ∨ (¬ p5503) ∨ (¬ p3645) ∨ p3425 ∨ p3461 ∨ p3125 ∨ (¬ p2911) ∨ p2156 ∨ (¬ p4877) ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51306 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step93127 (p2210 p2696 p2753 p2797 p3073 p3323 p3449 p3860 p4261 p4330 p4877 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73482 : p3860 ∨ p3449)
    (h51473 : (¬ p2210) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4330) ∨ (¬ p4877))
    : p3073 ∨ p3449 ∨ (¬ p4330) ∨ (¬ p2210) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p2696) ∨ (¬ p4877) ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51473 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step93135 (p2088 p2363 p3857 p3961 p4063 p4138 p5564 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h57903 : (¬ p2363) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4063) ∨ (¬ p4138) ∨ (¬ p5564))
    : (¬ p4063) ∨ (¬ p5564) ∨ (¬ p2363) ∨ p2088 ∨ (¬ p4138) ∨ (¬ p3961) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57903 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step93137 (p2122 p2819 p3791 p4138 p4358 p5564 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h42440 : (¬ p2122) ∨ (¬ p3791) ∨ (¬ p4138) ∨ (¬ p4358) ∨ (¬ p5564))
    : (¬ p3791) ∨ (¬ p5564) ∨ (¬ p2122) ∨ (¬ p4138) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42440 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step93139 (p2122 p2177 p2241 p2247 p2299 p2744 p2774 p2780 p3366 p3399 p3822 p4075 p5564 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73234 : p2299 ∨ p2177)
    (h73472 : p3822 ∨ p2122)
    (h73308 : p2780 ∨ p2774)
    (h61851 : (¬ p2247) ∨ (¬ p2299) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3822) ∨ (¬ p4075) ∨ (¬ p5564))
    : (¬ p4075) ∨ (¬ p5564) ∨ (¬ p2744) ∨ p2241 ∨ p2177 ∨ (¬ p3399) ∨ (¬ p3366) ∨ p2122 ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4075 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h61851 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step93141 (p2098 p2252 p2331 p2363 p2598 p2668 p2748 p2963 p3055 p3324 p4019 p4347 p4749 p5122 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73338 : p2963 ∨ p2331)
    (h73350 : p3055 ∨ p2598)
    (h73560 : p4347 ∨ p2363)
    (h42164 : (¬ p2098) ∨ (¬ p2252) ∨ (¬ p2748) ∨ (¬ p2963) ∨ (¬ p3055) ∨ (¬ p3324) ∨ (¬ p4019) ∨ (¬ p4347) ∨ (¬ p4749) ∨ (¬ p5122))
    : (¬ p4019) ∨ (¬ p2098) ∨ p2668 ∨ p2331 ∨ p2598 ∨ (¬ p5122) ∨ (¬ p4749) ∨ (¬ p2252) ∨ (¬ p2748) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4019 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h42164 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step93143 (p2098 p2427 p2598 p2850 p3055 p3684 p4235 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73350 : p3055 ∨ p2598)
    (h73536 : p4235 ∨ p2427)
    (h46662 : (¬ p2098) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p4235))
    : (¬ p2098) ∨ p2850 ∨ p2598 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46662 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step93145 (p2098 p2166 p2191 p2619 p4743 : Prop)
    (h73738 : p4743 ∨ (¬ p2619))
    (h73222 : p2191 ∨ p2166)
    (h65702 : (¬ p4743) ∨ (¬ p2098) ∨ (¬ p2191))
    : (¬ p2098) ∨ (¬ p2619) ∨ p2166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4743 := (Or.elim h73738 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u4 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h65702 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u4)))))))

theorem step93146 (p2098 p2437 p2440 p2542 p2598 p3055 p3742 p4186 p5373 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73270 : p2542 ∨ p2440)
    (h73350 : p3055 ∨ p2598)
    (h48820 : (¬ p2098) ∨ (¬ p2542) ∨ (¬ p3055) ∨ (¬ p3742) ∨ (¬ p4186) ∨ (¬ p5373))
    : (¬ p2098) ∨ p2437 ∨ p2440 ∨ p2598 ∨ (¬ p5373) ∨ (¬ p4186) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48820 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step93147 (p2098 p2598 p2748 p2901 p3051 p3055 p3115 p3368 p3556 p3609 p3645 p4208 p4749 p5059 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73414 : p3556 ∨ p3051)
    (h73350 : p3055 ∨ p2598)
    (h57474 : (¬ p2098) ∨ (¬ p2748) ∨ (¬ p2901) ∨ (¬ p3055) ∨ (¬ p3368) ∨ (¬ p3556) ∨ (¬ p3609) ∨ (¬ p3645) ∨ (¬ p4208) ∨ (¬ p4749) ∨ (¬ p5059))
    : (¬ p2098) ∨ (¬ p3368) ∨ (¬ p2748) ∨ p3115 ∨ (¬ p3645) ∨ (¬ p2901) ∨ p3051 ∨ (¬ p5059) ∨ p2598 ∨ (¬ p4749) ∨ (¬ p3609) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h57474 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step93152 (p2098 p2470 p2598 p4726 : Prop)
    (h73728 : p4726 ∨ p2598)
    (h67039 : (¬ p4726) ∨ (¬ p2098) ∨ p2470)
    : (¬ p2098) ∨ p2470 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4726 := (Or.elim h73728 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67039 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step93155 (p2098 p2598 p2737 p3055 p3537 p4242 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h73350 : p3055 ∨ p2598)
    (h53329 : (¬ p2098) ∨ (¬ p2737) ∨ (¬ p3055) ∨ (¬ p4242))
    : p3537 ∨ (¬ p2098) ∨ (¬ p2737) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53329 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step93159 (p2098 p2696 p2707 p3365 p3537 p4242 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h73390 : p3365 ∨ p2696)
    (h47366 : (¬ p2098) ∨ (¬ p2707) ∨ (¬ p3365) ∨ (¬ p4242))
    : p3537 ∨ (¬ p2098) ∨ (¬ p2707) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47366 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step93161 (p2098 p2241 p2247 p2744 p3537 p3589 p4242 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h73226 : p2247 ∨ p2241)
    (h41199 : (¬ p2098) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3589) ∨ (¬ p4242))
    : p3537 ∨ p2241 ∨ (¬ p2098) ∨ (¬ p2744) ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41199 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step93163 (p2098 p2753 p3537 p4242 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h6369 : (¬ p2098) ∨ (¬ p2753) ∨ (¬ p4242))
    : p3537 ∨ (¬ p2753) ∨ (¬ p2098) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6369 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step93166 (p2098 p2881 p3425 p3570 p4804 p4898 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h41276 : (¬ p2098) ∨ (¬ p3425) ∨ (¬ p3570) ∨ (¬ p4804) ∨ (¬ p4898))
    : (¬ p4804) ∨ (¬ p2098) ∨ p2881 ∨ (¬ p4898) ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4804 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4898 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41276 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93169 (p2098 p2352 p2459 p2493 p2499 p3379 p3452 p3609 p3956 p4348 p4503 p4733 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73260 : p2499 ∨ p2493)
    (h73500 : p3956 ∨ p2352)
    (h73562 : p4348 ∨ p2459)
    (h57696 : (¬ p2098) ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p3609) ∨ (¬ p3956) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4733))
    : p3379 ∨ p2493 ∨ (¬ p2098) ∨ (¬ p4733) ∨ (¬ p3609) ∨ p2352 ∨ p2459 ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h57696 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step93170 (p2098 p2717 p3425 p3537 p3659 p4242 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h73438 : p3659 ∨ p2717)
    (h43386 : (¬ p2098) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4242))
    : (¬ p2098) ∨ p3537 ∨ (¬ p3425) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43386 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step93171 (p2098 p2737 p2774 p2780 p3537 p4242 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73538 : p4242 ∨ p3537)
    (h57984 : (¬ p2098) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p4242))
    : (¬ p2098) ∨ p2774 ∨ (¬ p2737) ∨ p3537 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57984 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step93178 (p2098 p2598 p2946 p2952 p3055 p3115 p3361 p4019 p4208 p4322 p4749 p5119 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73350 : p3055 ∨ p2598)
    (h73330 : p2952 ∨ p2946)
    (h59519 : (¬ p2098) ∨ (¬ p2952) ∨ (¬ p3055) ∨ (¬ p3361) ∨ (¬ p4019) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4749) ∨ (¬ p5119))
    : (¬ p4019) ∨ (¬ p2098) ∨ p3115 ∨ (¬ p3361) ∨ (¬ p4749) ∨ p2598 ∨ (¬ p5119) ∨ p2946 ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4019 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h59519 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step93179 (p2098 p2641 p2696 p2745 p3365 p4078 p4154 p4328 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73390 : p3365 ∨ p2696)
    (h48463 : (¬ p2098) ∨ (¬ p2745) ∨ (¬ p3365) ∨ (¬ p4078) ∨ (¬ p4154) ∨ (¬ p4328))
    : (¬ p2098) ∨ p2641 ∨ (¬ p4078) ∨ (¬ p4328) ∨ p2696 ∨ (¬ p2745) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48463 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step93185 (p2192 p2210 p2274 p2696 p2797 p3323 p3365 p4037 p4195 p4620 p4736 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73390 : p3365 ∨ p2696)
    (h73508 : p4037 ∨ p3323)
    (h56784 : (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (¬ p3365) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4620) ∨ (¬ p4736))
    : p2797 ∨ (¬ p2274) ∨ (¬ p2192) ∨ (¬ p2210) ∨ p2696 ∨ (¬ p4736) ∨ p3323 ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h56784 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step93186 (p2437 p3016 p3564 p3574 p4137 p4620 p4710 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73524 : p4137 ∨ p3564)
    (h41333 : (¬ p2437) ∨ (¬ p3574) ∨ (¬ p4137) ∨ (¬ p4620) ∨ (¬ p4710))
    : (¬ p2437) ∨ p3016 ∨ (¬ p4620) ∨ (¬ p4710) ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41333 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93188 (p2284 p2901 p3654 p3946 p3952 p4140 p4356 p4620 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73492 : p3946 ∨ p3654)
    (h53510 : (¬ p2901) ∨ (¬ p3946) ∨ (¬ p3952) ∨ (¬ p4140) ∨ (¬ p4356) ∨ (¬ p4620))
    : (¬ p2901) ∨ p2284 ∨ (¬ p4620) ∨ (¬ p4140) ∨ (¬ p4356) ∨ p3654 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h53510 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step93189 (p2295 p3093 p3830 p3834 p3922 p4620 p5148 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h42019 : (¬ p2295) ∨ (¬ p3093) ∨ (¬ p3834) ∨ (¬ p3922) ∨ (¬ p4620) ∨ (¬ p5148))
    : p3830 ∨ (¬ p3922) ∨ (¬ p3093) ∨ (¬ p2295) ∨ (¬ p5148) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5148 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42019 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step93190 (p2284 p2901 p3309 p3549 p3952 p4140 p4514 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73406 : p3549 ∨ p3309)
    (h48169 : (¬ p2901) ∨ (¬ p3549) ∨ (¬ p3952) ∨ (¬ p4140) ∨ (¬ p4514))
    : (¬ p2901) ∨ (¬ p4140) ∨ (¬ p4514) ∨ p2284 ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48169 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93192 (p2187 p2307 p2383 p2387 p3309 p3549 p4514 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h73246 : p2387 ∨ p2383)
    (h48038 : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p3549) ∨ (¬ p4514))
    : p3309 ∨ (¬ p2187) ∨ (¬ p4514) ∨ (¬ p2307) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3309) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48038 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93195 (p2190 p2363 p3146 p3923 p4347 p4514 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h41625 : (¬ p2190) ∨ (¬ p3146) ∨ (¬ p3923) ∨ (¬ p4347) ∨ (¬ p4514))
    : p2363 ∨ (¬ p3146) ∨ (¬ p2190) ∨ (¬ p3923) ∨ (¬ p4514) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41625 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93202 (p2441 p2563 p2881 p2911 p3644 p4555 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h62255 : (¬ p2441) ∨ (¬ p2563) ∨ (¬ p2881) ∨ (¬ p3644) ∨ (¬ p4555))
    : p2911 ∨ (¬ p2881) ∨ (¬ p2441) ∨ (¬ p4555) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h62255 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93204 (p3564 p3917 p4137 p4342 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h31063 : p3917 ∨ (¬ p4137) ∨ (¬ p4342))
    : p3917 ∨ p3564 ∨ (¬ p4342) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3917) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h31063 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step93205 (p3323 p3917 p4037 p4337 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h38842 : p3917 ∨ (¬ p4037) ∨ (¬ p4337))
    : p3917 ∨ (¬ p4337) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3917) := (fun h => hn (Or.inl h));
    let u1 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h38842 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step93206 (p3461 p5248 p6058 : Prop)
    (h74401 : p3461 ∨ (¬ p6058))
    (h13353 : p5248 ∨ p6058)
    : p5248 ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5248) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6058) := (Or.elim h74401 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13353 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93207 (p3461 p5247 p6058 : Prop)
    (h74401 : p3461 ∨ (¬ p6058))
    (h13355 : p5247 ∨ p6058)
    : p5247 ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5247) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6058) := (Or.elim h74401 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13355 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93209 (p3461 p5250 p6058 : Prop)
    (h74401 : p3461 ∨ (¬ p6058))
    (h13357 : p5250 ∨ p6058)
    : p5250 ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5250) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6058) := (Or.elim h74401 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13357 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93210 (p2807 p3286 p3292 p3414 p4429 : Prop)
    (h73377 : (¬ p3286) ∨ (¬ p3292))
    (h73392 : p3414 ∨ p2807)
    (h28668 : p3292 ∨ (¬ p3414) ∨ (¬ p4429))
    : (¬ p4429) ∨ (¬ p3286) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4429 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3292) := (Or.elim h73377 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h28668 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u0)))))))

theorem step93212 (p3166 p3172 p3286 p3292 p4349 : Prop)
    (h73377 : (¬ p3286) ∨ (¬ p3292))
    (h73356 : p3172 ∨ p3166)
    (h6610 : (¬ p3172) ∨ p3292 ∨ (¬ p4349))
    : (¬ p4349) ∨ (¬ p3286) ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4349 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3292) := (Or.elim h73377 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6610 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step93214 (p2274 p2417 p3125 p3744 p4396 p4712 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h49264 : (¬ p2274) ∨ (¬ p2417) ∨ (¬ p3744) ∨ (¬ p4396) ∨ (¬ p4712))
    : (¬ p2417) ∨ p3125 ∨ (¬ p4712) ∨ (¬ p4396) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49264 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93220 (p2417 p2807 p3286 p3414 p4278 p4653 p4660 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73392 : p3414 ∨ p2807)
    (h41806 : (¬ p3286) ∨ (¬ p3414) ∨ (¬ p4278) ∨ (¬ p4653) ∨ (¬ p4660))
    : (¬ p4660) ∨ p2417 ∨ (¬ p3286) ∨ (¬ p4653) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4660 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41806 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step93221 (p2396 p2807 p3286 p3414 p3740 p4107 p4660 p4712 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73392 : p3414 ∨ p2807)
    (h49263 : (¬ p3286) ∨ (¬ p3414) ∨ (¬ p3740) ∨ (¬ p4107) ∨ (¬ p4660) ∨ (¬ p4712))
    : (¬ p4660) ∨ (¬ p3286) ∨ p2396 ∨ (¬ p3740) ∨ (¬ p4712) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4660 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49263 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step93223 (p2807 p3246 p3286 p3414 p3690 p4362 p5233 p5454 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73392 : p3414 ∨ p2807)
    (h42628 : (¬ p3286) ∨ (¬ p3414) ∨ (¬ p3690) ∨ (¬ p4362) ∨ (¬ p5233) ∨ (¬ p5454))
    : (¬ p5233) ∨ (¬ p5454) ∨ (¬ p3286) ∨ (¬ p4362) ∨ p3246 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5233 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5454 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42628 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step93226 (p2298 p2807 p3246 p3286 p3414 p3690 p4556 p4660 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73392 : p3414 ∨ p2807)
    (h59914 : (¬ p2298) ∨ (¬ p3286) ∨ (¬ p3414) ∨ (¬ p3690) ∨ (¬ p4556) ∨ (¬ p4660))
    : (¬ p4660) ∨ (¬ p2298) ∨ (¬ p3286) ∨ p3246 ∨ (¬ p4556) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4660 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h59914 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step93234 (p2946 p2952 p3286 p4314 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h32263 : (¬ p2952) ∨ (¬ p3286) ∨ (¬ p4314))
    : (¬ p3286) ∨ (¬ p4314) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4314 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h32263 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step93235 (p2946 p2952 p2992 p3286 p3680 p4039 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h56577 : (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3286) ∨ (¬ p3680) ∨ (¬ p4039))
    : (¬ p3286) ∨ (¬ p4039) ∨ (¬ p2992) ∨ (¬ p3680) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4039 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56577 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step93236 (p2946 p2952 p3105 p3286 p4039 p4385 p4906 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73576 : p4385 ∨ p3105)
    (h60152 : (¬ p2952) ∨ (¬ p3286) ∨ (¬ p4039) ∨ (¬ p4385) ∨ (¬ p4906))
    : (¬ p3286) ∨ (¬ p4039) ∨ p2946 ∨ p3105 ∨ (¬ p4906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4039 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4385 := (Or.elim h73576 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60152 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93239 (p2284 p2946 p2952 p3286 p3952 p4039 p5046 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73496 : p3952 ∨ p2284)
    (h58240 : (¬ p2952) ∨ (¬ p3286) ∨ (¬ p3952) ∨ (¬ p4039) ∨ (¬ p5046))
    : (¬ p3286) ∨ (¬ p4039) ∨ p2946 ∨ p2284 ∨ (¬ p5046) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4039 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58240 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93246 (p2248 p2417 p2922 p2928 p3266 p3286 p3379 p3452 p3506 p4278 p4444 p4669 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73394 : p3452 ∨ p3379)
    (h73320 : p2928 ∨ p2922)
    (h73546 : p4278 ∨ p2417)
    (h57834 : (¬ p2248) ∨ (¬ p2928) ∨ (¬ p3286) ∨ (¬ p3452) ∨ (¬ p3506) ∨ (¬ p4278) ∨ (¬ p4444) ∨ (¬ p4669))
    : (¬ p3506) ∨ p3266 ∨ p3379 ∨ p2922 ∨ (¬ p4669) ∨ (¬ p3286) ∨ (¬ p2248) ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h57834 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step93250 (p2630 p2761 p3755 p4035 p5284 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h43989 : (¬ p2630) ∨ (¬ p2761) ∨ (¬ p4035) ∨ (¬ p5284))
    : (¬ p5284) ∨ p3755 ∨ (¬ p2761) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43989 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step93251 (p2696 p2761 p3365 p3755 p4035 p5284 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h73390 : p3365 ∨ p2696)
    (h56952 : (¬ p2761) ∨ (¬ p3365) ∨ (¬ p4035) ∨ (¬ p5284))
    : (¬ p5284) ∨ p3755 ∨ p2696 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h56952 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step93253 (p2187 p2383 p2781 p3125 p3276 p3286 p3292 p3989 p4236 p5284 p5325 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h73378 : p3292 ∨ p3286)
    (h63536 : (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3125) ∨ (¬ p3276) ∨ (¬ p3292) ∨ (¬ p3989) ∨ (¬ p4236) ∨ (¬ p5284) ∨ (¬ p5325))
    : (¬ p5284) ∨ (¬ p3276) ∨ (¬ p2383) ∨ (¬ p2781) ∨ p2187 ∨ (¬ p4236) ∨ (¬ p5325) ∨ p3286 ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h63536 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step93255 (p2396 p2553 p2573 p3266 p3286 p3292 p3950 p4236 p4419 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h50915 : (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3266) ∨ (¬ p3950) ∨ (¬ p2553) ∨ (¬ p2396) ∨ p3286 ∨ (¬ p4419) ∨ (¬ p4236) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50915 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step93257 (p2630 p3276 p3755 p4035 p5284 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h44109 : (¬ p2630) ∨ (¬ p3276) ∨ (¬ p4035) ∨ (¬ p5284))
    : (¬ p5284) ∨ p3755 ∨ (¬ p3276) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44109 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step93260 (p2352 p3276 p3552 p3956 p4422 p4429 p5284 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h71986 : (¬ p5284) ∨ (¬ p3956) ∨ (¬ p4422) ∨ (¬ p3552) ∨ (¬ p4429) ∨ (¬ p3276))
    : (¬ p5284) ∨ (¬ p4422) ∨ (¬ p3552) ∨ (¬ p3276) ∨ (¬ p4429) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4429 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h71986 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step93265 (p2210 p2254 p2891 p3246 p3266 p3286 p3292 p3950 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h48915 : (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3950) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3266) ∨ (¬ p2891) ∨ (¬ p2210) ∨ p3286 ∨ (¬ p3950) ∨ (¬ p2254) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48915 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step93266 (p2230 p2252 p2750 p2753 p2850 p3266 p3286 p3292 p3333 p3362 p3684 p4332 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h73442 : p3684 ∨ p2850)
    (h64662 : (¬ p2230) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3684) ∨ (¬ p4332) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p2753) ∨ (¬ p2230) ∨ p3286 ∨ (¬ p2750) ∨ (¬ p3362) ∨ (¬ p3333) ∨ (¬ p2252) ∨ p2850 ∨ (¬ p3266) ∨ (¬ p4332) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h64662 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step93267 (p2264 p2717 p3266 p3659 p4136 p4429 p5284 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h62942 : (¬ p2264) ∨ (¬ p3266) ∨ (¬ p3659) ∨ (¬ p4136) ∨ (¬ p4429) ∨ (¬ p5284))
    : (¬ p4429) ∨ (¬ p5284) ∨ (¬ p2264) ∨ (¬ p4136) ∨ p2717 ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4429 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62942 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step93269 (p2254 p2363 p2946 p2952 p3063 p3093 p3680 p4314 p5059 p5284 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h61812 : (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3680) ∨ (¬ p4314) ∨ (¬ p5059) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3063) ∨ p2946 ∨ (¬ p2363) ∨ (¬ p2254) ∨ (¬ p4314) ∨ (¬ p3093) ∨ (¬ p3680) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4314 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61812 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step93276 (p2249 p2573 p2656 p2727 p2761 p2807 p3414 p3564 p4429 p4621 p5284 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h52073 : (¬ p2249) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2761) ∨ (¬ p3414) ∨ (¬ p3564) ∨ (¬ p4429) ∨ (¬ p4621) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (¬ p2761) ∨ (¬ p2727) ∨ (¬ p2249) ∨ p2807 ∨ (¬ p4621) ∨ (¬ p4429) ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4429 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h52073 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step93277 (p2331 p2641 p3286 p3292 p4154 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h73526 : p4154 ∨ p2641)
    (h54669 : (¬ p2331) ∨ (¬ p3292) ∨ (¬ p4154) ∨ (¬ p5284))
    : p3286 ∨ (¬ p5284) ∨ p2641 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54669 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step93280 (p2737 p2743 p2797 p3461 p4195 p5274 p5284 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73298 : p2743 ∨ p2737)
    (h48799 : (¬ p2743) ∨ (¬ p3461) ∨ (¬ p4195) ∨ (¬ p5274) ∨ (¬ p5284))
    : (¬ p5284) ∨ p2797 ∨ (¬ p3461) ∨ (¬ p5274) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48799 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step93281 (p2696 p2797 p3365 p3461 p4195 p5274 p5284 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73390 : p3365 ∨ p2696)
    (h59529 : (¬ p3365) ∨ (¬ p3461) ∨ (¬ p4195) ∨ (¬ p5274) ∨ (¬ p5284))
    : (¬ p5284) ∨ p2797 ∨ (¬ p3461) ∨ (¬ p5274) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59529 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step93283 (p2696 p3266 p3365 p3755 p4035 p5284 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h73390 : p3365 ∨ p2696)
    (h51906 : (¬ p3266) ∨ (¬ p3365) ∨ (¬ p4035) ∨ (¬ p5284))
    : (¬ p5284) ∨ p3755 ∨ p2696 ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51906 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step93288 (p2241 p2247 p3266 p3848 p5284 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h43940 : (¬ p2247) ∨ (¬ p3266) ∨ (¬ p3848) ∨ (¬ p5284))
    : (¬ p3848) ∨ (¬ p5284) ∨ p2241 ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3848 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43940 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step93289 (p3093 p3266 p3286 p3292 p3319 p3366 p3379 p3452 p4236 p4330 p4376 p5284 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h73394 : p3452 ∨ p3379)
    (h56278 : (¬ p3093) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3319) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p4236) ∨ (¬ p4330) ∨ (¬ p4376) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3266) ∨ p3286 ∨ (¬ p3093) ∨ (¬ p4236) ∨ (¬ p3319) ∨ p3379 ∨ (¬ p4330) ∨ (¬ p3366) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h56278 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step93292 (p2553 p2588 p3276 p4349 p4405 p4417 p4422 p5284 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h59930 : (¬ p2588) ∨ (¬ p3276) ∨ (¬ p4349) ∨ (¬ p4405) ∨ (¬ p4417) ∨ (¬ p4422) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p4349) ∨ (¬ p4422) ∨ (¬ p3276) ∨ (¬ p4405) ∨ p2553 ∨ (¬ p4417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4349 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h59930 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step93294 (p2139 p2696 p2911 p3051 p3365 p3755 p3941 p4001 p4035 p5119 p5284 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h73390 : p3365 ∨ p2696)
    (h62077 : (¬ p2139) ∨ (¬ p2911) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3941) ∨ (¬ p4001) ∨ (¬ p4035) ∨ (¬ p5119) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3941) ∨ (¬ p5119) ∨ p3755 ∨ (¬ p3051) ∨ (¬ p2911) ∨ p2696 ∨ (¬ p4001) ∨ (¬ p2139) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h62077 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step93297 (p2553 p2588 p3461 p3564 p5284 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h45375 : (¬ p2588) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3461) ∨ (¬ p3564) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45375 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step93298 (p2192 p2210 p2254 p2761 p2807 p3125 p3414 p4429 p4621 p5284 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h50508 : (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2761) ∨ (¬ p3125) ∨ (¬ p3414) ∨ (¬ p4429) ∨ (¬ p4621) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p2761) ∨ (¬ p4621) ∨ p2807 ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3125) ∨ (¬ p2254) ∨ (¬ p4429) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4429 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50508 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step93301 (p2307 p2696 p2781 p2911 p3365 p3755 p3921 p3941 p4035 p5119 p5284 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h73390 : p3365 ∨ p2696)
    (h58184 : (¬ p2307) ∨ (¬ p2781) ∨ (¬ p2911) ∨ (¬ p3365) ∨ (¬ p3921) ∨ (¬ p3941) ∨ (¬ p4035) ∨ (¬ p5119) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p2911) ∨ p3755 ∨ (¬ p3921) ∨ (¬ p3941) ∨ p2696 ∨ (¬ p2781) ∨ (¬ p5119) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h58184 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step93303 (p2230 p2373 p2696 p3365 p3366 p3519 p3755 p3969 p4035 p4376 p5119 p5284 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h73390 : p3365 ∨ p2696)
    (h58888 : (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3969) ∨ (¬ p4035) ∨ (¬ p4376) ∨ (¬ p5119) ∨ (¬ p5284))
    : (¬ p3969) ∨ (¬ p5119) ∨ p3755 ∨ (¬ p5284) ∨ (¬ p3366) ∨ p2696 ∨ (¬ p3519) ∨ (¬ p2230) ∨ (¬ p4376) ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h58888 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step93305 (p2383 p2387 p3552 p3767 p4036 p4429 p5284 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h71989 : (¬ p3767) ∨ (¬ p5284) ∨ (¬ p4036) ∨ (¬ p4429) ∨ (¬ p2387) ∨ (¬ p3552))
    : (¬ p5284) ∨ (¬ p3767) ∨ (¬ p4036) ∨ (¬ p4429) ∨ p2383 ∨ (¬ p3552) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4036 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4429 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71989 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step93311 (p2440 p3276 p3506 p4425 p4953 p5176 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h41652 : (¬ p2440) ∨ (¬ p3506) ∨ (¬ p4425) ∨ (¬ p4953) ∨ (¬ p5176))
    : p3276 ∨ (¬ p5176) ∨ (¬ p2440) ∨ (¬ p4953) ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p5176 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41652 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step93313 (p3016 p3276 p3506 p3574 p4425 p5176 p5324 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73422 : p3574 ∨ p3016)
    (h48552 : (¬ p3506) ∨ (¬ p3574) ∨ (¬ p4425) ∨ (¬ p5176) ∨ (¬ p5324))
    : p3276 ∨ (¬ p5176) ∨ p3016 ∨ (¬ p5324) ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p5176 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48552 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93323 (p3516 p3546 p3631 p3821 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h5635 : (¬ p3546) ∨ (¬ p3631) ∨ (¬ p3821))
    : (¬ p3631) ∨ p3516 ∨ (¬ p3546) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3546 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5635 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step93328 (p3527 p3542 p6076 : Prop)
    (h74417 : p3527 ∨ (¬ p6076))
    (h13484 : p3542 ∨ p6076)
    : p3542 ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3542) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6076) := (Or.elim h74417 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13484 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93329 (p2459 p3146 p3527 p3548 p3747 p4348 p4911 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73562 : p4348 ∨ p2459)
    (h58305 : (¬ p3146) ∨ (¬ p3548) ∨ (¬ p3747) ∨ (¬ p4348) ∨ (¬ p4911))
    : p3527 ∨ (¬ p3747) ∨ (¬ p4911) ∨ (¬ p3146) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58305 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93330 (p2122 p2573 p2579 p3389 p3822 p4710 p5222 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73472 : p3822 ∨ p2122)
    (h41916 : (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3822) ∨ (¬ p4710) ∨ (¬ p5222))
    : p2573 ∨ (¬ p4710) ∨ p2122 ∨ (¬ p5222) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41916 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93332 (p2122 p2230 p2440 p2542 p2589 p3016 p3093 p3309 p3574 p3822 p5193 p5222 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73284 : p2589 ∨ p2230)
    (h73422 : p3574 ∨ p3016)
    (h73270 : p2542 ∨ p2440)
    (h62197 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p3822) ∨ (¬ p5193) ∨ (¬ p5222))
    : p2122 ∨ (¬ p3309) ∨ (¬ p3093) ∨ (¬ p5193) ∨ p2230 ∨ p3016 ∨ (¬ p5222) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h62197 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step93333 (p2088 p2363 p2788 p2819 p4114 p4347 p4358 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73564 : p4358 ∨ p2819)
    (h49628 : (¬ p2088) ∨ (¬ p2788) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p4358))
    : p2363 ∨ (¬ p2088) ∨ (¬ p2788) ∨ p2819 ∨ (¬ p4114) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2788 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49628 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step93334 (p2177 p2299 p2685 p3005 p3543 p3572 p4155 p4378 p5145 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h73234 : p2299 ∨ p2177)
    (h48995 : (¬ p2299) ∨ (¬ p3005) ∨ (¬ p3543) ∨ (¬ p3572) ∨ (¬ p4155) ∨ (¬ p4378) ∨ (¬ p5145))
    : (¬ p5145) ∨ (¬ p3005) ∨ p2685 ∨ (¬ p4378) ∨ (¬ p3543) ∨ (¬ p4155) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h48995 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step93335 (p3246 p3399 p3690 p3830 p4366 p4914 p5362 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73446 : p3690 ∨ p3246)
    (h42422 : (¬ p3690) ∨ (¬ p3830) ∨ (¬ p4366) ∨ (¬ p4914) ∨ (¬ p5362))
    : (¬ p5362) ∨ p3399 ∨ (¬ p4914) ∨ p3246 ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5362 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42422 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step93337 (p2396 p3032 p3399 p3830 p4107 p4361 p4366 p5362 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73514 : p4107 ∨ p2396)
    (h42222 : (¬ p3032) ∨ (¬ p3830) ∨ (¬ p4107) ∨ (¬ p4361) ∨ (¬ p4366) ∨ (¬ p5362))
    : (¬ p5362) ∨ p3399 ∨ (¬ p3032) ∨ (¬ p3830) ∨ p2396 ∨ (¬ p4361) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5362 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42222 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step93340 (p2396 p3227 p3355 p3389 p3540 p4107 p4712 p5362 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73402 : p3540 ∨ p3389)
    (h49420 : (¬ p3227) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p4107) ∨ (¬ p4712) ∨ (¬ p5362))
    : (¬ p5362) ∨ (¬ p3355) ∨ (¬ p3227) ∨ p2396 ∨ p3389 ∨ (¬ p4712) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5362 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3227 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49420 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step93342 (p2761 p3707 p4321 p5362 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h19824 : (¬ p2761) ∨ (¬ p4321) ∨ (¬ p5362))
    : p3707 ∨ (¬ p5362) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p5362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h19824 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step93345 (p2396 p3399 p3830 p4107 p4366 p5145 p5362 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73514 : p4107 ∨ p2396)
    (h62771 : (¬ p3830) ∨ (¬ p4107) ∨ (¬ p4366) ∨ (¬ p5145) ∨ (¬ p5362))
    : (¬ p5362) ∨ p3399 ∨ p2396 ∨ (¬ p5145) ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5362 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62771 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step93346 (p2563 p3660 p4716 : Prop)
    (h73722 : p4716 ∨ (¬ p2563))
    (h7623 : p3660 ∨ (¬ p4716))
    : p3660 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3660) := (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h7623 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step93347 (p2563 p3660 p5879 : Prop)
    (h74179 : (¬ p2563) ∨ (¬ p5879))
    (h12264 : p3660 ∨ p5879)
    : p3660 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3660) := (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5879) := (Or.elim h74179 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12264 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93348 (p2459 p2493 p2499 p2553 p2588 p2901 p3051 p3156 p3379 p3452 p4042 p4320 p4521 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73552 : p4320 ∨ p2901)
    (h73260 : p2499 ∨ p2493)
    (h73282 : p2588 ∨ p2553)
    (h44206 : (¬ p2459) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p4042) ∨ (¬ p4320) ∨ (¬ p4521))
    : p3379 ∨ (¬ p4521) ∨ (¬ p4042) ∨ (¬ p3156) ∨ p2901 ∨ p2493 ∨ (¬ p2459) ∨ (¬ p3051) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h44206 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step93350 (p2459 p3146 p3692 p4042 p4348 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73561 : (¬ p2459) ∨ (¬ p4348))
    (h6613 : (¬ p3692) ∨ (¬ p4042) ∨ p4348)
    : (¬ p4042) ∨ p3146 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4042 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p4348) := (Or.elim h73561 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h6613 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u4 r1)))))))

theorem step93360 (p2230 p2870 p2933 p3389 p3540 p4885 p4909 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h41914 : (¬ p2230) ∨ (¬ p2870) ∨ (¬ p2933) ∨ (¬ p3540) ∨ (¬ p4885) ∨ (¬ p4909))
    : (¬ p2870) ∨ (¬ p2933) ∨ p3389 ∨ (¬ p2230) ∨ (¬ p4885) ∨ (¬ p4909) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2933 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41914 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step93365 (p2441 p2911 p3051 p3527 p3644 p4539 p4909 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h56163 : (¬ p2441) ∨ (¬ p3051) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p4539) ∨ (¬ p4909))
    : (¬ p3527) ∨ (¬ p4909) ∨ (¬ p4539) ∨ (¬ p2441) ∨ (¬ p3051) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56163 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step93368 (p2668 p3093 p3399 p3922 p4275 p4366 p4405 p4909 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h41898 : (¬ p2668) ∨ (¬ p3093) ∨ (¬ p3922) ∨ (¬ p4275) ∨ (¬ p4366) ∨ (¬ p4405) ∨ (¬ p4909))
    : p3399 ∨ (¬ p2668) ∨ (¬ p3922) ∨ (¬ p4275) ∨ (¬ p4909) ∨ (¬ p4405) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4909 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41898 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step93370 (p2881 p3399 p3449 p3570 p4366 p4914 p5307 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73418 : p3570 ∨ p2881)
    (h48476 : (¬ p3449) ∨ (¬ p3570) ∨ (¬ p4366) ∨ (¬ p4914) ∨ (¬ p5307))
    : (¬ p5307) ∨ p3399 ∨ p2881 ∨ (¬ p3449) ∨ (¬ p4914) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48476 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step93372 (p2177 p2299 p3399 p3449 p4366 p5145 p5307 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73234 : p2299 ∨ p2177)
    (h42192 : (¬ p2299) ∨ (¬ p3449) ∨ (¬ p4366) ∨ (¬ p5145) ∨ (¬ p5307))
    : p3399 ∨ (¬ p3449) ∨ (¬ p5145) ∨ (¬ p5307) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42192 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93373 (p2264 p3040 p3399 p3449 p3553 p4366 p5307 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73410 : p3553 ∨ p2264)
    (h62773 : (¬ p3040) ∨ (¬ p3449) ∨ (¬ p3553) ∨ (¬ p4366) ∨ (¬ p5307))
    : (¬ p5307) ∨ p3399 ∨ (¬ p3449) ∨ p2264 ∨ (¬ p3040) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62773 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step93374 (p2911 p2936 p3399 p3449 p3644 p4366 p5307 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73434 : p3644 ∨ p2911)
    (h41870 : (¬ p2936) ∨ (¬ p3449) ∨ (¬ p3644) ∨ (¬ p4366) ∨ (¬ p5307))
    : (¬ p5307) ∨ p3399 ∨ (¬ p2936) ∨ (¬ p3449) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2936 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41870 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step93375 (p3399 p3449 p4366 p4442 p5307 p5559 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h62883 : (¬ p3449) ∨ (¬ p4366) ∨ (¬ p4442) ∨ (¬ p5307) ∨ (¬ p5559))
    : (¬ p4442) ∨ p3399 ∨ (¬ p3449) ∨ (¬ p5307) ∨ (¬ p5559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4442 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62883 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93378 (p2992 p3662 p3922 p4153 p4759 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h35246 : (¬ p3662) ∨ (¬ p3922) ∨ (¬ p4153) ∨ (¬ p4759))
    : p2992 ∨ (¬ p4153) ∨ (¬ p3922) ∨ (¬ p4759) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h35246 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step93379 (p2132 p2742 p2778 p3319 p3654 p3946 p4759 p5052 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h51234 : (¬ p2132) ∨ (¬ p2742) ∨ (¬ p2778) ∨ (¬ p3319) ∨ (¬ p3946) ∨ (¬ p4759) ∨ (¬ p5052))
    : (¬ p2778) ∨ (¬ p3319) ∨ p3654 ∨ (¬ p4759) ∨ (¬ p2132) ∨ (¬ p5052) ∨ (¬ p2742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2778 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51234 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step93382 (p2533 p2946 p3156 p3266 p3680 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h43251 : (¬ p2533) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3680) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3680) ∨ (¬ p2946) ∨ (¬ p2533) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43251 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step93383 (p2363 p2533 p3266 p3680 p4134 p4347 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73560 : p4347 ∨ p2363)
    (h55233 : (¬ p2533) ∨ (¬ p3680) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4444))
    : (¬ p3680) ∨ p3266 ∨ (¬ p2533) ∨ (¬ p4134) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55233 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step93385 (p2459 p2533 p3266 p3680 p4348 p4444 p4905 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73562 : p4348 ∨ p2459)
    (h41740 : (¬ p2533) ∨ (¬ p3680) ∨ (¬ p4348) ∨ (¬ p4444) ∨ (¬ p4905))
    : (¬ p3680) ∨ p3266 ∨ (¬ p2533) ∨ p2459 ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41740 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93392 (p2230 p2427 p2696 p2748 p3189 p3246 p3256 p3365 p3873 p3950 p4118 p4360 p5190 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73390 : p3365 ∨ p2696)
    (h73520 : p4118 ∨ p3256)
    (h42102 : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2748) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p5190))
    : (¬ p3246) ∨ p3189 ∨ (¬ p3950) ∨ (¬ p2748) ∨ (¬ p2427) ∨ (¬ p5190) ∨ p2696 ∨ (¬ p2230) ∨ p3256 ∨ (¬ p3873) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h42102 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step93394 (p2608 p3093 p3367 p3591 p3918 p5221 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h56118 : (¬ p2608) ∨ (¬ p3367) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p5221))
    : p3093 ∨ (¬ p3918) ∨ (¬ p2608) ∨ (¬ p5221) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p3918 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5221 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h56118 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93396 (p2807 p4066 p5920 : Prop)
    (h74233 : p2807 ∨ (¬ p5920))
    (h12506 : p4066 ∨ p5920)
    : p4066 ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4066) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5920) := (Or.elim h74233 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12506 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93397 (p3083 p4437 p5977 : Prop)
    (h74305 : p3083 ∨ (¬ p5977))
    (h12852 : p4437 ∨ p5977)
    : p4437 ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5977) := (Or.elim h74305 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12852 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93398 (p3083 p3878 p5977 : Prop)
    (h74305 : p3083 ∨ (¬ p5977))
    (h12854 : p3878 ∨ p5977)
    : p3878 ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3878) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5977) := (Or.elim h74305 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12854 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93400 (p3083 p5009 p5977 : Prop)
    (h74305 : p3083 ∨ (¬ p5977))
    (h12856 : p5009 ∨ p5977)
    : p5009 ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5009) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5977) := (Or.elim h74305 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12856 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93401 (p2284 p2307 p3309 p3549 p3743 p4512 p4957 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h41942 : (¬ p2284) ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3743) ∨ (¬ p4512) ∨ (¬ p4957))
    : (¬ p2307) ∨ p3309 ∨ (¬ p3743) ∨ (¬ p4512) ∨ (¬ p2284) ∨ (¬ p4957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41942 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step93402 (p2246 p2751 p2901 p2958 p3051 p3136 p4315 p4320 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73552 : p4320 ∨ p2901)
    (h48970 : (¬ p2246) ∨ (¬ p2751) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4315) ∨ (¬ p4320))
    : (¬ p2246) ∨ (¬ p2751) ∨ (¬ p2958) ∨ (¬ p3051) ∨ p3136 ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48970 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step93405 (p2246 p2437 p2630 p2663 p2751 p2810 p3389 p3742 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73316 : p2810 ∨ p2630)
    (h63788 : (¬ p2246) ∨ (¬ p2663) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p3389) ∨ (¬ p3742))
    : p2437 ∨ (¬ p3389) ∨ (¬ p2663) ∨ (¬ p2751) ∨ (¬ p2246) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63788 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step93410 (p2241 p2247 p2630 p2751 p2810 p3379 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73316 : p2810 ∨ p2630)
    (h69106 : (¬ p2247) ∨ (¬ p2810) ∨ (¬ p2751) ∨ (¬ p3379))
    : p2241 ∨ (¬ p2751) ∨ (¬ p3379) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69106 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step93411 (p2210 p2241 p2247 p2751 p3136 p4282 p4315 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73550 : p4315 ∨ p3136)
    (h41005 : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2751) ∨ (¬ p4282) ∨ (¬ p4315))
    : p2241 ∨ (¬ p4282) ∨ (¬ p2751) ∨ (¬ p2210) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41005 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step93414 (p2630 p2662 p2751 p2810 p2922 p3389 p3540 p4281 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73402 : p3540 ∨ p3389)
    (h42498 : (¬ p2662) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p4281))
    : (¬ p2922) ∨ p2630 ∨ (¬ p4281) ∨ (¬ p2662) ∨ (¬ p2751) ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42498 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step93418 (p2751 p2797 p3319 p3323 p4037 p4195 p4759 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73508 : p4037 ∨ p3323)
    (h41445 : (¬ p2751) ∨ (¬ p3319) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4759))
    : (¬ p3319) ∨ p2797 ∨ (¬ p2751) ∨ p3323 ∨ (¬ p4759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41445 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93419 (p2493 p2630 p2751 p2810 p3016 p3574 p4281 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73316 : p2810 ∨ p2630)
    (h41443 : (¬ p2493) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p3574) ∨ (¬ p4281))
    : (¬ p2751) ∨ p3016 ∨ p2630 ∨ (¬ p4281) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41443 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93423 (p2122 p2284 p2318 p2901 p3691 p3822 p3952 p4889 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73496 : p3952 ∨ p2284)
    (h62924 : (¬ p2318) ∨ (¬ p2901) ∨ (¬ p3691) ∨ (¬ p3822) ∨ (¬ p3952) ∨ (¬ p4889))
    : (¬ p2901) ∨ (¬ p3691) ∨ p2122 ∨ p2284 ∨ (¬ p2318) ∨ (¬ p4889) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62924 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step93424 (p2088 p2187 p3609 p4078 p4170 p4340 p4889 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h53376 : (¬ p2088) ∨ (¬ p2187) ∨ (¬ p4078) ∨ (¬ p4170) ∨ (¬ p4340) ∨ (¬ p4889))
    : p3609 ∨ (¬ p2088) ∨ (¬ p4078) ∨ (¬ p4889) ∨ (¬ p4170) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53376 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step93426 (p2373 p2563 p2819 p4110 p4358 p4441 p4889 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73564 : p4358 ∨ p2819)
    (h42280 : (¬ p2373) ∨ (¬ p4110) ∨ (¬ p4358) ∨ (¬ p4441) ∨ (¬ p4889))
    : (¬ p2373) ∨ p2563 ∨ (¬ p4889) ∨ (¬ p4441) ∨ p2819 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42280 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93428 (p2761 p3051 p3136 p3246 p3556 p3645 p3690 p4282 p4315 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73550 : p4315 ∨ p3136)
    (h73446 : p3690 ∨ p3246)
    (h73414 : p3556 ∨ p3051)
    (h56119 : (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3690) ∨ (¬ p4282) ∨ (¬ p4315) ∨ (¬ p4381))
    : (¬ p4282) ∨ p2761 ∨ p3136 ∨ (¬ p3645) ∨ p3246 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4282 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56119 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step93430 (p2210 p2241 p2247 p2641 p4154 p4282 p4563 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73226 : p2247 ∨ p2241)
    (h54016 : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p4154) ∨ (¬ p4282) ∨ (¬ p4563))
    : p2641 ∨ p2241 ∨ (¬ p4563) ∨ (¬ p4282) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54016 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93431 (p2210 p2241 p2247 p3146 p3156 p4282 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h61312 : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4282))
    : p2241 ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4282) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h61312 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93432 (p2210 p2241 p2247 p2996 p4282 p4917 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h41374 : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2996) ∨ (¬ p4282) ∨ (¬ p4917))
    : (¬ p2996) ∨ p2241 ∨ (¬ p4917) ∨ (¬ p2210) ∨ (¬ p4282) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41374 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93433 (p2245 p2608 p2651 p2657 p2727 p2744 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h52517 : (¬ p2245) ∨ (¬ p2608) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2744))
    : (¬ p2245) ∨ (¬ p2608) ∨ p2651 ∨ (¬ p2744) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52517 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93438 (p2245 p2696 p3005 p3286 p3292 p4733 p5111 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h50800 : (¬ p2245) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3292) ∨ (¬ p4733) ∨ (¬ p5111))
    : p3286 ∨ (¬ p3005) ∨ (¬ p4733) ∨ (¬ p2245) ∨ (¬ p5111) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50800 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step93442 (p2245 p2264 p2553 p2598 p2807 p2881 p3414 p3422 p3553 p4559 p4733 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h73410 : p3553 ∨ p2264)
    (h62110 : (¬ p2245) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (¬ p2881) ∨ (¬ p3414) ∨ (¬ p3422) ∨ (¬ p3553) ∨ (¬ p4559) ∨ (¬ p4733))
    : (¬ p2245) ∨ (¬ p2553) ∨ p2807 ∨ (¬ p4559) ∨ (¬ p2881) ∨ (¬ p2598) ∨ p2264 ∨ (¬ p3422) ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h62110 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step93445 (p2331 p2901 p2958 p2963 p3051 p4320 p4700 p4972 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73338 : p2963 ∨ p2331)
    (h52613 : (¬ p2958) ∨ (¬ p2963) ∨ (¬ p3051) ∨ (¬ p4320) ∨ (¬ p4700) ∨ (¬ p4972))
    : p2901 ∨ p2331 ∨ (¬ p3051) ∨ (¬ p4700) ∨ (¬ p4972) ∨ (¬ p2958) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52613 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step93447 (p2220 p2331 p2958 p2963 p3156 p3497 p4700 p4972 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73338 : p2963 ∨ p2331)
    (h52583 : (¬ p2220) ∨ (¬ p2958) ∨ (¬ p2963) ∨ (¬ p3497) ∨ (¬ p4700) ∨ (¬ p4972))
    : p3156 ∨ (¬ p2220) ∨ (¬ p4972) ∨ p2331 ∨ (¬ p4700) ∨ (¬ p2958) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52583 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step93448 (p2319 p2727 p3031 p3516 p3567 p3631 p3817 p4972 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h41884 : (¬ p2319) ∨ (¬ p2727) ∨ (¬ p3031) ∨ (¬ p3516) ∨ (¬ p3567) ∨ (¬ p3817) ∨ (¬ p4972))
    : p3631 ∨ (¬ p3567) ∨ (¬ p3516) ∨ (¬ p2727) ∨ (¬ p3031) ∨ (¬ p4972) ∨ (¬ p2319) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41884 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step93452 (p2737 p2749 p2752 : Prop)
    (h73303 : (¬ p2737) ∨ (¬ p2752))
    (h3629 : p2749 ∨ p2752)
    : p2749 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2749) := (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2752) := (Or.elim h73303 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3629 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93454 (p2331 p3983 p5827 : Prop)
    (h74113 : p2331 ∨ (¬ p5827))
    (h11958 : p3983 ∨ p5827)
    : p3983 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3983) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5827) := (Or.elim h74113 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11958 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93474 (p2608 p3367 p3399 p4366 p4424 p5082 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h48391 : (¬ p2608) ∨ (¬ p3367) ∨ (¬ p4366) ∨ (¬ p4424) ∨ (¬ p5082))
    : (¬ p4424) ∨ p3399 ∨ (¬ p3367) ∨ (¬ p5082) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4424 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5082 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48391 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93475 (p2264 p2696 p3365 p3425 p3471 p3527 p3553 p4424 : Prop)
    (h73396 : p3471 ∨ p3425)
    (h73410 : p3553 ∨ p2264)
    (h73390 : p3365 ∨ p2696)
    (h53716 : (¬ p3365) ∨ (¬ p3471) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p4424))
    : (¬ p3527) ∨ p3425 ∨ p2264 ∨ (¬ p4424) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53716 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93476 (p2246 p2331 p2363 p2608 p2668 p2744 p3399 p3434 p4324 p4366 p4424 p4669 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73556 : p4324 ∨ p3434)
    (h58771 : (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p4324) ∨ (¬ p4366) ∨ (¬ p4424) ∨ (¬ p4669))
    : p3399 ∨ (¬ p2246) ∨ (¬ p4669) ∨ (¬ p2744) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p2331) ∨ p3434 ∨ (¬ p4424) ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h58771 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step93479 (p2177 p2299 p2437 p2651 p2657 p2737 p2743 p3361 p3425 p3471 p3527 p3742 p4424 p4712 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73396 : p3471 ∨ p3425)
    (h73234 : p2299 ∨ p2177)
    (h73452 : p3742 ∨ p2437)
    (h73288 : p2657 ∨ p2651)
    (h71993 : (¬ p4424) ∨ (¬ p3527) ∨ (¬ p2299) ∨ (¬ p3742) ∨ (¬ p3471) ∨ (¬ p2657) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p4712))
    : p2737 ∨ (¬ p4424) ∨ p3425 ∨ (¬ p3361) ∨ p2177 ∨ p2437 ∨ p2651 ∨ (¬ p3527) ∨ (¬ p4712) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2737) := (fun h => hn (Or.inl h));
    let u1 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71993 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step93481 (p2459 p2573 p2579 p3363 p3367 p3425 p3471 p3527 p3564 p3585 p4137 p4424 p4604 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73428 : p3585 ∨ p3367)
    (h73396 : p3471 ∨ p3425)
    (h73524 : p4137 ∨ p3564)
    (h71994 : (¬ p4137) ∨ (¬ p3527) ∨ (¬ p4604) ∨ (¬ p4424) ∨ (¬ p2579) ∨ (¬ p3471) ∨ (¬ p3585) ∨ (¬ p2459) ∨ (¬ p3363))
    : (¬ p4424) ∨ (¬ p3527) ∨ (¬ p4604) ∨ p2573 ∨ p3367 ∨ p3425 ∨ (¬ p3363) ∨ (¬ p2459) ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4424 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h71994 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step93488 (p2459 p2608 p2717 p3399 p3659 p4348 p4366 p4424 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73570 : p4366 ∨ p3399)
    (h73562 : p4348 ∨ p2459)
    (h43217 : (¬ p2608) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4424))
    : (¬ p4424) ∨ p2717 ∨ (¬ p2608) ∨ p3399 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4424 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43217 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step93490 (p2717 p3527 p3659 p4424 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h19959 : (¬ p3527) ∨ (¬ p3659) ∨ (¬ p4424))
    : (¬ p4424) ∨ (¬ p3527) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4424 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h19959 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step93493 (p2331 p2459 p2737 p2743 p2963 p3323 p3361 p3425 p3471 p3527 p4037 p4424 p4604 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73396 : p3471 ∨ p3425)
    (h73298 : p2743 ∨ p2737)
    (h73338 : p2963 ∨ p2331)
    (h71995 : (¬ p4037) ∨ (¬ p2743) ∨ (¬ p4424) ∨ (¬ p4604) ∨ (¬ p2963) ∨ (¬ p3527) ∨ (¬ p3361) ∨ (¬ p3471) ∨ (¬ p2459))
    : (¬ p4424) ∨ (¬ p3527) ∨ p3323 ∨ (¬ p4604) ∨ (¬ p3361) ∨ p3425 ∨ (¬ p2459) ∨ p2737 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4424 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h71995 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step93495 (p2246 p2573 p2608 p2663 p2744 p3016 p3343 p3399 p3434 p3574 p4324 p4366 p4424 p4638 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73556 : p4324 ∨ p3434)
    (h73422 : p3574 ∨ p3016)
    (h60534 : (¬ p2246) ∨ (¬ p2573) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p4324) ∨ (¬ p4366) ∨ (¬ p4424) ∨ (¬ p4638))
    : p3399 ∨ (¬ p4638) ∨ (¬ p2744) ∨ (¬ p2663) ∨ (¬ p2246) ∨ (¬ p4424) ∨ p3434 ∨ p3016 ∨ (¬ p2573) ∨ (¬ p3343) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h60534 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (False.elim (r9 u1)))))))))))))))))))))))

theorem step93498 (p2396 p2553 p2573 p2608 p2717 p3399 p3519 p3659 p4366 p4376 p4424 p4668 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73438 : p3659 ∨ p2717)
    (h50891 : (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3659) ∨ (¬ p4366) ∨ (¬ p4376) ∨ (¬ p4424) ∨ (¬ p4668))
    : p3399 ∨ (¬ p4424) ∨ (¬ p2573) ∨ p2717 ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p4668) ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50891 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step93500 (p3434 p3631 p3817 p4324 p4424 : Prop)
    (h73467 : (¬ p3631) ∨ (¬ p3817))
    (h73556 : p4324 ∨ p3434)
    (h27569 : p3817 ∨ (¬ p4324) ∨ (¬ p4424))
    : (¬ p3631) ∨ p3434 ∨ (¬ p4424) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3434) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3817) := (Or.elim h73467 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h27569 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u2)))))))

theorem step93504 (p2177 p2299 p2427 p2774 p2850 p3367 p3426 p3527 p3585 p3684 p4235 p4424 p4559 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73536 : p4235 ∨ p2427)
    (h73234 : p2299 ∨ p2177)
    (h73428 : p3585 ∨ p3367)
    (h71997 : (¬ p3527) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p3684) ∨ (¬ p4424) ∨ (¬ p3426) ∨ (¬ p2774) ∨ (¬ p2299) ∨ (¬ p3585))
    : (¬ p2774) ∨ p2850 ∨ (¬ p4559) ∨ (¬ p3426) ∨ p2427 ∨ (¬ p3527) ∨ (¬ p4424) ∨ p2177 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h71997 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (False.elim (r7 u12)))))))))))))))))))

theorem step93506 (p2192 p2881 p3527 p3548 p3554 p4555 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h40976 : (¬ p2192) ∨ (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p4555))
    : p3527 ∨ (¬ p2881) ∨ (¬ p2192) ∨ (¬ p3554) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h40976 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93507 (p2210 p3399 p3554 p3555 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h5171 : (¬ p3399) ∨ (¬ p3554) ∨ (¬ p3555))
    : (¬ p3399) ∨ p2210 ∨ (¬ p3554) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5171 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step93509 (p2192 p3246 p3554 p3631 p3817 p4555 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h42631 : (¬ p2192) ∨ (¬ p3246) ∨ (¬ p3554) ∨ (¬ p3817) ∨ (¬ p4555))
    : p3631 ∨ (¬ p3246) ∨ (¬ p4555) ∨ (¬ p2192) ∨ (¬ p3554) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42631 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93512 (p2177 p2192 p2299 p2396 p3554 p3631 p3817 : Prop)
    (h73468 : p3817 ∨ p3631)
    (h73234 : p2299 ∨ p2177)
    (h55834 : (¬ p2192) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p3554) ∨ (¬ p3817))
    : p3631 ∨ (¬ p2396) ∨ (¬ p3554) ∨ (¬ p2192) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55834 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step93514 (p2911 p3389 p3527 p3548 p3554 p4202 p5194 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h49359 : (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p4202) ∨ (¬ p5194))
    : p3527 ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p4202) ∨ (¬ p5194) ∨ (¬ p3554) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49359 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step93516 (p2427 p2881 p3527 p3548 p3554 p4629 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h40975 : (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p4629))
    : (¬ p3554) ∨ p3527 ∨ (¬ p2881) ∨ (¬ p4629) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3554 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h40975 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93524 (p2341 p2870 p3527 p3548 p3554 p3691 p4875 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h41069 : (¬ p2341) ∨ (¬ p2870) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p3691) ∨ (¬ p4875))
    : (¬ p2341) ∨ (¬ p2870) ∨ p3527 ∨ (¬ p4875) ∨ (¬ p3691) ∨ (¬ p3554) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41069 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step93532 (p2156 p2190 p2363 p2598 p2911 p3055 p3146 p3201 p3644 p3876 p4133 p4172 p4347 p4736 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73350 : p3055 ∨ p2598)
    (h73434 : p3644 ∨ p2911)
    (h73560 : p4347 ∨ p2363)
    (h49613 : (¬ p2156) ∨ (¬ p2190) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4133) ∨ (¬ p4172) ∨ (¬ p4347) ∨ (¬ p4736))
    : (¬ p2190) ∨ p3201 ∨ p2598 ∨ p2911 ∨ (¬ p3146) ∨ (¬ p4172) ∨ (¬ p4133) ∨ (¬ p2156) ∨ p2363 ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h49613 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step93534 (p2528 p3073 p3156 p3497 p4261 p4355 p4446 p4702 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73400 : p3497 ∨ p3156)
    (h41853 : (¬ p2528) ∨ (¬ p3497) ∨ (¬ p4261) ∨ (¬ p4355) ∨ (¬ p4446) ∨ (¬ p4702))
    : p3073 ∨ (¬ p2528) ∨ (¬ p4446) ∨ (¬ p4702) ∨ (¬ p4355) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4446 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41853 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step93535 (p3073 p3146 p3692 p4261 p4446 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73447 : (¬ p3146) ∨ (¬ p3692))
    (h35204 : p3692 ∨ (¬ p4261) ∨ (¬ p4446))
    : p3073 ∨ (¬ p3146) ∨ (¬ p4446) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4446 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3692) := (Or.elim h73447 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h35204 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step93542 (p2341 p2901 p2911 p3551 p3741 p4283 p4320 p4702 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73552 : p4320 ∨ p2901)
    (h41497 : (¬ p2911) ∨ (¬ p3551) ∨ (¬ p3741) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4702))
    : (¬ p2911) ∨ p2341 ∨ (¬ p3741) ∨ (¬ p4283) ∨ p2901 ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41497 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step93544 (p3246 p3516 p3690 p3821 p4283 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73445 : (¬ p3246) ∨ (¬ p3690))
    (h6477 : p3690 ∨ (¬ p3821) ∨ (¬ p4283))
    : p3516 ∨ (¬ p3246) ∨ (¬ p4283) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3690) := (Or.elim h73445 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h6477 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step93550 (p2901 p3516 p3631 p3821 p4283 p4320 p4431 p4960 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73552 : p4320 ∨ p2901)
    (h62677 : (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4431) ∨ (¬ p4960))
    : (¬ p3631) ∨ p3516 ∨ (¬ p4431) ∨ (¬ p4960) ∨ p2901 ∨ (¬ p4283) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62677 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step93551 (p2427 p3516 p3631 p3821 p4235 p4283 p4338 p4452 p4632 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73536 : p4235 ∨ p2427)
    (h42255 : (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4338) ∨ (¬ p4452) ∨ (¬ p4632))
    : (¬ p3631) ∨ p3516 ∨ (¬ p4452) ∨ (¬ p4283) ∨ p2427 ∨ (¬ p4632) ∨ (¬ p4338) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42255 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step93552 (p2341 p3246 p3551 p3657 p3690 p4283 : Prop)
    (h73445 : (¬ p3246) ∨ (¬ p3690))
    (h73408 : p3551 ∨ p2341)
    (h27163 : (¬ p3551) ∨ (¬ p3657) ∨ p3690 ∨ (¬ p4283))
    : (¬ p3657) ∨ (¬ p3246) ∨ (¬ p4283) ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p3690) := (Or.elim h73445 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h27163 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step93554 (p2284 p2396 p2901 p3516 p3821 p4283 p4320 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73552 : p4320 ∨ p2901)
    (h44932 : (¬ p2284) ∨ (¬ p2396) ∨ (¬ p3821) ∨ (¬ p4283) ∨ (¬ p4320))
    : p3516 ∨ (¬ p2396) ∨ p2901 ∨ (¬ p4283) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44932 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step93558 (p2088 p2192 p3073 p3857 p3961 p4173 p4283 p4496 p4558 : Prop)
    (h73528 : p4173 ∨ p2192)
    (h73480 : p3857 ∨ p2088)
    (h64787 : (¬ p3073) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4173) ∨ (¬ p4283) ∨ (¬ p4496) ∨ (¬ p4558))
    : (¬ p3073) ∨ (¬ p4558) ∨ p2192 ∨ (¬ p4496) ∨ (¬ p4283) ∨ p2088 ∨ (¬ p3961) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4496 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h64787 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step93560 (p2187 p4441 p5801 : Prop)
    (h74079 : (¬ p2187) ∨ (¬ p5801))
    (h11806 : p4441 ∨ p5801)
    : p4441 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4441) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5801) := (Or.elim h74079 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11806 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93561 (p2187 p2190 p5801 : Prop)
    (h74079 : (¬ p2187) ∨ (¬ p5801))
    (h11807 : p2190 ∨ p5801)
    : p2190 ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2190) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5801) := (Or.elim h74079 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11807 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93565 (p2331 p3567 p5827 : Prop)
    (h74113 : p2331 ∨ (¬ p5827))
    (h11957 : p3567 ∨ p5827)
    : p3567 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3567) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5827) := (Or.elim h74113 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11957 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93572 (p2177 p2911 p3644 p4710 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h20375 : (¬ p2177) ∨ (¬ p3644) ∨ (¬ p4710))
    : p2911 ∨ (¬ p4710) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20375 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step93575 (p2352 p2437 p2493 p2499 p3487 p3956 p4710 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73500 : p3956 ∨ p2352)
    (h72000 : (¬ p3956) ∨ (¬ p2437) ∨ (¬ p2499) ∨ (¬ p4710) ∨ (¬ p3487))
    : (¬ p2437) ∨ (¬ p3487) ∨ p2493 ∨ p2352 ∨ (¬ p4710) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72000 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step93577 (p2396 p2417 p4278 p4710 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h20221 : (¬ p2396) ∨ (¬ p4278) ∨ (¬ p4710))
    : (¬ p4710) ∨ p2417 ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4710 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20221 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step93579 (p2396 p2911 p3644 p3657 p4710 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h39423 : (¬ p2396) ∨ (¬ p3644) ∨ (¬ p3657) ∨ (¬ p4710))
    : (¬ p4710) ∨ (¬ p2396) ∨ p2911 ∨ (¬ p3657) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4710 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h39423 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step93581 (p2177 p2417 p2891 p3246 p4278 p4710 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h46330 : (¬ p2177) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p4278) ∨ (¬ p4710))
    : p2417 ∨ (¬ p3246) ∨ (¬ p2177) ∨ (¬ p2891) ∨ (¬ p4710) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46330 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93582 (p2177 p2284 p2417 p2449 p2995 p3952 p4278 p4710 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73496 : p3952 ∨ p2284)
    (h54298 : (¬ p2177) ∨ (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3952) ∨ (¬ p4278) ∨ (¬ p4710))
    : p2417 ∨ (¬ p2449) ∨ (¬ p2177) ∨ p2284 ∨ (¬ p4710) ∨ (¬ p2995) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54298 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step93584 (p2241 p2247 p2727 p3093 p3922 p4111 p4975 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73518 : p4111 ∨ p2727)
    (h50627 : (¬ p2247) ∨ (¬ p3093) ∨ (¬ p3922) ∨ (¬ p4111) ∨ (¬ p4975))
    : p2241 ∨ (¬ p3093) ∨ (¬ p4975) ∨ p2727 ∨ (¬ p3922) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50627 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93587 (p2668 p3324 p3922 p3923 : Prop)
    (h73385 : (¬ p2668) ∨ (¬ p3324))
    (h33335 : p3324 ∨ (¬ p3922) ∨ (¬ p3923))
    : (¬ p3922) ∨ (¬ p2668) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3324) := (Or.elim h73385 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h33335 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u2)))))))

theorem step93591 (p2295 p2417 p3319 p3922 p4026 p4396 p4712 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h51444 : (¬ p2295) ∨ (¬ p2417) ∨ (¬ p3922) ∨ (¬ p4026) ∨ (¬ p4396) ∨ (¬ p4712))
    : (¬ p3922) ∨ (¬ p2417) ∨ p3319 ∨ (¬ p2295) ∨ (¬ p4712) ∨ (¬ p4396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3319) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51444 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step93592 (p2295 p3309 p3549 p3922 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h19793 : (¬ p2295) ∨ (¬ p3549) ∨ (¬ p3922))
    : (¬ p2295) ∨ (¬ p3922) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h19793 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step93594 (p2137 p2417 p2441 p3051 p3246 p4278 p4885 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h42249 : (¬ p2137) ∨ (¬ p2441) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4278) ∨ (¬ p4885))
    : p2417 ∨ (¬ p3246) ∨ (¬ p3051) ∨ (¬ p2137) ∨ (¬ p2441) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42249 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step93596 (p2137 p2427 p2839 p2982 p3051 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h46177 : (¬ p2137) ∨ (¬ p2839) ∨ (¬ p2982) ∨ (¬ p3051) ∨ (¬ p4235))
    : (¬ p3051) ∨ (¬ p2137) ∨ (¬ p2982) ∨ p2427 ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46177 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step93602 (p2137 p2187 p2295 p2641 p2696 p2748 p2839 p3051 p3365 p3568 p4154 p4204 p4405 p4734 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h72735 : p4734)
    (h73390 : p3365 ∨ p2696)
    (h73526 : p4154 ∨ p2641)
    (h61144 : (¬ p2137) ∨ (¬ p2187) ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4204) ∨ (¬ p4405) ∨ (¬ p4734))
    : (¬ p3051) ∨ p2295 ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p2187) ∨ (¬ p4204) ∨ p2696 ∨ (¬ p2137) ∨ (¬ p4405) ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4734 := h72735;
    let u12 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h61144 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u11)))))))))))))))))))))))

theorem step93608 (p2383 p3379 p3452 p3923 p3953 p4376 p5020 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h42594 : (¬ p2383) ∨ (¬ p3452) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p4376) ∨ (¬ p5020))
    : (¬ p2383) ∨ p3379 ∨ (¬ p5020) ∨ (¬ p3923) ∨ (¬ p4376) ∨ (¬ p3953) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42594 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step93618 (p2383 p2608 p3923 p3954 p4870 p5020 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h42586 : (¬ p2383) ∨ (¬ p3923) ∨ (¬ p3954) ∨ (¬ p4870) ∨ (¬ p5020))
    : (¬ p2383) ∨ p2608 ∨ (¬ p3923) ∨ (¬ p4870) ∨ (¬ p5020) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42586 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93620 (p2608 p3319 p3654 p3954 p4026 p4870 p5020 : Prop)
    (h73504 : p4026 ∨ p3319)
    (h73498 : p3954 ∨ p2608)
    (h48099 : (¬ p3654) ∨ (¬ p3954) ∨ (¬ p4026) ∨ (¬ p4870) ∨ (¬ p5020))
    : (¬ p3654) ∨ p3319 ∨ (¬ p5020) ∨ (¬ p4870) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3319) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4026 := (Or.elim h73504 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48099 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93621 (p2307 p3309 p3319 p3461 p3549 p5020 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h49526 : (¬ p2307) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3549) ∨ (¬ p5020))
    : (¬ p3319) ∨ (¬ p3461) ∨ (¬ p5020) ∨ (¬ p2307) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49526 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93627 (p2307 p2497 p2608 p3309 p3549 p3954 p5020 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73406 : p3549 ∨ p3309)
    (h72001 : (¬ p3549) ∨ (¬ p5020) ∨ (¬ p3954) ∨ (¬ p2497) ∨ (¬ p2307))
    : p2608 ∨ p3309 ∨ (¬ p2307) ∨ (¬ p5020) ∨ (¬ p2497) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h72001 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93628 (p2307 p3309 p3449 p3549 p3860 p4994 p5020 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73406 : p3549 ∨ p3309)
    (h61066 : (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3860) ∨ (¬ p4994) ∨ (¬ p5020))
    : p3449 ∨ (¬ p2307) ∨ (¬ p4994) ∨ p3309 ∨ (¬ p5020) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4994 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61066 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93629 (p3266 p4200 p5120 : Prop)
    (h73928 : p5120 ∨ (¬ p3266))
    (h8651 : p4200 ∨ (¬ p5120))
    : p4200 ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4200) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5120 := (Or.elim h73928 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h8651 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step93630 (p3266 p4200 p6017 : Prop)
    (h74355 : (¬ p3266) ∨ (¬ p6017))
    (h13098 : p4200 ∨ p6017)
    : p4200 ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4200) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6017) := (Or.elim h74355 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13098 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93631 (p3146 p3949 p5055 : Prop)
    (h73896 : p5055 ∨ p3146)
    (h8472 : p3949 ∨ (¬ p5055))
    : p3949 ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3949) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr h));
    let u2 : p5055 := (Or.elim h73896 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h8472 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step93632 (p3146 p3949 p5995 : Prop)
    (h74329 : p3146 ∨ (¬ p5995))
    (h12957 : p3949 ∨ p5995)
    : p3949 ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3949) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5995) := (Or.elim h74329 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12957 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93633 (p2122 p2210 p2241 p2247 p2383 p2387 p2744 p2819 p2891 p3204 p3822 p3953 p4556 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73246 : p2387 ∨ p2383)
    (h73226 : p2247 ∨ p2241)
    (h52557 : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2387) ∨ (¬ p2744) ∨ (¬ p2819) ∨ (¬ p2891) ∨ (¬ p3204) ∨ (¬ p3822) ∨ (¬ p3953) ∨ (¬ p4556))
    : (¬ p2819) ∨ p2122 ∨ (¬ p2891) ∨ (¬ p4556) ∨ (¬ p3953) ∨ p2383 ∨ (¬ p2210) ∨ (¬ p3204) ∨ (¬ p2744) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h52557 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step93634 (p2608 p3093 p3953 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h5866 : (¬ p3093) ∨ (¬ p3953) ∨ (¬ p3954))
    : (¬ p3953) ∨ p2608 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3953 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5866 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step93637 (p2210 p2307 p3309 p3549 p3555 p3953 p4377 p5020 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73406 : p3549 ∨ p3309)
    (h42384 : (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3555) ∨ (¬ p3953) ∨ (¬ p4377) ∨ (¬ p5020))
    : p2210 ∨ (¬ p2307) ∨ (¬ p4377) ∨ (¬ p5020) ∨ (¬ p3953) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42384 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step93640 (p2122 p3309 p3367 p3549 p3953 p4426 p4752 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h51890 : (¬ p2122) ∨ (¬ p3367) ∨ (¬ p3549) ∨ (¬ p3953) ∨ (¬ p4426) ∨ (¬ p4752))
    : (¬ p3953) ∨ (¬ p2122) ∨ (¬ p3367) ∨ p3309 ∨ (¬ p4426) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3953 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51890 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step93644 (p2122 p2774 p3309 p3549 p3953 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h72002 : (¬ p3953) ∨ (¬ p3549) ∨ (¬ p2774) ∨ (¬ p2122))
    : (¬ p2122) ∨ p3309 ∨ (¬ p3953) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h72002 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step93645 (p2307 p2584 p2737 p3309 p3549 p3759 p3953 p4749 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h49519 : (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2737) ∨ (¬ p3549) ∨ (¬ p3759) ∨ (¬ p3953) ∨ (¬ p4749))
    : (¬ p3953) ∨ (¬ p3759) ∨ (¬ p2307) ∨ p3309 ∨ (¬ p2737) ∨ (¬ p4749) ∨ (¬ p2584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3953 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49519 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step93648 (p2177 p2459 p3256 p3919 p4118 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h72003 : (¬ p3919) ∨ (¬ p2459) ∨ (¬ p4118) ∨ (¬ p2177))
    : p3256 ∨ (¬ p2177) ∨ (¬ p3919) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h72003 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step93649 (p2187 p2192 p2210 p2254 p2459 p2807 p3256 p3414 p3919 p4118 p4133 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h73520 : p4118 ∨ p3256)
    (h48906 : (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2459) ∨ (¬ p3414) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4133))
    : p2807 ∨ (¬ p2187) ∨ (¬ p2254) ∨ p3256 ∨ (¬ p2459) ∨ (¬ p3919) ∨ (¬ p2210) ∨ (¬ p2192) ∨ (¬ p4133) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2807) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48906 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step93650 (p2459 p2881 p3256 p3919 p4118 p4280 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h48225 : (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4280))
    : p3256 ∨ (¬ p2881) ∨ (¬ p3919) ∨ (¬ p2459) ∨ (¬ p4280) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48225 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93654 (p2807 p3166 p3414 p3919 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h5808 : (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3919))
    : (¬ p3166) ∨ (¬ p3919) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h5808 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step93656 (p2459 p3256 p3579 p3868 p3919 p4118 p5564 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h41976 : (¬ p2459) ∨ (¬ p3579) ∨ (¬ p3868) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p5564))
    : (¬ p3868) ∨ (¬ p5564) ∨ (¬ p2459) ∨ (¬ p3919) ∨ (¬ p3579) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3868 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41976 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step93657 (p2528 p3609 p3919 p3931 p4340 p4383 p4967 p5564 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h42410 : (¬ p2528) ∨ (¬ p3919) ∨ (¬ p3931) ∨ (¬ p4340) ∨ (¬ p4383) ∨ (¬ p4967) ∨ (¬ p5564))
    : (¬ p3931) ∨ p3609 ∨ (¬ p3919) ∨ (¬ p2528) ∨ (¬ p4967) ∨ (¬ p5564) ∨ (¬ p4383) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3931 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4967 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42410 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step93662 (p2241 p2247 p2459 p2996 p3256 p3919 p4118 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73520 : p4118 ∨ p3256)
    (h61790 : (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2996) ∨ (¬ p3919) ∨ (¬ p4118))
    : (¬ p2996) ∨ p2241 ∨ p3256 ∨ (¬ p2459) ∨ (¬ p3919) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61790 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step93663 (p2177 p3073 p3146 p3919 p4132 p4261 p4288 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h72004 : (¬ p4261) ∨ (¬ p2177) ∨ (¬ p3146) ∨ (¬ p4288) ∨ (¬ p4132) ∨ (¬ p3919))
    : p3073 ∨ (¬ p4288) ∨ (¬ p3919) ∨ (¬ p4132) ∨ (¬ p2177) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4288 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h72004 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step93674 (p2440 p2542 p3878 p4355 p4437 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h25935 : (¬ p2542) ∨ (¬ p3878) ∨ (¬ p4355) ∨ (¬ p4437))
    : (¬ p4437) ∨ (¬ p3878) ∨ p2440 ∨ (¬ p4355) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h25935 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step93677 (p2563 p3146 p3256 p3692 p4110 p4355 p4437 p4509 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73516 : p4110 ∨ p2563)
    (h62066 : (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4110) ∨ (¬ p4355) ∨ (¬ p4437) ∨ (¬ p4509))
    : (¬ p3256) ∨ p3146 ∨ (¬ p4355) ∨ p2563 ∨ (¬ p4509) ∨ (¬ p4437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62066 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step93678 (p2144 p2156 p2427 p2563 p2598 p3055 p4110 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73350 : p3055 ∨ p2598)
    (h47260 : (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2427) ∨ (¬ p3055) ∨ (¬ p4110))
    : (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2427) ∨ p2563 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47260 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step93700 (p2122 p2144 p2156 p2187 p2819 p4358 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h46882 : (¬ p2122) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p4358))
    : (¬ p2144) ∨ (¬ p2187) ∨ (¬ p2156) ∨ p2819 ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46882 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step93702 (p2144 p2156 p2839 p2860 p3583 p3758 : Prop)
    (h73456 : p3758 ∨ p2860)
    (h73424 : p3583 ∨ p2839)
    (h72009 : (¬ p3758) ∨ (¬ p3583) ∨ (¬ p2156) ∨ (¬ p2144))
    : p2860 ∨ (¬ p2144) ∨ p2839 ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2860) := (fun h => hn (Or.inl h));
    let u1 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h72009 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step93705 (p2144 p2156 p2696 p2860 p3365 p3758 p5052 : Prop)
    (h73456 : p3758 ∨ p2860)
    (h73390 : p3365 ∨ p2696)
    (h50422 : (¬ p2144) ∨ (¬ p2156) ∨ (¬ p3365) ∨ (¬ p3758) ∨ (¬ p5052))
    : p2860 ∨ (¬ p2144) ∨ (¬ p5052) ∨ (¬ p2156) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2860) := (fun h => hn (Or.inl h));
    let u1 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50422 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93709 (p2132 p2144 p2230 p2241 p2573 p2608 p2696 p2737 p2743 p2901 p3016 p3574 p4320 p4365 p4535 p4702 p4717 p4735 p4882 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73734 : p4735 ∨ (¬ p2608))
    (h73622 : p4535 ∨ p2230)
    (h73298 : p2743 ∨ p2737)
    (h73552 : p4320 ∨ p2901)
    (h66977 : (¬ p4535) ∨ (¬ p4320) ∨ (¬ p2132) ∨ (¬ p2144) ∨ (¬ p4365) ∨ (¬ p4702) ∨ (¬ p4882) ∨ (¬ p2696) ∨ (¬ p2241) ∨ (¬ p4717) ∨ (¬ p3574) ∨ (¬ p4735) ∨ (¬ p2743) ∨ (¬ p2573))
    : p3016 ∨ (¬ p2573) ∨ (¬ p4365) ∨ (¬ p2132) ∨ (¬ p2608) ∨ (¬ p2144) ∨ (¬ p4702) ∨ (¬ p2696) ∨ p2230 ∨ p2737 ∨ (¬ p2241) ∨ (¬ p4717) ∨ p2901 ∨ (¬ p4882) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))));
    let u13 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))));
    let u14 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u15 : p4735 := (Or.elim h73734 (fun q0 => q0) (fun r0 => (False.elim (r0 u4))));
    let u16 : p4535 := (Or.elim h73622 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u17 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u18 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    (Or.elim h66977 (fun q0 => (False.elim (q0 u16))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u18))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u13))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u14))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u15))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u17))) (fun r12 => (False.elim (r12 u1)))))))))))))))))))))))))))))

theorem step93710 (p2144 p2156 p2252 p2264 p2750 p2807 p3125 p3366 p3414 p3461 p3553 p5123 p5558 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h73410 : p3553 ∨ p2264)
    (h64533 : (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3125) ∨ p3366 ∨ (¬ p3414) ∨ (¬ p3461) ∨ (¬ p3553) ∨ (¬ p5123) ∨ (¬ p5558))
    : p3366 ∨ (¬ p3461) ∨ (¬ p2252) ∨ (¬ p5123) ∨ (¬ p5558) ∨ p2807 ∨ (¬ p2750) ∨ (¬ p2144) ∨ (¬ p3125) ∨ (¬ p2156) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3366) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h64533 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u0 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u3))) (fun r9 => (False.elim (r9 u4)))))))))))))))))))))))

theorem step93714 (p2122 p2144 p2307 p2829 p2962 p3688 p3822 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h73444 : p3688 ∨ p2829)
    (h72012 : (¬ p3822) ∨ (¬ p3688) ∨ (¬ p2962) ∨ (¬ p2307) ∨ (¬ p2144))
    : (¬ p2307) ∨ p2122 ∨ (¬ p2144) ∨ (¬ p2962) ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2122) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h72012 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93717 (p2383 p4170 p5842 : Prop)
    (h74133 : p2383 ∨ (¬ p5842))
    (h12046 : p4170 ∨ p5842)
    : p4170 ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4170) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5842) := (Or.elim h74133 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12046 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93723 (p2088 p3146 p3692 p3857 p4115 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h73447 : (¬ p3146) ∨ (¬ p3692))
    (h6143 : p3692 ∨ (¬ p3857) ∨ (¬ p4115))
    : p2088 ∨ (¬ p3146) ∨ (¬ p4115) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2088) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p3692) := (Or.elim h73447 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h6143 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step93727 (p2373 p3880 p4109 p4115 p4238 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h16887 : (¬ p3880) ∨ (¬ p4109) ∨ (¬ p4115) ∨ (¬ p4238))
    : (¬ p4238) ∨ (¬ p4115) ∨ p2373 ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4238 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h16887 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step93733 (p2860 p3073 p3449 p3609 p4340 p4359 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h55061 : (¬ p2860) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p4340) ∨ (¬ p4359))
    : p3609 ∨ (¬ p3073) ∨ (¬ p2860) ∨ (¬ p3449) ∨ (¬ p4359) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55061 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93734 (p2608 p2839 p3146 p3583 p3609 p3954 p4340 p4359 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73498 : p3954 ∨ p2608)
    (h73424 : p3583 ∨ p2839)
    (h55150 : (¬ p3146) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4340) ∨ (¬ p4359))
    : p3609 ∨ p2608 ∨ p2839 ∨ (¬ p3146) ∨ (¬ p4359) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55150 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93737 (p2532 p3105 p3609 p4340 p4359 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h33865 : (¬ p2532) ∨ (¬ p3105) ∨ (¬ p4340) ∨ (¬ p4359))
    : p3609 ∨ (¬ p4359) ∨ (¬ p2532) ∨ (¬ p3105) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h33865 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step93738 (p3146 p3156 p3609 p4340 p4359 p4906 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h63200 : (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4906))
    : p3609 ∨ (¬ p3146) ∨ (¬ p4359) ∨ (¬ p3156) ∨ (¬ p4906) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h63200 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93739 (p2220 p3146 p3609 p4340 p4359 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h72013 : (¬ p2220) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p3146))
    : (¬ p4359) ∨ (¬ p3146) ∨ (¬ p2220) ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4359 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h72013 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step93741 (p2088 p3156 p3609 p3696 p4340 p4359 p4906 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h62334 : (¬ p2088) ∨ (¬ p3156) ∨ (¬ p3696) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4906))
    : p3609 ∨ (¬ p2088) ∨ (¬ p3156) ∨ (¬ p4906) ∨ (¬ p3696) ∨ (¬ p4359) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h62334 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step93742 (p2088 p2860 p3609 p3696 p4340 p4359 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h69533 : (¬ p4340) ∨ (¬ p2860) ∨ (¬ p3696) ∨ (¬ p2088) ∨ (¬ p4359))
    : p3609 ∨ (¬ p3696) ∨ (¬ p4359) ∨ (¬ p2860) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p3696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h69533 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93746 (p2870 p3073 p3093 p3609 p4317 p4340 p4359 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h46859 : (¬ p2870) ∨ (¬ p3073) ∨ (¬ p3093) ∨ (¬ p4317) ∨ (¬ p4340) ∨ (¬ p4359))
    : (¬ p4317) ∨ (¬ p3073) ∨ (¬ p4359) ∨ p3609 ∨ (¬ p2870) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4317 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46859 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step93747 (p2132 p2138 p2911 p2922 p3146 p3379 p3609 p4340 p4359 p4736 p4905 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73214 : p2138 ∨ p2132)
    (h57722 : (¬ p2138) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3146) ∨ (¬ p3379) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4736) ∨ (¬ p4905))
    : p3609 ∨ p2132 ∨ (¬ p2911) ∨ (¬ p4905) ∨ (¬ p2922) ∨ (¬ p3146) ∨ (¬ p4359) ∨ (¬ p3379) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h57722 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step93748 (p2088 p2319 p2563 p3609 p3957 p4340 p4359 p4590 p4882 p5016 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h54519 : (¬ p2088) ∨ (¬ p2319) ∨ (¬ p2563) ∨ (¬ p3957) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4590) ∨ (¬ p4882) ∨ (¬ p5016))
    : (¬ p5016) ∨ (¬ p2319) ∨ p3609 ∨ (¬ p2563) ∨ (¬ p2088) ∨ (¬ p4882) ∨ (¬ p3957) ∨ (¬ p4590) ∨ (¬ p4359) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4882 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54519 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step93749 (p2098 p2104 p2132 p2860 p4740 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h69534 : (¬ p2104) ∨ (¬ p2860) ∨ (¬ p2132) ∨ (¬ p4740))
    : (¬ p4740) ∨ p2098 ∨ (¬ p2860) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4740 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h69534 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step93750 (p2839 p2860 p3537 p4242 p4740 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h69535 : (¬ p4242) ∨ (¬ p2860) ∨ (¬ p2839) ∨ (¬ p4740))
    : p3537 ∨ (¬ p4740) ∨ (¬ p2860) ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p4740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h69535 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step93751 (p2839 p2870 p3537 p4242 p4740 p4901 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h62116 : (¬ p2839) ∨ (¬ p2870) ∨ (¬ p4242) ∨ (¬ p4740) ∨ (¬ p4901))
    : p3537 ∨ (¬ p4740) ∨ (¬ p2839) ∨ (¬ p4901) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p4740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h62116 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93752 (p2098 p2104 p2132 p3156 p4740 p4906 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h48000 : (¬ p2104) ∨ (¬ p2132) ∨ (¬ p3156) ∨ (¬ p4740) ∨ (¬ p4906))
    : p2098 ∨ (¬ p4740) ∨ (¬ p2132) ∨ (¬ p4906) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p4740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48000 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step93759 (p2761 p4829 p5915 : Prop)
    (h74227 : (¬ p2761) ∨ (¬ p5915))
    (h12472 : p4829 ∨ p5915)
    : p4829 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4829) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5915) := (Or.elim h74227 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12472 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93760 (p2210 p2253 p2651 p2727 p3555 p4111 p4448 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73412 : p3555 ∨ p2210)
    (h51676 : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p3555) ∨ (¬ p4111) ∨ (¬ p4448))
    : p2727 ∨ (¬ p2253) ∨ (¬ p4448) ∨ p2210 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4448 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51676 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93761 (p2166 p2220 p2241 p3369 p4120 p4448 : Prop)
    (h73522 : p4120 ∨ p2220)
    (h49215 : (¬ p2166) ∨ (¬ p2241) ∨ (¬ p3369) ∨ (¬ p4120) ∨ (¬ p4448))
    : (¬ p3369) ∨ p2220 ∨ (¬ p2241) ∨ (¬ p2166) ∨ (¬ p4448) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3369 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4448 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49215 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93764 (p2383 p4197 p5842 : Prop)
    (h74133 : p2383 ∨ (¬ p5842))
    (h12048 : p4197 ∨ p5842)
    : p4197 ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4197) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5842) := (Or.elim h74133 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12048 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93765 (p2651 p2657 p2751 p2946 p3136 p3487 p4281 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73288 : p2657 ∨ p2651)
    (h44973 : (¬ p2657) ∨ (¬ p2751) ∨ (¬ p2946) ∨ (¬ p3487) ∨ (¬ p4281) ∨ (¬ p4315))
    : p3136 ∨ (¬ p2946) ∨ p2651 ∨ (¬ p2751) ∨ (¬ p4281) ∨ (¬ p3487) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44973 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step93767 (p2220 p2284 p2406 p3156 p3497 p4109 p4281 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h47411 : (¬ p2220) ∨ (¬ p2284) ∨ (¬ p2406) ∨ (¬ p3497) ∨ (¬ p4109) ∨ (¬ p4281))
    : p3156 ∨ (¬ p2220) ∨ (¬ p4281) ∨ (¬ p4109) ∨ (¬ p2284) ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47411 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step93770 (p2241 p2437 p2440 p2542 p2922 p3742 p4281 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73270 : p2542 ∨ p2440)
    (h47220 : (¬ p2241) ∨ (¬ p2542) ∨ (¬ p2922) ∨ (¬ p3742) ∨ (¬ p4281))
    : (¬ p2922) ∨ p2437 ∨ (¬ p2241) ∨ p2440 ∨ (¬ p4281) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47220 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93774 (p2331 p2406 p2440 p2641 p4117 p4154 p4281 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h49181 : (¬ p2331) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (¬ p4117) ∨ (¬ p4154) ∨ (¬ p4281))
    : p2641 ∨ (¬ p2406) ∨ (¬ p2331) ∨ (¬ p4117) ∨ (¬ p4281) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49181 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step93781 (p2088 p3171 p3256 p5106 : Prop)
    (h73922 : p5106 ∨ p3256)
    (h67071 : (¬ p5106) ∨ (¬ p3171) ∨ (¬ p2088))
    : p3256 ∨ (¬ p3171) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p5106 := (Or.elim h73922 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h67071 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step93784 (p3005 p3136 p3171 p3998 p4315 p5693 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h55195 : (¬ p3005) ∨ (¬ p3171) ∨ (¬ p3998) ∨ (¬ p4315) ∨ (¬ p5693))
    : (¬ p5693) ∨ (¬ p3998) ∨ (¬ p3005) ∨ p3136 ∨ (¬ p3171) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55195 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step93785 (p2166 p2191 p3005 p3136 p3171 p4115 p4315 p4957 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73222 : p2191 ∨ p2166)
    (h49106 : (¬ p2191) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p4115) ∨ (¬ p4315) ∨ (¬ p4957))
    : (¬ p3005) ∨ (¬ p4957) ∨ (¬ p4115) ∨ p3136 ∨ (¬ p3171) ∨ p2166 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49106 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step93790 (p2685 p3005 p3034 p3171 p3527 p3548 p3572 p4403 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h73404 : p3548 ∨ p3527)
    (h40988 : (¬ p3005) ∨ (¬ p3034) ∨ (¬ p3171) ∨ (¬ p3548) ∨ (¬ p3572) ∨ (¬ p4403))
    : (¬ p4403) ∨ (¬ p3005) ∨ p2685 ∨ (¬ p3034) ∨ (¬ p3171) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4403 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h40988 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step93791 (p2685 p3005 p3171 p3572 p3998 p5693 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h47859 : (¬ p3005) ∨ (¬ p3171) ∨ (¬ p3572) ∨ (¬ p3998) ∨ (¬ p5693))
    : (¬ p5693) ∨ (¬ p3998) ∨ (¬ p3005) ∨ p2685 ∨ (¬ p3171) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47859 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step93793 (p2249 p2656 p2727 p2807 p3051 p3414 p3699 p4399 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h52518 : (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3051) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p4399))
    : (¬ p4399) ∨ (¬ p3051) ∨ (¬ p2656) ∨ (¬ p3699) ∨ p2807 ∨ (¬ p2249) ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52518 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step93801 (p3166 p3256 p3609 p4340 p4364 p4790 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h59156 : (¬ p3166) ∨ (¬ p3256) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p4790))
    : p3609 ∨ (¬ p4364) ∨ (¬ p4790) ∨ (¬ p3256) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p4364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h59156 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93811 (p2088 p2630 p3567 p3609 p4114 p4340 p4364 p4972 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h42547 : (¬ p2088) ∨ (¬ p2630) ∨ (¬ p3567) ∨ (¬ p4114) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p4972))
    : p3609 ∨ (¬ p4114) ∨ (¬ p4972) ∨ (¬ p3567) ∨ (¬ p4364) ∨ (¬ p2630) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p4114 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42547 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step93814 (p2807 p4853 p5921 : Prop)
    (h74235 : (¬ p2807) ∨ (¬ p5921))
    (h12509 : p4853 ∨ p5921)
    : p4853 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4853) := (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5921) := (Or.elim h74235 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12509 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93815 (p2807 p4854 p5921 : Prop)
    (h74235 : (¬ p2807) ∨ (¬ p5921))
    (h12510 : p4854 ∨ p5921)
    : p4854 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4854) := (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5921) := (Or.elim h74235 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12510 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93816 (p2807 p4104 p5921 : Prop)
    (h74235 : (¬ p2807) ∨ (¬ p5921))
    (h12511 : p4104 ∨ p5921)
    : p4104 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4104) := (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5921) := (Or.elim h74235 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93817 (p2807 p4155 p5921 : Prop)
    (h74235 : (¬ p2807) ∨ (¬ p5921))
    (h12513 : p4155 ∨ p5921)
    : p4155 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4155) := (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5921) := (Or.elim h74235 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12513 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93826 (p2331 p2651 p2963 p3083 p4389 p4598 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h49608 : (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3083) ∨ (¬ p4389) ∨ (¬ p4598))
    : p2331 ∨ (¬ p3083) ∨ (¬ p4598) ∨ (¬ p4389) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49608 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93827 (p2156 p2192 p2440 p3646 p3948 p4031 p4814 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h50175 : (¬ p2192) ∨ (¬ p2440) ∨ (¬ p3646) ∨ (¬ p3948) ∨ (¬ p4031) ∨ (¬ p4814))
    : (¬ p2192) ∨ (¬ p3948) ∨ p2156 ∨ (¬ p4814) ∨ (¬ p2440) ∨ (¬ p4031) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50175 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step93830 (p2946 p2951 p2955 : Prop)
    (h73331 : p2946 ∨ (¬ p2955))
    (h4035 : p2951 ∨ p2955)
    : p2951 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2951) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2955) := (Or.elim h73331 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h4035 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step93841 (p2166 p2210 p2241 p2247 p2363 p2744 p2774 p2780 p3366 p3609 p4078 p4340 p4433 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73226 : p2247 ∨ p2241)
    (h73308 : p2780 ∨ p2774)
    (h63877 : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4433))
    : p3609 ∨ (¬ p4078) ∨ (¬ p3366) ∨ (¬ p2210) ∨ (¬ p2363) ∨ (¬ p2166) ∨ (¬ p4433) ∨ p2241 ∨ (¬ p2744) ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h63877 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step93844 (p2230 p2241 p2247 p2406 p3238 p4079 p4813 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73226 : p2247 ∨ p2241)
    (h41083 : (¬ p2230) ∨ (¬ p2247) ∨ (¬ p3238) ∨ (¬ p4079) ∨ (¬ p4813))
    : p2406 ∨ (¬ p4079) ∨ (¬ p4813) ∨ (¬ p2230) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4813 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41083 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93850 (p2139 p2331 p2373 p2427 p2797 p2963 p3005 p3051 p3877 p4043 p4235 p4236 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73338 : p2963 ∨ p2331)
    (h73536 : p4235 ∨ p2427)
    (h57469 : (¬ p2139) ∨ (¬ p2373) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3051) ∨ (¬ p3877) ∨ (¬ p4043) ∨ (¬ p4235) ∨ (¬ p4236))
    : p3005 ∨ p2331 ∨ (¬ p4043) ∨ (¬ p2797) ∨ (¬ p2139) ∨ p2427 ∨ (¬ p2373) ∨ (¬ p4236) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h57469 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step93862 (p2139 p2156 p2274 p2396 p2651 p2657 p3276 p4236 p4641 p5170 p5284 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h42405 : (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2657) ∨ (¬ p3276) ∨ (¬ p4236) ∨ (¬ p4641) ∨ (¬ p5170) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p2396) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2139) ∨ (¬ p5170) ∨ (¬ p4236) ∨ (¬ p3276) ∨ p2651 ∨ (¬ p4641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h42405 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step93873 (p2230 p2331 p2363 p2427 p2819 p2963 p3246 p3366 p3519 p3950 p4236 p4328 p4347 p4358 p4376 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73338 : p2963 ∨ p2331)
    (h73564 : p4358 ∨ p2819)
    (h42599 : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2963) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4328) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4376))
    : p2363 ∨ (¬ p4236) ∨ p2331 ∨ p2819 ∨ (¬ p3246) ∨ (¬ p4376) ∨ (¬ p2230) ∨ (¬ p3519) ∨ (¬ p3950) ∨ (¬ p4328) ∨ (¬ p3366) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u13 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u14 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42599 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u12))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u14))) (fun r10 => (False.elim (r10 u5)))))))))))))))))))))))))

theorem step93874 (p2187 p2230 p2563 p2630 p2810 p3005 p3166 p3172 p3366 p3519 p3979 p4236 p4376 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73356 : p3172 ∨ p3166)
    (h47845 : (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3979) ∨ (¬ p4236) ∨ (¬ p4376))
    : (¬ p3366) ∨ (¬ p2187) ∨ (¬ p3005) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p2563) ∨ (¬ p2230) ∨ p2630 ∨ (¬ p4236) ∨ p3166 ∨ (¬ p3979) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3366 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h47845 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u4)))))))))))))))))))))))

theorem step93876 (p2220 p2459 p2630 p2651 p2657 p3005 p3146 p3366 p3370 p3877 p4041 p4236 p4348 p4377 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73488 : p3877 ∨ p3005)
    (h73288 : p2657 ∨ p2651)
    (h63420 : (¬ p2220) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p4236) ∨ (¬ p4348) ∨ (¬ p4377))
    : (¬ p3370) ∨ (¬ p3146) ∨ p2459 ∨ (¬ p4377) ∨ (¬ p3366) ∨ p3005 ∨ p2651 ∨ (¬ p2630) ∨ (¬ p2220) ∨ (¬ p4041) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3370 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h63420 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (False.elim (r9 u3)))))))))))))))))))))))

theorem step93877 (p2630 p2651 p2657 p3005 p3877 p4149 p4236 p4286 p4437 : Prop)
    (h73548 : p4286 ∨ p4149)
    (h73488 : p3877 ∨ p3005)
    (h73288 : p2657 ∨ p2651)
    (h47157 : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4286) ∨ (¬ p4437))
    : p4149 ∨ (¬ p4236) ∨ (¬ p2630) ∨ p3005 ∨ p2651 ∨ (¬ p4437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4149) := (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4286 := (Or.elim h73548 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47157 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step93880 (p2563 p2651 p2657 p3727 p4110 p4236 p4700 p5740 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73288 : p2657 ∨ p2651)
    (h45658 : (¬ p2657) ∨ (¬ p3727) ∨ (¬ p4110) ∨ (¬ p4236) ∨ (¬ p4700) ∨ (¬ p5740))
    : (¬ p3727) ∨ (¬ p5740) ∨ p2563 ∨ (¬ p4700) ∨ p2651 ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45658 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step93886 (p2553 p2573 p2579 p2588 p2641 p2668 p2696 p2742 p3363 p3367 p3585 p4405 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73274 : p2579 ∨ p2573)
    (h73428 : p3585 ∨ p3367)
    (h72017 : (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2579) ∨ (¬ p4405) ∨ (¬ p3585) ∨ (¬ p2588) ∨ (¬ p2742) ∨ (¬ p3363))
    : (¬ p2742) ∨ (¬ p2668) ∨ p2553 ∨ (¬ p2641) ∨ (¬ p4405) ∨ (¬ p2696) ∨ (¬ p3363) ∨ p2573 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2742 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u11 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h72017 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step93892 (p2685 p2742 p2996 p3027 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h28200 : p2685 ∨ (¬ p2742) ∨ (¬ p3027))
    : (¬ p2742) ∨ p2996 ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2742 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h28200 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step93897 (p2449 p2619 p2696 p2742 p2839 p2996 p3027 p3146 p3583 p3692 p3694 p3950 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73450 : p3694 ∨ p2619)
    (h73424 : p3583 ∨ p2839)
    (h73340 : p3027 ∨ p2996)
    (h72018 : (¬ p3583) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3950) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p2449) ∨ (¬ p2696))
    : (¬ p2742) ∨ p3146 ∨ (¬ p2449) ∨ p2619 ∨ p2839 ∨ (¬ p2696) ∨ (¬ p3950) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2742 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2619) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3694 := (Or.elim h73450 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h72018 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step93898 (p2264 p2696 p2742 p2881 p2996 p3027 p3570 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h73418 : p3570 ∨ p2881)
    (h45205 : (¬ p2264) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3570))
    : (¬ p2264) ∨ p2996 ∨ (¬ p2742) ∨ p2881 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45205 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step93899 (p2143 p2220 p2449 p2696 p2742 p2839 p2996 p3027 p3146 p3583 p3692 p3950 p4120 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73340 : p3027 ∨ p2996)
    (h73424 : p3583 ∨ p2839)
    (h73522 : p4120 ∨ p2220)
    (h72019 : (¬ p3583) ∨ (¬ p2449) ∨ (¬ p2143) ∨ (¬ p3950) ∨ (¬ p2742) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p2696) ∨ (¬ p3027))
    : p3146 ∨ (¬ p3950) ∨ (¬ p2143) ∨ p2996 ∨ (¬ p2742) ∨ p2839 ∨ (¬ p2449) ∨ p2220 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h72019 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u10)))))))))))))))))))

theorem step93903 (p2630 p2727 p2742 p2810 p4111 : Prop)
    (h73517 : (¬ p2727) ∨ (¬ p4111))
    (h73316 : p2810 ∨ p2630)
    (h6752 : (¬ p2742) ∨ (¬ p2810) ∨ p4111)
    : (¬ p2742) ∨ (¬ p2727) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2742 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4111) := (Or.elim h73517 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6752 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (u3 r1)))))))

theorem step93905 (p2641 p2742 p2797 p4154 p4195 : Prop)
    (h73525 : (¬ p2641) ∨ (¬ p4154))
    (h73532 : p4195 ∨ p2797)
    (h37634 : (¬ p2742) ∨ p4154 ∨ (¬ p4195))
    : (¬ p2641) ∨ p2797 ∨ (¬ p2742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4154) := (Or.elim h73525 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h37634 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u4)))))))

theorem step93914 (p2427 p2440 p2542 p2696 p2727 p2742 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h45182 : (¬ p2427) ∨ (¬ p2542) ∨ (¬ p2696) ∨ (¬ p2727) ∨ (¬ p2742))
    : (¬ p2742) ∨ (¬ p2727) ∨ (¬ p2427) ∨ p2440 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2742 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45182 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step93922 (p2742 p3005 p3189 p3877 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h32601 : (¬ p2742) ∨ (¬ p3189) ∨ (¬ p3877))
    : (¬ p3189) ∨ p3005 ∨ (¬ p2742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h32601 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step93924 (p2143 p2696 p2742 p2839 p3051 p3189 p3246 p3256 p3556 p3583 p3690 p4669 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73424 : p3583 ∨ p2839)
    (h73446 : p3690 ∨ p3246)
    (h72024 : (¬ p3690) ∨ (¬ p3583) ∨ (¬ p2696) ∨ (¬ p3556) ∨ (¬ p2742) ∨ (¬ p3189) ∨ (¬ p4669) ∨ (¬ p2143) ∨ (¬ p3256))
    : (¬ p3189) ∨ p3051 ∨ p2839 ∨ (¬ p3256) ∨ p3246 ∨ (¬ p2742) ∨ (¬ p4669) ∨ (¬ p2696) ∨ (¬ p2143) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h72024 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step93926 (p2246 p2742 p2946 p3136 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h20578 : (¬ p2246) ∨ (¬ p2742) ∨ (¬ p2946) ∨ (¬ p4315))
    : (¬ p2246) ∨ (¬ p2742) ∨ (¬ p2946) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h20578 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step93929 (p2696 p2742 p2911 p2992 p3156 p3363 p3367 p3389 p3540 p3585 p3644 p4902 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h73434 : p3644 ∨ p2911)
    (h73402 : p3540 ∨ p3389)
    (h72025 : (¬ p3585) ∨ (¬ p2742) ∨ (¬ p4902) ∨ (¬ p3644) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3540) ∨ (¬ p3363) ∨ (¬ p2696))
    : (¬ p2992) ∨ p3367 ∨ (¬ p3156) ∨ (¬ p2696) ∨ p2911 ∨ (¬ p4902) ∨ (¬ p2742) ∨ p3389 ∨ (¬ p3363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h72025 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step93934 (p2156 p2284 p2901 p2911 p3399 p3527 p3548 p3952 p4366 p4521 p4647 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73570 : p4366 ∨ p3399)
    (h73404 : p3548 ∨ p3527)
    (h54238 : (¬ p2156) ∨ (¬ p2901) ∨ (¬ p2911) ∨ (¬ p3548) ∨ (¬ p3952) ∨ (¬ p4366) ∨ (¬ p4521) ∨ (¬ p4647))
    : (¬ p2901) ∨ p2284 ∨ p3399 ∨ (¬ p2911) ∨ (¬ p2156) ∨ (¬ p4521) ∨ p3527 ∨ (¬ p4647) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h54238 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step93936 (p2156 p2274 p2396 p2509 p2528 p2534 p3379 p3452 p3950 p4521 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73394 : p3452 ∨ p3379)
    (h55974 : (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p3452) ∨ (¬ p3950) ∨ (¬ p4521))
    : (¬ p2396) ∨ (¬ p2274) ∨ p2528 ∨ (¬ p2509) ∨ (¬ p2156) ∨ (¬ p4521) ∨ p3379 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h55974 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step93938 (p2156 p2177 p2241 p2247 p2274 p2727 p3083 p4111 p4256 p4438 p4521 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73542 : p4256 ∨ p3083)
    (h73518 : p4111 ∨ p2727)
    (h48145 : (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2274) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4438) ∨ (¬ p4521))
    : (¬ p2274) ∨ p2241 ∨ p3083 ∨ (¬ p4521) ∨ (¬ p4438) ∨ (¬ p2177) ∨ p2727 ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h48145 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step93941 (p2187 p2274 p2307 p2608 p2962 p3097 p3367 p3585 p3641 p3874 p3954 p4384 p4521 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73498 : p3954 ∨ p2608)
    (h73484 : p3874 ∨ p3641)
    (h73428 : p3585 ∨ p3367)
    (h42014 : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3585) ∨ (¬ p3874) ∨ (¬ p3954) ∨ (¬ p4384) ∨ (¬ p4521))
    : (¬ p2307) ∨ p2274 ∨ (¬ p2962) ∨ (¬ p2187) ∨ p2608 ∨ p3641 ∨ (¬ p4384) ∨ p3367 ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h42014 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step93948 (p2284 p3005 p3136 p3189 p3952 p4315 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73550 : p4315 ∨ p3136)
    (h73496 : p3952 ∨ p2284)
    (h58198 : (¬ p3005) ∨ (¬ p3952) ∨ (¬ p4315) ∨ (¬ p4360))
    : (¬ p3005) ∨ p3189 ∨ p3136 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58198 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step93949 (p2241 p2247 p2630 p2810 p3005 p3189 p4360 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73566 : p4360 ∨ p3189)
    (h73316 : p2810 ∨ p2630)
    (h46256 : (¬ p2247) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p4360))
    : (¬ p3005) ∨ p2241 ∨ p3189 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46256 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step93950 (p2901 p3005 p3136 p3189 p4315 p4320 p4360 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73550 : p4315 ∨ p3136)
    (h73566 : p4360 ∨ p3189)
    (h43091 : (¬ p3005) ∨ (¬ p4315) ∨ (¬ p4320) ∨ (¬ p4360))
    : (¬ p3005) ∨ p2901 ∨ p3136 ∨ p3189 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43091 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step93953 (p2440 p2630 p2810 p3005 p3166 p3172 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73316 : p2810 ∨ p2630)
    (h47817 : (¬ p2440) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3172))
    : (¬ p3005) ∨ p3166 ∨ (¬ p2440) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47817 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step93954 (p2630 p2810 p3005 p3016 p3166 p3172 p3574 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73356 : p3172 ∨ p3166)
    (h73316 : p2810 ∨ p2630)
    (h45412 : (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3574))
    : (¬ p3005) ∨ p3016 ∨ p3166 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45412 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step93959 (p2470 p2476 p2630 p2659 p2810 p3005 p4346 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73250 : p2476 ∨ p2470)
    (h45645 : (¬ p2476) ∨ (¬ p2659) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p4346))
    : (¬ p3005) ∨ (¬ p4346) ∨ (¬ p2659) ∨ p2630 ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45645 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step93962 (p2406 p2630 p2810 p3005 p3238 p4346 p4607 p4811 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73316 : p2810 ∨ p2630)
    (h48041 : (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3238) ∨ (¬ p4346) ∨ (¬ p4607) ∨ (¬ p4811))
    : (¬ p3005) ∨ (¬ p4346) ∨ (¬ p4811) ∨ (¬ p4607) ∨ p2406 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48041 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step93965 (p2481 p2509 p2630 p2810 p3005 p3171 p4811 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h41130 : (¬ p2481) ∨ (¬ p2509) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p4811))
    : (¬ p2481) ∨ (¬ p3171) ∨ (¬ p4811) ∨ (¬ p3005) ∨ (¬ p2509) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2481 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41130 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step93966 (p2630 p2651 p2810 p3005 p4009 p4117 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h46483 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p4009) ∨ (¬ p4117))
    : (¬ p4009) ∨ (¬ p3005) ∨ (¬ p4117) ∨ p2630 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46483 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step93968 (p2145 p2220 p2459 p2630 p2651 p2810 p3005 p3146 p3692 p4117 p4120 p4550 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73522 : p4120 ∨ p2220)
    (h73316 : p2810 ∨ p2630)
    (h53817 : (¬ p2145) ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3692) ∨ (¬ p4117) ∨ (¬ p4120) ∨ (¬ p4550))
    : p3146 ∨ p2220 ∨ (¬ p4117) ∨ (¬ p4550) ∨ (¬ p2651) ∨ (¬ p2145) ∨ (¬ p3005) ∨ p2630 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h53817 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step93969 (p2284 p3005 p3136 p3166 p3172 p3952 p4315 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73550 : p4315 ∨ p3136)
    (h73496 : p3952 ∨ p2284)
    (h47944 : (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3952) ∨ (¬ p4315))
    : (¬ p3005) ∨ p3166 ∨ p3136 ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47944 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step93972 (p2352 p2630 p2651 p2810 p3005 p3956 p4117 p4417 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h73316 : p2810 ∨ p2630)
    (h47423 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3956) ∨ (¬ p4117) ∨ (¬ p4417))
    : (¬ p4417) ∨ (¬ p3005) ∨ p2352 ∨ p2630 ∨ (¬ p4117) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47423 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step93973 (p2331 p2630 p2651 p2810 p2963 p3005 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73316 : p2810 ∨ p2630)
    (h54264 : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (¬ p3005))
    : (¬ p3005) ∨ p2331 ∨ (¬ p2651) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54264 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step93979 (p2177 p2252 p2299 p2630 p2741 p2810 p3005 p3166 p3172 p3379 p3399 p3452 p3527 p4376 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73316 : p2810 ∨ p2630)
    (h73234 : p2299 ∨ p2177)
    (h73356 : p3172 ∨ p3166)
    (h64864 : (¬ p2252) ∨ (¬ p2299) ∨ (¬ p2741) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3527) ∨ (¬ p4376))
    : p3379 ∨ (¬ p2252) ∨ (¬ p3005) ∨ (¬ p3399) ∨ (¬ p3527) ∨ p2630 ∨ p2177 ∨ (¬ p4376) ∨ (¬ p2741) ∨ p3166 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h64864 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step93981 (p2145 p2156 p2177 p2274 p2299 p2630 p2651 p2810 p3005 p3097 p3646 p4117 p4550 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73234 : p2299 ∨ p2177)
    (h73436 : p3646 ∨ p2156)
    (h73352 : p3097 ∨ p2274)
    (h61332 : (¬ p2145) ∨ (¬ p2299) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4117) ∨ (¬ p4550))
    : (¬ p2651) ∨ p2630 ∨ (¬ p2145) ∨ (¬ p4117) ∨ p2177 ∨ p2156 ∨ (¬ p4550) ∨ p2274 ∨ (¬ p3005) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h61332 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step93982 (p2696 p2741 p3005 p3189 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h72029 : (¬ p3005) ∨ (¬ p4360) ∨ (¬ p2696) ∨ (¬ p2741))
    : p3189 ∨ (¬ p3005) ∨ (¬ p2696) ∨ (¬ p2741) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h72029 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step93983 (p2509 p2630 p2810 p3005 p4346 p4811 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h48042 : (¬ p2509) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p4346) ∨ (¬ p4811))
    : (¬ p3005) ∨ (¬ p4346) ∨ (¬ p2509) ∨ p2630 ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48042 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step93984 (p2459 p2797 p3005 p3256 p4195 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73532 : p4195 ∨ p2797)
    (h45459 : (¬ p3005) ∨ (¬ p3256) ∨ (¬ p4195) ∨ (¬ p4348))
    : (¬ p3005) ∨ (¬ p3256) ∨ p2459 ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45459 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step93986 (p3005 p3136 p4009 p4315 p5580 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h47162 : (¬ p3005) ∨ (¬ p4009) ∨ (¬ p4315) ∨ (¬ p5580))
    : (¬ p4009) ∨ (¬ p3005) ∨ (¬ p5580) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47162 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step93988 (p2331 p2459 p2470 p2476 p2528 p2534 p2797 p3005 p4117 p4195 p4550 p4729 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73532 : p4195 ∨ p2797)
    (h73250 : p2476 ∨ p2470)
    (h62091 : (¬ p2331) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3005) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4550) ∨ (¬ p4729))
    : p2528 ∨ p2797 ∨ p2470 ∨ (¬ p2459) ∨ (¬ p2331) ∨ (¬ p4117) ∨ (¬ p4729) ∨ (¬ p3005) ∨ (¬ p4550) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62091 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step93990 (p2177 p2299 p2553 p2573 p2579 p2588 p2608 p2737 p3005 p4550 p5193 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73282 : p2588 ∨ p2553)
    (h73274 : p2579 ∨ p2573)
    (h63858 : (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3005) ∨ (¬ p4550) ∨ (¬ p5193))
    : (¬ p3005) ∨ (¬ p2608) ∨ (¬ p2737) ∨ p2177 ∨ (¬ p4550) ∨ p2553 ∨ p2573 ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h63858 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step93993 (p2307 p2313 p2352 p2553 p2787 p2946 p3005 p3136 p3956 p4117 p4315 p4771 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73500 : p3956 ∨ p2352)
    (h73550 : p4315 ∨ p3136)
    (h55184 : (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2787) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3956) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4771))
    : (¬ p2553) ∨ p2307 ∨ (¬ p2946) ∨ p2352 ∨ (¬ p3005) ∨ (¬ p4771) ∨ (¬ p4117) ∨ (¬ p2787) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4771 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h55184 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step93994 (p2246 p2749 p2946 p3005 p3136 p3379 p3399 p3527 p3548 p4315 p4366 p4550 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73404 : p3548 ∨ p3527)
    (h73550 : p4315 ∨ p3136)
    (h72030 : (¬ p3379) ∨ (¬ p2946) ∨ (¬ p2749) ∨ (¬ p2246) ∨ (¬ p4315) ∨ (¬ p4550) ∨ (¬ p3548) ∨ (¬ p3005) ∨ (¬ p4366))
    : (¬ p2246) ∨ p3399 ∨ (¬ p4550) ∨ p3527 ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p2749) ∨ (¬ p3379) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h72030 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step93995 (p2177 p2248 p2299 p2946 p3005 p3093 p3136 p3309 p3549 p3591 p4315 p4550 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73550 : p4315 ∨ p3136)
    (h73234 : p2299 ∨ p2177)
    (h73406 : p3549 ∨ p3309)
    (h62829 : (¬ p2248) ∨ (¬ p2299) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4315) ∨ (¬ p4550))
    : p3093 ∨ (¬ p3005) ∨ (¬ p2946) ∨ p3136 ∨ p2177 ∨ (¬ p4550) ∨ (¬ p2248) ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h62829 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step93998 (p2696 p3005 p4009 p4149 p4286 : Prop)
    (h73548 : p4286 ∨ p4149)
    (h46465 : (¬ p2696) ∨ (¬ p3005) ∨ (¬ p4009) ∨ (¬ p4286))
    : p4149 ∨ (¬ p4009) ∨ (¬ p3005) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4149) := (fun h => hn (Or.inl h));
    let u1 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4286 := (Or.elim h73548 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46465 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step94000 (p2230 p2427 p2589 p2696 p3005 p3246 p3256 p3690 p4235 p4669 p4729 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73536 : p4235 ∨ p2427)
    (h73446 : p3690 ∨ p3246)
    (h49748 : (¬ p2589) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4669) ∨ (¬ p4729))
    : (¬ p3005) ∨ (¬ p3256) ∨ p2230 ∨ p2427 ∨ (¬ p2696) ∨ (¬ p4729) ∨ (¬ p4669) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49748 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step94001 (p2220 p2954 p3005 p3136 p4120 p4311 p4315 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73522 : p4120 ∨ p2220)
    (h55332 : (¬ p2954) ∨ (¬ p3005) ∨ (¬ p4120) ∨ (¬ p4311) ∨ (¬ p4315))
    : (¬ p4311) ∨ (¬ p3005) ∨ p3136 ∨ (¬ p2954) ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4311 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2220) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4120 := (Or.elim h73522 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55332 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94003 (p2230 p2331 p2427 p2589 p2797 p2881 p3005 p3570 p4117 p4195 p4235 p4550 p4729 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73536 : p4235 ∨ p2427)
    (h73284 : p2589 ∨ p2230)
    (h73418 : p3570 ∨ p2881)
    (h50770 : (¬ p2331) ∨ (¬ p2589) ∨ (¬ p3005) ∨ (¬ p3570) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4235) ∨ (¬ p4550) ∨ (¬ p4729))
    : p2797 ∨ (¬ p3005) ∨ (¬ p2331) ∨ (¬ p4550) ∨ p2427 ∨ (¬ p4729) ∨ p2230 ∨ p2881 ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50770 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step94005 (p2230 p2589 p2696 p2982 p3005 p4009 p4322 p4729 p4948 p5119 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73846 : p4948 ∨ p2982)
    (h49484 : (¬ p2589) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p4009) ∨ (¬ p4322) ∨ (¬ p4729) ∨ (¬ p4948) ∨ (¬ p5119))
    : (¬ p4322) ∨ (¬ p4009) ∨ (¬ p2696) ∨ p2230 ∨ (¬ p4729) ∨ (¬ p3005) ∨ (¬ p5119) ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49484 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step94014 (p3005 p3136 p3146 p3256 p3692 p4315 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73550 : p4315 ∨ p3136)
    (h46746 : (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4315))
    : (¬ p3256) ∨ (¬ p3005) ∨ p3146 ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46746 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step94015 (p2363 p3005 p3136 p3256 p4315 p4347 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73560 : p4347 ∨ p2363)
    (h56734 : (¬ p3005) ∨ (¬ p3256) ∨ (¬ p4315) ∨ (¬ p4347))
    : (¬ p3256) ∨ (¬ p3005) ∨ p3136 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56734 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step94016 (p2417 p2696 p2761 p3005 p3389 p3540 p4009 p4278 p4381 p4729 p5119 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73402 : p3540 ∨ p3389)
    (h73546 : p4278 ∨ p2417)
    (h50189 : (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3540) ∨ (¬ p4009) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p4729) ∨ (¬ p5119))
    : p2761 ∨ (¬ p4009) ∨ (¬ p4729) ∨ p3389 ∨ p2417 ∨ (¬ p5119) ∨ (¬ p3005) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50189 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step94020 (p2230 p2427 p2589 p2608 p2737 p2881 p3005 p3570 p4235 p4550 p5193 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73418 : p3570 ∨ p2881)
    (h73284 : p2589 ∨ p2230)
    (h51439 : (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3005) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4550) ∨ (¬ p5193))
    : (¬ p3005) ∨ (¬ p2608) ∨ (¬ p5193) ∨ (¬ p4550) ∨ p2427 ∨ p2881 ∨ (¬ p2737) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51439 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step94023 (p2737 p2839 p3005 p3583 p4316 p5065 : Prop)
    (h73424 : p3583 ∨ p2839)
    (h51607 : (¬ p2737) ∨ (¬ p3005) ∨ (¬ p3583) ∨ (¬ p4316) ∨ (¬ p5065))
    : (¬ p3005) ∨ p2839 ∨ (¬ p5065) ∨ (¬ p2737) ∨ (¬ p4316) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5065 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4316 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51607 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94027 (p2230 p2274 p2563 p2685 p3005 p3166 p3172 p3366 p3519 p3572 p4236 p4361 p4376 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h73356 : p3172 ∨ p3166)
    (h53996 : (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3572) ∨ (¬ p4236) ∨ (¬ p4361) ∨ (¬ p4376))
    : p2685 ∨ p3166 ∨ (¬ p2230) ∨ (¬ p3519) ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p2563) ∨ (¬ p4361) ∨ (¬ p4236) ∨ (¬ p2274) ∨ (¬ p3005) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53996 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u7))) (fun r9 => (False.elim (r9 u5)))))))))))))))))))))))

theorem step94029 (p2230 p2563 p2589 p2696 p3005 p3125 p3256 p3744 p4110 p4604 p4729 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73516 : p4110 ∨ p2563)
    (h73284 : p2589 ∨ p2230)
    (h59003 : (¬ p2589) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4604) ∨ (¬ p4729))
    : (¬ p3005) ∨ p3125 ∨ p2563 ∨ (¬ p4729) ∨ p2230 ∨ (¬ p4604) ∨ (¬ p3256) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59003 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step94031 (p2187 p2230 p2563 p2589 p2608 p2737 p3005 p3989 p4110 p4771 p5193 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73502 : p3989 ∨ p2187)
    (h73516 : p4110 ∨ p2563)
    (h48027 : (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3005) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4771) ∨ (¬ p5193))
    : (¬ p3005) ∨ (¬ p2608) ∨ p2230 ∨ (¬ p2737) ∨ p2187 ∨ p2563 ∨ (¬ p5193) ∨ (¬ p4771) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4771 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48027 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step94039 (p2651 p2727 p3005 p3166 p3172 p4111 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73518 : p4111 ∨ p2727)
    (h42681 : (¬ p2651) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p4111))
    : (¬ p3005) ∨ p3166 ∨ (¬ p2651) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42681 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step94042 (p2696 p3005 p3146 p3256 p3692 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h46658 : (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3692))
    : (¬ p3005) ∨ (¬ p3256) ∨ (¬ p2696) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46658 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step94043 (p3005 p3136 p4311 p4315 p5569 p5740 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h54664 : (¬ p3005) ∨ (¬ p4311) ∨ (¬ p4315) ∨ (¬ p5569) ∨ (¬ p5740))
    : (¬ p5569) ∨ (¬ p5740) ∨ p3136 ∨ (¬ p4311) ∨ (¬ p3005) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5569 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54664 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step94044 (p2352 p2363 p2573 p2579 p2696 p3005 p3956 p4009 p4347 p4729 p5122 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73500 : p3956 ∨ p2352)
    (h73274 : p2579 ∨ p2573)
    (h62824 : (¬ p2579) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3956) ∨ (¬ p4009) ∨ (¬ p4347) ∨ (¬ p4729) ∨ (¬ p5122))
    : (¬ p4009) ∨ p2363 ∨ p2352 ∨ (¬ p5122) ∨ p2573 ∨ (¬ p4729) ∨ (¬ p3005) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4009 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62824 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step94046 (p2630 p2810 p3005 p3170 p4009 p5590 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h46747 : (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3170) ∨ (¬ p4009) ∨ (¬ p5590))
    : (¬ p5590) ∨ (¬ p3005) ∨ p2630 ∨ (¬ p4009) ∨ (¬ p3170) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5590 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4009 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46747 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step94047 (p2598 p3005 p3166 p3172 p4236 p4752 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h40956 : (¬ p2598) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p4236) ∨ (¬ p4752))
    : (¬ p4236) ∨ p3166 ∨ (¬ p2598) ∨ (¬ p3005) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3166) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h40956 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94051 (p2363 p2696 p3005 p3256 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h46434 : (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p4347))
    : (¬ p3005) ∨ (¬ p3256) ∨ p2363 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46434 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step94053 (p2331 p2373 p2427 p2797 p3005 p3051 p3556 p3880 p3904 p4117 p4195 p4729 p5063 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73414 : p3556 ∨ p3051)
    (h73490 : p3880 ∨ p2373)
    (h50776 : (¬ p2331) ∨ (¬ p2427) ∨ (¬ p3005) ∨ (¬ p3556) ∨ (¬ p3880) ∨ (¬ p3904) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4729) ∨ (¬ p5063))
    : p2797 ∨ (¬ p3005) ∨ (¬ p5063) ∨ (¬ p3904) ∨ (¬ p4117) ∨ (¬ p2331) ∨ (¬ p2427) ∨ (¬ p4729) ∨ p3051 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u12 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h50776 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step94054 (p2331 p2363 p2797 p3005 p4117 p4195 p4417 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h50367 : (¬ p2331) ∨ (¬ p2363) ∨ (¬ p3005) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4417))
    : p2797 ∨ (¬ p3005) ∨ (¬ p4417) ∨ (¬ p2363) ∨ (¬ p2331) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50367 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step94058 (p2295 p2797 p3005 p3568 p4195 p4405 p4417 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73416 : p3568 ∨ p2295)
    (h41265 : (¬ p3005) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4405) ∨ (¬ p4417))
    : p2797 ∨ (¬ p3005) ∨ (¬ p4417) ∨ p2295 ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41265 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94066 (p2088 p3005 p3180 p3755 p4035 p5107 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h52624 : (¬ p2088) ∨ (¬ p3005) ∨ (¬ p3180) ∨ (¬ p4035) ∨ (¬ p5107))
    : (¬ p5107) ∨ p3755 ∨ (¬ p3180) ∨ (¬ p2088) ∨ (¬ p3005) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5107 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3755) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3180 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52624 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step94072 (p2685 p3005 p3073 p3256 p3572 p4261 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73420 : p3572 ∨ p2685)
    (h55380 : (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3572) ∨ (¬ p4261))
    : (¬ p3005) ∨ p3073 ∨ (¬ p3256) ∨ p2685 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55380 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step94080 (p2187 p2192 p2210 p2248 p2685 p2807 p3005 p3555 p3572 p3989 p4173 p4771 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73420 : p3572 ∨ p2685)
    (h73528 : p4173 ∨ p2192)
    (h73502 : p3989 ∨ p2187)
    (h48972 : (¬ p2248) ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3555) ∨ (¬ p3572) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4771))
    : (¬ p3005) ∨ p2210 ∨ p2685 ∨ p2192 ∨ p2187 ∨ (¬ p2807) ∨ (¬ p2248) ∨ (¬ p4771) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4771 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48972 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step94081 (p2630 p2810 p3005 p3877 p3878 : Prop)
    (h73487 : (¬ p3005) ∨ (¬ p3877))
    (h73316 : p2810 ∨ p2630)
    (h5738 : (¬ p2810) ∨ p3877 ∨ (¬ p3878))
    : (¬ p3005) ∨ (¬ p3878) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3877) := (Or.elim h73487 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h5738 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step94086 (p2651 p2657 p2737 p3166 p3537 p4242 p4963 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h73288 : p2657 ∨ p2651)
    (h46612 : (¬ p2657) ∨ (¬ p2737) ∨ (¬ p3166) ∨ (¬ p4242) ∨ (¬ p4963))
    : (¬ p3166) ∨ p3537 ∨ (¬ p4963) ∨ p2651 ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3537) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46612 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94087 (p2098 p2104 p2696 p2737 p2743 p3256 p4118 p4963 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h73298 : p2743 ∨ p2737)
    (h73520 : p4118 ∨ p3256)
    (h57043 : (¬ p2104) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p4118) ∨ (¬ p4963))
    : p2098 ∨ (¬ p4963) ∨ (¬ p2696) ∨ p2737 ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p4963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57043 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step94089 (p2230 p2427 p2753 p3073 p3609 p4129 p4261 p4419 p4436 p4963 p5560 p5600 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h64648 : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2753) ∨ (¬ p3609) ∨ (¬ p4129) ∨ (¬ p4261) ∨ (¬ p4419) ∨ (¬ p4436) ∨ (¬ p4963) ∨ (¬ p5560) ∨ (¬ p5600))
    : (¬ p5600) ∨ (¬ p4963) ∨ (¬ p2753) ∨ (¬ p2230) ∨ p3073 ∨ (¬ p3609) ∨ (¬ p4419) ∨ (¬ p4436) ∨ (¬ p2427) ∨ (¬ p5560) ∨ (¬ p4129) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5600 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4436 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5560 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h64648 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step94090 (p2331 p2963 p3166 p3367 p3537 p4242 p4963 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73538 : p4242 ∨ p3537)
    (h60138 : (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3367) ∨ (¬ p4242) ∨ (¬ p4963))
    : (¬ p3166) ∨ p2331 ∨ (¬ p3367) ∨ p3537 ∨ (¬ p4963) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60138 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94092 (p2177 p2230 p2373 p3367 p3425 p3527 p3548 p3576 p3759 p4119 p4556 p4734 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h72735 : p4734)
    (h59335 : (¬ p2177) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3367) ∨ (¬ p3425) ∨ (¬ p3548) ∨ (¬ p3576) ∨ (¬ p3759) ∨ (¬ p4119) ∨ (¬ p4556) ∨ (¬ p4734))
    : (¬ p3759) ∨ p3527 ∨ (¬ p4556) ∨ (¬ p3425) ∨ (¬ p2373) ∨ (¬ p3576) ∨ (¬ p3367) ∨ (¬ p2230) ∨ (¬ p2177) ∨ (¬ p4119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3759 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3576 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4734 := h72735;
    (Or.elim h59335 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u11)))))))))))))))))))))))

theorem step94096 (p2156 p2187 p2249 p2459 p2951 p2992 p3073 p3166 p3172 p4133 p4261 p4288 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73544 : p4261 ∨ p3073)
    (h52265 : (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2249) ∨ (¬ p2459) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3172) ∨ (¬ p4133) ∨ (¬ p4261) ∨ (¬ p4288))
    : (¬ p4288) ∨ (¬ p2156) ∨ p3166 ∨ p3073 ∨ (¬ p2992) ∨ (¬ p2951) ∨ (¬ p2459) ∨ (¬ p2187) ∨ (¬ p4133) ∨ (¬ p2249) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4288 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3166) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52265 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step94097 (p2241 p2247 p3146 p3256 p3449 p3692 p4288 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73448 : p3692 ∨ p3146)
    (h50774 : (¬ p2247) ∨ (¬ p3256) ∨ (¬ p3449) ∨ (¬ p3692) ∨ (¬ p4288))
    : (¬ p3256) ∨ (¬ p4288) ∨ p2241 ∨ (¬ p3449) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4288 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50774 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step94098 (p3073 p3256 p4118 p4261 p4288 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73519 : (¬ p3256) ∨ (¬ p4118))
    (h26420 : p4118 ∨ (¬ p4261) ∨ (¬ p4288))
    : p3073 ∨ (¬ p4288) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p4288 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p4118) := (Or.elim h73519 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h26420 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step94104 (p2751 p2951 p2992 p3005 p3051 p3246 p3266 p3440 p3707 p3877 p3950 p4288 p4321 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73488 : p3877 ∨ p3005)
    (h56599 : (¬ p2751) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3266) ∨ (¬ p3440) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4288) ∨ (¬ p4321))
    : p3707 ∨ (¬ p2951) ∨ (¬ p3266) ∨ (¬ p3246) ∨ p3005 ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p2751) ∨ (¬ p4288) ∨ (¬ p3440) ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4288 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56599 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u11)))))))))))))))))))))))

theorem step94116 (p3073 p4261 p5315 p5343 p5344 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h37231 : (¬ p4261) ∨ (¬ p5315) ∨ (¬ p5343) ∨ (¬ p5344))
    : (¬ p5315) ∨ p3073 ∨ (¬ p5343) ∨ (¬ p5344) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5315 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h37231 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step94118 (p3537 p3599 p4242 p4379 p5344 : Prop)
    (h73537 : (¬ p3537) ∨ (¬ p4242))
    (h73572 : p4379 ∨ p3599)
    (h38087 : p4242 ∨ (¬ p4379) ∨ (¬ p5344))
    : (¬ p3537) ∨ p3599 ∨ (¬ p5344) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4242) := (Or.elim h73537 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h38087 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u2)))))))

theorem step94120 (p2850 p3232 p3670 p3684 p3707 p4321 p4354 p4953 p5344 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73442 : p3684 ∨ p2850)
    (h58101 : (¬ p3232) ∨ (¬ p3670) ∨ (¬ p3684) ∨ (¬ p4321) ∨ (¬ p4354) ∨ (¬ p4953) ∨ (¬ p5344))
    : p3707 ∨ (¬ p3670) ∨ (¬ p5344) ∨ (¬ p4354) ∨ p2850 ∨ (¬ p4953) ∨ (¬ p3232) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4354 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58101 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step94122 (p2470 p2528 p2630 p2656 p2717 p2807 p3414 p3659 p4325 p5118 p5558 : Prop)
    (h73392 : p3414 ∨ p2807)
    (h73438 : p3659 ∨ p2717)
    (h72040 : (¬ p5558) ∨ (¬ p2470) ∨ (¬ p2656) ∨ (¬ p3414) ∨ (¬ p5118) ∨ (¬ p2630) ∨ (¬ p4325) ∨ (¬ p3659) ∨ (¬ p2528))
    : (¬ p5558) ∨ p2807 ∨ (¬ p5118) ∨ (¬ p2528) ∨ (¬ p2470) ∨ (¬ p2656) ∨ (¬ p2630) ∨ (¬ p4325) ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2807) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h72040 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step94123 (p2608 p2911 p3073 p3389 p3449 p3519 p3860 p3941 p4261 p4376 p5122 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73482 : p3860 ∨ p3449)
    (h50907 : (¬ p2608) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3860) ∨ (¬ p3941) ∨ (¬ p4261) ∨ (¬ p4376) ∨ (¬ p5122))
    : (¬ p3941) ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p3389) ∨ p3073 ∨ p3449 ∨ (¬ p5122) ∨ (¬ p3519) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3941 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50907 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step94125 (p2383 p3125 p3743 p3744 p3979 p4171 p5122 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h41486 : (¬ p2383) ∨ (¬ p3743) ∨ (¬ p3744) ∨ (¬ p3979) ∨ (¬ p4171) ∨ (¬ p5122))
    : (¬ p3979) ∨ (¬ p5122) ∨ p3125 ∨ (¬ p2383) ∨ (¬ p3743) ∨ (¬ p4171) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3979 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41486 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step94126 (p2284 p2761 p2946 p2952 p3361 p3425 p3619 p3952 p4393 p4778 p5233 p5254 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73496 : p3952 ∨ p2284)
    (h41546 : (¬ p2761) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3425) ∨ (¬ p3619) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p4778) ∨ (¬ p5233) ∨ (¬ p5254))
    : (¬ p3619) ∨ (¬ p4393) ∨ (¬ p3425) ∨ (¬ p3361) ∨ p2946 ∨ p2284 ∨ (¬ p4778) ∨ (¬ p5233) ∨ (¬ p5254) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41546 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step94130 (p2598 p3055 p3619 p5158 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h20539 : (¬ p3055) ∨ (¬ p3619) ∨ (¬ p5158))
    : (¬ p3619) ∨ (¬ p5158) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20539 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step94153 (p2598 p2737 p2743 p2774 p3055 p3367 p4845 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73350 : p3055 ∨ p2598)
    (h51949 : (¬ p2743) ∨ (¬ p2774) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p4845))
    : (¬ p2774) ∨ (¬ p3367) ∨ p2737 ∨ p2598 ∨ (¬ p4845) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2774 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51949 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step94154 (p2774 p2946 p2952 p3136 p4236 p4845 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h62054 : (¬ p2774) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4236) ∨ (¬ p4845))
    : (¬ p4236) ∨ p2946 ∨ (¬ p4845) ∨ (¬ p2774) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4236 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62054 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94157 (p2383 p2737 p2743 p2819 p4358 p4845 p4869 p5016 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73564 : p4358 ∨ p2819)
    (h61854 : (¬ p2383) ∨ (¬ p2743) ∨ (¬ p4358) ∨ (¬ p4845) ∨ (¬ p4869) ∨ (¬ p5016))
    : (¬ p4869) ∨ (¬ p2383) ∨ p2737 ∨ (¬ p5016) ∨ p2819 ∨ (¬ p4845) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4869 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h61854 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step94158 (p2098 p2307 p2313 p2417 p2696 p2761 p3204 p3365 p4019 p4024 p4278 p4381 p4710 p4845 p5119 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73546 : p4278 ∨ p2417)
    (h73574 : p4381 ∨ p2761)
    (h73390 : p3365 ∨ p2696)
    (h56987 : (¬ p2098) ∨ (¬ p2313) ∨ (¬ p3204) ∨ (¬ p3365) ∨ (¬ p4019) ∨ (¬ p4024) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p4710) ∨ (¬ p4845) ∨ (¬ p5119))
    : (¬ p4019) ∨ (¬ p2098) ∨ (¬ p4845) ∨ p2307 ∨ (¬ p5119) ∨ (¬ p4024) ∨ p2417 ∨ (¬ p3204) ∨ (¬ p4710) ∨ p2761 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4019 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u14 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h56987 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u14))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u4)))))))))))))))))))))))

theorem step94164 (p2946 p2952 p3166 p3172 p3661 : Prop)
    (h73355 : (¬ p3166) ∨ (¬ p3172))
    (h73330 : p2952 ∨ p2946)
    (h6463 : (¬ p2952) ∨ p3172 ∨ (¬ p3661))
    : (¬ p3166) ∨ (¬ p3661) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3172) := (Or.elim h73355 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6463 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step94171 (p2284 p2685 p3136 p3572 p3699 p4555 : Prop)
    (h73420 : p3572 ∨ p2685)
    (h52314 : (¬ p2284) ∨ (¬ p3136) ∨ (¬ p3572) ∨ (¬ p3699) ∨ (¬ p4555))
    : (¬ p2284) ∨ (¬ p3136) ∨ (¬ p4555) ∨ p2685 ∨ (¬ p3699) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52314 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step94177 (p2088 p3073 p3379 p3452 p4261 p4376 p4436 p5242 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73394 : p3452 ∨ p3379)
    (h59733 : (¬ p2088) ∨ (¬ p3452) ∨ (¬ p4261) ∨ (¬ p4376) ∨ (¬ p4436) ∨ (¬ p5242))
    : p3073 ∨ p3379 ∨ (¬ p4376) ∨ (¬ p2088) ∨ (¬ p4436) ∨ (¬ p5242) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4436 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h59733 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step94191 (p2177 p2299 p3093 p3309 p3549 p3591 p4588 p5242 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73406 : p3549 ∨ p3309)
    (h73234 : p2299 ∨ p2177)
    (h61467 : (¬ p2299) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4588) ∨ (¬ p5242))
    : (¬ p5242) ∨ p3093 ∨ p3309 ∨ (¬ p4588) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5242 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h61467 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step94192 (p2241 p2247 p2744 p3998 p4436 p5242 p5693 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h52552 : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3998) ∨ (¬ p4436) ∨ (¬ p5242) ∨ (¬ p5693))
    : (¬ p5693) ∨ (¬ p3998) ∨ p2241 ∨ (¬ p4436) ∨ (¬ p5242) ∨ (¬ p2744) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4436 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52552 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step94194 (p3379 p3452 p3998 p4376 p4492 p4874 p5242 p5693 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h54008 : (¬ p3452) ∨ (¬ p3998) ∨ (¬ p4376) ∨ (¬ p4492) ∨ (¬ p4874) ∨ (¬ p5242) ∨ (¬ p5693))
    : (¬ p5693) ∨ (¬ p3998) ∨ (¬ p5242) ∨ p3379 ∨ (¬ p4376) ∨ (¬ p4492) ∨ (¬ p4874) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54008 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u0)))))))))))))))

theorem step94201 (p2241 p2247 p2744 p3073 p3366 p3449 p3670 p3680 p4232 p5059 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73226 : p2247 ∨ p2241)
    (h58267 : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3680) ∨ (¬ p4232) ∨ (¬ p5059) ∨ (¬ p5387))
    : (¬ p4232) ∨ p3670 ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p2744) ∨ p2241 ∨ (¬ p3073) ∨ (¬ p5059) ∨ (¬ p3680) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4232 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h58267 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step94204 (p3266 p3366 p3367 p3670 p4232 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h45691 : (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3367) ∨ (¬ p4232) ∨ (¬ p5387))
    : p3670 ∨ (¬ p4232) ∨ (¬ p3266) ∨ (¬ p3367) ∨ (¬ p3366) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p4232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45691 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94209 (p2246 p2264 p2459 p2744 p2807 p3379 p3449 p3860 p4257 p5118 p5693 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h52877 : (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4257) ∨ (¬ p5118) ∨ (¬ p5693))
    : (¬ p5693) ∨ p3449 ∨ (¬ p2807) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p2459) ∨ (¬ p5118) ∨ (¬ p4257) ∨ (¬ p2264) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52877 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step94210 (p2246 p2264 p2459 p2608 p2663 p2744 p3389 p3740 p3830 p3834 p4351 p5118 p5693 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h53438 : (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3389) ∨ (¬ p3740) ∨ (¬ p3834) ∨ (¬ p4351) ∨ (¬ p5118) ∨ (¬ p5693))
    : (¬ p5693) ∨ p3830 ∨ (¬ p2246) ∨ (¬ p5118) ∨ (¬ p2663) ∨ (¬ p3389) ∨ (¬ p4351) ∨ (¬ p2744) ∨ (¬ p2459) ∨ (¬ p2264) ∨ (¬ p2608) ∨ (¬ p3740) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4351 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))));
    let u12 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h53438 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u3))) (fun r10 => (False.elim (r10 u0)))))))))))))))))))))))))

theorem step94211 (p3379 p3449 p3860 p4149 p5693 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h61472 : (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4149) ∨ (¬ p5693))
    : (¬ p5693) ∨ (¬ p4149) ∨ p3449 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h61472 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step94212 (p2230 p2241 p2750 p2753 p3105 p3362 p3449 p3680 p3698 p3860 p5123 p5693 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h64651 : (¬ p2230) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3105) ∨ (¬ p3362) ∨ (¬ p3680) ∨ (¬ p3698) ∨ (¬ p3860) ∨ (¬ p5123) ∨ (¬ p5693))
    : (¬ p5693) ∨ (¬ p2753) ∨ (¬ p2750) ∨ p3449 ∨ (¬ p3680) ∨ (¬ p5123) ∨ (¬ p3105) ∨ (¬ p2241) ∨ (¬ p3698) ∨ (¬ p3362) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64651 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u5))) (fun r9 => (False.elim (r9 u0)))))))))))))))))))))))

theorem step94216 (p2528 p2534 p3449 p3860 p4149 p5693 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73268 : p2534 ∨ p2528)
    (h47832 : (¬ p2534) ∨ (¬ p3860) ∨ (¬ p4149) ∨ (¬ p5693))
    : (¬ p5693) ∨ (¬ p4149) ∨ p3449 ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47832 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step94218 (p2331 p2753 p3323 p3379 p3449 p3461 p3860 p4117 p5123 p5693 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h72045 : (¬ p5693) ∨ (¬ p3461) ∨ (¬ p4117) ∨ (¬ p5123) ∨ (¬ p3379) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p2753) ∨ (¬ p3860))
    : (¬ p5693) ∨ (¬ p5123) ∨ (¬ p2753) ∨ (¬ p3461) ∨ (¬ p4117) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3379) ∨ p3449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h72045 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step94220 (p2459 p2504 p2553 p3941 p4348 p4371 p5693 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h56927 : (¬ p2504) ∨ (¬ p2553) ∨ (¬ p3941) ∨ (¬ p4348) ∨ (¬ p4371) ∨ (¬ p5693))
    : (¬ p5693) ∨ (¬ p2553) ∨ (¬ p4371) ∨ p2459 ∨ (¬ p3941) ∨ (¬ p2504) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56927 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step94221 (p2210 p3449 p3860 p3969 p4132 p5693 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h45151 : (¬ p2210) ∨ (¬ p3860) ∨ (¬ p3969) ∨ (¬ p4132) ∨ (¬ p5693))
    : (¬ p5693) ∨ p3449 ∨ (¬ p2210) ∨ (¬ p4132) ∨ (¬ p3969) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45151 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step94222 (p2246 p2608 p2744 p2946 p3115 p3449 p3680 p3860 p5123 p5693 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h63998 : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p3860) ∨ (¬ p5123) ∨ (¬ p5693))
    : (¬ p5693) ∨ (¬ p2246) ∨ (¬ p3115) ∨ (¬ p2946) ∨ p3449 ∨ (¬ p5123) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3680) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63998 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step94223 (p2482 p3449 p3860 p3998 p5190 p5693 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h42449 : (¬ p2482) ∨ (¬ p3860) ∨ (¬ p3998) ∨ (¬ p5190) ∨ (¬ p5693))
    : (¬ p5693) ∨ (¬ p3998) ∨ p3449 ∨ (¬ p5190) ∨ (¬ p2482) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3449) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2482 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42449 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step94224 (p2241 p2598 p2750 p2753 p3276 p3333 p3449 p3860 p5123 p5693 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h64708 : (¬ p2241) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3860) ∨ (¬ p5123) ∨ (¬ p5693))
    : p3449 ∨ (¬ p5693) ∨ (¬ p3333) ∨ (¬ p2750) ∨ (¬ p2598) ∨ (¬ p5123) ∨ (¬ p3276) ∨ (¬ p2241) ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h64708 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step94227 (p2608 p3954 p3998 p5242 p5317 p5693 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h41583 : (¬ p3954) ∨ (¬ p3998) ∨ (¬ p5242) ∨ (¬ p5317) ∨ (¬ p5693))
    : (¬ p5693) ∨ (¬ p3998) ∨ (¬ p5242) ∨ (¬ p5317) ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5693 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5317 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41583 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step94229 (p3461 p3670 p4191 p5265 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h21366 : (¬ p3670) ∨ (¬ p4191) ∨ (¬ p5265))
    : (¬ p3670) ∨ p3461 ∨ (¬ p5265) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5265 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h21366 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step94238 (p3425 p3670 p3767 p4439 p4736 p5228 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h49523 : (¬ p3425) ∨ (¬ p3767) ∨ (¬ p4439) ∨ (¬ p4736) ∨ (¬ p5228) ∨ (¬ p5387))
    : p3670 ∨ (¬ p5228) ∨ (¬ p4736) ∨ (¬ p3425) ∨ (¬ p3767) ∨ (¬ p4439) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p5228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4439 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49523 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step94241 (p2528 p2651 p2761 p2778 p3083 p3654 p3670 p3946 p4669 p4786 p5269 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73492 : p3946 ∨ p3654)
    (h42365 : (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2761) ∨ (¬ p2778) ∨ (¬ p3083) ∨ (¬ p3946) ∨ (¬ p4669) ∨ (¬ p4786) ∨ (¬ p5269) ∨ (¬ p5387))
    : p3670 ∨ (¬ p5269) ∨ (¬ p4669) ∨ (¬ p4786) ∨ (¬ p2761) ∨ (¬ p2528) ∨ (¬ p3083) ∨ p3654 ∨ (¬ p2651) ∨ (¬ p2778) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p5269 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3654) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h42365 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u10)))))))))))))))))))))

theorem step94242 (p2396 p2761 p3670 p4473 p5228 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h48332 : (¬ p2396) ∨ (¬ p2761) ∨ (¬ p4473) ∨ (¬ p5228) ∨ (¬ p5387))
    : p3670 ∨ (¬ p4473) ∨ (¬ p5228) ∨ (¬ p2761) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48332 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step94243 (p2246 p2417 p2437 p2651 p2744 p3266 p3599 p3670 p3950 p4379 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73572 : p4379 ∨ p3599)
    (h52708 : (¬ p2246) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3266) ∨ (¬ p3950) ∨ (¬ p4379) ∨ (¬ p5387))
    : p3670 ∨ (¬ p3266) ∨ (¬ p2744) ∨ (¬ p2651) ∨ (¬ p2437) ∨ p3599 ∨ (¬ p3950) ∨ (¬ p2246) ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h52708 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

end ElevenRUP
