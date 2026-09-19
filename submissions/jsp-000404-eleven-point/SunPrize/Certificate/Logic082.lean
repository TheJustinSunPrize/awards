import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step132038 (p2098 p2132 p2137 p2156 p2166 p2177 p2187 p2220 p2274 p2284 p2331 p2341 p2352 p2363 p2406 p2459 p2493 p2553 p2563 p2608 p2619 p2630 p2641 p2651 p2696 p2707 p2727 p2737 p2748 p2749 p2797 p2829 p2839 p2850 p2870 p2881 p2901 p2911 p2946 p3125 p3146 p3156 p3201 p3323 p3367 p3371 p3379 p3422 p3425 p3541 p3577 p3581 p3747 p3873 p4169 p4281 p5083 : Prop)
    (h132015 : p3873)
    (h132006 : (¬ p2608))
    (h131645 : p2737)
    (h132018 : (¬ p3379))
    (h130735 : p2563)
    (h131647 : p2749)
    (h131182 : (¬ p2274))
    (h131646 : p2748)
    (h131998 : (¬ p2696))
    (h131921 : p2459)
    (h102249 : p3581 ∨ p2553)
    (h132026 : (¬ p2132) ∨ (¬ p2363) ∨ (¬ p2651) ∨ (¬ p3581))
    (h125321 : (¬ p2651) ∨ p2727 ∨ p2608)
    (h104526 : p2839 ∨ (¬ p2737) ∨ (¬ p2727))
    (h132027 : p3146 ∨ (¬ p2363) ∨ (¬ p2651) ∨ p2553)
    (h116567 : (¬ p2839) ∨ (¬ p2098) ∨ (¬ p3146) ∨ p2132)
    (h120332 : p2630 ∨ (¬ p3873) ∨ (¬ p2651) ∨ p2696)
    (h113198 : (¬ p2630) ∨ (¬ p2737) ∨ p3367)
    (h129728 : (¬ p2850) ∨ (¬ p3367))
    (h95899 : p4281 ∨ (¬ p2727))
    (h31669 : (¬ p2749) ∨ p3541 ∨ (¬ p4281))
    (h130369 : (¬ p2406) ∨ p2850 ∨ (¬ p3541) ∨ p2132)
    (h102427 : p2137 ∨ p2132)
    (h96372 : p3371 ∨ (¬ p2839))
    (h107095 : p2829 ∨ (¬ p2737) ∨ (¬ p2630))
    (h132033 : (¬ p2619) ∨ p2352 ∨ (¬ p2177) ∨ (¬ p2363) ∨ (¬ p2651) ∨ p2553)
    (h91585 : (¬ p3371) ∨ p2132 ∨ (¬ p2166) ∨ p2619)
    (h23469 : (¬ p2137) ∨ (¬ p2220) ∨ p2619)
    (h103244 : p2166 ∨ (¬ p2563) ∨ p2406 ∨ (¬ p2493))
    (h78229 : (¬ p3156) ∨ p2220 ∨ (¬ p2651))
    (h77708 : p2850 ∨ p3379 ∨ p2493 ∨ (¬ p3422))
    (h99313 : p2911 ∨ p2493 ∨ (¬ p3581) ∨ p3379 ∨ (¬ p2177))
    (h99321 : p2493 ∨ (¬ p2187) ∨ p3379 ∨ p2352)
    (h77109 : (¬ p3201) ∨ p3422 ∨ (¬ p3581))
    (h101920 : p5083 ∨ p3201)
    (h116469 : p2098 ∨ (¬ p5083) ∨ (¬ p2911) ∨ p3425)
    (h96166 : p3577 ∨ (¬ p3425))
    (h132037 : p2881 ∨ p2166 ∨ (¬ p2177))
    (h96359 : p3747 ∨ (¬ p2881))
    (h132036 : (¬ p2881) ∨ (¬ p2331) ∨ p2619 ∨ (¬ p2363) ∨ (¬ p2651) ∨ p2553)
    (h6913 : p2619 ∨ (¬ p2870) ∨ (¬ p3747))
    (h26059 : (¬ p2901) ∨ p3156 ∨ (¬ p3747))
    (h125336 : (¬ p2946) ∨ p2331 ∨ (¬ p2563))
    (h130846 : (¬ p2797) ∨ p2331 ∨ (¬ p2630) ∨ (¬ p2829))
    (h119362 : (¬ p2651) ∨ p2284 ∨ p2187 ∨ (¬ p2563) ∨ p2331)
    (h96362 : p4169 ∨ p2870)
    (h102867 : p2946 ∨ p2156 ∨ (¬ p2563) ∨ (¬ p2651))
    (h82804 : (¬ p2641) ∨ p2797 ∨ (¬ p2749) ∨ p2696)
    (h115431 : p2274 ∨ (¬ p3125) ∨ (¬ p2284) ∨ p2901)
    (h125551 : p2220 ∨ p2341 ∨ (¬ p2881) ∨ (¬ p2156))
    (h120670 : (¬ p2839) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p4169) ∨ p2707)
    (h124846 : (¬ p3577) ∨ p2641 ∨ p3323 ∨ (¬ p2707) ∨ (¬ p2748) ∨ (¬ p2341) ∨ (¬ p2459) ∨ p2696)
    (h79125 : (¬ p3323) ∨ p3125 ∨ p3156)
    : p2352 ∨ (¬ p2177) ∨ (¬ p2363) ∨ (¬ p2651) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2352) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3873 := h132015;
    let u6 : (¬ p2608) := h132006;
    let u7 : p2737 := h131645;
    let u8 : (¬ p3379) := h132018;
    let u9 : p2563 := h130735;
    let u10 : p2749 := h131647;
    let u11 : (¬ p2274) := h131182;
    let u12 : p2748 := h131646;
    let u13 : (¬ p2696) := h131998;
    let u14 : p2459 := h131921;
    let u15 : p3581 := (Or.elim h102249 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u16 : (¬ p2132) := (Or.elim h132026 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u15))))))));
    let u17 : p2727 := (Or.elim h125321 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u6 r1))))));
    let u18 : p2839 := (Or.elim h104526 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (False.elim (r1 u17))))));
    let u19 : p3146 := (Or.elim h132027 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u4 r2))))))));
    let u20 : (¬ p2098) := (Or.elim h116567 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u19))) (fun r2 => (False.elim (u16 r2))))))));
    let u21 : p2630 := (Or.elim h120332 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (u13 r2))))))));
    let u22 : p3367 := (Or.elim h113198 (fun q0 => (False.elim (q0 u21))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => r1))));
    let u23 : (¬ p2850) := (Or.elim h129728 (fun q0 => q0) (fun r0 => (False.elim (r0 u22))));
    let u24 : p4281 := (Or.elim h95899 (fun q0 => q0) (fun r0 => (False.elim (r0 u17))));
    let u25 : p3541 := (Or.elim h31669 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u24))))));
    let u26 : (¬ p2406) := (Or.elim h130369 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u23 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u25))) (fun r2 => (False.elim (u16 r2))))))));
    let u27 : p2137 := (Or.elim h102427 (fun q0 => q0) (fun r0 => (False.elim (u16 r0))));
    let u28 : p3371 := (Or.elim h96372 (fun q0 => q0) (fun r0 => (False.elim (r0 u18))));
    let u29 : p2829 := (Or.elim h107095 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (False.elim (r1 u21))))));
    let u30 : (¬ p2619) := (Or.elim h132033 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u4 r4))))))))))));
    let u31 : (¬ p2166) := (Or.elim h91585 (fun q0 => (False.elim (q0 u28))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u16 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u30 r2))))))));
    let u32 : (¬ p2220) := (Or.elim h23469 (fun q0 => (False.elim (q0 u27))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u30 r1))))));
    let u33 : (¬ p2493) := (Or.elim h103244 (fun q0 => (False.elim (u31 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u26 q2))) (fun r2 => r2))))));
    let u34 : (¬ p3156) := (Or.elim h78229 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u32 q1))) (fun r1 => (False.elim (r1 u3))))));
    let u35 : (¬ p3422) := (Or.elim h77708 (fun q0 => (False.elim (u23 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u33 q2))) (fun r2 => r2))))));
    let u36 : p2911 := (Or.elim h99313 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u33 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (False.elim (r3 u1))))))))));
    let u37 : (¬ p2187) := (Or.elim h99321 (fun q0 => (False.elim (u33 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (False.elim (u0 r2))))))));
    let u38 : (¬ p3201) := (Or.elim h77109 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u35 q1))) (fun r1 => (False.elim (r1 u15))))));
    let u39 : p5083 := (Or.elim h101920 (fun q0 => q0) (fun r0 => (False.elim (u38 r0))));
    let u40 : p3425 := (Or.elim h116469 (fun q0 => (False.elim (u20 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u39))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u36))) (fun r2 => r2))))));
    let u41 : p3577 := (Or.elim h96166 (fun q0 => q0) (fun r0 => (False.elim (r0 u40))));
    let u42 : p2881 := (Or.elim h132037 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u31 q1))) (fun r1 => (False.elim (r1 u1))))));
    let u43 : p3747 := (Or.elim h96359 (fun q0 => q0) (fun r0 => (False.elim (r0 u42))));
    let u44 : (¬ p2331) := (Or.elim h132036 (fun q0 => (False.elim (q0 u42))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u30 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (u4 r4))))))))))));
    let u45 : (¬ p2870) := (Or.elim h6913 (fun q0 => (False.elim (u30 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u43))))));
    let u46 : (¬ p2901) := (Or.elim h26059 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u34 q1))) (fun r1 => (False.elim (r1 u43))))));
    let u47 : (¬ p2946) := (Or.elim h125336 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u44 q1))) (fun r1 => (False.elim (r1 u9))))));
    let u48 : (¬ p2797) := (Or.elim h130846 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u44 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u21))) (fun r2 => (False.elim (r2 u29))))))));
    let u49 : p2284 := (Or.elim h119362 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u37 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (False.elim (u44 r3))))))))));
    let u50 : p4169 := (Or.elim h96362 (fun q0 => q0) (fun r0 => (False.elim (u45 r0))));
    let u51 : p2156 := (Or.elim h102867 (fun q0 => (False.elim (u47 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (False.elim (r2 u3))))))));
    let u52 : (¬ p2641) := (Or.elim h82804 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u48 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (False.elim (u13 r2))))))));
    let u53 : (¬ p3125) := (Or.elim h115431 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u49))) (fun r2 => (False.elim (u46 r2))))))));
    let u54 : p2341 := (Or.elim h125551 (fun q0 => (False.elim (u32 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u42))) (fun r2 => (False.elim (r2 u51))))))));
    let u55 : p2707 := (Or.elim h120670 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u27))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u51))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u50))) (fun r3 => r3))))))));
    let u56 : p3323 := (Or.elim h124846 (fun q0 => (False.elim (q0 u41))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u52 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u55))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u54))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u14))) (fun r6 => (False.elim (u13 r6))))))))))))))));
    (Or.elim h79125 (fun q0 => (False.elim (q0 u56))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u53 q1))) (fun r1 => (False.elim (u34 r1)))))))

theorem step132039 (p2132 p2137 p2156 p2187 p2246 p2331 p2352 p2363 p2437 p2553 p2563 p2608 p2619 p2630 p2651 p2696 p2727 p2737 p2811 p2839 p2881 p2946 p3016 p3146 p3581 p3873 : Prop)
    (h131998 : (¬ p2696))
    (h132015 : p3873)
    (h132006 : (¬ p2608))
    (h131999 : p2811)
    (h131645 : p2737)
    (h132005 : p2246)
    (h130735 : p2563)
    (h132027 : p3146 ∨ (¬ p2363) ∨ (¬ p2651) ∨ p2553)
    (h102249 : p3581 ∨ p2553)
    (h132026 : (¬ p2132) ∨ (¬ p2363) ∨ (¬ p2651) ∨ (¬ p3581))
    (h102427 : p2137 ∨ p2132)
    (h125321 : (¬ p2651) ∨ p2727 ∨ p2608)
    (h104526 : p2839 ∨ (¬ p2737) ∨ (¬ p2727))
    (h120332 : p2630 ∨ (¬ p3873) ∨ (¬ p2651) ∨ p2696)
    (h131735 : (¬ p2352) ∨ p2881 ∨ p2553)
    (h43763 : (¬ p2352) ∨ (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3016))
    (h103131 : p3016 ∨ (¬ p3581) ∨ (¬ p2437))
    (h132028 : (¬ p2881) ∨ p2437 ∨ (¬ p2619) ∨ (¬ p3146) ∨ p2132 ∨ (¬ p2363) ∨ (¬ p2651))
    (h131812 : p2187 ∨ p2619 ∨ (¬ p2352) ∨ (¬ p2246) ∨ (¬ p2630) ∨ p2553)
    (h132036 : (¬ p2881) ∨ (¬ p2331) ∨ p2619 ∨ (¬ p2363) ∨ (¬ p2651) ∨ p2553)
    (h46020 : (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2839))
    (h125336 : (¬ p2946) ∨ p2331 ∨ (¬ p2563))
    (h102867 : p2946 ∨ p2156 ∨ (¬ p2563) ∨ (¬ p2651))
    : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2651) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2696) := h131998;
    let u5 : p3873 := h132015;
    let u6 : (¬ p2608) := h132006;
    let u7 : p2811 := h131999;
    let u8 : p2737 := h131645;
    let u9 : p2246 := h132005;
    let u10 : p2563 := h130735;
    let u11 : p3146 := (Or.elim h132027 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u3 r2))))))));
    let u12 : p3581 := (Or.elim h102249 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u13 : (¬ p2132) := (Or.elim h132026 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u12))))))));
    let u14 : p2137 := (Or.elim h102427 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u15 : p2727 := (Or.elim h125321 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u6 r1))))));
    let u16 : p2839 := (Or.elim h104526 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (False.elim (r1 u15))))));
    let u17 : p2630 := (Or.elim h120332 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (u4 r2))))))));
    let u18 : p2881 := (Or.elim h131735 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u3 r1))))));
    let u19 : (¬ p3016) := (Or.elim h43763 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => r3))))))));
    let u20 : (¬ p2437) := (Or.elim h103131 (fun q0 => (False.elim (u19 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => r1))));
    let u21 : (¬ p2619) := (Or.elim h132028 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u20 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u13 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u2))))))))))))));
    let u22 : p2187 := (Or.elim h131812 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u21 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u17))) (fun r4 => (False.elim (u3 r4))))))))))));
    let u23 : (¬ p2331) := (Or.elim h132036 (fun q0 => (False.elim (q0 u18))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u21 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (u3 r4))))))))))));
    let u24 : (¬ p2156) := (Or.elim h46020 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u22))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u16))))))))));
    let u25 : (¬ p2946) := (Or.elim h125336 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u23 q1))) (fun r1 => (False.elim (r1 u10))))));
    (Or.elim h102867 (fun q0 => (False.elim (u25 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u24 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step132040 (p2132 p2136 p2166 p2177 p2220 p2274 p2284 p2352 p2363 p2373 p2406 p2493 p2553 p2563 p2608 p2619 p2630 p2651 p2696 p2727 p2737 p2749 p2811 p2839 p2850 p2946 p2958 p2992 p3016 p3136 p3146 p3156 p3309 p3367 p3371 p3379 p3541 p3581 p3660 p3873 p4203 p4236 p4281 p5191 : Prop)
    (h131647 : p2749)
    (h132006 : (¬ p2608))
    (h132015 : p3873)
    (h132021 : p5191)
    (h131182 : (¬ p2274))
    (h130737 : p3660)
    (h130736 : p4203)
    (h132018 : (¬ p3379))
    (h130735 : p2563)
    (h131998 : (¬ p2696))
    (h132000 : p4236)
    (h131645 : p2737)
    (h131999 : p2811)
    (h120332 : p2630 ∨ (¬ p3873) ∨ (¬ p2651) ∨ p2696)
    (h113198 : (¬ p2630) ∨ (¬ p2737) ∨ p3367)
    (h129728 : (¬ p2850) ∨ (¬ p3367))
    (h125321 : (¬ p2651) ∨ p2727 ∨ p2608)
    (h104526 : p2839 ∨ (¬ p2737) ∨ (¬ p2727))
    (h96372 : p3371 ∨ (¬ p2839))
    (h95899 : p4281 ∨ (¬ p2727))
    (h31669 : (¬ p2749) ∨ p3541 ∨ (¬ p4281))
    (h102249 : p3581 ∨ p2553)
    (h132026 : (¬ p2132) ∨ (¬ p2363) ∨ (¬ p2651) ∨ (¬ p3581))
    (h102521 : p2136 ∨ p2132)
    (h130369 : (¬ p2406) ∨ p2850 ∨ (¬ p3541) ∨ p2132)
    (h129216 : (¬ p3309) ∨ p2553 ∨ (¬ p5191) ∨ p2406)
    (h132027 : p3146 ∨ (¬ p2363) ∨ (¬ p2651) ∨ p2553)
    (h132039 : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2651) ∨ p2553)
    (h132038 : p2352 ∨ (¬ p2177) ∨ (¬ p2363) ∨ (¬ p2651) ∨ p2553)
    (h125595 : p3379 ∨ (¬ p3660) ∨ p2284 ∨ (¬ p4203) ∨ p2406 ∨ p2274 ∨ p2177)
    (h103294 : p2373 ∨ p3379 ∨ p2177 ∨ p3309 ∨ p2406 ∨ (¬ p2563))
    (h79801 : p2493 ∨ p3379 ∨ p2177 ∨ p2553)
    (h132032 : (¬ p3016) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p2651))
    (h103244 : p2166 ∨ (¬ p2563) ∨ p2406 ∨ (¬ p2493))
    (h85729 : p2992 ∨ p3016 ∨ (¬ p4281) ∨ (¬ p2493))
    (h91585 : (¬ p3371) ∨ p2132 ∨ (¬ p2166) ∨ p2619)
    (h103692 : p3136 ∨ (¬ p2992) ∨ p2696)
    (h83726 : (¬ p2619) ∨ (¬ p2839) ∨ p2220 ∨ (¬ p2136))
    (h58637 : (¬ p2737) ∨ (¬ p3136) ∨ (¬ p3146) ∨ (¬ p3156))
    (h84333 : (¬ p4236) ∨ p2946 ∨ (¬ p2737) ∨ (¬ p3136))
    (h79109 : p3156 ∨ (¬ p2220) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2958) ∨ (¬ p2284))
    (h96895 : p2958 ∨ (¬ p2946))
    : (¬ p2363) ∨ (¬ p2651) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2749 := h131647;
    let u4 : (¬ p2608) := h132006;
    let u5 : p3873 := h132015;
    let u6 : p5191 := h132021;
    let u7 : (¬ p2274) := h131182;
    let u8 : p3660 := h130737;
    let u9 : p4203 := h130736;
    let u10 : (¬ p3379) := h132018;
    let u11 : p2563 := h130735;
    let u12 : (¬ p2696) := h131998;
    let u13 : p4236 := h132000;
    let u14 : p2737 := h131645;
    let u15 : p2811 := h131999;
    let u16 : p2630 := (Or.elim h120332 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u12 r2))))))));
    let u17 : p3367 := (Or.elim h113198 (fun q0 => (False.elim (q0 u16))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => r1))));
    let u18 : (¬ p2850) := (Or.elim h129728 (fun q0 => q0) (fun r0 => (False.elim (r0 u17))));
    let u19 : p2727 := (Or.elim h125321 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u4 r1))))));
    let u20 : p2839 := (Or.elim h104526 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (False.elim (r1 u19))))));
    let u21 : p3371 := (Or.elim h96372 (fun q0 => q0) (fun r0 => (False.elim (r0 u20))));
    let u22 : p4281 := (Or.elim h95899 (fun q0 => q0) (fun r0 => (False.elim (r0 u19))));
    let u23 : p3541 := (Or.elim h31669 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u22))))));
    let u24 : p3581 := (Or.elim h102249 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u25 : (¬ p2132) := (Or.elim h132026 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u24))))))));
    let u26 : p2136 := (Or.elim h102521 (fun q0 => q0) (fun r0 => (False.elim (u25 r0))));
    let u27 : (¬ p2406) := (Or.elim h130369 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u18 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u23))) (fun r2 => (False.elim (u25 r2))))))));
    let u28 : (¬ p3309) := (Or.elim h129216 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (u27 r2))))))));
    let u29 : p3146 := (Or.elim h132027 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    let u30 : (¬ p2352) := (Or.elim h132039 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u2 r2))))))));
    let u31 : (¬ p2177) := (Or.elim h132038 (fun q0 => (False.elim (u30 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3))))))))));
    let u32 : p2284 := (Or.elim h125595 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u27 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (False.elim (u31 r5))))))))))))));
    let u33 : p2373 := (Or.elim h103294 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u31 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u28 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u27 q4))) (fun r4 => (False.elim (r4 u11))))))))))));
    let u34 : p2493 := (Or.elim h79801 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u31 q2))) (fun r2 => (False.elim (u2 r2))))))));
    let u35 : (¬ p3016) := (Or.elim h132032 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u33))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u29))) (fun r2 => (False.elim (r2 u1))))))));
    let u36 : p2166 := (Or.elim h103244 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u27 q2))) (fun r2 => (False.elim (r2 u34))))))));
    let u37 : p2992 := (Or.elim h85729 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u35 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u22))) (fun r2 => (False.elim (r2 u34))))))));
    let u38 : p2619 := (Or.elim h91585 (fun q0 => (False.elim (q0 u21))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u25 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u36))) (fun r2 => r2))))));
    let u39 : p3136 := (Or.elim h103692 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u37))) (fun r1 => (False.elim (u12 r1))))));
    let u40 : p2220 := (Or.elim h83726 (fun q0 => (False.elim (q0 u38))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u20))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u26))))))));
    let u41 : (¬ p3156) := (Or.elim h58637 (fun q0 => (False.elim (q0 u14))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u39))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u29))) (fun r2 => r2))))));
    let u42 : p2946 := (Or.elim h84333 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (False.elim (r2 u39))))))));
    let u43 : (¬ p2958) := (Or.elim h79109 (fun q0 => (False.elim (u41 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u40))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u14))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u15))) (fun r3 => (Or.elim r3 (fun q4 => q4) (fun r4 => (False.elim (r4 u32))))))))))));
    (Or.elim h96895 (fun q0 => (False.elim (u43 q0))) (fun r0 => (False.elim (r0 u42)))))

theorem step132041 (p2177 p2352 p2363 p2406 p2459 p2493 p2505 p2553 p2598 p2608 p2630 p2651 p2696 p2727 p2737 p2749 p2829 p2850 p2881 p3063 p3093 p3367 p3379 p3422 p3541 p3550 p3873 p3923 p4281 p4870 p4992 : Prop)
    (h132006 : (¬ p2608))
    (h131647 : p2749)
    (h132015 : p3873)
    (h131921 : p2459)
    (h132018 : (¬ p3379))
    (h131998 : (¬ p2696))
    (h131645 : p2737)
    (h125321 : (¬ p2651) ∨ p2727 ∨ p2608)
    (h120332 : p2630 ∨ (¬ p3873) ∨ (¬ p2651) ∨ p2696)
    (h95899 : p4281 ∨ (¬ p2727))
    (h113198 : (¬ p2630) ∨ (¬ p2737) ∨ p3367)
    (h107095 : p2829 ∨ (¬ p2737) ∨ (¬ p2630))
    (h31669 : (¬ p2749) ∨ p3541 ∨ (¬ p4281))
    (h129728 : (¬ p2850) ∨ (¬ p3367))
    (h102586 : p4870 ∨ (¬ p2829))
    (h96029 : p2696 ∨ (¬ p3093) ∨ (¬ p4870) ∨ (¬ p3873) ∨ (¬ p2737))
    (h132040 : (¬ p2363) ∨ (¬ p2651) ∨ p2553)
    (h74478 : p2363 ∨ (¬ p3550) ∨ (¬ p2459))
    (h125400 : (¬ p2881) ∨ (¬ p2459) ∨ p2363)
    (h80464 : p3093 ∨ p2363 ∨ (¬ p3923) ∨ (¬ p2459))
    (h96472 : p3550 ∨ (¬ p2177))
    (h131735 : (¬ p2352) ∨ p2881 ∨ p2553)
    (h8334 : p3923 ∨ (¬ p4992))
    (h79801 : p2493 ∨ p3379 ∨ p2177 ∨ p2553)
    (h108969 : p4992 ∨ p3063)
    (h96943 : p2505 ∨ (¬ p2493))
    (h120583 : p2406 ∨ (¬ p3063) ∨ (¬ p2505) ∨ p2352)
    (h120564 : p3422 ∨ (¬ p3063) ∨ (¬ p2505) ∨ p2352)
    (h81128 : p2598 ∨ (¬ p3541) ∨ p2850 ∨ (¬ p2406))
    (h82549 : (¬ p2598) ∨ p2696 ∨ (¬ p2737) ∨ (¬ p3422))
    : (¬ p2651) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2608) := h132006;
    let u3 : p2749 := h131647;
    let u4 : p3873 := h132015;
    let u5 : p2459 := h131921;
    let u6 : (¬ p3379) := h132018;
    let u7 : (¬ p2696) := h131998;
    let u8 : p2737 := h131645;
    let u9 : p2727 := (Or.elim h125321 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (u2 r1))))));
    let u10 : p2630 := (Or.elim h120332 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u7 r2))))))));
    let u11 : p4281 := (Or.elim h95899 (fun q0 => q0) (fun r0 => (False.elim (r0 u9))));
    let u12 : p3367 := (Or.elim h113198 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => r1))));
    let u13 : p2829 := (Or.elim h107095 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (False.elim (r1 u10))))));
    let u14 : p3541 := (Or.elim h31669 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u11))))));
    let u15 : (¬ p2850) := (Or.elim h129728 (fun q0 => q0) (fun r0 => (False.elim (r0 u12))));
    let u16 : p4870 := (Or.elim h102586 (fun q0 => q0) (fun r0 => (False.elim (r0 u13))));
    let u17 : (¬ p3093) := (Or.elim h96029 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u16))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u8))))))))));
    let u18 : (¬ p2363) := (Or.elim h132040 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1))))));
    let u19 : (¬ p3550) := (Or.elim h74478 (fun q0 => (False.elim (u18 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u5))))));
    let u20 : (¬ p2881) := (Or.elim h125400 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (False.elim (u18 r1))))));
    let u21 : (¬ p3923) := (Or.elim h80464 (fun q0 => (False.elim (u17 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u18 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (r2 u5))))))));
    let u22 : (¬ p2177) := (Or.elim h96472 (fun q0 => (False.elim (u19 q0))) (fun r0 => r0));
    let u23 : (¬ p2352) := (Or.elim h131735 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u20 q1))) (fun r1 => (False.elim (u1 r1))))));
    let u24 : (¬ p4992) := (Or.elim h8334 (fun q0 => (False.elim (u21 q0))) (fun r0 => r0));
    let u25 : p2493 := (Or.elim h79801 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u22 q2))) (fun r2 => (False.elim (u1 r2))))))));
    let u26 : p3063 := (Or.elim h108969 (fun q0 => (False.elim (u24 q0))) (fun r0 => r0));
    let u27 : p2505 := (Or.elim h96943 (fun q0 => q0) (fun r0 => (False.elim (r0 u25))));
    let u28 : p2406 := (Or.elim h120583 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u26))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u27))) (fun r2 => (False.elim (u23 r2))))))));
    let u29 : p3422 := (Or.elim h120564 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u26))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u27))) (fun r2 => (False.elim (u23 r2))))))));
    let u30 : p2598 := (Or.elim h81128 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u14))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u15 q2))) (fun r2 => (False.elim (r2 u28))))))));
    (Or.elim h82549 (fun q0 => (False.elim (q0 u30))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (False.elim (r2 u29)))))))))

theorem step132042 (p2132 p2136 p2137 p2241 p2264 p2295 p2331 p2341 p2427 p2459 p2553 p2598 p2630 p2641 p2651 p2685 p2696 p2707 p2737 p2748 p2749 p2797 p2807 p2829 p2839 p2850 p2870 p2881 p2946 p3016 p3019 p3051 p3246 p3367 p3422 p3425 p3434 p3516 p3577 p3587 p3873 p4357 p4841 p4988 : Prop)
    (h131647 : p2749)
    (h131645 : p2737)
    (h132004 : (¬ p2241))
    (h131921 : p2459)
    (h131998 : (¬ p2696))
    (h131646 : p2748)
    (h132015 : p3873)
    (h132041 : (¬ p2651) ∨ p2553)
    (h129395 : (¬ p2331) ∨ p2651)
    (h129396 : (¬ p2946) ∨ p2651)
    (h130974 : (¬ p2807) ∨ p2651)
    (h131033 : (¬ p2630) ∨ (¬ p2737) ∨ p2651)
    (h117846 : p2696 ∨ p2651 ∨ (¬ p2132))
    (h107098 : (¬ p2598) ∨ p2696 ∨ p2651)
    (h129429 : (¬ p2797) ∨ p2630 ∨ p2331)
    (h129740 : (¬ p2850) ∨ p2946)
    (h87375 : p2807 ∨ (¬ p2737) ∨ (¬ p2685))
    (h82677 : p2630 ∨ p2696 ∨ p3016 ∨ p2553)
    (h129343 : p2630 ∨ p2696 ∨ p2427)
    (h102427 : p2137 ∨ p2132)
    (h102521 : p2136 ∨ p2132)
    (h129707 : p3422 ∨ p2598 ∨ (¬ p3016))
    (h102194 : p4841 ∨ p2797)
    (h82804 : (¬ p2641) ∨ p2797 ∨ (¬ p2749) ∨ p2696)
    (h82527 : (¬ p2737) ∨ p3367 ∨ p2850 ∨ p2696)
    (h102054 : p4357 ∨ p2685)
    (h101604 : p3019 ∨ (¬ p3016))
    (h111165 : p2850 ∨ p2870 ∨ (¬ p3422) ∨ (¬ p2427))
    (h126098 : (¬ p3367) ∨ p2829 ∨ (¬ p3016))
    (h115087 : p2850 ∨ p2839 ∨ (¬ p3422) ∨ (¬ p3367))
    (h82904 : p3425 ∨ p2696 ∨ (¬ p4357))
    (h131207 : (¬ p2295) ∨ p2553 ∨ (¬ p3019))
    (h102334 : p3587 ∨ (¬ p2870))
    (h83665 : (¬ p2870) ∨ p3051 ∨ (¬ p2839) ∨ (¬ p2136))
    (h96166 : p3577 ∨ (¬ p3425))
    (h126603 : p2696 ∨ p2797 ∨ p2685 ∨ p2264 ∨ p2295)
    (h83673 : p2707 ∨ (¬ p2839) ∨ (¬ p3587))
    (h102490 : p4988 ∨ (¬ p3051))
    (h46036 : (¬ p2137) ∨ (¬ p2459) ∨ (¬ p2839) ∨ (¬ p2881) ∨ (¬ p3051))
    (h104070 : (¬ p2264) ∨ p2341)
    (h126903 : (¬ p3246) ∨ (¬ p3577) ∨ (¬ p2341) ∨ (¬ p2829) ∨ p2641 ∨ (¬ p4841) ∨ (¬ p2137) ∨ p2241 ∨ p2696 ∨ p2295 ∨ (¬ p4988) ∨ p2881 ∨ (¬ p2459))
    (h114176 : (¬ p2459) ∨ p3516 ∨ (¬ p2341))
    (h120432 : (¬ p3434) ∨ (¬ p2707) ∨ (¬ p2748) ∨ p2696 ∨ p2641 ∨ p2295 ∨ p3246)
    (h122028 : p3434 ∨ (¬ p3516) ∨ (¬ p3873) ∨ (¬ p3425))
    : p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn h);
    let u1 : p2749 := h131647;
    let u2 : p2737 := h131645;
    let u3 : (¬ p2241) := h132004;
    let u4 : p2459 := h131921;
    let u5 : (¬ p2696) := h131998;
    let u6 : p2748 := h131646;
    let u7 : p3873 := h132015;
    let u8 : (¬ p2651) := (Or.elim h132041 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : (¬ p2331) := (Or.elim h129395 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u10 : (¬ p2946) := (Or.elim h129396 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u11 : (¬ p2807) := (Or.elim h130974 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u12 : (¬ p2630) := (Or.elim h131033 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u8 r1))))));
    let u13 : (¬ p2132) := (Or.elim h117846 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u8 q1))) (fun r1 => r1))));
    let u14 : (¬ p2598) := (Or.elim h107098 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (False.elim (u8 r1))))));
    let u15 : (¬ p2797) := (Or.elim h129429 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u12 q1))) (fun r1 => (False.elim (u9 r1))))));
    let u16 : (¬ p2850) := (Or.elim h129740 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u17 : (¬ p2685) := (Or.elim h87375 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => r1))));
    let u18 : p3016 := (Or.elim h82677 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => q2) (fun r2 => (False.elim (u0 r2))))))));
    let u19 : p2427 := (Or.elim h129343 (fun q0 => (False.elim (u12 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => r1))));
    let u20 : p2137 := (Or.elim h102427 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u21 : p2136 := (Or.elim h102521 (fun q0 => q0) (fun r0 => (False.elim (u13 r0))));
    let u22 : p3422 := (Or.elim h129707 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u14 q1))) (fun r1 => (False.elim (r1 u18))))));
    let u23 : p4841 := (Or.elim h102194 (fun q0 => q0) (fun r0 => (False.elim (u15 r0))));
    let u24 : (¬ p2641) := (Or.elim h82804 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u15 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (u5 r2))))))));
    let u25 : p3367 := (Or.elim h82527 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u16 q2))) (fun r2 => (False.elim (u5 r2))))))));
    let u26 : p4357 := (Or.elim h102054 (fun q0 => q0) (fun r0 => (False.elim (u17 r0))));
    let u27 : p3019 := (Or.elim h101604 (fun q0 => q0) (fun r0 => (False.elim (r0 u18))));
    let u28 : p2870 := (Or.elim h111165 (fun q0 => (False.elim (u16 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u22))) (fun r2 => (False.elim (r2 u19))))))));
    let u29 : p2829 := (Or.elim h126098 (fun q0 => (False.elim (q0 u25))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u18))))));
    let u30 : p2839 := (Or.elim h115087 (fun q0 => (False.elim (u16 q0))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u22))) (fun r2 => (False.elim (r2 u25))))))));
    let u31 : p3425 := (Or.elim h82904 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (False.elim (r1 u26))))));
    let u32 : (¬ p2295) := (Or.elim h131207 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u27))))));
    let u33 : p3587 := (Or.elim h102334 (fun q0 => q0) (fun r0 => (False.elim (r0 u28))));
    let u34 : p3051 := (Or.elim h83665 (fun q0 => (False.elim (q0 u28))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u30))) (fun r2 => (False.elim (r2 u21))))))));
    let u35 : p3577 := (Or.elim h96166 (fun q0 => q0) (fun r0 => (False.elim (r0 u31))));
    let u36 : p2264 := (Or.elim h126603 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u15 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u17 q2))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (u32 r3))))))))));
    let u37 : p2707 := (Or.elim h83673 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u30))) (fun r1 => (False.elim (r1 u33))))));
    let u38 : p4988 := (Or.elim h102490 (fun q0 => q0) (fun r0 => (False.elim (r0 u34))));
    let u39 : (¬ p2881) := (Or.elim h46036 (fun q0 => (False.elim (q0 u20))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u30))) (fun r2 => (Or.elim r2 (fun q3 => q3) (fun r3 => (False.elim (r3 u34))))))))));
    let u40 : p2341 := (Or.elim h104070 (fun q0 => (False.elim (q0 u36))) (fun r0 => r0));
    let u41 : (¬ p3246) := (Or.elim h126903 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u35))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u40))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u29))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u24 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u23))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u20))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (u3 q7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (u5 q8))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u32 q9))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u38))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (u39 q11))) (fun r11 => (False.elim (r11 u4))))))))))))))))))))))))));
    let u42 : p3516 := (Or.elim h114176 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => q1) (fun r1 => (False.elim (r1 u40))))));
    let u43 : (¬ p3434) := (Or.elim h120432 (fun q0 => q0) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u37))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u5 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u24 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u32 q5))) (fun r5 => (False.elim (u41 r5))))))))))))));
    (Or.elim h122028 (fun q0 => (False.elim (u43 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u42))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u31)))))))))

theorem step132044 (p2553 p3920 : Prop)
    (h132042 : p2553)
    (h94485 : p3920 ∨ (¬ p2553))
    : p3920 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3920) := (fun h => hn h);
    let u1 : p2553 := h132042;
    (Or.elim h94485 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u1)))))

theorem step132045 (p2274 p2437 p2553 : Prop)
    (h132042 : p2553)
    (h131182 : (¬ p2274))
    (h129377 : (¬ p2553) ∨ p2274 ∨ (¬ p2437))
    : (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn h);
    let u1 : p2553 := h132042;
    let u2 : (¬ p2274) := h131182;
    (Or.elim h129377 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step132054 (p2241 p2363 p2553 : Prop)
    (h132042 : p2553)
    (h132004 : (¬ p2241))
    (h129258 : (¬ p2363) ∨ p2241 ∨ (¬ p2553))
    : (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn h);
    let u1 : p2553 := h132042;
    let u2 : (¬ p2241) := h132004;
    (Or.elim h129258 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step132058 (p2437 p3016 p3920 : Prop)
    (h132045 : (¬ p2437))
    (h132044 : p3920)
    (h114302 : p2437 ∨ (¬ p3016) ∨ (¬ p3920))
    : (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2437) := h132045;
    let u2 : p3920 := h132044;
    (Or.elim h114302 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u2)))))))

theorem step132081 (p2363 p2459 p3550 : Prop)
    (h132054 : (¬ p2363))
    (h131921 : p2459)
    (h74478 : p2363 ∨ (¬ p3550) ∨ (¬ p2459))
    : (¬ p3550) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3550 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2363) := h132054;
    let u2 : p2459 := h131921;
    (Or.elim h74478 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u2)))))))

theorem step132082 (p2363 p2459 p2881 : Prop)
    (h132054 : (¬ p2363))
    (h131921 : p2459)
    (h125400 : (¬ p2881) ∨ (¬ p2459) ∨ p2363)
    : (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2363) := h132054;
    let u2 : p2459 := h131921;
    (Or.elim h125400 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step132091 (p3016 p3093 p3379 : Prop)
    (h132058 : (¬ p3016))
    (h132018 : (¬ p3379))
    (h130761 : (¬ p3093) ∨ p3016 ∨ p3379)
    : (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p3016) := h132058;
    let u2 : (¬ p3379) := h132018;
    (Or.elim h130761 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step132104 (p2177 p3550 : Prop)
    (h132081 : (¬ p3550))
    (h96472 : p3550 ∨ (¬ p2177))
    : (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p3550) := h132081;
    (Or.elim h96472 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step132106 (p2274 p2553 p2881 p2911 : Prop)
    (h132082 : (¬ p2881))
    (h131182 : (¬ p2274))
    (h132042 : p2553)
    (h125828 : (¬ p2553) ∨ p2881 ∨ p2274 ∨ (¬ p2911))
    : (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2881) := h132082;
    let u2 : (¬ p2274) := h131182;
    let u3 : p2553 := h132042;
    (Or.elim h125828 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u2 q2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step132121 (p2295 p2553 p3093 : Prop)
    (h132091 : (¬ p3093))
    (h132042 : p2553)
    (h103846 : p3093 ∨ p2295 ∨ (¬ p2553))
    : p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn h);
    let u1 : (¬ p3093) := h132091;
    let u2 : p2553 := h132042;
    (Or.elim h103846 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step132128 (p2177 p3955 : Prop)
    (h132104 : (¬ p2177))
    (h78596 : p3955 ∨ p2177)
    : p3955 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3955) := (fun h => hn h);
    let u1 : (¬ p2177) := h132104;
    (Or.elim h78596 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u1 r0)))))

theorem step132134 (p2437 p2630 p2696 p2911 : Prop)
    (h132106 : (¬ p2911))
    (h132045 : (¬ p2437))
    (h131998 : (¬ p2696))
    (h82675 : p2437 ∨ p2911 ∨ p2630 ∨ p2696)
    : p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn h);
    let u1 : (¬ p2911) := h132106;
    let u2 : (¬ p2437) := h132045;
    let u3 : (¬ p2696) := h131998;
    (Or.elim h82675 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step132148 (p2295 p2363 p2459 p2668 : Prop)
    (h132121 : p2295)
    (h132054 : (¬ p2363))
    (h131921 : p2459)
    (h79363 : (¬ p2295) ∨ p2363 ∨ p2668 ∨ (¬ p2459))
    : p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2668) := (fun h => hn h);
    let u1 : p2295 := h132121;
    let u2 : (¬ p2363) := h132054;
    let u3 : p2459 := h131921;
    (Or.elim h79363 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u2 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u0 q2))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step132149 (p2274 p2295 p2331 p2737 p2811 : Prop)
    (h132121 : p2295)
    (h131999 : p2811)
    (h131182 : (¬ p2274))
    (h131645 : p2737)
    (h81874 : (¬ p2811) ∨ (¬ p2737) ∨ (¬ p2295) ∨ p2274 ∨ (¬ p2331))
    : (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn h);
    let u1 : p2295 := h132121;
    let u2 : p2811 := h131999;
    let u3 : (¬ p2274) := h131182;
    let u4 : p2737 := h131645;
    (Or.elim h81874 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u3 q3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step132158 (p2187 p2274 p3955 : Prop)
    (h132128 : p3955)
    (h131182 : (¬ p2274))
    (h78588 : p2274 ∨ (¬ p2187) ∨ (¬ p3955))
    : (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn h);
    let u1 : p3955 := h132128;
    let u2 : (¬ p2274) := h131182;
    (Or.elim h78588 (fun q0 => (False.elim (u2 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step132168 (p2630 p2651 p2737 : Prop)
    (h132134 : p2630)
    (h131645 : p2737)
    (h131033 : (¬ p2630) ∨ (¬ p2737) ∨ p2651)
    : p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn h);
    let u1 : p2630 := h132134;
    let u2 : p2737 := h131645;
    (Or.elim h131033 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u0 r1)))))))

theorem step132191 (p2187 p2331 p2668 p3166 : Prop)
    (h132148 : p2668)
    (h132149 : (¬ p2331))
    (h132158 : (¬ p2187))
    (h112323 : (¬ p2668) ∨ p2187 ∨ (¬ p3166) ∨ p2331)
    : (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn h);
    let u1 : p2668 := h132148;
    let u2 : (¬ p2331) := h132149;
    let u3 : (¬ p2187) := h132158;
    (Or.elim h112323 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u2 r2)))))))))

theorem step132207 (p2187 p2363 p3256 : Prop)
    (h132158 : (¬ p2187))
    (h132054 : (¬ p2363))
    (h117577 : (¬ p3256) ∨ p2187 ∨ p2363)
    : (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2187) := h132158;
    let u2 : (¬ p2363) := h132054;
    (Or.elim h117577 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u1 q1))) (fun r1 => (False.elim (u2 r1)))))))

theorem step132253 (p2459 p2651 p3166 p3256 : Prop)
    (h132207 : (¬ p3256))
    (h132191 : (¬ p3166))
    (h131921 : p2459)
    (h132168 : p2651)
    (h100966 : p3166 ∨ p3256 ∨ (¬ p2651) ∨ (¬ p2459))
    : False :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := h132207;
    let u1 : (¬ p3166) := h132191;
    let u2 : p2459 := h131921;
    let u3 : p2651 := h132168;
    (Or.elim h100966 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

end ElevenRUP
