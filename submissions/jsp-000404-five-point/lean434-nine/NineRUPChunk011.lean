import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step22443 (p327 p328 p332 p333 p334 p335 p336 p337 p338 p339 p340 p341 : Prop)
    (h1719 : p327 ∨ p328 ∨ (¬ p332) ∨ (¬ p333) ∨ (¬ p334) ∨ (¬ p335) ∨ (¬ p336))
    (h1804 : p333 ∨ p337)
    (h1805 : p333 ∨ p338)
    (h1806 : p333 ∨ p339)
    (h1807 : p333 ∨ p340)
    (h1808 : p333 ∨ p341)
    (h1744 : p327 ∨ p328 ∨ (¬ p337) ∨ (¬ p338) ∨ (¬ p339) ∨ (¬ p340) ∨ (¬ p341)) : (¬ p332) ∨ (¬ p335) ∨ p328 ∨ (¬ p336) ∨ p327 ∨ (¬ p334) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p332 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p328) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p336 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p327) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p333) := by
    rcases h1719 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u0)
    · exact q3
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u3)
  have u7 : p337 := by
    rcases h1804 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p338 := by
    rcases h1805 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p339 := by
    rcases h1806 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p340 := by
    rcases h1807 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p341 := by
    rcases h1808 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1744 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22444 (p327 p328 p332 p334 p335 p336 : Prop)
    (h22429 : p332 ∨ p327 ∨ p328)
    (h22430 : p336 ∨ p327 ∨ p328)
    (h22431 : p335 ∨ p327 ∨ p328)
    (h22432 : p334 ∨ p327 ∨ p328)
    (h22443 : (¬ p332) ∨ (¬ p335) ∨ p328 ∨ (¬ p336) ∨ p327 ∨ (¬ p334)) : p327 ∨ p328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p327) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p328) := fun hu => hn (Or.inr hu)
  have u2 : p332 := by
    rcases h22429 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p336 := by
    rcases h22430 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p335 := by
    rcases h22431 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p334 := by
    rcases h22432 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22443 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u5)

theorem step22448 (p599 p601 p604 p609 p610 p611 p612 p613 : Prop)
    (h3465 : p604 ∨ p609)
    (h3466 : p604 ∨ p610)
    (h3467 : p604 ∨ p611)
    (h3468 : p604 ∨ p612)
    (h3469 : p604 ∨ p613)
    (h3412 : p599 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p604 ∨ p599 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p604) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p599) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3465 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3466 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3467 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3468 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3469 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3412 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22449 (p599 p601 p608 p609 p610 p611 p612 p613 : Prop)
    (h3485 : p608 ∨ p609)
    (h3486 : p608 ∨ p610)
    (h3487 : p608 ∨ p611)
    (h3488 : p608 ∨ p612)
    (h3489 : p608 ∨ p613)
    (h3412 : p599 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p608 ∨ p599 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p608) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p599) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3485 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3486 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3487 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3488 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3489 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3412 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22450 (p599 p601 p607 p609 p610 p611 p612 p613 : Prop)
    (h3480 : p607 ∨ p609)
    (h3481 : p607 ∨ p610)
    (h3482 : p607 ∨ p611)
    (h3483 : p607 ∨ p612)
    (h3484 : p607 ∨ p613)
    (h3412 : p599 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p607 ∨ p599 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p607) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p599) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3480 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3481 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3482 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3483 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3484 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3412 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22451 (p599 p601 p606 p609 p610 p611 p612 p613 : Prop)
    (h3475 : p606 ∨ p609)
    (h3476 : p606 ∨ p610)
    (h3477 : p606 ∨ p611)
    (h3478 : p606 ∨ p612)
    (h3479 : p606 ∨ p613)
    (h3412 : p599 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p606 ∨ p599 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p606) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p599) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3475 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3476 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3477 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3478 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3479 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3412 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22452 (p596 p599 p601 p604 p605 p606 p607 p608 p609 p610 p611 p612 p613 : Prop)
    (h22448 : p604 ∨ p599 ∨ p601)
    (h22449 : p608 ∨ p599 ∨ p601)
    (h22450 : p607 ∨ p599 ∨ p601)
    (h22451 : p606 ∨ p599 ∨ p601)
    (h3385 : p596 ∨ p599 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608))
    (h3470 : p605 ∨ p609)
    (h3471 : p605 ∨ p610)
    (h3472 : p605 ∨ p611)
    (h3473 : p605 ∨ p612)
    (h3474 : p605 ∨ p613)
    (h3412 : p599 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p599 ∨ p596 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p599) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p596) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p604 := by
    rcases h22448 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p608 := by
    rcases h22449 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p607 := by
    rcases h22450 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p606 := by
    rcases h22451 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p605) := by
    rcases h3385 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact q3
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u4)
  have u8 : p609 := by
    rcases h3470 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p610 := by
    rcases h3471 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p611 := by
    rcases h3472 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p612 := by
    rcases h3473 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u12 : p613 := by
    rcases h3474 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h3412 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step22453 (p346 p349 p356 p357 p358 p359 p360 p361 : Prop)
    (h1945 : p356 ∨ p357)
    (h1946 : p356 ∨ p358)
    (h1947 : p356 ∨ p359)
    (h1948 : p356 ∨ p360)
    (h1949 : p356 ∨ p361)
    (h1861 : p346 ∨ p349 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p356 ∨ p349 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p356) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p349) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p357 := by
    rcases h1945 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p358 := by
    rcases h1946 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p359 := by
    rcases h1947 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p360 := by
    rcases h1948 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p361 := by
    rcases h1949 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1861 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22454 (p346 p349 p355 p357 p358 p359 p360 p361 : Prop)
    (h1940 : p355 ∨ p357)
    (h1941 : p355 ∨ p358)
    (h1942 : p355 ∨ p359)
    (h1943 : p355 ∨ p360)
    (h1944 : p355 ∨ p361)
    (h1861 : p346 ∨ p349 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p355 ∨ p349 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p355) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p349) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p357 := by
    rcases h1940 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p358 := by
    rcases h1941 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p359 := by
    rcases h1942 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p360 := by
    rcases h1943 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p361 := by
    rcases h1944 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1861 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22455 (p346 p349 p354 p357 p358 p359 p360 p361 : Prop)
    (h1935 : p354 ∨ p357)
    (h1936 : p354 ∨ p358)
    (h1937 : p354 ∨ p359)
    (h1938 : p354 ∨ p360)
    (h1939 : p354 ∨ p361)
    (h1861 : p346 ∨ p349 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p354 ∨ p349 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p354) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p349) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p357 := by
    rcases h1935 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p358 := by
    rcases h1936 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p359 := by
    rcases h1937 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p360 := by
    rcases h1938 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p361 := by
    rcases h1939 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1861 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22456 (p346 p349 p353 p357 p358 p359 p360 p361 : Prop)
    (h1930 : p353 ∨ p357)
    (h1931 : p353 ∨ p358)
    (h1932 : p353 ∨ p359)
    (h1933 : p353 ∨ p360)
    (h1934 : p353 ∨ p361)
    (h1861 : p346 ∨ p349 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p353 ∨ p349 ∨ p346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p353) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p349) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p357 := by
    rcases h1930 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p358 := by
    rcases h1931 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p359 := by
    rcases h1932 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p360 := by
    rcases h1933 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p361 := by
    rcases h1934 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1861 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22457 (p4 p346 p349 p352 p353 p354 p355 p356 p357 p358 p359 p360 p361 : Prop)
    (h22453 : p356 ∨ p349 ∨ p346)
    (h22454 : p355 ∨ p349 ∨ p346)
    (h22455 : p354 ∨ p349 ∨ p346)
    (h22456 : p353 ∨ p349 ∨ p346)
    (h1831 : p4 ∨ p349 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356))
    (h1925 : p352 ∨ p357)
    (h1926 : p352 ∨ p358)
    (h1927 : p352 ∨ p359)
    (h1928 : p352 ∨ p360)
    (h1929 : p352 ∨ p361)
    (h1861 : p346 ∨ p349 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p349 ∨ p346 ∨ p4 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p349) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p346) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p4) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p356 := by
    rcases h22453 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p355 := by
    rcases h22454 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p354 := by
    rcases h22455 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p353 := by
    rcases h22456 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p352) := by
    rcases h1831 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact q2
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u3)
  have u8 : p357 := by
    rcases h1925 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p358 := by
    rcases h1926 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p359 := by
    rcases h1927 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p360 := by
    rcases h1928 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u12 : p361 := by
    rcases h1929 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h1861 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step22464 (p532 p1454 p1459 p1460 p1461 p1462 p1463 p1464 : Prop)
    (h8903 : p1459 ∨ p1460)
    (h8904 : p1459 ∨ p1461)
    (h8905 : p1459 ∨ p1462)
    (h8906 : p1459 ∨ p1463)
    (h8907 : p1459 ∨ p1464)
    (h8822 : p532 ∨ p1454 ∨ (¬ p1460) ∨ (¬ p1461) ∨ (¬ p1462) ∨ (¬ p1463) ∨ (¬ p1464)) : p1459 ∨ p1454 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1459) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1454) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p532) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1460 := by
    rcases h8903 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1461 := by
    rcases h8904 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1462 := by
    rcases h8905 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1463 := by
    rcases h8906 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1464 := by
    rcases h8907 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8822 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22465 (p532 p1454 p1458 p1460 p1461 p1462 p1463 p1464 : Prop)
    (h8898 : p1458 ∨ p1460)
    (h8899 : p1458 ∨ p1461)
    (h8900 : p1458 ∨ p1462)
    (h8901 : p1458 ∨ p1463)
    (h8902 : p1458 ∨ p1464)
    (h8822 : p532 ∨ p1454 ∨ (¬ p1460) ∨ (¬ p1461) ∨ (¬ p1462) ∨ (¬ p1463) ∨ (¬ p1464)) : p1458 ∨ p1454 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1458) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1454) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p532) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1460 := by
    rcases h8898 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1461 := by
    rcases h8899 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1462 := by
    rcases h8900 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1463 := by
    rcases h8901 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1464 := by
    rcases h8902 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8822 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22466 (p532 p1454 p1457 p1460 p1461 p1462 p1463 p1464 : Prop)
    (h8893 : p1457 ∨ p1460)
    (h8894 : p1457 ∨ p1461)
    (h8895 : p1457 ∨ p1462)
    (h8896 : p1457 ∨ p1463)
    (h8897 : p1457 ∨ p1464)
    (h8822 : p532 ∨ p1454 ∨ (¬ p1460) ∨ (¬ p1461) ∨ (¬ p1462) ∨ (¬ p1463) ∨ (¬ p1464)) : p1457 ∨ p1454 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1457) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1454) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p532) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1460 := by
    rcases h8893 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1461 := by
    rcases h8894 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1462 := by
    rcases h8895 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1463 := by
    rcases h8896 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1464 := by
    rcases h8897 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8822 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22467 (p532 p1454 p1456 p1460 p1461 p1462 p1463 p1464 : Prop)
    (h8888 : p1456 ∨ p1460)
    (h8889 : p1456 ∨ p1461)
    (h8890 : p1456 ∨ p1462)
    (h8891 : p1456 ∨ p1463)
    (h8892 : p1456 ∨ p1464)
    (h8822 : p532 ∨ p1454 ∨ (¬ p1460) ∨ (¬ p1461) ∨ (¬ p1462) ∨ (¬ p1463) ∨ (¬ p1464)) : p1456 ∨ p1454 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1456) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1454) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p532) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1460 := by
    rcases h8888 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1461 := by
    rcases h8889 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1462 := by
    rcases h8890 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1463 := by
    rcases h8891 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1464 := by
    rcases h8892 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8822 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22468 (p532 p1454 p1455 p1456 p1457 p1458 p1459 p1460 p1461 p1462 p1463 p1464 : Prop)
    (h8797 : p532 ∨ p1454 ∨ (¬ p1455) ∨ (¬ p1456) ∨ (¬ p1457) ∨ (¬ p1458) ∨ (¬ p1459))
    (h8883 : p1455 ∨ p1460)
    (h8884 : p1455 ∨ p1461)
    (h8885 : p1455 ∨ p1462)
    (h8886 : p1455 ∨ p1463)
    (h8887 : p1455 ∨ p1464)
    (h8822 : p532 ∨ p1454 ∨ (¬ p1460) ∨ (¬ p1461) ∨ (¬ p1462) ∨ (¬ p1463) ∨ (¬ p1464)) : (¬ p1456) ∨ (¬ p1459) ∨ p532 ∨ p1454 ∨ (¬ p1457) ∨ (¬ p1458) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1459 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p532) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1454) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1457 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1458 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1455) := by
    rcases h8797 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p1460 := by
    rcases h8883 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1461 := by
    rcases h8884 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1462 := by
    rcases h8885 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1463 := by
    rcases h8886 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1464 := by
    rcases h8887 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h8822 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22469 (p532 p1454 p1456 p1457 p1458 p1459 : Prop)
    (h22464 : p1459 ∨ p1454 ∨ p532)
    (h22465 : p1458 ∨ p1454 ∨ p532)
    (h22466 : p1457 ∨ p1454 ∨ p532)
    (h22467 : p1456 ∨ p1454 ∨ p532)
    (h22468 : (¬ p1456) ∨ (¬ p1459) ∨ p532 ∨ p1454 ∨ (¬ p1457) ∨ (¬ p1458)) : p1454 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1454) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p532) := fun hu => hn (Or.inr hu)
  have u2 : p1459 := by
    rcases h22464 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1458 := by
    rcases h22465 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1457 := by
    rcases h22466 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1456 := by
    rcases h22467 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22468 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22470 (p436 p443 p449 p450 p451 p452 p453 p454 : Prop)
    (h2467 : p449 ∨ p450)
    (h2468 : p449 ∨ p451)
    (h2469 : p449 ∨ p452)
    (h2470 : p449 ∨ p453)
    (h2471 : p449 ∨ p454)
    (h2375 : p436 ∨ p443 ∨ (¬ p450) ∨ (¬ p451) ∨ (¬ p452) ∨ (¬ p453) ∨ (¬ p454)) : p449 ∨ p443 ∨ p436 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p449) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p443) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p436) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p450 := by
    rcases h2467 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p451 := by
    rcases h2468 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p452 := by
    rcases h2469 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p453 := by
    rcases h2470 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p454 := by
    rcases h2471 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2375 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22471 (p436 p443 p448 p450 p451 p452 p453 p454 : Prop)
    (h2462 : p448 ∨ p450)
    (h2463 : p448 ∨ p451)
    (h2464 : p448 ∨ p452)
    (h2465 : p448 ∨ p453)
    (h2466 : p448 ∨ p454)
    (h2375 : p436 ∨ p443 ∨ (¬ p450) ∨ (¬ p451) ∨ (¬ p452) ∨ (¬ p453) ∨ (¬ p454)) : p448 ∨ p443 ∨ p436 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p448) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p443) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p436) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p450 := by
    rcases h2462 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p451 := by
    rcases h2463 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p452 := by
    rcases h2464 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p453 := by
    rcases h2465 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p454 := by
    rcases h2466 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2375 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22472 (p436 p443 p447 p450 p451 p452 p453 p454 : Prop)
    (h2457 : p447 ∨ p450)
    (h2458 : p447 ∨ p451)
    (h2459 : p447 ∨ p452)
    (h2460 : p447 ∨ p453)
    (h2461 : p447 ∨ p454)
    (h2375 : p436 ∨ p443 ∨ (¬ p450) ∨ (¬ p451) ∨ (¬ p452) ∨ (¬ p453) ∨ (¬ p454)) : p447 ∨ p443 ∨ p436 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p447) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p443) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p436) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p450 := by
    rcases h2457 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p451 := by
    rcases h2458 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p452 := by
    rcases h2459 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p453 := by
    rcases h2460 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p454 := by
    rcases h2461 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2375 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22473 (p436 p443 p446 p450 p451 p452 p453 p454 : Prop)
    (h2452 : p446 ∨ p450)
    (h2453 : p446 ∨ p451)
    (h2454 : p446 ∨ p452)
    (h2455 : p446 ∨ p453)
    (h2456 : p446 ∨ p454)
    (h2375 : p436 ∨ p443 ∨ (¬ p450) ∨ (¬ p451) ∨ (¬ p452) ∨ (¬ p453) ∨ (¬ p454)) : p446 ∨ p443 ∨ p436 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p446) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p443) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p436) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p450 := by
    rcases h2452 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p451 := by
    rcases h2453 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p452 := by
    rcases h2454 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p453 := by
    rcases h2455 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p454 := by
    rcases h2456 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2375 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22474 (p436 p443 p445 p446 p447 p448 p449 p450 p451 p452 p453 p454 : Prop)
    (h2350 : p436 ∨ p443 ∨ (¬ p445) ∨ (¬ p446) ∨ (¬ p447) ∨ (¬ p448) ∨ (¬ p449))
    (h2447 : p445 ∨ p450)
    (h2448 : p445 ∨ p451)
    (h2449 : p445 ∨ p452)
    (h2450 : p445 ∨ p453)
    (h2451 : p445 ∨ p454)
    (h2375 : p436 ∨ p443 ∨ (¬ p450) ∨ (¬ p451) ∨ (¬ p452) ∨ (¬ p453) ∨ (¬ p454)) : (¬ p446) ∨ (¬ p449) ∨ p436 ∨ p443 ∨ (¬ p447) ∨ (¬ p448) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p446 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p436) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p443) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p447 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p448 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p445) := by
    rcases h2350 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p450 := by
    rcases h2447 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p451 := by
    rcases h2448 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p452 := by
    rcases h2449 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p453 := by
    rcases h2450 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p454 := by
    rcases h2451 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h2375 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22475 (p436 p443 p446 p447 p448 p449 : Prop)
    (h22470 : p449 ∨ p443 ∨ p436)
    (h22471 : p448 ∨ p443 ∨ p436)
    (h22472 : p447 ∨ p443 ∨ p436)
    (h22473 : p446 ∨ p443 ∨ p436)
    (h22474 : (¬ p446) ∨ (¬ p449) ∨ p436 ∨ p443 ∨ (¬ p447) ∨ (¬ p448)) : p443 ∨ p436 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p443) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p436) := fun hu => hn (Or.inr hu)
  have u2 : p449 := by
    rcases h22470 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p448 := by
    rcases h22471 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p447 := by
    rcases h22472 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p446 := by
    rcases h22473 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22474 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22476 (p363 p367 p375 p376 p377 p378 p379 p380 : Prop)
    (h2074 : p375 ∨ p376)
    (h2075 : p375 ∨ p377)
    (h2076 : p375 ∨ p378)
    (h2077 : p375 ∨ p379)
    (h2078 : p375 ∨ p380)
    (h1979 : p363 ∨ p367 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p375 ∨ p363 ∨ p367 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p375) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p363) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p367) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p376 := by
    rcases h2074 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p377 := by
    rcases h2075 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p378 := by
    rcases h2076 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p379 := by
    rcases h2077 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p380 := by
    rcases h2078 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1979 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22477 (p363 p367 p374 p376 p377 p378 p379 p380 : Prop)
    (h2069 : p374 ∨ p376)
    (h2070 : p374 ∨ p377)
    (h2071 : p374 ∨ p378)
    (h2072 : p374 ∨ p379)
    (h2073 : p374 ∨ p380)
    (h1979 : p363 ∨ p367 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p374 ∨ p363 ∨ p367 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p374) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p363) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p367) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p376 := by
    rcases h2069 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p377 := by
    rcases h2070 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p378 := by
    rcases h2071 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p379 := by
    rcases h2072 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p380 := by
    rcases h2073 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1979 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22478 (p363 p367 p373 p376 p377 p378 p379 p380 : Prop)
    (h2064 : p373 ∨ p376)
    (h2065 : p373 ∨ p377)
    (h2066 : p373 ∨ p378)
    (h2067 : p373 ∨ p379)
    (h2068 : p373 ∨ p380)
    (h1979 : p363 ∨ p367 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p373 ∨ p363 ∨ p367 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p373) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p363) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p367) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p376 := by
    rcases h2064 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p377 := by
    rcases h2065 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p378 := by
    rcases h2066 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p379 := by
    rcases h2067 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p380 := by
    rcases h2068 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1979 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22479 (p363 p367 p372 p376 p377 p378 p379 p380 : Prop)
    (h2059 : p372 ∨ p376)
    (h2060 : p372 ∨ p377)
    (h2061 : p372 ∨ p378)
    (h2062 : p372 ∨ p379)
    (h2063 : p372 ∨ p380)
    (h1979 : p363 ∨ p367 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p372 ∨ p363 ∨ p367 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p372) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p363) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p367) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p376 := by
    rcases h2059 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p377 := by
    rcases h2060 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p378 := by
    rcases h2061 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p379 := by
    rcases h2062 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p380 := by
    rcases h2063 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1979 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22480 (p363 p367 p371 p372 p373 p374 p375 p376 p377 p378 p379 p380 : Prop)
    (h1954 : p363 ∨ p367 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375))
    (h2054 : p371 ∨ p376)
    (h2055 : p371 ∨ p377)
    (h2056 : p371 ∨ p378)
    (h2057 : p371 ∨ p379)
    (h2058 : p371 ∨ p380)
    (h1979 : p363 ∨ p367 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : (¬ p372) ∨ p363 ∨ p367 ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p372 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p363) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p367) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p373 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p374 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p375 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p371) := by
    rcases h1954 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p376 := by
    rcases h2054 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p377 := by
    rcases h2055 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p378 := by
    rcases h2056 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p379 := by
    rcases h2057 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p380 := by
    rcases h2058 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1979 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22481 (p363 p367 p372 p373 p374 p375 : Prop)
    (h22476 : p375 ∨ p363 ∨ p367)
    (h22477 : p374 ∨ p363 ∨ p367)
    (h22478 : p373 ∨ p363 ∨ p367)
    (h22479 : p372 ∨ p363 ∨ p367)
    (h22480 : (¬ p372) ∨ p363 ∨ p367 ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p363 ∨ p367 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p363) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p367) := fun hu => hn (Or.inr hu)
  have u2 : p375 := by
    rcases h22476 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p374 := by
    rcases h22477 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p373 := by
    rcases h22478 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p372 := by
    rcases h22479 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22480 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step22483 (p923 p928 p930 p935 p936 p937 p938 p939 : Prop)
    (h5433 : p930 ∨ p935)
    (h5434 : p930 ∨ p936)
    (h5435 : p930 ∨ p937)
    (h5436 : p930 ∨ p938)
    (h5437 : p930 ∨ p939)
    (h5365 : p923 ∨ p928 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p930 ∨ p923 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p930) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p923) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p928) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5433 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5434 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5435 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5436 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5437 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5365 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22484 (p923 p928 p930 p931 p932 p933 p934 : Prop)
    (h22018 : p931 ∨ p923 ∨ p928)
    (h22483 : p930 ∨ p923 ∨ p928)
    (h22015 : p934 ∨ p923 ∨ p928)
    (h22016 : p933 ∨ p923 ∨ p928)
    (h22017 : p932 ∨ p923 ∨ p928)
    (h5340 : p923 ∨ p928 ∨ (¬ p930) ∨ (¬ p931) ∨ (¬ p932) ∨ (¬ p933) ∨ (¬ p934)) : p923 ∨ p928 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p923) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p928) := fun hu => hn (Or.inr hu)
  have u2 : p931 := by
    rcases h22018 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p930 := by
    rcases h22483 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p934 := by
    rcases h22015 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p933 := by
    rcases h22016 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p932 := by
    rcases h22017 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h5340 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u4)

theorem step22486 (p312 p532 p980 p983 p1061 p1078 p1082 : Prop)
    (h17629 : (¬ p312) ∨ (¬ p532) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1078))
    (h11317 : (¬ p532) ∨ p980 ∨ (¬ p1082))
    (h21885 : p1082 ∨ p1078) : (¬ p532) ∨ (¬ p983) ∨ p980 ∨ (¬ p312) ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p980) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p1078) := by
    rcases h17629 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u4)
    · exact q4
  have u6 : (¬ p1082) := by
    rcases h11317 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (u2 q1)
    · exact q2
  rcases h21885 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step22492 (p789 p858 p865 p870 p871 p872 p873 p874 : Prop)
    (h5027 : p865 ∨ p870)
    (h5028 : p865 ∨ p871)
    (h5029 : p865 ∨ p872)
    (h5030 : p865 ∨ p873)
    (h5031 : p865 ∨ p874)
    (h4964 : p789 ∨ p858 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : p865 ∨ p858 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p865) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p858) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p870 := by
    rcases h5027 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p871 := by
    rcases h5028 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p872 := by
    rcases h5029 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p873 := by
    rcases h5030 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p874 := by
    rcases h5031 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4964 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22493 (p789 p858 p869 p870 p871 p872 p873 p874 : Prop)
    (h5047 : p869 ∨ p870)
    (h5048 : p869 ∨ p871)
    (h5049 : p869 ∨ p872)
    (h5050 : p869 ∨ p873)
    (h5051 : p869 ∨ p874)
    (h4964 : p789 ∨ p858 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : p869 ∨ p858 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p869) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p858) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p870 := by
    rcases h5047 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p871 := by
    rcases h5048 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p872 := by
    rcases h5049 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p873 := by
    rcases h5050 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p874 := by
    rcases h5051 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4964 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22494 (p789 p858 p868 p870 p871 p872 p873 p874 : Prop)
    (h5042 : p868 ∨ p870)
    (h5043 : p868 ∨ p871)
    (h5044 : p868 ∨ p872)
    (h5045 : p868 ∨ p873)
    (h5046 : p868 ∨ p874)
    (h4964 : p789 ∨ p858 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : p868 ∨ p858 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p868) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p858) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p870 := by
    rcases h5042 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p871 := by
    rcases h5043 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p872 := by
    rcases h5044 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p873 := by
    rcases h5045 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p874 := by
    rcases h5046 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4964 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22495 (p789 p858 p867 p870 p871 p872 p873 p874 : Prop)
    (h5037 : p867 ∨ p870)
    (h5038 : p867 ∨ p871)
    (h5039 : p867 ∨ p872)
    (h5040 : p867 ∨ p873)
    (h5041 : p867 ∨ p874)
    (h4964 : p789 ∨ p858 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : p867 ∨ p858 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p867) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p858) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p870 := by
    rcases h5037 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p871 := by
    rcases h5038 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p872 := by
    rcases h5039 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p873 := by
    rcases h5040 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p874 := by
    rcases h5041 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4964 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22496 (p789 p858 p865 p866 p867 p868 p869 p870 p871 p872 p873 p874 : Prop)
    (h4939 : p789 ∨ p858 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869))
    (h5032 : p866 ∨ p870)
    (h5033 : p866 ∨ p871)
    (h5034 : p866 ∨ p872)
    (h5035 : p866 ∨ p873)
    (h5036 : p866 ∨ p874)
    (h4964 : p789 ∨ p858 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : (¬ p867) ∨ (¬ p865) ∨ p789 ∨ p858 ∨ (¬ p868) ∨ (¬ p869) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p867 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p865 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p789) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p858) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p868 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p869 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p866) := by
    rcases h4939 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p870 := by
    rcases h5032 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p871 := by
    rcases h5033 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p872 := by
    rcases h5034 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p873 := by
    rcases h5035 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p874 := by
    rcases h5036 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h4964 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22497 (p789 p858 p865 p867 p868 p869 : Prop)
    (h22492 : p865 ∨ p858 ∨ p789)
    (h22493 : p869 ∨ p858 ∨ p789)
    (h22494 : p868 ∨ p858 ∨ p789)
    (h22495 : p867 ∨ p858 ∨ p789)
    (h22496 : (¬ p867) ∨ (¬ p865) ∨ p789 ∨ p858 ∨ (¬ p868) ∨ (¬ p869)) : p858 ∨ p789 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p858) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p789) := fun hu => hn (Or.inr hu)
  have u2 : p865 := by
    rcases h22492 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p869 := by
    rcases h22493 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p868 := by
    rcases h22494 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p867 := by
    rcases h22495 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22496 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22499 (p857 p862 p866 p870 p871 p872 p873 p874 : Prop)
    (h5032 : p866 ∨ p870)
    (h5033 : p866 ∨ p871)
    (h5034 : p866 ∨ p872)
    (h5035 : p866 ∨ p873)
    (h5036 : p866 ∨ p874)
    (h4958 : p857 ∨ p862 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : p866 ∨ p857 ∨ p862 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p866) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p857) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p862) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p870 := by
    rcases h5032 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p871 := by
    rcases h5033 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p872 := by
    rcases h5034 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p873 := by
    rcases h5035 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p874 := by
    rcases h5036 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4958 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22500 (p857 p862 p865 p870 p871 p872 p873 p874 : Prop)
    (h5027 : p865 ∨ p870)
    (h5028 : p865 ∨ p871)
    (h5029 : p865 ∨ p872)
    (h5030 : p865 ∨ p873)
    (h5031 : p865 ∨ p874)
    (h4958 : p857 ∨ p862 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : p865 ∨ p857 ∨ p862 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p865) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p857) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p862) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p870 := by
    rcases h5027 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p871 := by
    rcases h5028 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p872 := by
    rcases h5029 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p873 := by
    rcases h5030 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p874 := by
    rcases h5031 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4958 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22501 (p857 p862 p869 p870 p871 p872 p873 p874 : Prop)
    (h5047 : p869 ∨ p870)
    (h5048 : p869 ∨ p871)
    (h5049 : p869 ∨ p872)
    (h5050 : p869 ∨ p873)
    (h5051 : p869 ∨ p874)
    (h4958 : p857 ∨ p862 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : p869 ∨ p857 ∨ p862 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p869) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p857) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p862) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p870 := by
    rcases h5047 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p871 := by
    rcases h5048 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p872 := by
    rcases h5049 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p873 := by
    rcases h5050 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p874 := by
    rcases h5051 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4958 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22502 (p857 p862 p868 p870 p871 p872 p873 p874 : Prop)
    (h5042 : p868 ∨ p870)
    (h5043 : p868 ∨ p871)
    (h5044 : p868 ∨ p872)
    (h5045 : p868 ∨ p873)
    (h5046 : p868 ∨ p874)
    (h4958 : p857 ∨ p862 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874)) : p868 ∨ p857 ∨ p862 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p868) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p857) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p862) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p870 := by
    rcases h5042 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p871 := by
    rcases h5043 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p872 := by
    rcases h5044 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p873 := by
    rcases h5045 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p874 := by
    rcases h5046 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4958 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22508 (p224 p237 p789 p835 p836 p839 p858 p980 p1333 : Prop)
    (h15381 : (¬ p224) ∨ (¬ p835) ∨ p858)
    (h22497 : p858 ∨ p789)
    (h22442 : p839 ∨ p835 ∨ p836)
    (h17443 : (¬ p237) ∨ (¬ p789) ∨ (¬ p839) ∨ (¬ p980) ∨ (¬ p1333)) : p858 ∨ (¬ p980) ∨ (¬ p1333) ∨ p836 ∨ (¬ p224) ∨ (¬ p237) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p858) := fun hu => hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p836) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p835) := by
    rcases h15381 with q0 | q1 | q2
    · exact False.elim (q0 u4)
    · exact q1
    · exact False.elim (u0 q2)
  have u7 : p789 := by
    rcases h22497 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u8 : p839 := by
    rcases h22442 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u3 q2)
  rcases h17443 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u7)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step22511 (p63 p85 p918 p926 p928 p983 p1074 p1095 p1096 p1116 : Prop)
    (h21470 : p926 ∨ p918)
    (h13519 : (¬ p926) ∨ (¬ p1074) ∨ (¬ p1116))
    (h22311 : p1074 ∨ p1095)
    (h22025 : p918 ∨ p928)
    (h18598 : (¬ p63) ∨ (¬ p928) ∨ (¬ p983) ∨ (¬ p1116))
    (h16629 : (¬ p85) ∨ (¬ p983) ∨ (¬ p1095) ∨ (¬ p1096))
    (h22211 : p85 ∨ p63) : (¬ p983) ∨ (¬ p1096) ∨ p918 ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p926 := by
    rcases h21470 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : (¬ p1074) := by
    rcases h13519 with q0 | q1 | q2
    · exact False.elim (q0 u4)
    · exact q1
    · exact False.elim (q2 u3)
  have u6 : p1095 := by
    rcases h22311 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u7 : p928 := by
    rcases h22025 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u8 : (¬ p63) := by
    rcases h18598 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u3)
  have u9 : (¬ p85) := by
    rcases h16629 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u1)
  rcases h22211 with q0 | q1
  · exact False.elim (u9 q0)
  · exact False.elim (u8 q1)

theorem step22515 (p38 p64 p69 p73 p74 p75 p76 p77 p78 p79 p80 p81 p82 : Prop)
    (h21805 : p77 ∨ p69 ∨ p38)
    (h21806 : p76 ∨ p69 ∨ p38)
    (h21807 : p75 ∨ p69 ∨ p38)
    (h21808 : p74 ∨ p69 ∨ p38)
    (h269 : p38 ∨ p64 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77))
    (h369 : p73 ∨ p78)
    (h370 : p73 ∨ p79)
    (h371 : p73 ∨ p80)
    (h372 : p73 ∨ p81)
    (h373 : p73 ∨ p82)
    (h304 : p38 ∨ p69 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p38 ∨ p64 ∨ p69 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p38) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p64) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p69) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p77 := by
    rcases h21805 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u0 q2)
  have u4 : p76 := by
    rcases h21806 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u0 q2)
  have u5 : p75 := by
    rcases h21807 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u0 q2)
  have u6 : p74 := by
    rcases h21808 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u0 q2)
  have u7 : (¬ p73) := by
    rcases h269 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact q2
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u3)
  have u8 : p78 := by
    rcases h369 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p79 := by
    rcases h370 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p80 := by
    rcases h371 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p81 := by
    rcases h372 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u12 : p82 := by
    rcases h373 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h304 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step22518 (p1385 p1391 p1400 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8469 : p1400 ∨ p1401)
    (h8470 : p1400 ∨ p1402)
    (h8471 : p1400 ∨ p1403)
    (h8472 : p1400 ∨ p1404)
    (h8473 : p1400 ∨ p1405)
    (h8384 : p1385 ∨ p1391 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : p1400 ∨ p1391 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1400) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1391) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1401 := by
    rcases h8469 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1402 := by
    rcases h8470 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1403 := by
    rcases h8471 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1404 := by
    rcases h8472 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1405 := by
    rcases h8473 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8384 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22519 (p1385 p1391 p1396 p1397 p1398 p1399 p1400 p1405 : Prop)
    (h22518 : p1400 ∨ p1391 ∨ p1385)
    (h8453 : p1396 ∨ p1405)
    (h8458 : p1397 ∨ p1405)
    (h8463 : p1398 ∨ p1405)
    (h8468 : p1399 ∨ p1405)
    (h8359 : p1385 ∨ p1391 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1405 ∨ p1391 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1405) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1391) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1400 := by
    rcases h22518 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1396 := by
    rcases h8453 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1397 := by
    rcases h8458 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1398 := by
    rcases h8463 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1399 := by
    rcases h8468 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22520 (p1385 p1391 p1396 p1397 p1398 p1399 p1400 p1404 : Prop)
    (h22518 : p1400 ∨ p1391 ∨ p1385)
    (h8452 : p1396 ∨ p1404)
    (h8457 : p1397 ∨ p1404)
    (h8462 : p1398 ∨ p1404)
    (h8467 : p1399 ∨ p1404)
    (h8359 : p1385 ∨ p1391 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1404 ∨ p1391 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1404) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1391) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1400 := by
    rcases h22518 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1396 := by
    rcases h8452 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1397 := by
    rcases h8457 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1398 := by
    rcases h8462 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1399 := by
    rcases h8467 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22521 (p1385 p1391 p1396 p1397 p1398 p1399 p1400 p1403 : Prop)
    (h22518 : p1400 ∨ p1391 ∨ p1385)
    (h8451 : p1396 ∨ p1403)
    (h8456 : p1397 ∨ p1403)
    (h8461 : p1398 ∨ p1403)
    (h8466 : p1399 ∨ p1403)
    (h8359 : p1385 ∨ p1391 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1403 ∨ p1391 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1403) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1391) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1400 := by
    rcases h22518 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1396 := by
    rcases h8451 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1397 := by
    rcases h8456 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1398 := by
    rcases h8461 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1399 := by
    rcases h8466 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22522 (p1385 p1391 p1396 p1397 p1398 p1399 p1400 p1402 : Prop)
    (h22518 : p1400 ∨ p1391 ∨ p1385)
    (h8450 : p1396 ∨ p1402)
    (h8455 : p1397 ∨ p1402)
    (h8460 : p1398 ∨ p1402)
    (h8465 : p1399 ∨ p1402)
    (h8359 : p1385 ∨ p1391 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1402 ∨ p1391 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1402) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1391) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1400 := by
    rcases h22518 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1396 := by
    rcases h8450 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1397 := by
    rcases h8455 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1398 := by
    rcases h8460 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1399 := by
    rcases h8465 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22523 (p1385 p1387 p1391 p1396 p1397 p1398 p1399 p1400 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h22518 : p1400 ∨ p1391 ∨ p1385)
    (h22519 : p1405 ∨ p1391 ∨ p1385)
    (h22520 : p1404 ∨ p1391 ∨ p1385)
    (h22521 : p1403 ∨ p1391 ∨ p1385)
    (h22522 : p1402 ∨ p1391 ∨ p1385)
    (h8374 : p1387 ∨ p1391 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405))
    (h8449 : p1396 ∨ p1401)
    (h8454 : p1397 ∨ p1401)
    (h8459 : p1398 ∨ p1401)
    (h8464 : p1399 ∨ p1401)
    (h8359 : p1385 ∨ p1391 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1391 ∨ p1387 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1391) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1400 := by
    rcases h22518 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p1405 := by
    rcases h22519 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p1404 := by
    rcases h22520 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p1403 := by
    rcases h22521 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : p1402 := by
    rcases h22522 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u8 : (¬ p1401) := by
    rcases h8374 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact q2
    · exact False.elim (q3 u7)
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u4)
  have u9 : p1396 := by
    rcases h8449 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u10 : p1397 := by
    rcases h8454 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u11 : p1398 := by
    rcases h8459 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u12 : p1399 := by
    rcases h8464 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h8359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u3)

theorem step22524 (p1249 p1274 p1276 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7682 : p1276 ∨ p1281)
    (h7683 : p1276 ∨ p1282)
    (h7684 : p1276 ∨ p1283)
    (h7685 : p1276 ∨ p1284)
    (h7686 : p1276 ∨ p1285)
    (h7620 : p1249 ∨ p1274 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1276 ∨ p1274 ∨ p1249 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1276) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1274) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1249) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7682 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7683 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7684 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7685 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7686 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7620 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22525 (p1249 p1274 p1280 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7702 : p1280 ∨ p1281)
    (h7703 : p1280 ∨ p1282)
    (h7704 : p1280 ∨ p1283)
    (h7705 : p1280 ∨ p1284)
    (h7706 : p1280 ∨ p1285)
    (h7620 : p1249 ∨ p1274 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1280 ∨ p1274 ∨ p1249 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1280) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1274) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1249) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7702 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7703 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7704 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7705 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7706 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7620 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22526 (p1249 p1274 p1279 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7697 : p1279 ∨ p1281)
    (h7698 : p1279 ∨ p1282)
    (h7699 : p1279 ∨ p1283)
    (h7700 : p1279 ∨ p1284)
    (h7701 : p1279 ∨ p1285)
    (h7620 : p1249 ∨ p1274 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1279 ∨ p1274 ∨ p1249 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1279) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1274) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1249) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7697 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7698 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7699 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7700 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7701 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7620 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22527 (p1249 p1274 p1278 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7692 : p1278 ∨ p1281)
    (h7693 : p1278 ∨ p1282)
    (h7694 : p1278 ∨ p1283)
    (h7695 : p1278 ∨ p1284)
    (h7696 : p1278 ∨ p1285)
    (h7620 : p1249 ∨ p1274 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1278 ∨ p1274 ∨ p1249 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1278) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1274) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1249) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7692 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7693 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7694 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7695 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7696 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7620 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22529 (p1096 p1097 p1105 p1110 p1111 p1112 p1113 p1114 : Prop)
    (h6579 : p1105 ∨ p1110)
    (h6580 : p1105 ∨ p1111)
    (h6581 : p1105 ∨ p1112)
    (h6582 : p1105 ∨ p1113)
    (h6583 : p1105 ∨ p1114)
    (h6506 : p1096 ∨ p1097 ∨ (¬ p1110) ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113) ∨ (¬ p1114)) : p1105 ∨ p1097 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1105) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1097) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1110 := by
    rcases h6579 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1111 := by
    rcases h6580 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1112 := by
    rcases h6581 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1113 := by
    rcases h6582 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1114 := by
    rcases h6583 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6506 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22530 (p1096 p1097 p1109 p1110 p1111 p1112 p1113 p1114 : Prop)
    (h6599 : p1109 ∨ p1110)
    (h6600 : p1109 ∨ p1111)
    (h6601 : p1109 ∨ p1112)
    (h6602 : p1109 ∨ p1113)
    (h6603 : p1109 ∨ p1114)
    (h6506 : p1096 ∨ p1097 ∨ (¬ p1110) ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113) ∨ (¬ p1114)) : p1109 ∨ p1097 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1109) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1097) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1110 := by
    rcases h6599 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1111 := by
    rcases h6600 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1112 := by
    rcases h6601 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1113 := by
    rcases h6602 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1114 := by
    rcases h6603 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6506 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22531 (p1096 p1097 p1108 p1110 p1111 p1112 p1113 p1114 : Prop)
    (h6594 : p1108 ∨ p1110)
    (h6595 : p1108 ∨ p1111)
    (h6596 : p1108 ∨ p1112)
    (h6597 : p1108 ∨ p1113)
    (h6598 : p1108 ∨ p1114)
    (h6506 : p1096 ∨ p1097 ∨ (¬ p1110) ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113) ∨ (¬ p1114)) : p1108 ∨ p1097 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1108) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1097) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1110 := by
    rcases h6594 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1111 := by
    rcases h6595 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1112 := by
    rcases h6596 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1113 := by
    rcases h6597 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1114 := by
    rcases h6598 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6506 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22532 (p1096 p1097 p1107 p1110 p1111 p1112 p1113 p1114 : Prop)
    (h6589 : p1107 ∨ p1110)
    (h6590 : p1107 ∨ p1111)
    (h6591 : p1107 ∨ p1112)
    (h6592 : p1107 ∨ p1113)
    (h6593 : p1107 ∨ p1114)
    (h6506 : p1096 ∨ p1097 ∨ (¬ p1110) ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113) ∨ (¬ p1114)) : p1107 ∨ p1097 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1107) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1097) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1110 := by
    rcases h6589 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1111 := by
    rcases h6590 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1112 := by
    rcases h6591 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1113 := by
    rcases h6592 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1114 := by
    rcases h6593 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6506 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22533 (p1096 p1097 p1105 p1106 p1107 p1108 p1109 p1110 p1111 p1112 p1113 p1114 : Prop)
    (h6481 : p1096 ∨ p1097 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109))
    (h6584 : p1106 ∨ p1110)
    (h6585 : p1106 ∨ p1111)
    (h6586 : p1106 ∨ p1112)
    (h6587 : p1106 ∨ p1113)
    (h6588 : p1106 ∨ p1114)
    (h6506 : p1096 ∨ p1097 ∨ (¬ p1110) ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113) ∨ (¬ p1114)) : (¬ p1107) ∨ (¬ p1105) ∨ p1096 ∨ p1097 ∨ (¬ p1108) ∨ (¬ p1109) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1096) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1097) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1106) := by
    rcases h6481 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p1110 := by
    rcases h6584 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1111 := by
    rcases h6585 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1112 := by
    rcases h6586 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1113 := by
    rcases h6587 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1114 := by
    rcases h6588 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h6506 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22534 (p1096 p1097 p1105 p1107 p1108 p1109 : Prop)
    (h22529 : p1105 ∨ p1097 ∨ p1096)
    (h22530 : p1109 ∨ p1097 ∨ p1096)
    (h22531 : p1108 ∨ p1097 ∨ p1096)
    (h22532 : p1107 ∨ p1097 ∨ p1096)
    (h22533 : (¬ p1107) ∨ (¬ p1105) ∨ p1096 ∨ p1097 ∨ (¬ p1108) ∨ (¬ p1109)) : p1097 ∨ p1096 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1097) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1096) := fun hu => hn (Or.inr hu)
  have u2 : p1105 := by
    rcases h22529 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1109 := by
    rcases h22530 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1108 := by
    rcases h22531 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1107 := by
    rcases h22532 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22533 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22535 (p1289 p1293 p1300 p1301 p1302 p1303 p1304 p1305 : Prop)
    (h7830 : p1300 ∨ p1301)
    (h7831 : p1300 ∨ p1302)
    (h7832 : p1300 ∨ p1303)
    (h7833 : p1300 ∨ p1304)
    (h7834 : p1300 ∨ p1305)
    (h7741 : p1289 ∨ p1293 ∨ (¬ p1301) ∨ (¬ p1302) ∨ (¬ p1303) ∨ (¬ p1304) ∨ (¬ p1305)) : p1300 ∨ p1289 ∨ p1293 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1300) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1289) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1293) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1301 := by
    rcases h7830 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1302 := by
    rcases h7831 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1303 := by
    rcases h7832 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1304 := by
    rcases h7833 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1305 := by
    rcases h7834 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7741 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22536 (p1289 p1293 p1299 p1301 p1302 p1303 p1304 p1305 : Prop)
    (h7825 : p1299 ∨ p1301)
    (h7826 : p1299 ∨ p1302)
    (h7827 : p1299 ∨ p1303)
    (h7828 : p1299 ∨ p1304)
    (h7829 : p1299 ∨ p1305)
    (h7741 : p1289 ∨ p1293 ∨ (¬ p1301) ∨ (¬ p1302) ∨ (¬ p1303) ∨ (¬ p1304) ∨ (¬ p1305)) : p1299 ∨ p1289 ∨ p1293 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1299) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1289) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1293) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1301 := by
    rcases h7825 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1302 := by
    rcases h7826 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1303 := by
    rcases h7827 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1304 := by
    rcases h7828 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1305 := by
    rcases h7829 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7741 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22537 (p1289 p1293 p1298 p1301 p1302 p1303 p1304 p1305 : Prop)
    (h7820 : p1298 ∨ p1301)
    (h7821 : p1298 ∨ p1302)
    (h7822 : p1298 ∨ p1303)
    (h7823 : p1298 ∨ p1304)
    (h7824 : p1298 ∨ p1305)
    (h7741 : p1289 ∨ p1293 ∨ (¬ p1301) ∨ (¬ p1302) ∨ (¬ p1303) ∨ (¬ p1304) ∨ (¬ p1305)) : p1298 ∨ p1289 ∨ p1293 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1298) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1289) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1293) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1301 := by
    rcases h7820 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1302 := by
    rcases h7821 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1303 := by
    rcases h7822 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1304 := by
    rcases h7823 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1305 := by
    rcases h7824 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7741 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22538 (p1289 p1293 p1297 p1301 p1302 p1303 p1304 p1305 : Prop)
    (h7815 : p1297 ∨ p1301)
    (h7816 : p1297 ∨ p1302)
    (h7817 : p1297 ∨ p1303)
    (h7818 : p1297 ∨ p1304)
    (h7819 : p1297 ∨ p1305)
    (h7741 : p1289 ∨ p1293 ∨ (¬ p1301) ∨ (¬ p1302) ∨ (¬ p1303) ∨ (¬ p1304) ∨ (¬ p1305)) : p1297 ∨ p1289 ∨ p1293 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1297) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1289) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1293) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1301 := by
    rcases h7815 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1302 := by
    rcases h7816 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1303 := by
    rcases h7817 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1304 := by
    rcases h7818 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1305 := by
    rcases h7819 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7741 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22539 (p1289 p1293 p1296 p1301 p1302 p1303 p1304 p1305 : Prop)
    (h7810 : p1296 ∨ p1301)
    (h7811 : p1296 ∨ p1302)
    (h7812 : p1296 ∨ p1303)
    (h7813 : p1296 ∨ p1304)
    (h7814 : p1296 ∨ p1305)
    (h7741 : p1289 ∨ p1293 ∨ (¬ p1301) ∨ (¬ p1302) ∨ (¬ p1303) ∨ (¬ p1304) ∨ (¬ p1305)) : p1296 ∨ p1289 ∨ p1293 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1296) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1289) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1293) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1301 := by
    rcases h7810 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1302 := by
    rcases h7811 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1303 := by
    rcases h7812 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1304 := by
    rcases h7813 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1305 := by
    rcases h7814 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7741 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22540 (p1289 p1293 p1296 p1297 p1298 p1299 p1300 : Prop)
    (h22535 : p1300 ∨ p1289 ∨ p1293)
    (h22536 : p1299 ∨ p1289 ∨ p1293)
    (h22537 : p1298 ∨ p1289 ∨ p1293)
    (h22538 : p1297 ∨ p1289 ∨ p1293)
    (h22539 : p1296 ∨ p1289 ∨ p1293)
    (h7716 : p1289 ∨ p1293 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : p1289 ∨ p1293 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1289) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1293) := fun hu => hn (Or.inr hu)
  have u2 : p1300 := by
    rcases h22535 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1299 := by
    rcases h22536 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1298 := by
    rcases h22537 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1297 := by
    rcases h22538 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1296 := by
    rcases h22539 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h7716 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u2)

theorem step22543 (p2 p5 p63 p224 p419 p657 p665 p666 p928 p1116 : Prop)
    (h17977 : (¬ p2) ∨ (¬ p5) ∨ (¬ p63) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p928) ∨ (¬ p1116))
    (h22434 : (¬ p928) ∨ (¬ p666) ∨ (¬ p63) ∨ (¬ p419) ∨ (¬ p5) ∨ (¬ p1116) ∨ (¬ p2))
    (h22069 : p665 ∨ p657)
    (h22413 : p666 ∨ p224)
    (h6747 : (¬ p224) ∨ (¬ p657)) : (¬ p63) ∨ (¬ p928) ∨ (¬ p2) ∨ (¬ p5) ∨ (¬ p419) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p665) := by
    rcases h17977 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u4)
    · exact q4
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u5)
  have u7 : (¬ p666) := by
    rcases h22434 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u2)
  have u8 : p657 := by
    rcases h22069 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p224 := by
    rcases h22413 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h6747 with q0 | q1
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u8)

theorem step22544 (p2 p15 p64 p69 p86 p234 p237 p419 p1044 p1116 p1141 p1187 : Prop)
    (h21316 : p64 ∨ p15)
    (h21946 : p69 ∨ p15)
    (h18821 : (¬ p2) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p234) ∨ (¬ p237) ∨ (¬ p1044) ∨ (¬ p1116) ∨ (¬ p1141))
    (h22225 : (¬ p419) ∨ (¬ p237) ∨ (¬ p86) ∨ (¬ p1187) ∨ (¬ p1116) ∨ (¬ p69))
    (h21531 : p1187 ∨ p234) : p15 ∨ (¬ p1141) ∨ (¬ p86) ∨ (¬ p419) ∨ (¬ p1044) ∨ (¬ p1116) ∨ (¬ p237) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p15) := fun hu => hn (Or.inl hu)
  have u1 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p64 := by
    rcases h21316 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p69 := by
    rcases h21946 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u10 : (¬ p234) := by
    rcases h18821 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u8)
    · exact False.elim (q2 u2)
    · exact q3
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
    · exact False.elim (q7 u1)
  have u11 : (¬ p1187) := by
    rcases h22225 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u6)
    · exact False.elim (q2 u2)
    · exact q3
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u9)
  rcases h21531 with q0 | q1
  · exact False.elim (u11 q0)
  · exact False.elim (u10 q1)

theorem step22545 (p15 p41 p47 p85 p1249 p1250 p1251 : Prop)
    (h11730 : (¬ p41) ∨ (¬ p1249) ∨ (¬ p1250))
    (h16301 : (¬ p15) ∨ (¬ p47) ∨ (¬ p85) ∨ (¬ p1249) ∨ (¬ p1251))
    (h22056 : p1251 ∨ p1250) : (¬ p1249) ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p47) ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p1250) := by
    rcases h11730 with q0 | q1 | q2
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u0)
    · exact q2
  have u6 : (¬ p1251) := by
    rcases h16301 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u0)
    · exact q4
  rcases h22056 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step22546 (p476 p481 p488 p489 p490 p491 p492 p493 : Prop)
    (h2722 : p488 ∨ p489)
    (h2723 : p488 ∨ p490)
    (h2724 : p488 ∨ p491)
    (h2725 : p488 ∨ p492)
    (h2726 : p488 ∨ p493)
    (h2634 : p476 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p488 ∨ p476 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p488) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p476) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p481) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p489 := by
    rcases h2722 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p490 := by
    rcases h2723 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p491 := by
    rcases h2724 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p492 := by
    rcases h2725 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p493 := by
    rcases h2726 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2634 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22547 (p476 p481 p487 p489 p490 p491 p492 p493 : Prop)
    (h2717 : p487 ∨ p489)
    (h2718 : p487 ∨ p490)
    (h2719 : p487 ∨ p491)
    (h2720 : p487 ∨ p492)
    (h2721 : p487 ∨ p493)
    (h2634 : p476 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p487 ∨ p476 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p487) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p476) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p481) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p489 := by
    rcases h2717 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p490 := by
    rcases h2718 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p491 := by
    rcases h2719 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p492 := by
    rcases h2720 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p493 := by
    rcases h2721 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2634 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22548 (p476 p481 p486 p489 p490 p491 p492 p493 : Prop)
    (h2712 : p486 ∨ p489)
    (h2713 : p486 ∨ p490)
    (h2714 : p486 ∨ p491)
    (h2715 : p486 ∨ p492)
    (h2716 : p486 ∨ p493)
    (h2634 : p476 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p486 ∨ p476 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p486) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p476) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p481) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p489 := by
    rcases h2712 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p490 := by
    rcases h2713 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p491 := by
    rcases h2714 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p492 := by
    rcases h2715 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p493 := by
    rcases h2716 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2634 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22549 (p476 p481 p485 p489 p490 p491 p492 p493 : Prop)
    (h2707 : p485 ∨ p489)
    (h2708 : p485 ∨ p490)
    (h2709 : p485 ∨ p491)
    (h2710 : p485 ∨ p492)
    (h2711 : p485 ∨ p493)
    (h2634 : p476 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : p485 ∨ p476 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p485) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p476) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p481) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p489 := by
    rcases h2707 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p490 := by
    rcases h2708 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p491 := by
    rcases h2709 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p492 := by
    rcases h2710 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p493 := by
    rcases h2711 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2634 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22550 (p476 p481 p484 p485 p486 p487 p488 p489 p490 p491 p492 p493 : Prop)
    (h2609 : p476 ∨ p481 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488))
    (h2702 : p484 ∨ p489)
    (h2703 : p484 ∨ p490)
    (h2704 : p484 ∨ p491)
    (h2705 : p484 ∨ p492)
    (h2706 : p484 ∨ p493)
    (h2634 : p476 ∨ p481 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493)) : (¬ p485) ∨ (¬ p488) ∨ p476 ∨ p481 ∨ (¬ p486) ∨ (¬ p487) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p485 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p488 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p476) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p481) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p486 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p487 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p484) := by
    rcases h2609 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p489 := by
    rcases h2702 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p490 := by
    rcases h2703 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p491 := by
    rcases h2704 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p492 := by
    rcases h2705 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p493 := by
    rcases h2706 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h2634 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22551 (p476 p481 p485 p486 p487 p488 : Prop)
    (h22546 : p488 ∨ p476 ∨ p481)
    (h22547 : p487 ∨ p476 ∨ p481)
    (h22548 : p486 ∨ p476 ∨ p481)
    (h22549 : p485 ∨ p476 ∨ p481)
    (h22550 : (¬ p485) ∨ (¬ p488) ∨ p476 ∨ p481 ∨ (¬ p486) ∨ (¬ p487)) : p476 ∨ p481 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p476) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p481) := fun hu => hn (Or.inr hu)
  have u2 : p488 := by
    rcases h22546 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p487 := by
    rcases h22547 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p486 := by
    rcases h22548 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p485 := by
    rcases h22549 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22550 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22555 (p344 p346 p356 p357 p358 p359 p360 p361 : Prop)
    (h1945 : p356 ∨ p357)
    (h1946 : p356 ∨ p358)
    (h1947 : p356 ∨ p359)
    (h1948 : p356 ∨ p360)
    (h1949 : p356 ∨ p361)
    (h1862 : p344 ∨ p346 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p356 ∨ p346 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p356) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p346) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p357 := by
    rcases h1945 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p358 := by
    rcases h1946 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p359 := by
    rcases h1947 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p360 := by
    rcases h1948 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p361 := by
    rcases h1949 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1862 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22556 (p344 p346 p355 p357 p358 p359 p360 p361 : Prop)
    (h1940 : p355 ∨ p357)
    (h1941 : p355 ∨ p358)
    (h1942 : p355 ∨ p359)
    (h1943 : p355 ∨ p360)
    (h1944 : p355 ∨ p361)
    (h1862 : p344 ∨ p346 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p355 ∨ p346 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p355) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p346) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p357 := by
    rcases h1940 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p358 := by
    rcases h1941 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p359 := by
    rcases h1942 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p360 := by
    rcases h1943 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p361 := by
    rcases h1944 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1862 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22557 (p344 p346 p354 p357 p358 p359 p360 p361 : Prop)
    (h1935 : p354 ∨ p357)
    (h1936 : p354 ∨ p358)
    (h1937 : p354 ∨ p359)
    (h1938 : p354 ∨ p360)
    (h1939 : p354 ∨ p361)
    (h1862 : p344 ∨ p346 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p354 ∨ p346 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p354) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p346) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p357 := by
    rcases h1935 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p358 := by
    rcases h1936 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p359 := by
    rcases h1937 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p360 := by
    rcases h1938 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p361 := by
    rcases h1939 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1862 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22558 (p344 p346 p353 p357 p358 p359 p360 p361 : Prop)
    (h1930 : p353 ∨ p357)
    (h1931 : p353 ∨ p358)
    (h1932 : p353 ∨ p359)
    (h1933 : p353 ∨ p360)
    (h1934 : p353 ∨ p361)
    (h1862 : p344 ∨ p346 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p353 ∨ p346 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p353) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p346) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p357 := by
    rcases h1930 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p358 := by
    rcases h1931 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p359 := by
    rcases h1932 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p360 := by
    rcases h1933 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p361 := by
    rcases h1934 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1862 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22559 (p344 p346 p352 p353 p354 p355 p356 p357 p358 p359 p360 p361 : Prop)
    (h1837 : p344 ∨ p346 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356))
    (h1925 : p352 ∨ p357)
    (h1926 : p352 ∨ p358)
    (h1927 : p352 ∨ p359)
    (h1928 : p352 ∨ p360)
    (h1929 : p352 ∨ p361)
    (h1862 : p344 ∨ p346 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : (¬ p353) ∨ (¬ p356) ∨ (¬ p354) ∨ p346 ∨ p344 ∨ (¬ p355) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p353 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p356 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p354 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p346) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p355 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p352) := by
    rcases h1837 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u2)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p357 := by
    rcases h1925 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p358 := by
    rcases h1926 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p359 := by
    rcases h1927 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p360 := by
    rcases h1928 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p361 := by
    rcases h1929 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1862 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22560 (p344 p346 p353 p354 p355 p356 : Prop)
    (h22555 : p356 ∨ p346 ∨ p344)
    (h22556 : p355 ∨ p346 ∨ p344)
    (h22557 : p354 ∨ p346 ∨ p344)
    (h22558 : p353 ∨ p346 ∨ p344)
    (h22559 : (¬ p353) ∨ (¬ p356) ∨ (¬ p354) ∨ p346 ∨ p344 ∨ (¬ p355)) : p346 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p346) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr hu)
  have u2 : p356 := by
    rcases h22555 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p355 := by
    rcases h22556 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p354 := by
    rcases h22557 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p353 := by
    rcases h22558 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22559 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (u0 q3)
  · exact False.elim (u1 q4)
  · exact False.elim (q5 u3)

theorem step22561 (p4 p344 p352 p357 p358 p359 p360 p361 : Prop)
    (h1925 : p352 ∨ p357)
    (h1926 : p352 ∨ p358)
    (h1927 : p352 ∨ p359)
    (h1928 : p352 ∨ p360)
    (h1929 : p352 ∨ p361)
    (h1857 : p4 ∨ p344 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p352 ∨ p4 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p352) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p4) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p357 := by
    rcases h1925 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p358 := by
    rcases h1926 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p359 := by
    rcases h1927 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p360 := by
    rcases h1928 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p361 := by
    rcases h1929 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1857 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22562 (p4 p344 p356 p357 p358 p359 p360 p361 : Prop)
    (h1945 : p356 ∨ p357)
    (h1946 : p356 ∨ p358)
    (h1947 : p356 ∨ p359)
    (h1948 : p356 ∨ p360)
    (h1949 : p356 ∨ p361)
    (h1857 : p4 ∨ p344 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p356 ∨ p4 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p356) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p4) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p357 := by
    rcases h1945 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p358 := by
    rcases h1946 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p359 := by
    rcases h1947 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p360 := by
    rcases h1948 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p361 := by
    rcases h1949 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1857 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22563 (p4 p344 p355 p357 p358 p359 p360 p361 : Prop)
    (h1940 : p355 ∨ p357)
    (h1941 : p355 ∨ p358)
    (h1942 : p355 ∨ p359)
    (h1943 : p355 ∨ p360)
    (h1944 : p355 ∨ p361)
    (h1857 : p4 ∨ p344 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p355 ∨ p4 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p355) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p4) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p357 := by
    rcases h1940 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p358 := by
    rcases h1941 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p359 := by
    rcases h1942 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p360 := by
    rcases h1943 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p361 := by
    rcases h1944 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1857 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22564 (p4 p344 p354 p357 p358 p359 p360 p361 : Prop)
    (h1935 : p354 ∨ p357)
    (h1936 : p354 ∨ p358)
    (h1937 : p354 ∨ p359)
    (h1938 : p354 ∨ p360)
    (h1939 : p354 ∨ p361)
    (h1857 : p4 ∨ p344 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p354 ∨ p4 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p354) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p4) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p357 := by
    rcases h1935 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p358 := by
    rcases h1936 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p359 := by
    rcases h1937 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p360 := by
    rcases h1938 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p361 := by
    rcases h1939 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1857 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22565 (p4 p344 p352 p353 p354 p355 p356 p357 p358 p359 p360 p361 : Prop)
    (h1832 : p4 ∨ p344 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356))
    (h1930 : p353 ∨ p357)
    (h1931 : p353 ∨ p358)
    (h1932 : p353 ∨ p359)
    (h1933 : p353 ∨ p360)
    (h1934 : p353 ∨ p361)
    (h1857 : p4 ∨ p344 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : (¬ p354) ∨ (¬ p352) ∨ p344 ∨ p4 ∨ (¬ p355) ∨ (¬ p356) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p354 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p352 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p4) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p355 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p356 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p353) := by
    rcases h1832 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p357 := by
    rcases h1930 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p358 := by
    rcases h1931 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p359 := by
    rcases h1932 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p360 := by
    rcases h1933 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p361 := by
    rcases h1934 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1857 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22566 (p4 p344 p352 p354 p355 p356 : Prop)
    (h22561 : p352 ∨ p4 ∨ p344)
    (h22562 : p356 ∨ p4 ∨ p344)
    (h22563 : p355 ∨ p4 ∨ p344)
    (h22564 : p354 ∨ p4 ∨ p344)
    (h22565 : (¬ p354) ∨ (¬ p352) ∨ p344 ∨ p4 ∨ (¬ p355) ∨ (¬ p356)) : p4 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p4) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr hu)
  have u2 : p352 := by
    rcases h22561 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p356 := by
    rcases h22562 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p355 := by
    rcases h22563 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p354 := by
    rcases h22564 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22565 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22567 (p420 p596 p604 p609 p610 p611 p612 p613 : Prop)
    (h3465 : p604 ∨ p609)
    (h3466 : p604 ∨ p610)
    (h3467 : p604 ∨ p611)
    (h3468 : p604 ∨ p612)
    (h3469 : p604 ∨ p613)
    (h3400 : p420 ∨ p596 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p604 ∨ p596 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p604) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p596) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3465 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3466 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3467 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3468 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3469 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3400 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22568 (p420 p596 p608 p609 p610 p611 p612 p613 : Prop)
    (h3485 : p608 ∨ p609)
    (h3486 : p608 ∨ p610)
    (h3487 : p608 ∨ p611)
    (h3488 : p608 ∨ p612)
    (h3489 : p608 ∨ p613)
    (h3400 : p420 ∨ p596 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p608 ∨ p596 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p608) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p596) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3485 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3486 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3487 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3488 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3489 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3400 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22569 (p420 p596 p607 p609 p610 p611 p612 p613 : Prop)
    (h3480 : p607 ∨ p609)
    (h3481 : p607 ∨ p610)
    (h3482 : p607 ∨ p611)
    (h3483 : p607 ∨ p612)
    (h3484 : p607 ∨ p613)
    (h3400 : p420 ∨ p596 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p607 ∨ p596 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p607) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p596) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3480 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3481 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3482 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3483 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3484 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3400 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22570 (p420 p596 p606 p609 p610 p611 p612 p613 : Prop)
    (h3475 : p606 ∨ p609)
    (h3476 : p606 ∨ p610)
    (h3477 : p606 ∨ p611)
    (h3478 : p606 ∨ p612)
    (h3479 : p606 ∨ p613)
    (h3400 : p420 ∨ p596 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p606 ∨ p596 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p606) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p596) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3475 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3476 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3477 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3478 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3479 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3400 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22571 (p420 p596 p604 p605 p606 p607 p608 p609 p610 p611 p612 p613 : Prop)
    (h3375 : p420 ∨ p596 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608))
    (h3470 : p605 ∨ p609)
    (h3471 : p605 ∨ p610)
    (h3472 : p605 ∨ p611)
    (h3473 : p605 ∨ p612)
    (h3474 : p605 ∨ p613)
    (h3400 : p420 ∨ p596 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : (¬ p606) ∨ p596 ∨ p420 ∨ (¬ p607) ∨ (¬ p608) ∨ (¬ p604) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p606 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p596) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p607 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p608 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p605) := by
    rcases h3375 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u4)
  have u7 : p609 := by
    rcases h3470 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p610 := by
    rcases h3471 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p611 := by
    rcases h3472 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p612 := by
    rcases h3473 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p613 := by
    rcases h3474 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3400 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22572 (p420 p596 p604 p606 p607 p608 : Prop)
    (h22567 : p604 ∨ p596 ∨ p420)
    (h22568 : p608 ∨ p596 ∨ p420)
    (h22569 : p607 ∨ p596 ∨ p420)
    (h22570 : p606 ∨ p596 ∨ p420)
    (h22571 : (¬ p606) ∨ p596 ∨ p420 ∨ (¬ p607) ∨ (¬ p608) ∨ (¬ p604)) : p596 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p596) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p420) := fun hu => hn (Or.inr hu)
  have u2 : p604 := by
    rcases h22567 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p608 := by
    rcases h22568 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p607 := by
    rcases h22569 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p606 := by
    rcases h22570 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22571 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step22573 (p656 p680 p720 p721 p722 p723 p724 p725 : Prop)
    (h4144 : p720 ∨ p721)
    (h4145 : p720 ∨ p722)
    (h4146 : p720 ∨ p723)
    (h4147 : p720 ∨ p724)
    (h4148 : p720 ∨ p725)
    (h4055 : p656 ∨ p680 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : p720 ∨ p680 ∨ p656 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p720) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p680) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p656) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p721 := by
    rcases h4144 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p722 := by
    rcases h4145 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p723 := by
    rcases h4146 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p724 := by
    rcases h4147 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p725 := by
    rcases h4148 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4055 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22574 (p656 p680 p719 p721 p722 p723 p724 p725 : Prop)
    (h4139 : p719 ∨ p721)
    (h4140 : p719 ∨ p722)
    (h4141 : p719 ∨ p723)
    (h4142 : p719 ∨ p724)
    (h4143 : p719 ∨ p725)
    (h4055 : p656 ∨ p680 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : p719 ∨ p680 ∨ p656 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p719) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p680) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p656) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p721 := by
    rcases h4139 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p722 := by
    rcases h4140 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p723 := by
    rcases h4141 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p724 := by
    rcases h4142 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p725 := by
    rcases h4143 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4055 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22575 (p656 p680 p718 p721 p722 p723 p724 p725 : Prop)
    (h4134 : p718 ∨ p721)
    (h4135 : p718 ∨ p722)
    (h4136 : p718 ∨ p723)
    (h4137 : p718 ∨ p724)
    (h4138 : p718 ∨ p725)
    (h4055 : p656 ∨ p680 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : p718 ∨ p680 ∨ p656 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p718) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p680) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p656) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p721 := by
    rcases h4134 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p722 := by
    rcases h4135 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p723 := by
    rcases h4136 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p724 := by
    rcases h4137 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p725 := by
    rcases h4138 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4055 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22576 (p656 p680 p717 p721 p722 p723 p724 p725 : Prop)
    (h4129 : p717 ∨ p721)
    (h4130 : p717 ∨ p722)
    (h4131 : p717 ∨ p723)
    (h4132 : p717 ∨ p724)
    (h4133 : p717 ∨ p725)
    (h4055 : p656 ∨ p680 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : p717 ∨ p680 ∨ p656 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p717) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p680) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p656) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p721 := by
    rcases h4129 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p722 := by
    rcases h4130 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p723 := by
    rcases h4131 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p724 := by
    rcases h4132 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p725 := by
    rcases h4133 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4055 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22578 (p41 p237 p657 p858 p918 p1385 : Prop)
    (h22352 : p1385 ∨ (¬ p918) ∨ (¬ p237) ∨ (¬ p657))
    (h19748 : (¬ p41) ∨ (¬ p657) ∨ (¬ p858) ∨ (¬ p1385)) : (¬ p657) ∨ (¬ p858) ∨ (¬ p41) ∨ (¬ p918) ∨ (¬ p237) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1385 := by
    rcases h22352 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u0)
  rcases h19748 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)

theorem step22579 (p110 p346 p557 p656 p680 p687 p710 p716 p717 p718 p719 p720 p721 p722 p723 p724 p725 p734 : Prop)
    (h12634 : (¬ p656) ∨ (¬ p687) ∨ (¬ p734))
    (h17519 : (¬ p110) ∨ (¬ p346) ∨ (¬ p557) ∨ (¬ p680) ∨ (¬ p687) ∨ (¬ p734))
    (h22573 : p720 ∨ p680 ∨ p656)
    (h22574 : p719 ∨ p680 ∨ p656)
    (h22575 : p718 ∨ p680 ∨ p656)
    (h22576 : p717 ∨ p680 ∨ p656)
    (h4035 : p680 ∨ p710 ∨ (¬ p716) ∨ (¬ p717) ∨ (¬ p718) ∨ (¬ p719) ∨ (¬ p720))
    (h4124 : p716 ∨ p721)
    (h4125 : p716 ∨ p722)
    (h4126 : p716 ∨ p723)
    (h4127 : p716 ∨ p724)
    (h4128 : p716 ∨ p725)
    (h4055 : p656 ∨ p680 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : (¬ p687) ∨ (¬ p734) ∨ (¬ p346) ∨ (¬ p110) ∨ p710 ∨ (¬ p557) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p710) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p656) := by
    rcases h12634 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u1)
  have u7 : (¬ p680) := by
    rcases h17519 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u1)
  have u8 : p720 := by
    rcases h22573 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u6 q2)
  have u9 : p719 := by
    rcases h22574 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u6 q2)
  have u10 : p718 := by
    rcases h22575 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u6 q2)
  have u11 : p717 := by
    rcases h22576 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (u6 q2)
  have u12 : (¬ p716) := by
    rcases h4035 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u7 q0)
    · exact False.elim (u4 q1)
    · exact q2
    · exact False.elim (q3 u11)
    · exact False.elim (q4 u10)
    · exact False.elim (q5 u9)
    · exact False.elim (q6 u8)
  have u13 : p721 := by
    rcases h4124 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  have u14 : p722 := by
    rcases h4125 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  have u15 : p723 := by
    rcases h4126 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  have u16 : p724 := by
    rcases h4127 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  have u17 : p725 := by
    rcases h4128 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  rcases h4055 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u13)
  · exact False.elim (q3 u14)
  · exact False.elim (q4 u15)
  · exact False.elim (q5 u16)
  · exact False.elim (q6 u17)

theorem step22588 (p13 p1076 p1089 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6470 : p1089 ∨ p1090)
    (h6471 : p1089 ∨ p1091)
    (h6472 : p1089 ∨ p1092)
    (h6473 : p1089 ∨ p1093)
    (h6474 : p1089 ∨ p1094)
    (h6389 : p13 ∨ p1076 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1089 ∨ p1076 ∨ p13 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1089) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p13) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1090 := by
    rcases h6470 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1091 := by
    rcases h6471 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1092 := by
    rcases h6472 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1093 := by
    rcases h6473 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1094 := by
    rcases h6474 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6389 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22589 (p13 p1076 p1088 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6465 : p1088 ∨ p1090)
    (h6466 : p1088 ∨ p1091)
    (h6467 : p1088 ∨ p1092)
    (h6468 : p1088 ∨ p1093)
    (h6469 : p1088 ∨ p1094)
    (h6389 : p13 ∨ p1076 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1088 ∨ p1076 ∨ p13 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1088) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p13) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1090 := by
    rcases h6465 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1091 := by
    rcases h6466 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1092 := by
    rcases h6467 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1093 := by
    rcases h6468 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1094 := by
    rcases h6469 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6389 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22590 (p13 p1076 p1087 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6460 : p1087 ∨ p1090)
    (h6461 : p1087 ∨ p1091)
    (h6462 : p1087 ∨ p1092)
    (h6463 : p1087 ∨ p1093)
    (h6464 : p1087 ∨ p1094)
    (h6389 : p13 ∨ p1076 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1087 ∨ p1076 ∨ p13 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1087) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p13) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1090 := by
    rcases h6460 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1091 := by
    rcases h6461 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1092 := by
    rcases h6462 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1093 := by
    rcases h6463 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1094 := by
    rcases h6464 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6389 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22591 (p13 p1076 p1086 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6455 : p1086 ∨ p1090)
    (h6456 : p1086 ∨ p1091)
    (h6457 : p1086 ∨ p1092)
    (h6458 : p1086 ∨ p1093)
    (h6459 : p1086 ∨ p1094)
    (h6389 : p13 ∨ p1076 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1086 ∨ p1076 ∨ p13 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1086) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p13) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1090 := by
    rcases h6455 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1091 := by
    rcases h6456 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1092 := by
    rcases h6457 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1093 := by
    rcases h6458 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1094 := by
    rcases h6459 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6389 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22592 (p13 p1076 p1085 p1086 p1087 p1088 p1089 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6364 : p13 ∨ p1076 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089))
    (h6450 : p1085 ∨ p1090)
    (h6451 : p1085 ∨ p1091)
    (h6452 : p1085 ∨ p1092)
    (h6453 : p1085 ∨ p1093)
    (h6454 : p1085 ∨ p1094)
    (h6389 : p13 ∨ p1076 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : (¬ p1086) ∨ p1076 ∨ p13 ∨ (¬ p1087) ∨ (¬ p1089) ∨ (¬ p1088) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1086 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1076) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p13) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1087 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1089 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1088 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1085) := by
    rcases h6364 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u4)
  have u7 : p1090 := by
    rcases h6450 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1091 := by
    rcases h6451 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1092 := by
    rcases h6452 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1093 := by
    rcases h6453 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1094 := by
    rcases h6454 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h6389 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22593 (p13 p1076 p1086 p1087 p1088 p1089 : Prop)
    (h22588 : p1089 ∨ p1076 ∨ p13)
    (h22589 : p1088 ∨ p1076 ∨ p13)
    (h22590 : p1087 ∨ p1076 ∨ p13)
    (h22591 : p1086 ∨ p1076 ∨ p13)
    (h22592 : (¬ p1086) ∨ p1076 ∨ p13 ∨ (¬ p1087) ∨ (¬ p1089) ∨ (¬ p1088)) : p1076 ∨ p13 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1076) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p13) := fun hu => hn (Or.inr hu)
  have u2 : p1089 := by
    rcases h22588 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1088 := by
    rcases h22589 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1087 := by
    rcases h22590 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1086 := by
    rcases h22591 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22592 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step22595 (p6 p211 p218 p219 p220 p221 p222 p223 : Prop)
    (h1167 : p218 ∨ p219)
    (h1168 : p218 ∨ p220)
    (h1169 : p218 ∨ p221)
    (h1170 : p218 ∨ p222)
    (h1171 : p218 ∨ p223)
    (h1083 : p6 ∨ p211 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : p218 ∨ p211 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p218) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p211) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p219 := by
    rcases h1167 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p220 := by
    rcases h1168 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p221 := by
    rcases h1169 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p222 := by
    rcases h1170 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p223 := by
    rcases h1171 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1083 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22596 (p6 p211 p217 p219 p220 p221 p222 p223 : Prop)
    (h1162 : p217 ∨ p219)
    (h1163 : p217 ∨ p220)
    (h1164 : p217 ∨ p221)
    (h1165 : p217 ∨ p222)
    (h1166 : p217 ∨ p223)
    (h1083 : p6 ∨ p211 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : p217 ∨ p211 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p217) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p211) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p219 := by
    rcases h1162 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p220 := by
    rcases h1163 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p221 := by
    rcases h1164 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p222 := by
    rcases h1165 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p223 := by
    rcases h1166 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1083 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22597 (p6 p211 p216 p219 p220 p221 p222 p223 : Prop)
    (h1157 : p216 ∨ p219)
    (h1158 : p216 ∨ p220)
    (h1159 : p216 ∨ p221)
    (h1160 : p216 ∨ p222)
    (h1161 : p216 ∨ p223)
    (h1083 : p6 ∨ p211 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : p216 ∨ p211 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p216) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p211) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p219 := by
    rcases h1157 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p220 := by
    rcases h1158 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p221 := by
    rcases h1159 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p222 := by
    rcases h1160 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p223 := by
    rcases h1161 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1083 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22598 (p6 p211 p215 p219 p220 p221 p222 p223 : Prop)
    (h1152 : p215 ∨ p219)
    (h1153 : p215 ∨ p220)
    (h1154 : p215 ∨ p221)
    (h1155 : p215 ∨ p222)
    (h1156 : p215 ∨ p223)
    (h1083 : p6 ∨ p211 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : p215 ∨ p211 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p215) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p211) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p219 := by
    rcases h1152 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p220 := by
    rcases h1153 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p221 := by
    rcases h1154 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p222 := by
    rcases h1155 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p223 := by
    rcases h1156 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1083 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22600 (p6 p127 p218 p219 p220 p221 p222 p223 : Prop)
    (h1167 : p218 ∨ p219)
    (h1168 : p218 ∨ p220)
    (h1169 : p218 ∨ p221)
    (h1170 : p218 ∨ p222)
    (h1171 : p218 ∨ p223)
    (h1084 : p6 ∨ p127 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : p218 ∨ p127 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p218) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p127) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p219 := by
    rcases h1167 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p220 := by
    rcases h1168 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p221 := by
    rcases h1169 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p222 := by
    rcases h1170 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p223 := by
    rcases h1171 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1084 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22601 (p6 p127 p217 p219 p220 p221 p222 p223 : Prop)
    (h1162 : p217 ∨ p219)
    (h1163 : p217 ∨ p220)
    (h1164 : p217 ∨ p221)
    (h1165 : p217 ∨ p222)
    (h1166 : p217 ∨ p223)
    (h1084 : p6 ∨ p127 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : p217 ∨ p127 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p217) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p127) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p219 := by
    rcases h1162 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p220 := by
    rcases h1163 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p221 := by
    rcases h1164 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p222 := by
    rcases h1165 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p223 := by
    rcases h1166 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1084 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22602 (p6 p127 p216 p219 p220 p221 p222 p223 : Prop)
    (h1157 : p216 ∨ p219)
    (h1158 : p216 ∨ p220)
    (h1159 : p216 ∨ p221)
    (h1160 : p216 ∨ p222)
    (h1161 : p216 ∨ p223)
    (h1084 : p6 ∨ p127 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : p216 ∨ p127 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p216) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p127) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p219 := by
    rcases h1157 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p220 := by
    rcases h1158 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p221 := by
    rcases h1159 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p222 := by
    rcases h1160 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p223 := by
    rcases h1161 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1084 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22603 (p6 p127 p215 p219 p220 p221 p222 p223 : Prop)
    (h1152 : p215 ∨ p219)
    (h1153 : p215 ∨ p220)
    (h1154 : p215 ∨ p221)
    (h1155 : p215 ∨ p222)
    (h1156 : p215 ∨ p223)
    (h1084 : p6 ∨ p127 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : p215 ∨ p127 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p215) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p127) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p219 := by
    rcases h1152 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p220 := by
    rcases h1153 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p221 := by
    rcases h1154 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p222 := by
    rcases h1155 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p223 := by
    rcases h1156 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1084 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22604 (p6 p127 p214 p215 p216 p217 p218 p219 p220 p221 p222 p223 : Prop)
    (h1059 : p6 ∨ p127 ∨ (¬ p214) ∨ (¬ p215) ∨ (¬ p216) ∨ (¬ p217) ∨ (¬ p218))
    (h1147 : p214 ∨ p219)
    (h1148 : p214 ∨ p220)
    (h1149 : p214 ∨ p221)
    (h1150 : p214 ∨ p222)
    (h1151 : p214 ∨ p223)
    (h1084 : p6 ∨ p127 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : (¬ p215) ∨ (¬ p218) ∨ p6 ∨ p127 ∨ (¬ p216) ∨ (¬ p217) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p215 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p218 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p6) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p127) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p216 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p217 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p214) := by
    rcases h1059 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p219 := by
    rcases h1147 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p220 := by
    rcases h1148 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p221 := by
    rcases h1149 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p222 := by
    rcases h1150 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p223 := by
    rcases h1151 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1084 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22605 (p6 p127 p215 p216 p217 p218 : Prop)
    (h22600 : p218 ∨ p127 ∨ p6)
    (h22601 : p217 ∨ p127 ∨ p6)
    (h22602 : p216 ∨ p127 ∨ p6)
    (h22603 : p215 ∨ p127 ∨ p6)
    (h22604 : (¬ p215) ∨ (¬ p218) ∨ p6 ∨ p127 ∨ (¬ p216) ∨ (¬ p217)) : p127 ∨ p6 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p127) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p6) := fun hu => hn (Or.inr hu)
  have u2 : p218 := by
    rcases h22600 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p217 := by
    rcases h22601 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p216 := by
    rcases h22602 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p215 := by
    rcases h22603 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22604 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22606 (p2 p6 p10 p127 p134 p303 p323 p325 p329 p387 p419 : Prop)
    (h13807 : (¬ p2) ∨ p6 ∨ (¬ p329))
    (h21610 : p329 ∨ p10)
    (h1698 : (¬ p10) ∨ (¬ p323))
    (h21607 : p329 ∨ p323 ∨ p325)
    (h22605 : p127 ∨ p6)
    (h18332 : (¬ p2) ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p303) ∨ (¬ p325))
    (h18693 : (¬ p2) ∨ (¬ p127) ∨ (¬ p387) ∨ (¬ p419))
    (h21394 : p387 ∨ p303) : p6 ∨ (¬ p134) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p329) := by
    rcases h13807 with q0 | q1 | q2
    · exact False.elim (q0 u3)
    · exact False.elim (u0 q1)
    · exact q2
  have u5 : p10 := by
    rcases h21610 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u6 : (¬ p323) := by
    rcases h1698 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  have u7 : p325 := by
    rcases h21607 with q0 | q1 | q2
    · exact False.elim (u4 q0)
    · exact False.elim (u6 q1)
    · exact q2
  have u8 : p127 := by
    rcases h22605 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : (¬ p303) := by
    rcases h18332 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u8)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u7)
  have u10 : (¬ p387) := by
    rcases h18693 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u8)
    · exact q2
    · exact False.elim (q3 u2)
  rcases h21394 with q0 | q1
  · exact False.elim (u10 q0)
  · exact False.elim (u9 q1)

theorem step22609 (p387 p595 p599 p616 p1232 p1289 p1293 : Prop)
    (h21790 : p616 ∨ p595)
    (h10564 : p616 ∨ (¬ p1232) ∨ (¬ p1293))
    (h16490 : (¬ p387) ∨ (¬ p595) ∨ (¬ p599) ∨ (¬ p1232) ∨ (¬ p1289))
    (h22540 : p1289 ∨ p1293) : (¬ p1232) ∨ p616 ∨ (¬ p599) ∨ (¬ p387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p616) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p599 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p595 := by
    rcases h21790 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u5 : (¬ p1293) := by
    rcases h10564 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact False.elim (q1 u0)
    · exact q2
  have u6 : (¬ p1289) := by
    rcases h16490 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u0)
    · exact q4
  rcases h22540 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step22610 (p188 p194 p196 p201 p202 p203 p204 p205 : Prop)
    (h1022 : p196 ∨ p201)
    (h1023 : p196 ∨ p202)
    (h1024 : p196 ∨ p203)
    (h1025 : p196 ∨ p204)
    (h1026 : p196 ∨ p205)
    (h950 : p188 ∨ p194 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p196 ∨ p194 ∨ p188 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p196) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p194) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p188) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p201 := by
    rcases h1022 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p202 := by
    rcases h1023 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p203 := by
    rcases h1024 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p204 := by
    rcases h1025 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p205 := by
    rcases h1026 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h950 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22611 (p188 p194 p200 p201 p202 p203 p204 p205 : Prop)
    (h1042 : p200 ∨ p201)
    (h1043 : p200 ∨ p202)
    (h1044 : p200 ∨ p203)
    (h1045 : p200 ∨ p204)
    (h1046 : p200 ∨ p205)
    (h950 : p188 ∨ p194 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p200 ∨ p194 ∨ p188 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p200) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p194) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p188) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p201 := by
    rcases h1042 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p202 := by
    rcases h1043 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p203 := by
    rcases h1044 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p204 := by
    rcases h1045 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p205 := by
    rcases h1046 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h950 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22612 (p188 p194 p199 p201 p202 p203 p204 p205 : Prop)
    (h1037 : p199 ∨ p201)
    (h1038 : p199 ∨ p202)
    (h1039 : p199 ∨ p203)
    (h1040 : p199 ∨ p204)
    (h1041 : p199 ∨ p205)
    (h950 : p188 ∨ p194 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p199 ∨ p194 ∨ p188 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p199) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p194) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p188) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p201 := by
    rcases h1037 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p202 := by
    rcases h1038 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p203 := by
    rcases h1039 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p204 := by
    rcases h1040 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p205 := by
    rcases h1041 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h950 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22613 (p188 p194 p198 p201 p202 p203 p204 p205 : Prop)
    (h1032 : p198 ∨ p201)
    (h1033 : p198 ∨ p202)
    (h1034 : p198 ∨ p203)
    (h1035 : p198 ∨ p204)
    (h1036 : p198 ∨ p205)
    (h950 : p188 ∨ p194 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p198 ∨ p194 ∨ p188 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p198) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p194) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p188) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p201 := by
    rcases h1032 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p202 := by
    rcases h1033 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p203 := by
    rcases h1034 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p204 := by
    rcases h1035 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p205 := by
    rcases h1036 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h950 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22614 (p188 p194 p196 p197 p198 p199 p200 p201 p202 p203 p204 p205 : Prop)
    (h925 : p188 ∨ p194 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200))
    (h1027 : p197 ∨ p201)
    (h1028 : p197 ∨ p202)
    (h1029 : p197 ∨ p203)
    (h1030 : p197 ∨ p204)
    (h1031 : p197 ∨ p205)
    (h950 : p188 ∨ p194 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : (¬ p198) ∨ (¬ p200) ∨ (¬ p196) ∨ p188 ∨ p194 ∨ (¬ p199) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p198 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p200 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p196 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p188) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p194) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p199 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p197) := by
    rcases h925 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u2)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p201 := by
    rcases h1027 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p202 := by
    rcases h1028 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p203 := by
    rcases h1029 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p204 := by
    rcases h1030 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p205 := by
    rcases h1031 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h950 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22615 (p188 p194 p196 p198 p199 p200 : Prop)
    (h22610 : p196 ∨ p194 ∨ p188)
    (h22611 : p200 ∨ p194 ∨ p188)
    (h22612 : p199 ∨ p194 ∨ p188)
    (h22613 : p198 ∨ p194 ∨ p188)
    (h22614 : (¬ p198) ∨ (¬ p200) ∨ (¬ p196) ∨ p188 ∨ p194 ∨ (¬ p199)) : p194 ∨ p188 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p194) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p188) := fun hu => hn (Or.inr hu)
  have u2 : p196 := by
    rcases h22610 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p200 := by
    rcases h22611 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p199 := by
    rcases h22612 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p198 := by
    rcases h22613 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22614 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (u1 q3)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u4)

theorem step22617 (p303 p383 p390 p391 p392 p393 p394 p395 p396 p397 p398 p399 : Prop)
    (h2116 : p303 ∨ p383 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399))
    (h2183 : p390 ∨ p397)
    (h2188 : p391 ∨ p397)
    (h2193 : p392 ∨ p397)
    (h2198 : p393 ∨ p397)
    (h2203 : p394 ∨ p397)
    (h2091 : p303 ∨ p383 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : (¬ p399) ∨ (¬ p396) ∨ p383 ∨ p303 ∨ (¬ p395) ∨ (¬ p398) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p399 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p396 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p383) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p303) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p395 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p397) := by
    rcases h2116 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u1)
    · exact q4
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u0)
  have u7 : p390 := by
    rcases h2183 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p391 := by
    rcases h2188 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p392 := by
    rcases h2193 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p393 := by
    rcases h2198 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p394 := by
    rcases h2203 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h2091 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22618 (p303 p383 p395 p396 p398 p399 : Prop)
    (h20926 : p398 ∨ p383 ∨ p303)
    (h20927 : p399 ∨ p383 ∨ p303)
    (h20928 : p395 ∨ p383 ∨ p303)
    (h20929 : p396 ∨ p383 ∨ p303)
    (h22617 : (¬ p399) ∨ (¬ p396) ∨ p383 ∨ p303 ∨ (¬ p395) ∨ (¬ p398)) : p383 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p383) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p303) := fun hu => hn (Or.inr hu)
  have u2 : p398 := by
    rcases h20926 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p399 := by
    rcases h20927 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p395 := by
    rcases h20928 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p396 := by
    rcases h20929 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22617 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step22619 (p1249 p1272 p1276 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7682 : p1276 ∨ p1281)
    (h7683 : p1276 ∨ p1282)
    (h7684 : p1276 ∨ p1283)
    (h7685 : p1276 ∨ p1284)
    (h7686 : p1276 ∨ p1285)
    (h7617 : p1249 ∨ p1272 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1276 ∨ p1272 ∨ p1249 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1276) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1272) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1249) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7682 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7683 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7684 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7685 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7686 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7617 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22620 (p1249 p1272 p1280 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7702 : p1280 ∨ p1281)
    (h7703 : p1280 ∨ p1282)
    (h7704 : p1280 ∨ p1283)
    (h7705 : p1280 ∨ p1284)
    (h7706 : p1280 ∨ p1285)
    (h7617 : p1249 ∨ p1272 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1280 ∨ p1272 ∨ p1249 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1280) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1272) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1249) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7702 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7703 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7704 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7705 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7706 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7617 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22621 (p1249 p1272 p1279 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7697 : p1279 ∨ p1281)
    (h7698 : p1279 ∨ p1282)
    (h7699 : p1279 ∨ p1283)
    (h7700 : p1279 ∨ p1284)
    (h7701 : p1279 ∨ p1285)
    (h7617 : p1249 ∨ p1272 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1279 ∨ p1272 ∨ p1249 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1279) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1272) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1249) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7697 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7698 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7699 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7700 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7701 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7617 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22622 (p1249 p1272 p1278 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7692 : p1278 ∨ p1281)
    (h7693 : p1278 ∨ p1282)
    (h7694 : p1278 ∨ p1283)
    (h7695 : p1278 ∨ p1284)
    (h7696 : p1278 ∨ p1285)
    (h7617 : p1249 ∨ p1272 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1278 ∨ p1272 ∨ p1249 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1278) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1272) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1249) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7692 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7693 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7694 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7695 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7696 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7617 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22623 (p1249 p1272 p1276 p1277 p1278 p1279 p1280 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7592 : p1249 ∨ p1272 ∨ (¬ p1276) ∨ (¬ p1277) ∨ (¬ p1278) ∨ (¬ p1279) ∨ (¬ p1280))
    (h7687 : p1277 ∨ p1281)
    (h7688 : p1277 ∨ p1282)
    (h7689 : p1277 ∨ p1283)
    (h7690 : p1277 ∨ p1284)
    (h7691 : p1277 ∨ p1285)
    (h7617 : p1249 ∨ p1272 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : (¬ p1278) ∨ (¬ p1276) ∨ p1249 ∨ p1272 ∨ (¬ p1279) ∨ (¬ p1280) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1278 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1276 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1249) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1272) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1279 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1280 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1277) := by
    rcases h7592 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p1281 := by
    rcases h7687 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1282 := by
    rcases h7688 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1283 := by
    rcases h7689 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1284 := by
    rcases h7690 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1285 := by
    rcases h7691 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7617 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22624 (p1249 p1272 p1276 p1278 p1279 p1280 : Prop)
    (h22619 : p1276 ∨ p1272 ∨ p1249)
    (h22620 : p1280 ∨ p1272 ∨ p1249)
    (h22621 : p1279 ∨ p1272 ∨ p1249)
    (h22622 : p1278 ∨ p1272 ∨ p1249)
    (h22623 : (¬ p1278) ∨ (¬ p1276) ∨ p1249 ∨ p1272 ∨ (¬ p1279) ∨ (¬ p1280)) : p1272 ∨ p1249 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1272) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1249) := fun hu => hn (Or.inr hu)
  have u2 : p1276 := by
    rcases h22619 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1280 := by
    rcases h22620 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1279 := by
    rcases h22621 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1278 := by
    rcases h22622 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22623 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22625 (p1231 p1236 p1239 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h7428 : p1239 ∨ p1244)
    (h7429 : p1239 ∨ p1245)
    (h7430 : p1239 ∨ p1246)
    (h7431 : p1239 ∨ p1247)
    (h7432 : p1239 ∨ p1248)
    (h7359 : p1231 ∨ p1236 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1239 ∨ p1231 ∨ p1236 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1239) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1231) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1236) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1244 := by
    rcases h7428 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1245 := by
    rcases h7429 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1246 := by
    rcases h7430 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1247 := by
    rcases h7431 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1248 := by
    rcases h7432 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22626 (p1231 p1236 p1243 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h7448 : p1243 ∨ p1244)
    (h7449 : p1243 ∨ p1245)
    (h7450 : p1243 ∨ p1246)
    (h7451 : p1243 ∨ p1247)
    (h7452 : p1243 ∨ p1248)
    (h7359 : p1231 ∨ p1236 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1243 ∨ p1231 ∨ p1236 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1243) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1231) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1236) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1244 := by
    rcases h7448 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1245 := by
    rcases h7449 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1246 := by
    rcases h7450 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1247 := by
    rcases h7451 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1248 := by
    rcases h7452 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22627 (p1231 p1236 p1242 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h7443 : p1242 ∨ p1244)
    (h7444 : p1242 ∨ p1245)
    (h7445 : p1242 ∨ p1246)
    (h7446 : p1242 ∨ p1247)
    (h7447 : p1242 ∨ p1248)
    (h7359 : p1231 ∨ p1236 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1242 ∨ p1231 ∨ p1236 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1242) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1231) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1236) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1244 := by
    rcases h7443 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1245 := by
    rcases h7444 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1246 := by
    rcases h7445 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1247 := by
    rcases h7446 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1248 := by
    rcases h7447 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22628 (p1231 p1236 p1241 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h7438 : p1241 ∨ p1244)
    (h7439 : p1241 ∨ p1245)
    (h7440 : p1241 ∨ p1246)
    (h7441 : p1241 ∨ p1247)
    (h7442 : p1241 ∨ p1248)
    (h7359 : p1231 ∨ p1236 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : p1241 ∨ p1231 ∨ p1236 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1241) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1231) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1236) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1244 := by
    rcases h7438 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1245 := by
    rcases h7439 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1246 := by
    rcases h7440 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1247 := by
    rcases h7441 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1248 := by
    rcases h7442 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22629 (p1231 p1236 p1239 p1240 p1241 p1242 p1243 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h7334 : p1231 ∨ p1236 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243))
    (h7433 : p1240 ∨ p1244)
    (h7434 : p1240 ∨ p1245)
    (h7435 : p1240 ∨ p1246)
    (h7436 : p1240 ∨ p1247)
    (h7437 : p1240 ∨ p1248)
    (h7359 : p1231 ∨ p1236 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248)) : (¬ p1241) ∨ (¬ p1239) ∨ p1231 ∨ p1236 ∨ (¬ p1242) ∨ (¬ p1243) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1239 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1231) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1236) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1240) := by
    rcases h7334 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p1244 := by
    rcases h7433 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1245 := by
    rcases h7434 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1246 := by
    rcases h7435 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1247 := by
    rcases h7436 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1248 := by
    rcases h7437 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22630 (p1231 p1236 p1239 p1241 p1242 p1243 : Prop)
    (h22625 : p1239 ∨ p1231 ∨ p1236)
    (h22626 : p1243 ∨ p1231 ∨ p1236)
    (h22627 : p1242 ∨ p1231 ∨ p1236)
    (h22628 : p1241 ∨ p1231 ∨ p1236)
    (h22629 : (¬ p1241) ∨ (¬ p1239) ∨ p1231 ∨ p1236 ∨ (¬ p1242) ∨ (¬ p1243)) : p1231 ∨ p1236 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1231) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1236) := fun hu => hn (Or.inr hu)
  have u2 : p1239 := by
    rcases h22625 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1243 := by
    rcases h22626 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1242 := by
    rcases h22627 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1241 := by
    rcases h22628 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22629 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22633 (p24 p102 p323 p345 p350 p499 p601 p633 p635 p1099 : Prop)
    (h14419 : (¬ p24) ∨ (¬ p323) ∨ p601)
    (h21505 : p633 ∨ p635)
    (h11161 : (¬ p24) ∨ (¬ p102) ∨ p633)
    (h16807 : (¬ p350) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p635) ∨ (¬ p1099))
    (h15917 : p102 ∨ (¬ p323) ∨ (¬ p345))
    (h21667 : p350 ∨ p345) : p633 ∨ (¬ p323) ∨ (¬ p499) ∨ (¬ p1099) ∨ (¬ p24) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p601 := by
    rcases h14419 with q0 | q1 | q2
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u1)
    · exact q2
  have u6 : p635 := by
    rcases h21505 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : (¬ p102) := by
    rcases h11161 with q0 | q1 | q2
    · exact False.elim (q0 u4)
    · exact q1
    · exact False.elim (u0 q2)
  have u8 : (¬ p350) := by
    rcases h16807 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u3)
  have u9 : (¬ p345) := by
    rcases h15917 with q0 | q1 | q2
    · exact False.elim (u7 q0)
    · exact False.elim (q1 u1)
    · exact q2
  rcases h21667 with q0 | q1
  · exact False.elim (u8 q0)
  · exact False.elim (u9 q1)

theorem step22635 (p24 p102 p323 p345 p350 p495 p595 p596 p633 p636 : Prop)
    (h11161 : (¬ p24) ∨ (¬ p102) ∨ p633)
    (h21879 : p636 ∨ p633)
    (h15917 : p102 ∨ (¬ p323) ∨ (¬ p345))
    (h19255 : (¬ p350) ∨ (¬ p495) ∨ (¬ p595) ∨ (¬ p596) ∨ (¬ p636))
    (h21667 : p350 ∨ p345) : p633 ∨ (¬ p323) ∨ (¬ p495) ∨ (¬ p596) ∨ (¬ p595) ∨ (¬ p24) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p633) := fun hu => hn (Or.inl hu)
  have u1 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p102) := by
    rcases h11161 with q0 | q1 | q2
    · exact False.elim (q0 u5)
    · exact q1
    · exact False.elim (u0 q2)
  have u7 : p636 := by
    rcases h21879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : (¬ p345) := by
    rcases h15917 with q0 | q1 | q2
    · exact False.elim (u6 q0)
    · exact False.elim (q1 u1)
    · exact q2
  have u9 : (¬ p350) := by
    rcases h19255 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u7)
  rcases h21667 with q0 | q1
  · exact False.elim (u9 q0)
  · exact False.elim (u8 q1)

theorem step22637 (p138 p142 p148 p149 p150 p151 p152 p153 : Prop)
    (h776 : p148 ∨ p149)
    (h777 : p148 ∨ p150)
    (h778 : p148 ∨ p151)
    (h779 : p148 ∨ p152)
    (h780 : p148 ∨ p153)
    (h698 : p138 ∨ p142 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153)) : p148 ∨ p138 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p148) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p138) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p142) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p149 := by
    rcases h776 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p150 := by
    rcases h777 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p151 := by
    rcases h778 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p152 := by
    rcases h779 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p153 := by
    rcases h780 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h698 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22638 (p138 p142 p144 p145 p146 p147 p148 p153 : Prop)
    (h22637 : p148 ∨ p138 ∨ p142)
    (h760 : p144 ∨ p153)
    (h765 : p145 ∨ p153)
    (h770 : p146 ∨ p153)
    (h775 : p147 ∨ p153)
    (h673 : p138 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p153 ∨ p138 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p153) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p138) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p142) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p148 := by
    rcases h22637 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p144 := by
    rcases h760 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p145 := by
    rcases h765 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p146 := by
    rcases h770 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p147 := by
    rcases h775 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h673 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22639 (p138 p142 p144 p145 p146 p147 p148 p152 : Prop)
    (h22637 : p148 ∨ p138 ∨ p142)
    (h759 : p144 ∨ p152)
    (h764 : p145 ∨ p152)
    (h769 : p146 ∨ p152)
    (h774 : p147 ∨ p152)
    (h673 : p138 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p152 ∨ p138 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p152) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p138) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p142) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p148 := by
    rcases h22637 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p144 := by
    rcases h759 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p145 := by
    rcases h764 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p146 := by
    rcases h769 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p147 := by
    rcases h774 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h673 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22640 (p138 p142 p144 p145 p146 p147 p148 p151 : Prop)
    (h22637 : p148 ∨ p138 ∨ p142)
    (h758 : p144 ∨ p151)
    (h763 : p145 ∨ p151)
    (h768 : p146 ∨ p151)
    (h773 : p147 ∨ p151)
    (h673 : p138 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p151 ∨ p138 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p151) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p138) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p142) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p148 := by
    rcases h22637 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p144 := by
    rcases h758 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p145 := by
    rcases h763 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p146 := by
    rcases h768 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p147 := by
    rcases h773 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h673 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22641 (p138 p142 p144 p145 p146 p147 p148 p150 : Prop)
    (h22637 : p148 ∨ p138 ∨ p142)
    (h757 : p144 ∨ p150)
    (h762 : p145 ∨ p150)
    (h767 : p146 ∨ p150)
    (h772 : p147 ∨ p150)
    (h673 : p138 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p150 ∨ p138 ∨ p142 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p150) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p138) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p142) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p148 := by
    rcases h22637 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p144 := by
    rcases h757 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p145 := by
    rcases h762 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p146 := by
    rcases h767 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p147 := by
    rcases h772 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h673 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22643 (p11 p85 p126 p457 p461 p495 p1229 : Prop)
    (h10248 : (¬ p457) ∨ (¬ p495) ∨ (¬ p1229))
    (h16585 : (¬ p11) ∨ (¬ p85) ∨ (¬ p126) ∨ (¬ p461) ∨ (¬ p1229))
    (h22380 : p461 ∨ p457) : (¬ p1229) ∨ (¬ p11) ∨ (¬ p126) ∨ (¬ p495) ∨ (¬ p85) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p457) := by
    rcases h10248 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u0)
  have u6 : (¬ p461) := by
    rcases h16585 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u2)
    · exact q3
    · exact False.elim (q4 u0)
  rcases h22380 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step22644 (p124 p227 p304 p310 p1061 p1079 p1083 : Prop)
    (h21128 : p310 ∨ p304)
    (h21106 : p124 ∨ p304)
    (h13431 : (¬ p124) ∨ p227 ∨ (¬ p1083))
    (h12270 : p227 ∨ (¬ p310) ∨ (¬ p1061) ∨ (¬ p1079))
    (h20699 : p1079 ∨ p1083) : p227 ∨ p304 ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p227) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p304) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p310 := by
    rcases h21128 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u4 : p124 := by
    rcases h21106 with q0 | q1
    · exact q0
    · exact False.elim (u1 q1)
  have u5 : (¬ p1083) := by
    rcases h13431 with q0 | q1 | q2
    · exact False.elim (q0 u4)
    · exact False.elim (u0 q1)
    · exact q2
  have u6 : (¬ p1079) := by
    rcases h12270 with q0 | q1 | q2 | q3
    · exact False.elim (u0 q0)
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u2)
    · exact q3
  rcases h20699 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step22645 (p1385 p1394 p1400 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h8469 : p1400 ∨ p1401)
    (h8470 : p1400 ∨ p1402)
    (h8471 : p1400 ∨ p1403)
    (h8472 : p1400 ∨ p1404)
    (h8473 : p1400 ∨ p1405)
    (h8387 : p1385 ∨ p1394 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405)) : p1400 ∨ p1394 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1400) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1394) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1401 := by
    rcases h8469 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1402 := by
    rcases h8470 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1403 := by
    rcases h8471 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1404 := by
    rcases h8472 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1405 := by
    rcases h8473 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h8387 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22646 (p1385 p1394 p1396 p1397 p1398 p1399 p1400 p1405 : Prop)
    (h22645 : p1400 ∨ p1394 ∨ p1385)
    (h8453 : p1396 ∨ p1405)
    (h8458 : p1397 ∨ p1405)
    (h8463 : p1398 ∨ p1405)
    (h8468 : p1399 ∨ p1405)
    (h8362 : p1385 ∨ p1394 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1405 ∨ p1394 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1405) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1394) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1400 := by
    rcases h22645 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1396 := by
    rcases h8453 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1397 := by
    rcases h8458 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1398 := by
    rcases h8463 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1399 := by
    rcases h8468 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8362 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22647 (p1385 p1394 p1396 p1397 p1398 p1399 p1400 p1404 : Prop)
    (h22645 : p1400 ∨ p1394 ∨ p1385)
    (h8452 : p1396 ∨ p1404)
    (h8457 : p1397 ∨ p1404)
    (h8462 : p1398 ∨ p1404)
    (h8467 : p1399 ∨ p1404)
    (h8362 : p1385 ∨ p1394 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1404 ∨ p1394 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1404) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1394) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1400 := by
    rcases h22645 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1396 := by
    rcases h8452 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1397 := by
    rcases h8457 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1398 := by
    rcases h8462 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1399 := by
    rcases h8467 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8362 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22648 (p1385 p1394 p1396 p1397 p1398 p1399 p1400 p1403 : Prop)
    (h22645 : p1400 ∨ p1394 ∨ p1385)
    (h8451 : p1396 ∨ p1403)
    (h8456 : p1397 ∨ p1403)
    (h8461 : p1398 ∨ p1403)
    (h8466 : p1399 ∨ p1403)
    (h8362 : p1385 ∨ p1394 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1403 ∨ p1394 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1403) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1394) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1400 := by
    rcases h22645 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1396 := by
    rcases h8451 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1397 := by
    rcases h8456 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1398 := by
    rcases h8461 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1399 := by
    rcases h8466 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8362 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22649 (p1385 p1394 p1396 p1397 p1398 p1399 p1400 p1402 : Prop)
    (h22645 : p1400 ∨ p1394 ∨ p1385)
    (h8450 : p1396 ∨ p1402)
    (h8455 : p1397 ∨ p1402)
    (h8460 : p1398 ∨ p1402)
    (h8465 : p1399 ∨ p1402)
    (h8362 : p1385 ∨ p1394 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1402 ∨ p1394 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1402) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1394) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1400 := by
    rcases h22645 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1396 := by
    rcases h8450 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1397 := by
    rcases h8455 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1398 := by
    rcases h8460 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1399 := by
    rcases h8465 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8362 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step22650 (p1385 p1387 p1393 p1394 p1396 p1397 p1398 p1399 p1400 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h22426 : p1387 ∨ p1393)
    (h11319 : (¬ p1385) ∨ (¬ p1393))
    (h22645 : p1400 ∨ p1394 ∨ p1385)
    (h22646 : p1405 ∨ p1394 ∨ p1385)
    (h22647 : p1404 ∨ p1394 ∨ p1385)
    (h22648 : p1403 ∨ p1394 ∨ p1385)
    (h22649 : p1402 ∨ p1394 ∨ p1385)
    (h8377 : p1387 ∨ p1394 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405))
    (h8449 : p1396 ∨ p1401)
    (h8454 : p1397 ∨ p1401)
    (h8459 : p1398 ∨ p1401)
    (h8464 : p1399 ∨ p1401)
    (h8362 : p1385 ∨ p1394 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1394 ∨ p1387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1394) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1387) := fun hu => hn (Or.inr hu)
  have u2 : p1393 := by
    rcases h22426 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u3 : (¬ p1385) := by
    rcases h11319 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u4 : p1400 := by
    rcases h22645 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u3 q2)
  have u5 : p1405 := by
    rcases h22646 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u3 q2)
  have u6 : p1404 := by
    rcases h22647 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u3 q2)
  have u7 : p1403 := by
    rcases h22648 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u3 q2)
  have u8 : p1402 := by
    rcases h22649 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u3 q2)
  have u9 : (¬ p1401) := by
    rcases h8377 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact q2
    · exact False.elim (q3 u8)
    · exact False.elim (q4 u7)
    · exact False.elim (q5 u6)
    · exact False.elim (q6 u5)
  have u10 : p1396 := by
    rcases h8449 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u11 : p1397 := by
    rcases h8454 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u12 : p1398 := by
    rcases h8459 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u13 : p1399 := by
    rcases h8464 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h8362 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u13)
  · exact False.elim (q6 u4)

theorem step22651 (p15 p49 p304 p425 p494 p580 p633 : Prop)
    (h11188 : (¬ p304) ∨ (¬ p425) ∨ (¬ p633))
    (h16480 : (¬ p15) ∨ (¬ p49) ∨ (¬ p304) ∨ (¬ p494) ∨ (¬ p580) ∨ (¬ p633))
    (h22344 : p425 ∨ p494) : (¬ p304) ∨ (¬ p580) ∨ (¬ p633) ∨ (¬ p49) ∨ (¬ p15) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p425) := by
    rcases h11188 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u2)
  have u6 : (¬ p494) := by
    rcases h16480 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u0)
    · exact q3
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u2)
  rcases h22344 with q0 | q1
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)

theorem step22653 (p101 p108 p111 p116 p117 p118 p119 p120 : Prop)
    (h620 : p111 ∨ p116)
    (h621 : p111 ∨ p117)
    (h622 : p111 ∨ p118)
    (h623 : p111 ∨ p119)
    (h624 : p111 ∨ p120)
    (h556 : p101 ∨ p108 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p111 ∨ p108 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p111) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p108) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h620 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h621 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h622 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h623 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h624 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h556 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22654 (p101 p108 p114 p116 p117 p118 p119 p120 : Prop)
    (h635 : p114 ∨ p116)
    (h636 : p114 ∨ p117)
    (h637 : p114 ∨ p118)
    (h638 : p114 ∨ p119)
    (h639 : p114 ∨ p120)
    (h556 : p101 ∨ p108 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p114 ∨ p108 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p114) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p108) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h635 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h636 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h637 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h638 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h639 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h556 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22655 (p101 p108 p112 p116 p117 p118 p119 p120 : Prop)
    (h625 : p112 ∨ p116)
    (h626 : p112 ∨ p117)
    (h627 : p112 ∨ p118)
    (h628 : p112 ∨ p119)
    (h629 : p112 ∨ p120)
    (h556 : p101 ∨ p108 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p112 ∨ p108 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p112) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p108) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h625 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h626 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h627 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h628 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h629 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h556 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22656 (p101 p108 p115 p116 p117 p118 p119 p120 : Prop)
    (h640 : p115 ∨ p116)
    (h641 : p115 ∨ p117)
    (h642 : p115 ∨ p118)
    (h643 : p115 ∨ p119)
    (h644 : p115 ∨ p120)
    (h556 : p101 ∨ p108 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p115 ∨ p108 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p115) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p108) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h640 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h641 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h642 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h643 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h644 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h556 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22657 (p101 p108 p111 p112 p113 p114 p115 p116 p117 p118 p119 p120 : Prop)
    (h531 : p101 ∨ p108 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115))
    (h630 : p113 ∨ p116)
    (h631 : p113 ∨ p117)
    (h632 : p113 ∨ p118)
    (h633 : p113 ∨ p119)
    (h634 : p113 ∨ p120)
    (h556 : p101 ∨ p108 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : (¬ p115) ∨ (¬ p114) ∨ p101 ∨ (¬ p112) ∨ p108 ∨ (¬ p111) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p114 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p112 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p108) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p111 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p113) := by
    rcases h531 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u3)
    · exact q4
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u0)
  have u7 : p116 := by
    rcases h630 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p117 := by
    rcases h631 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p118 := by
    rcases h632 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p119 := by
    rcases h633 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p120 := by
    rcases h634 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h556 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22658 (p101 p108 p111 p112 p114 p115 : Prop)
    (h22653 : p111 ∨ p108 ∨ p101)
    (h22654 : p114 ∨ p108 ∨ p101)
    (h22655 : p112 ∨ p108 ∨ p101)
    (h22656 : p115 ∨ p108 ∨ p101)
    (h22657 : (¬ p115) ∨ (¬ p114) ∨ p101 ∨ (¬ p112) ∨ p108 ∨ (¬ p111)) : p108 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p108) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p101) := fun hu => hn (Or.inr hu)
  have u2 : p111 := by
    rcases h22653 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p114 := by
    rcases h22654 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p112 := by
    rcases h22655 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p115 := by
    rcases h22656 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22657 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u2)

theorem step22664 (p616 p620 p627 p628 p629 p630 p631 p632 : Prop)
    (h3610 : p627 ∨ p628)
    (h3611 : p627 ∨ p629)
    (h3612 : p627 ∨ p630)
    (h3613 : p627 ∨ p631)
    (h3614 : p627 ∨ p632)
    (h3526 : p616 ∨ p620 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : p627 ∨ p620 ∨ p616 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p627) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p620) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p616) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p628 := by
    rcases h3610 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p629 := by
    rcases h3611 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p630 := by
    rcases h3612 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p631 := by
    rcases h3613 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p632 := by
    rcases h3614 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3526 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22665 (p616 p620 p626 p628 p629 p630 p631 p632 : Prop)
    (h3605 : p626 ∨ p628)
    (h3606 : p626 ∨ p629)
    (h3607 : p626 ∨ p630)
    (h3608 : p626 ∨ p631)
    (h3609 : p626 ∨ p632)
    (h3526 : p616 ∨ p620 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : p626 ∨ p620 ∨ p616 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p626) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p620) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p616) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p628 := by
    rcases h3605 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p629 := by
    rcases h3606 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p630 := by
    rcases h3607 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p631 := by
    rcases h3608 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p632 := by
    rcases h3609 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3526 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22666 (p616 p620 p625 p628 p629 p630 p631 p632 : Prop)
    (h3600 : p625 ∨ p628)
    (h3601 : p625 ∨ p629)
    (h3602 : p625 ∨ p630)
    (h3603 : p625 ∨ p631)
    (h3604 : p625 ∨ p632)
    (h3526 : p616 ∨ p620 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : p625 ∨ p620 ∨ p616 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p625) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p620) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p616) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p628 := by
    rcases h3600 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p629 := by
    rcases h3601 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p630 := by
    rcases h3602 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p631 := by
    rcases h3603 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p632 := by
    rcases h3604 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3526 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22667 (p616 p620 p624 p628 p629 p630 p631 p632 : Prop)
    (h3595 : p624 ∨ p628)
    (h3596 : p624 ∨ p629)
    (h3597 : p624 ∨ p630)
    (h3598 : p624 ∨ p631)
    (h3599 : p624 ∨ p632)
    (h3526 : p616 ∨ p620 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : p624 ∨ p620 ∨ p616 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p624) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p620) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p616) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p628 := by
    rcases h3595 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p629 := by
    rcases h3596 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p630 := by
    rcases h3597 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p631 := by
    rcases h3598 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p632 := by
    rcases h3599 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3526 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22668 (p616 p620 p623 p624 p625 p626 p627 p628 p629 p630 p631 p632 : Prop)
    (h3501 : p616 ∨ p620 ∨ (¬ p623) ∨ (¬ p624) ∨ (¬ p625) ∨ (¬ p626) ∨ (¬ p627))
    (h3590 : p623 ∨ p628)
    (h3591 : p623 ∨ p629)
    (h3592 : p623 ∨ p630)
    (h3593 : p623 ∨ p631)
    (h3594 : p623 ∨ p632)
    (h3526 : p616 ∨ p620 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632)) : (¬ p624) ∨ (¬ p625) ∨ p616 ∨ (¬ p626) ∨ (¬ p627) ∨ p620 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p625 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p616) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p626 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p627 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p620) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p623) := by
    rcases h3501 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u5 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u4)
  have u7 : p628 := by
    rcases h3590 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p629 := by
    rcases h3591 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p630 := by
    rcases h3592 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p631 := by
    rcases h3593 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p632 := by
    rcases h3594 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3526 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22669 (p616 p620 p624 p625 p626 p627 : Prop)
    (h22664 : p627 ∨ p620 ∨ p616)
    (h22665 : p626 ∨ p620 ∨ p616)
    (h22666 : p625 ∨ p620 ∨ p616)
    (h22667 : p624 ∨ p620 ∨ p616)
    (h22668 : (¬ p624) ∨ (¬ p625) ∨ p616 ∨ (¬ p626) ∨ (¬ p627) ∨ p620) : p620 ∨ p616 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p620) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p616) := fun hu => hn (Or.inr hu)
  have u2 : p627 := by
    rcases h22664 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p626 := by
    rcases h22665 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p625 := by
    rcases h22666 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p624 := by
    rcases h22667 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22668 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (u0 q5)

theorem step22670 (p815 p821 p823 p828 p829 p830 p831 p832 : Prop)
    (h4769 : p823 ∨ p828)
    (h4770 : p823 ∨ p829)
    (h4771 : p823 ∨ p830)
    (h4772 : p823 ∨ p831)
    (h4773 : p823 ∨ p832)
    (h4697 : p815 ∨ p821 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : p823 ∨ p821 ∨ p815 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p823) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p821) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p815) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p828 := by
    rcases h4769 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p829 := by
    rcases h4770 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p830 := by
    rcases h4771 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p831 := by
    rcases h4772 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p832 := by
    rcases h4773 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4697 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22671 (p815 p821 p827 p828 p829 p830 p831 p832 : Prop)
    (h4789 : p827 ∨ p828)
    (h4790 : p827 ∨ p829)
    (h4791 : p827 ∨ p830)
    (h4792 : p827 ∨ p831)
    (h4793 : p827 ∨ p832)
    (h4697 : p815 ∨ p821 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : p827 ∨ p821 ∨ p815 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p827) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p821) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p815) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p828 := by
    rcases h4789 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p829 := by
    rcases h4790 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p830 := by
    rcases h4791 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p831 := by
    rcases h4792 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p832 := by
    rcases h4793 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4697 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22672 (p815 p821 p826 p828 p829 p830 p831 p832 : Prop)
    (h4784 : p826 ∨ p828)
    (h4785 : p826 ∨ p829)
    (h4786 : p826 ∨ p830)
    (h4787 : p826 ∨ p831)
    (h4788 : p826 ∨ p832)
    (h4697 : p815 ∨ p821 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : p826 ∨ p821 ∨ p815 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p826) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p821) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p815) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p828 := by
    rcases h4784 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p829 := by
    rcases h4785 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p830 := by
    rcases h4786 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p831 := by
    rcases h4787 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p832 := by
    rcases h4788 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4697 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22673 (p815 p821 p825 p828 p829 p830 p831 p832 : Prop)
    (h4779 : p825 ∨ p828)
    (h4780 : p825 ∨ p829)
    (h4781 : p825 ∨ p830)
    (h4782 : p825 ∨ p831)
    (h4783 : p825 ∨ p832)
    (h4697 : p815 ∨ p821 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : p825 ∨ p821 ∨ p815 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p825) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p821) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p815) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p828 := by
    rcases h4779 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p829 := by
    rcases h4780 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p830 := by
    rcases h4781 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p831 := by
    rcases h4782 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p832 := by
    rcases h4783 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4697 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22674 (p815 p821 p823 p824 p825 p826 p827 p828 p829 p830 p831 p832 : Prop)
    (h4672 : p815 ∨ p821 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827))
    (h4774 : p824 ∨ p828)
    (h4775 : p824 ∨ p829)
    (h4776 : p824 ∨ p830)
    (h4777 : p824 ∨ p831)
    (h4778 : p824 ∨ p832)
    (h4697 : p815 ∨ p821 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832)) : (¬ p825) ∨ (¬ p823) ∨ p815 ∨ p821 ∨ (¬ p826) ∨ (¬ p827) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p825 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p823 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p815) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p821) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p826 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p827 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p824) := by
    rcases h4672 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p828 := by
    rcases h4774 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p829 := by
    rcases h4775 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p830 := by
    rcases h4776 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p831 := by
    rcases h4777 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p832 := by
    rcases h4778 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h4697 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22675 (p815 p821 p823 p825 p826 p827 : Prop)
    (h22670 : p823 ∨ p821 ∨ p815)
    (h22671 : p827 ∨ p821 ∨ p815)
    (h22672 : p826 ∨ p821 ∨ p815)
    (h22673 : p825 ∨ p821 ∨ p815)
    (h22674 : (¬ p825) ∨ (¬ p823) ∨ p815 ∨ p821 ∨ (¬ p826) ∨ (¬ p827)) : p821 ∨ p815 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p821) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p815) := fun hu => hn (Or.inr hu)
  have u2 : p823 := by
    rcases h22670 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p827 := by
    rcases h22671 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p826 := by
    rcases h22672 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p825 := by
    rcases h22673 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22674 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22676 (p10 p11 p126 p227 p266 p325 p331 p434 p690 p821 p1366 : Prop)
    (h13541 : (¬ p325) ∨ p434 ∨ (¬ p1366))
    (h18080 : (¬ p11) ∨ (¬ p126) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p331) ∨ (¬ p690) ∨ (¬ p821) ∨ (¬ p1366))
    (h22236 : p331 ∨ p325 ∨ p10) : (¬ p1366) ∨ (¬ p821) ∨ (¬ p690) ∨ p434 ∨ (¬ p11) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p126) ∨ p10 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p821 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p434) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p325) := by
    rcases h13541 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u0)
  have u10 : (¬ p331) := by
    rcases h18080 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u6)
    · exact q4
    · exact False.elim (q5 u2)
    · exact False.elim (q6 u1)
    · exact False.elim (q7 u0)
  rcases h22236 with q0 | q1 | q2
  · exact False.elim (u10 q0)
  · exact False.elim (u9 q1)
  · exact False.elim (u8 q2)

theorem step22677 (p255 p288 p293 p295 p296 p297 p298 p299 p300 : Prop)
    (h21417 : p297 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h21416 : p296 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h21415 : p300 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h1558 : p293 ∨ p298)
    (h1559 : p293 ∨ p299)
    (h1478 : p255 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p293 ∨ (¬ p295) ∨ p255 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p293) := fun hu => hn (Or.inl hu)
  have u1 : p295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p255) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p288) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p297 := by
    rcases h21417 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (u2 q2)
    · exact False.elim (u3 q3)
  have u5 : p296 := by
    rcases h21416 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (u2 q2)
    · exact False.elim (u3 q3)
  have u6 : p300 := by
    rcases h21415 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (u2 q2)
    · exact False.elim (u3 q3)
  have u7 : p298 := by
    rcases h1558 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u8 : p299 := by
    rcases h1559 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1478 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u6)

theorem step22678 (p255 p288 p292 p295 p296 p297 p298 p299 p300 : Prop)
    (h21417 : p297 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h21416 : p296 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h21415 : p300 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h1553 : p292 ∨ p298)
    (h1554 : p292 ∨ p299)
    (h1478 : p255 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p292 ∨ (¬ p295) ∨ p255 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p292) := fun hu => hn (Or.inl hu)
  have u1 : p295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p255) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p288) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p297 := by
    rcases h21417 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (u2 q2)
    · exact False.elim (u3 q3)
  have u5 : p296 := by
    rcases h21416 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (u2 q2)
    · exact False.elim (u3 q3)
  have u6 : p300 := by
    rcases h21415 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (u2 q2)
    · exact False.elim (u3 q3)
  have u7 : p298 := by
    rcases h1553 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u8 : p299 := by
    rcases h1554 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1478 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u6)

theorem step22680 (p255 p288 p295 p299 : Prop)
    (h1569 : p295 ∨ p299)
    (h21414 : p295 ∨ (¬ p299) ∨ p255 ∨ p288) : p295 ∨ p255 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p295) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p255) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p299 := by
    rcases h1569 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h21414 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (u2 q3)

theorem step22681 (p255 p288 p294 p295 p296 p297 p298 p299 p300 : Prop)
    (h22680 : p295 ∨ p255 ∨ p288)
    (h21417 : p297 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h21416 : p296 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h21415 : p300 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h1563 : p294 ∨ p298)
    (h1564 : p294 ∨ p299)
    (h1478 : p255 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : p294 ∨ p255 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p294) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p255) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p295 := by
    rcases h22680 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p297 := by
    rcases h21417 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p296 := by
    rcases h21416 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p300 := by
    rcases h21415 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : p298 := by
    rcases h1563 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u8 : p299 := by
    rcases h1564 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1478 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u6)

theorem step22682 (p255 p288 p291 p292 p293 p294 p295 p296 p297 p298 p299 p300 : Prop)
    (h21415 : p300 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h21416 : p296 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h21417 : p297 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h22677 : p293 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h22678 : p292 ∨ (¬ p295) ∨ p255 ∨ p288)
    (h22681 : p294 ∨ p255 ∨ p288)
    (h1453 : p255 ∨ p288 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295))
    (h1548 : p291 ∨ p298)
    (h1549 : p291 ∨ p299)
    (h1478 : p255 ∨ p288 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300)) : (¬ p295) ∨ p255 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p295 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p255) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p300 := by
    rcases h21415 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p296 := by
    rcases h21416 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p297 := by
    rcases h21417 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p293 := by
    rcases h22677 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : p292 := by
    rcases h22678 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u8 : p294 := by
    rcases h22681 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u9 : (¬ p291) := by
    rcases h1453 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u7)
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u8)
    · exact False.elim (q6 u0)
  have u10 : p298 := by
    rcases h1548 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  have u11 : p299 := by
    rcases h1549 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  rcases h1478 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step22683 (p255 p288 p295 : Prop)
    (h22680 : p295 ∨ p255 ∨ p288)
    (h22682 : (¬ p295) ∨ p255 ∨ p288) : p255 ∨ p288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p255) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p288) := fun hu => hn (Or.inr hu)
  have u2 : p295 := by
    rcases h22680 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22682 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)

theorem step22684 (p38 p64 p68 p69 p595 p1188 : Prop)
    (h12344 : p38 ∨ p68)
    (h22515 : p38 ∨ p64 ∨ p69)
    (h10823 : (¬ p64) ∨ (¬ p68) ∨ (¬ p595) ∨ (¬ p1188)) : p38 ∨ (¬ p595) ∨ (¬ p1188) ∨ p69 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p38) := fun hu => hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p69) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p68 := by
    rcases h12344 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p64 := by
    rcases h22515 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (u3 q2)
  rcases h10823 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)

theorem step22690 (p10 p11 p126 p193 p227 p266 p419 p434 p690 p815 p821 p1366 : Prop)
    (h22676 : (¬ p1366) ∨ (¬ p821) ∨ (¬ p690) ∨ p434 ∨ (¬ p11) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p126) ∨ p10)
    (h17589 : (¬ p193) ∨ (¬ p419) ∨ (¬ p690) ∨ (¬ p815) ∨ (¬ p1366))
    (h22675 : p821 ∨ p815) : (¬ p1366) ∨ (¬ p690) ∨ p434 ∨ (¬ p11) ∨ (¬ p126) ∨ (¬ p227) ∨ (¬ p193) ∨ (¬ p266) ∨ p10 ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p434) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p10) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p821) := by
    rcases h22676 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u1)
    · exact False.elim (u2 q3)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u7)
    · exact False.elim (q7 u4)
    · exact False.elim (u8 q8)
  have u11 : (¬ p815) := by
    rcases h17589 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u6)
    · exact False.elim (q1 u9)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u0)
  rcases h22675 with q0 | q1
  · exact False.elim (u10 q0)
  · exact False.elim (u11 q1)

theorem step22691 (p1443 p1493 p1502 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9173 : p1502 ∨ p1503)
    (h9174 : p1502 ∨ p1504)
    (h9175 : p1502 ∨ p1505)
    (h9176 : p1502 ∨ p1506)
    (h9177 : p1502 ∨ p1507)
    (h9085 : p1443 ∨ p1493 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1502 ∨ p1493 ∨ p1443 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1502) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1493) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1443) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9173 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9174 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9175 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9176 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9177 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9085 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22692 (p1443 p1493 p1501 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9168 : p1501 ∨ p1503)
    (h9169 : p1501 ∨ p1504)
    (h9170 : p1501 ∨ p1505)
    (h9171 : p1501 ∨ p1506)
    (h9172 : p1501 ∨ p1507)
    (h9085 : p1443 ∨ p1493 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1501 ∨ p1493 ∨ p1443 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1501) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1493) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1443) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9168 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9169 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9170 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9171 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9172 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9085 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22693 (p1443 p1493 p1500 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9163 : p1500 ∨ p1503)
    (h9164 : p1500 ∨ p1504)
    (h9165 : p1500 ∨ p1505)
    (h9166 : p1500 ∨ p1506)
    (h9167 : p1500 ∨ p1507)
    (h9085 : p1443 ∨ p1493 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1500 ∨ p1493 ∨ p1443 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1500) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1493) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1443) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9163 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9164 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9165 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9166 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9167 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9085 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22694 (p1443 p1493 p1499 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9158 : p1499 ∨ p1503)
    (h9159 : p1499 ∨ p1504)
    (h9160 : p1499 ∨ p1505)
    (h9161 : p1499 ∨ p1506)
    (h9162 : p1499 ∨ p1507)
    (h9085 : p1443 ∨ p1493 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1499 ∨ p1493 ∨ p1443 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1499) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1493) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1443) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9158 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9159 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9160 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9161 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9162 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9085 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22696 (p1443 p1490 p1502 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9173 : p1502 ∨ p1503)
    (h9174 : p1502 ∨ p1504)
    (h9175 : p1502 ∨ p1505)
    (h9176 : p1502 ∨ p1506)
    (h9177 : p1502 ∨ p1507)
    (h9100 : p1443 ∨ p1490 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1502 ∨ p1490 ∨ p1443 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1502) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1490) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1443) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9173 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9174 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9175 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9176 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9177 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22697 (p1443 p1490 p1501 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9168 : p1501 ∨ p1503)
    (h9169 : p1501 ∨ p1504)
    (h9170 : p1501 ∨ p1505)
    (h9171 : p1501 ∨ p1506)
    (h9172 : p1501 ∨ p1507)
    (h9100 : p1443 ∨ p1490 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1501 ∨ p1490 ∨ p1443 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1501) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1490) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1443) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9168 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9169 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9170 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9171 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9172 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22698 (p1443 p1490 p1500 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9163 : p1500 ∨ p1503)
    (h9164 : p1500 ∨ p1504)
    (h9165 : p1500 ∨ p1505)
    (h9166 : p1500 ∨ p1506)
    (h9167 : p1500 ∨ p1507)
    (h9100 : p1443 ∨ p1490 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1500 ∨ p1490 ∨ p1443 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1500) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1490) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1443) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9163 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9164 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9165 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9166 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9167 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22699 (p1443 p1490 p1499 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9158 : p1499 ∨ p1503)
    (h9159 : p1499 ∨ p1504)
    (h9160 : p1499 ∨ p1505)
    (h9161 : p1499 ∨ p1506)
    (h9162 : p1499 ∨ p1507)
    (h9100 : p1443 ∨ p1490 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1499 ∨ p1490 ∨ p1443 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1499) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1490) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1443) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9158 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9159 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9160 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9161 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9162 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22701 (p1492 p1495 p1502 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9173 : p1502 ∨ p1503)
    (h9174 : p1502 ∨ p1504)
    (h9175 : p1502 ∨ p1505)
    (h9176 : p1502 ∨ p1506)
    (h9177 : p1502 ∨ p1507)
    (h9078 : p1492 ∨ p1495 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1502 ∨ p1492 ∨ p1495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1502) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1492) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1495) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9173 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9174 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9175 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9176 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9177 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9078 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22702 (p1492 p1495 p1501 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9168 : p1501 ∨ p1503)
    (h9169 : p1501 ∨ p1504)
    (h9170 : p1501 ∨ p1505)
    (h9171 : p1501 ∨ p1506)
    (h9172 : p1501 ∨ p1507)
    (h9078 : p1492 ∨ p1495 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1501 ∨ p1492 ∨ p1495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1501) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1492) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1495) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9168 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9169 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9170 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9171 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9172 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9078 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22703 (p1492 p1495 p1500 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9163 : p1500 ∨ p1503)
    (h9164 : p1500 ∨ p1504)
    (h9165 : p1500 ∨ p1505)
    (h9166 : p1500 ∨ p1506)
    (h9167 : p1500 ∨ p1507)
    (h9078 : p1492 ∨ p1495 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1500 ∨ p1492 ∨ p1495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1500) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1492) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1495) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9163 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9164 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9165 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9166 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9167 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9078 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22704 (p1492 p1495 p1499 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9158 : p1499 ∨ p1503)
    (h9159 : p1499 ∨ p1504)
    (h9160 : p1499 ∨ p1505)
    (h9161 : p1499 ∨ p1506)
    (h9162 : p1499 ∨ p1507)
    (h9078 : p1492 ∨ p1495 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1499 ∨ p1492 ∨ p1495 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1499) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1492) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1495) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9158 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9159 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9160 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9161 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9162 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9078 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22706 (p85 p576 p983 p1061 p1100 p1454 p1644 : Prop)
    (h21912 : p1100)
    (h18934 : (¬ p85) ∨ (¬ p576) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1100) ∨ (¬ p1454) ∨ (¬ p1644)) : (¬ p1644) ∨ (¬ p576) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p85) ∨ (¬ p1454) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1644 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h18934 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)

theorem step22707 (p8 p41 p83 p189 p576 p657 p1100 p1333 : Prop)
    (h21912 : p1100)
    (h19966 : (¬ p8) ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1333)) : (¬ p576) ∨ (¬ p189) ∨ (¬ p657) ∨ (¬ p1333) ∨ (¬ p8) ∨ (¬ p41) ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1100 := by
    exact h21912
  rcases h19966 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u3)

theorem step22708 (p102 p139 p241 p306 p581 p918 : Prop)
    (h22404 : p139)
    (h17256 : (¬ p102) ∨ (¬ p139) ∨ (¬ p241) ∨ (¬ p306) ∨ (¬ p581) ∨ (¬ p918)) : (¬ p581) ∨ (¬ p306) ∨ (¬ p241) ∨ (¬ p102) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p241 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p139 := by
    exact h22404
  rcases h17256 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u4)

theorem step22709 (p41 p83 p110 p166 p189 p918 p1061 p1076 p1100 : Prop)
    (h21912 : p1100)
    (h17557 : (¬ p41) ∨ (¬ p83) ∨ (¬ p110) ∨ (¬ p166) ∨ (¬ p189) ∨ (¬ p918) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p1100)) : (¬ p189) ∨ (¬ p918) ∨ (¬ p83) ∨ (¬ p166) ∨ (¬ p110) ∨ (¬ p1061) ∨ (¬ p41) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p166 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1100 := by
    exact h21912
  rcases h17557 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u8)

theorem step22710 (p124 p125 p139 p258 p323 : Prop)
    (h22404 : p139)
    (h19760 : (¬ p124) ∨ (¬ p125) ∨ (¬ p139) ∨ (¬ p258) ∨ (¬ p323)) : (¬ p258) ∨ (¬ p125) ∨ (¬ p323) ∨ (¬ p124) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p139 := by
    exact h22404
  rcases h19760 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u2)

theorem step22711 (p89 p125 p139 p237 p323 p500 p581 p918 : Prop)
    (h22404 : p139)
    (h18343 : (¬ p89) ∨ (¬ p125) ∨ (¬ p139) ∨ (¬ p237) ∨ (¬ p323) ∨ (¬ p500) ∨ (¬ p581) ∨ (¬ p918)) : (¬ p500) ∨ (¬ p125) ∨ (¬ p323) ∨ (¬ p918) ∨ (¬ p237) ∨ (¬ p581) ∨ (¬ p89) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p139 := by
    exact h22404
  rcases h18343 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u6)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u3)

theorem step22712 (p139 p256 p323 p515 p814 : Prop)
    (h22404 : p139)
    (h20554 : (¬ p139) ∨ (¬ p256) ∨ (¬ p323) ∨ (¬ p515) ∨ (¬ p814)) : (¬ p515) ∨ (¬ p814) ∨ (¬ p256) ∨ (¬ p323) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p139 := by
    exact h22404
  rcases h20554 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step22714 (p303 p420 p495 p840 p1061 p1100 p1115 : Prop)
    (h21912 : p1100)
    (h18736 : (¬ p303) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p840) ∨ (¬ p1061) ∨ (¬ p1100) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p840) ∨ (¬ p303) ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h18736 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)

theorem step22715 (p121 p139 p581 p1249 p1493 : Prop)
    (h22404 : p139)
    (h17071 : (¬ p121) ∨ (¬ p139) ∨ (¬ p581) ∨ (¬ p1249) ∨ (¬ p1493)) : (¬ p1493) ∨ (¬ p581) ∨ (¬ p121) ∨ (¬ p1249) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1493 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p139 := by
    exact h22404
  rcases h17071 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step22716 (p85 p864 p983 p1061 p1100 p1249 p1325 : Prop)
    (h21912 : p1100)
    (h20183 : (¬ p85) ∨ (¬ p864) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1100) ∨ (¬ p1249) ∨ (¬ p1325)) : (¬ p864) ∨ (¬ p983) ∨ (¬ p1249) ∨ (¬ p1325) ∨ (¬ p85) ∨ (¬ p1061) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h20183 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step22722 (p17 p83 p420 p438 p579 p983 p1061 p1100 p1335 : Prop)
    (h21912 : p1100)
    (h19273 : (¬ p17) ∨ (¬ p83) ∨ (¬ p420) ∨ (¬ p438) ∨ (¬ p579) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1100) ∨ (¬ p1335)) : (¬ p17) ∨ (¬ p438) ∨ (¬ p83) ∨ (¬ p420) ∨ (¬ p579) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1100 := by
    exact h21912
  rcases h19273 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u7)

theorem step22723 (p3 p6 p107 p139 p258 : Prop)
    (h22404 : p139)
    (h18092 : (¬ p3) ∨ (¬ p6) ∨ (¬ p107) ∨ (¬ p139) ∨ (¬ p258)) : (¬ p258) ∨ (¬ p3) ∨ (¬ p107) ∨ (¬ p6) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p139 := by
    exact h22404
  rcases h18092 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)

theorem step22725 (p45 p85 p110 p167 p1061 p1076 p1100 : Prop)
    (h21912 : p1100)
    (h17556 : (¬ p45) ∨ (¬ p85) ∨ (¬ p110) ∨ (¬ p167) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p1100)) : (¬ p45) ∨ (¬ p110) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p167) ∨ (¬ p85) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h17556 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step22726 (p69 p344 p545 p1061 p1076 p1100 p1187 : Prop)
    (h21912 : p1100)
    (h17594 : (¬ p69) ∨ (¬ p344) ∨ (¬ p545) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p1100) ∨ (¬ p1187)) : (¬ p545) ∨ (¬ p69) ∨ (¬ p344) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h17594 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step22727 (p18 p69 p983 p1061 p1100 p1454 p1666 : Prop)
    (h21912 : p1100)
    (h18957 : (¬ p18) ∨ (¬ p69) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1100) ∨ (¬ p1454) ∨ (¬ p1666)) : (¬ p1454) ∨ (¬ p1666) ∨ (¬ p983) ∨ (¬ p69) ∨ (¬ p1061) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h18957 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u1)

theorem step22729 (p8 p11 p85 p389 p576 p657 p1100 : Prop)
    (h21912 : p1100)
    (h19545 : (¬ p8) ∨ (¬ p11) ∨ (¬ p85) ∨ (¬ p389) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p1100)) : (¬ p389) ∨ (¬ p576) ∨ (¬ p85) ∨ (¬ p11) ∨ (¬ p657) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h19545 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)

theorem step22730 (p8 p45 p85 p134 p657 p1100 p1333 : Prop)
    (h21912 : p1100)
    (h19965 : (¬ p8) ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p134) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1333)) : (¬ p45) ∨ (¬ p657) ∨ (¬ p8) ∨ (¬ p134) ∨ (¬ p85) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h19965 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u5)

theorem step22731 (p8 p304 p346 p494 p1100 : Prop)
    (h21912 : p1100)
    (h16987 : (¬ p8) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p494) ∨ (¬ p1100)) : (¬ p346) ∨ (¬ p494) ∨ (¬ p304) ∨ (¬ p8) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1100 := by
    exact h21912
  rcases h16987 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)

theorem step22732 (p8 p41 p83 p189 p290 p346 p918 p1100 : Prop)
    (h21912 : p1100)
    (h19473 : (¬ p8) ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p290) ∨ (¬ p346) ∨ (¬ p918) ∨ (¬ p1100)) : (¬ p346) ∨ (¬ p290) ∨ (¬ p918) ∨ (¬ p189) ∨ (¬ p8) ∨ (¬ p41) ∨ (¬ p83) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p290 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1100 := by
    exact h21912
  rcases h19473 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u7)

theorem step22733 (p536 p616 p840 p1100 p1287 p1325 p1584 : Prop)
    (h21912 : p1100)
    (h17002 : (¬ p536) ∨ (¬ p616) ∨ (¬ p840) ∨ (¬ p1100) ∨ (¬ p1287) ∨ (¬ p1325) ∨ (¬ p1584)) : (¬ p1584) ∨ (¬ p536) ∨ (¬ p840) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h17002 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)

theorem step22734 (p8 p45 p85 p134 p346 p1077 p1100 : Prop)
    (h21912 : p1100)
    (h19487 : (¬ p8) ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p134) ∨ (¬ p346) ∨ (¬ p1077) ∨ (¬ p1100)) : (¬ p346) ∨ (¬ p45) ∨ (¬ p134) ∨ (¬ p8) ∨ (¬ p1077) ∨ (¬ p85) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h19487 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)

theorem step22735 (p8 p69 p728 p1100 p1141 p1330 p1465 : Prop)
    (h21912 : p1100)
    (h18428 : (¬ p8) ∨ (¬ p69) ∨ (¬ p728) ∨ (¬ p1100) ∨ (¬ p1141) ∨ (¬ p1330) ∨ (¬ p1465)) : (¬ p728) ∨ (¬ p69) ∨ (¬ p8) ∨ (¬ p1330) ∨ (¬ p1141) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h18428 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)

theorem step22736 (p8 p420 p431 p438 p495 p657 p1100 : Prop)
    (h21912 : p1100)
    (h19700 : (¬ p8) ∨ (¬ p420) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p495) ∨ (¬ p657) ∨ (¬ p1100)) : (¬ p420) ∨ (¬ p495) ∨ (¬ p431) ∨ (¬ p8) ∨ (¬ p657) ∨ (¬ p438) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h19700 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u6)

theorem step22737 (p8 p456 p495 p532 p728 p1100 p1330 : Prop)
    (h21912 : p1100)
    (h20206 : (¬ p8) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p532) ∨ (¬ p728) ∨ (¬ p1100) ∨ (¬ p1330)) : (¬ p532) ∨ (¬ p728) ∨ (¬ p1330) ∨ (¬ p456) ∨ (¬ p8) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h20206 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u2)

theorem step22738 (p18 p69 p224 p351 p386 p406 p680 p1100 p1206 : Prop)
    (h21912 : p1100)
    (h19983 : (¬ p18) ∨ (¬ p69) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p386) ∨ (¬ p406) ∨ (¬ p680) ∨ (¬ p1100) ∨ (¬ p1206)) : (¬ p680) ∨ (¬ p351) ∨ (¬ p1206) ∨ (¬ p224) ∨ (¬ p386) ∨ (¬ p406) ∨ (¬ p69) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1100 := by
    exact h21912
  rcases h19983 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u2)

theorem step22739 (p8 p106 p225 p455 p494 p636 p961 p1100 : Prop)
    (h21912 : p1100)
    (h20185 : (¬ p8) ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p455) ∨ (¬ p494) ∨ (¬ p636) ∨ (¬ p961) ∨ (¬ p1100)) : (¬ p961) ∨ (¬ p455) ∨ (¬ p8) ∨ (¬ p225) ∨ (¬ p494) ∨ (¬ p106) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1100 := by
    exact h21912
  rcases h20185 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u7)

theorem step22740 (p6 p139 p301 p328 p481 : Prop)
    (h22404 : p139)
    (h18060 : (¬ p6) ∨ (¬ p139) ∨ (¬ p301) ∨ (¬ p328) ∨ (¬ p481)) : (¬ p481) ∨ (¬ p6) ∨ (¬ p301) ∨ (¬ p328) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p139 := by
    exact h22404
  rcases h18060 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step22741 (p108 p139 p258 p309 p544 p710 : Prop)
    (h22404 : p139)
    (h18073 : (¬ p108) ∨ (¬ p139) ∨ (¬ p258) ∨ (¬ p309) ∨ (¬ p544) ∨ (¬ p710)) : (¬ p710) ∨ (¬ p108) ∨ (¬ p309) ∨ (¬ p258) ∨ (¬ p544) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p139 := by
    exact h22404
  rcases h18073 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u0)

theorem step22743 (p102 p139 p185 p255 p256 : Prop)
    (h22404 : p139)
    (h16167 : (¬ p102) ∨ (¬ p139) ∨ (¬ p185) ∨ (¬ p255) ∨ (¬ p256)) : (¬ p185) ∨ (¬ p255) ∨ (¬ p102) ∨ (¬ p256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p255 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p139 := by
    exact h22404
  rcases h16167 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step22744 (p121 p139 p458 p499 p579 p1232 : Prop)
    (h22404 : p139)
    (h16330 : (¬ p121) ∨ (¬ p139) ∨ (¬ p458) ∨ (¬ p499) ∨ (¬ p579) ∨ (¬ p1232)) : (¬ p458) ∨ (¬ p121) ∨ (¬ p1232) ∨ (¬ p579) ∨ (¬ p499) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p458 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p139 := by
    exact h22404
  rcases h16330 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step22745 (p108 p139 p258 p534 p726 : Prop)
    (h22404 : p139)
    (h16451 : (¬ p108) ∨ (¬ p139) ∨ (¬ p258) ∨ (¬ p534) ∨ (¬ p726)) : (¬ p726) ∨ (¬ p534) ∨ (¬ p258) ∨ (¬ p108) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p139 := by
    exact h22404
  rcases h16451 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step22746 (p102 p139 p283 p1077 p1115 : Prop)
    (h22404 : p139)
    (h17264 : (¬ p102) ∨ (¬ p139) ∨ (¬ p283) ∨ (¬ p1077) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p102) ∨ (¬ p283) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p139 := by
    exact h22404
  rcases h17264 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)

theorem step22747 (p139 p301 p303 p329 p996 : Prop)
    (h22404 : p139)
    (h17948 : (¬ p139) ∨ (¬ p301) ∨ (¬ p303) ∨ (¬ p329) ∨ (¬ p996)) : (¬ p996) ∨ (¬ p301) ∨ (¬ p329) ∨ (¬ p303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p139 := by
    exact h22404
  rcases h17948 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u0)

theorem step22748 (p21 p139 p583 : Prop)
    (h22404 : p139)
    (h14345 : (¬ p21) ∨ (¬ p139) ∨ p583) : p583 ∨ (¬ p21) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p583) := fun hu => hn (Or.inl hu)
  have u1 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p139 := by
    exact h22404
  rcases h14345 with q0 | q1 | q2
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)

theorem step22749 (p139 p323 p364 p406 p514 p858 : Prop)
    (h22404 : p139)
    (h20552 : (¬ p139) ∨ (¬ p323) ∨ (¬ p364) ∨ (¬ p406) ∨ (¬ p514) ∨ (¬ p858)) : (¬ p514) ∨ (¬ p364) ∨ (¬ p858) ∨ (¬ p323) ∨ (¬ p406) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p514 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p139 := by
    exact h22404
  rcases h20552 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u2)

theorem step22750 (p102 p139 p283 p756 p1584 : Prop)
    (h22404 : p139)
    (h20605 : (¬ p102) ∨ (¬ p139) ∨ (¬ p283) ∨ (¬ p756) ∨ (¬ p1584)) : (¬ p1584) ∨ (¬ p756) ∨ (¬ p102) ∨ (¬ p283) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p139 := by
    exact h22404
  rcases h20605 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u0)

theorem step22751 (p139 p323 p364 p581 p819 p1385 : Prop)
    (h22404 : p139)
    (h20614 : (¬ p139) ∨ (¬ p323) ∨ (¬ p364) ∨ (¬ p581) ∨ (¬ p819) ∨ (¬ p1385)) : (¬ p364) ∨ (¬ p581) ∨ (¬ p1385) ∨ (¬ p819) ∨ (¬ p323) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p819 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p139 := by
    exact h22404
  rcases h20614 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step22752 (p1 p108 p139 p301 p438 p1366 : Prop)
    (h22404 : p139)
    (h16605 : (¬ p1) ∨ (¬ p108) ∨ (¬ p139) ∨ (¬ p301) ∨ (¬ p438) ∨ (¬ p1366)) : (¬ p301) ∨ (¬ p438) ∨ (¬ p1) ∨ (¬ p108) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p139 := by
    exact h22404
  rcases h16605 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)

theorem step22753 (p8 p102 p139 p283 p306 p836 : Prop)
    (h22404 : p139)
    (h18328 : (¬ p8) ∨ (¬ p102) ∨ (¬ p139) ∨ (¬ p283) ∨ (¬ p306) ∨ (¬ p836)) : (¬ p8) ∨ (¬ p836) ∨ (¬ p102) ∨ (¬ p306) ∨ (¬ p283) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p139 := by
    exact h22404
  rcases h18328 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u1)

theorem step22754 (p11 p18 p139 p423 p1211 : Prop)
    (h22404 : p139)
    (h16439 : (¬ p11) ∨ (¬ p18) ∨ (¬ p139) ∨ (¬ p423) ∨ (¬ p1211)) : (¬ p423) ∨ (¬ p1211) ∨ (¬ p11) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p139 := by
    exact h22404
  rcases h16439 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)

theorem step22755 (p12 p108 p139 p265 p304 p1076 : Prop)
    (h22404 : p139)
    (h16628 : (¬ p12) ∨ (¬ p108) ∨ (¬ p139) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p1076)) : (¬ p108) ∨ (¬ p304) ∨ (¬ p12) ∨ (¬ p1076) ∨ (¬ p265) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p139 := by
    exact h22404
  rcases h16628 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u3)

theorem step22756 (p18 p68 p139 p301 p328 p481 : Prop)
    (h22404 : p139)
    (h17639 : (¬ p18) ∨ (¬ p68) ∨ (¬ p139) ∨ (¬ p301) ∨ (¬ p328) ∨ (¬ p481)) : (¬ p328) ∨ (¬ p481) ∨ (¬ p68) ∨ (¬ p301) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p68 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p139 := by
    exact h22404
  rcases h17639 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u1)

theorem step22757 (p14 p18 p107 p139 p258 : Prop)
    (h22404 : p139)
    (h17454 : (¬ p14) ∨ (¬ p18) ∨ (¬ p107) ∨ (¬ p139) ∨ (¬ p258)) : (¬ p107) ∨ (¬ p14) ∨ (¬ p18) ∨ (¬ p258) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p139 := by
    exact h22404
  rcases h17454 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)

theorem step22758 (p89 p102 p139 p304 p500 p581 p790 p1385 : Prop)
    (h22404 : p139)
    (h20615 : (¬ p89) ∨ (¬ p102) ∨ (¬ p139) ∨ (¬ p304) ∨ (¬ p500) ∨ (¬ p581) ∨ (¬ p790) ∨ (¬ p1385)) : (¬ p500) ∨ (¬ p1385) ∨ (¬ p790) ∨ (¬ p89) ∨ (¬ p102) ∨ (¬ p581) ∨ (¬ p304) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p89 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p139 := by
    exact h22404
  rcases h20615 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u2)
  · exact False.elim (q7 u1)

theorem step22759 (p41 p83 p189 p224 p406 p680 p842 p1100 p1385 : Prop)
    (h21912 : p1100)
    (h19837 : (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p406) ∨ (¬ p680) ∨ (¬ p842) ∨ (¬ p1100) ∨ (¬ p1385)) : (¬ p680) ∨ (¬ p842) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p83) ∨ (¬ p41) ∨ (¬ p406) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1100 := by
    exact h21912
  rcases h19837 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u7)

theorem step22761 (p69 p435 p983 p1061 p1100 p1187 p1335 : Prop)
    (h21912 : p1100)
    (h18723 : (¬ p69) ∨ (¬ p435) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1100) ∨ (¬ p1187) ∨ (¬ p1335)) : (¬ p435) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p69) ∨ (¬ p1187) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h18723 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step22762 (p8 p12 p13 p225 p456 p495 p1100 : Prop)
    (h21912 : p1100)
    (h20178 : (¬ p8) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p225) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p1100)) : (¬ p225) ∨ (¬ p8) ∨ (¬ p495) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p456) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h20178 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u6)

theorem step22763 (p6 p8 p19 p64 p657 p1100 p1187 p1333 : Prop)
    (h21912 : p1100)
    (h18004 : (¬ p6) ∨ (¬ p8) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1187) ∨ (¬ p1333)) : (¬ p8) ∨ (¬ p1187) ∨ (¬ p6) ∨ (¬ p19) ∨ (¬ p657) ∨ (¬ p64) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1100 := by
    exact h21912
  rcases h18004 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)
  · exact False.elim (q7 u6)

theorem step22764 (p8 p18 p69 p101 p657 p1100 p1333 : Prop)
    (h21912 : p1100)
    (h18429 : (¬ p8) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1333)) : (¬ p657) ∨ (¬ p8) ∨ (¬ p1333) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p101) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h18429 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u0)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u2)

theorem step22765 (p8 p18 p69 p389 p657 p1100 p1206 : Prop)
    (h21912 : p1100)
    (h19840 : (¬ p8) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1206)) : (¬ p389) ∨ (¬ p69) ∨ (¬ p1206) ∨ (¬ p18) ∨ (¬ p8) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h19840 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u2)

theorem step22766 (p6 p8 p19 p64 p389 p657 p1100 p1141 p1208 : Prop)
    (h21912 : p1100)
    (h19998 : (¬ p6) ∨ (¬ p8) ∨ (¬ p19) ∨ (¬ p64) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p1100) ∨ (¬ p1141) ∨ (¬ p1208)) : (¬ p1208) ∨ (¬ p8) ∨ (¬ p6) ∨ (¬ p19) ∨ (¬ p389) ∨ (¬ p657) ∨ (¬ p64) ∨ (¬ p1141) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1208 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1100 := by
    exact h21912
  rcases h19998 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u8)
  · exact False.elim (q7 u7)
  · exact False.elim (q8 u0)

theorem step22767 (p8 p17 p83 p172 p225 p581 p918 p1100 : Prop)
    (h21912 : p1100)
    (h19296 : (¬ p8) ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p172) ∨ (¬ p225) ∨ (¬ p581) ∨ (¬ p918) ∨ (¬ p1100)) : (¬ p172) ∨ (¬ p225) ∨ (¬ p8) ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p172 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1100 := by
    exact h21912
  rcases h19296 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)
  · exact False.elim (q7 u7)

theorem step22768 (p8 p17 p83 p581 p657 p864 p1100 p1249 : Prop)
    (h21912 : p1100)
    (h20201 : (¬ p8) ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p657) ∨ (¬ p864) ∨ (¬ p1100) ∨ (¬ p1249)) : (¬ p864) ∨ (¬ p17) ∨ (¬ p8) ∨ (¬ p581) ∨ (¬ p83) ∨ (¬ p657) ∨ (¬ p1249) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p864 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p1100 := by
    exact h21912
  rcases h20201 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u6)

theorem step22769 (p8 p85 p106 p225 p258 p576 p1100 : Prop)
    (h21912 : p1100)
    (h20136 : (¬ p8) ∨ (¬ p85) ∨ (¬ p106) ∨ (¬ p225) ∨ (¬ p258) ∨ (¬ p576) ∨ (¬ p1100)) : (¬ p8) ∨ (¬ p225) ∨ (¬ p85) ∨ (¬ p106) ∨ (¬ p258) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h20136 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step22771 (p8 p69 p419 p728 p1100 p1187 p1334 : Prop)
    (h21912 : p1100)
    (h18304 : (¬ p8) ∨ (¬ p69) ∨ (¬ p419) ∨ (¬ p728) ∨ (¬ p1100) ∨ (¬ p1187) ∨ (¬ p1334)) : (¬ p728) ∨ (¬ p69) ∨ (¬ p1187) ∨ (¬ p8) ∨ (¬ p1334) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h18304 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u4)

theorem step22772 (p85 p983 p1015 p1061 p1100 p1335 p1385 : Prop)
    (h21912 : p1100)
    (h16894 : (¬ p85) ∨ (¬ p983) ∨ (¬ p1015) ∨ (¬ p1061) ∨ (¬ p1100) ∨ (¬ p1335) ∨ (¬ p1385)) : (¬ p1015) ∨ (¬ p1385) ∨ (¬ p1335) ∨ (¬ p1061) ∨ (¬ p983) ∨ (¬ p85) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h16894 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u1)

theorem step22793 (p6 p24 p64 p420 p438 p983 p1061 p1100 p1335 : Prop)
    (h21912 : p1100)
    (h18713 : (¬ p6) ∨ (¬ p24) ∨ (¬ p64) ∨ (¬ p420) ∨ (¬ p438) ∨ (¬ p983) ∨ (¬ p1061) ∨ (¬ p1100) ∨ (¬ p1335)) : (¬ p64) ∨ (¬ p420) ∨ (¬ p6) ∨ (¬ p983) ∨ (¬ p24) ∨ (¬ p1061) ∨ (¬ p438) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p1100 := by
    exact h21912
  rcases h18713 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u8)
  · exact False.elim (q8 u7)

theorem step22794 (p139 p207 p268 : Prop)
    (h22404 : p139)
    (h12051 : (¬ p139) ∨ (¬ p207) ∨ p268) : p268 ∨ (¬ p207) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p268) := fun hu => hn (Or.inl hu)
  have u1 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p139 := by
    exact h22404
  rcases h12051 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u1)
  · exact False.elim (u0 q2)

theorem step22795 (p18 p69 p101 p285 p1061 p1100 p1115 : Prop)
    (h21912 : p1100)
    (h18719 : (¬ p18) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p285) ∨ (¬ p1061) ∨ (¬ p1100) ∨ (¬ p1115)) : (¬ p1115) ∨ (¬ p285) ∨ (¬ p1061) ∨ (¬ p101) ∨ (¬ p69) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p285 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p1100 := by
    exact h21912
  rcases h18719 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u0)

theorem step22821 (p2 p18 p64 p86 p124 p139 p234 p258 p266 : Prop)
    (h22404 : p139)
    (h18817 : (¬ p2) ∨ (¬ p18) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p124) ∨ (¬ p139) ∨ (¬ p234) ∨ (¬ p258) ∨ (¬ p266)) : (¬ p234) ∨ (¬ p124) ∨ (¬ p2) ∨ (¬ p18) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p258) ∨ (¬ p266) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p139 := by
    exact h22404
  rcases h18817 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u0)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step22822 (p11 p18 p139 p423 p1206 : Prop)
    (h22404 : p139)
    (h21823 : (¬ p423) ∨ p1206 ∨ (¬ p139) ∨ (¬ p11) ∨ (¬ p18)) : (¬ p423) ∨ p1206 ∨ (¬ p11) ∨ (¬ p18) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1206) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p139 := by
    exact h22404
  rcases h21823 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step22826 (p12 p139 p258 p268 p309 p310 p1076 : Prop)
    (h22404 : p139)
    (h22252 : (¬ p258) ∨ (¬ p268) ∨ (¬ p309) ∨ (¬ p310) ∨ (¬ p139) ∨ (¬ p1076) ∨ (¬ p12)) : (¬ p258) ∨ (¬ p268) ∨ (¬ p1076) ∨ (¬ p310) ∨ (¬ p309) ∨ (¬ p12) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p139 := by
    exact h22404
  rcases h22252 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u5)

theorem step22829 (p2 p194 p224 p256 p419 p435 p657 p662 p666 p980 p983 p1328 p1333 p1335 p1366 p1443 p1452 : Prop)
    (h20687 : p980 ∨ p983)
    (h17334 : (¬ p980) ∨ p1335)
    (h17407 : (¬ p256) ∨ (¬ p662) ∨ (¬ p980) ∨ (¬ p1443) ∨ (¬ p1452))
    (h17511 : (¬ p2) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p1443) ∨ (¬ p1452))
    (h21721 : p662 ∨ p657)
    (h21910 : p1366 ∨ p435)
    (h6747 : (¬ p224) ∨ (¬ p657))
    (h12635 : (¬ p419) ∨ (¬ p1328) ∨ (¬ p1366))
    (h22413 : p666 ∨ p224)
    (h21460 : p1328 ∨ p1333)
    (h15453 : (¬ p666) ∨ p983 ∨ (¬ p1333)) : p983 ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p983) := fun hu => hn (Or.inl hu)
  have u1 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p980 := by
    rcases h20687 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : p1335 := by
    rcases h17334 with q0 | q1
    · exact False.elim (q0 u7)
    · exact q1
  have u9 : (¬ p662) := by
    rcases h17407 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u4)
    · exact q1
    · exact False.elim (q2 u7)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u2)
  have u10 : (¬ p435) := by
    rcases h17511 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u6)
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u4)
    · exact q3
    · exact False.elim (q4 u8)
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u2)
  have u11 : p657 := by
    rcases h21721 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  have u12 : p1366 := by
    rcases h21910 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u13 : (¬ p224) := by
    rcases h6747 with q0 | q1
    · exact q0
    · exact False.elim (q1 u11)
  have u14 : (¬ p1328) := by
    rcases h12635 with q0 | q1 | q2
    · exact False.elim (q0 u5)
    · exact q1
    · exact False.elim (q2 u12)
  have u15 : p666 := by
    rcases h22413 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  have u16 : p1333 := by
    rcases h21460 with q0 | q1
    · exact False.elim (u14 q0)
    · exact q1
  rcases h15453 with q0 | q1 | q2
  · exact False.elim (q0 u15)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u16)

theorem step22830 (p657 p664 p670 p671 p672 p673 p674 p675 p676 p677 p678 p679 : Prop)
    (h3801 : p657 ∨ p664 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679))
    (h3863 : p670 ∨ p679)
    (h3868 : p671 ∨ p679)
    (h3873 : p672 ∨ p679)
    (h3878 : p673 ∨ p679)
    (h3883 : p674 ∨ p679)
    (h3776 : p657 ∨ p664 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : (¬ p677) ∨ p664 ∨ p657 ∨ (¬ p678) ∨ (¬ p675) ∨ (¬ p676) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p677 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p664) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p678 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p675 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p676 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p679) := by
    rcases h3801 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u3)
    · exact q6
  have u7 : p670 := by
    rcases h3863 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p671 := by
    rcases h3868 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p672 := by
    rcases h3873 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p673 := by
    rcases h3878 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p674 := by
    rcases h3883 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h3776 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22831 (p657 p664 p675 p676 p677 p678 : Prop)
    (h20767 : p675 ∨ p664 ∨ p657)
    (h20768 : p676 ∨ p664 ∨ p657)
    (h20769 : p677 ∨ p664 ∨ p657)
    (h20770 : p678 ∨ p664 ∨ p657)
    (h22830 : (¬ p677) ∨ p664 ∨ p657 ∨ (¬ p678) ∨ (¬ p675) ∨ (¬ p676)) : p664 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p664) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p657) := fun hu => hn (Or.inr hu)
  have u2 : p675 := by
    rcases h20767 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p676 := by
    rcases h20768 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p677 := by
    rcases h20769 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p678 := by
    rcases h20770 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22830 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step22833 (p2 p38 p49 p69 p85 p419 p595 p616 p620 p687 p1188 p1334 p1387 p1394 p1542 p1545 : Prop)
    (h21790 : p616 ∨ p595)
    (h22669 : p620 ∨ p616)
    (h11318 : (¬ p85) ∨ p616 ∨ (¬ p1387))
    (h22684 : p38 ∨ (¬ p595) ∨ (¬ p1188) ∨ p69)
    (h22650 : p1394 ∨ p1387)
    (h18237 : (¬ p2) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p1334) ∨ (¬ p1542))
    (h19706 : (¬ p85) ∨ (¬ p620) ∨ (¬ p687) ∨ (¬ p1394) ∨ (¬ p1545))
    (h20851 : p1542 ∨ p1545) : p616 ∨ (¬ p1188) ∨ p69 ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p687) ∨ (¬ p1334) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p616) := fun hu => hn (Or.inl hu)
  have u1 : p1188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p69) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p595 := by
    rcases h21790 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u10 : p620 := by
    rcases h22669 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : (¬ p1387) := by
    rcases h11318 with q0 | q1 | q2
    · exact False.elim (q0 u4)
    · exact False.elim (u0 q1)
    · exact q2
  have u12 : p38 := by
    rcases h22684 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u9)
    · exact False.elim (q2 u1)
    · exact False.elim (u2 q3)
  have u13 : p1394 := by
    rcases h22650 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u14 : (¬ p1542) := by
    rcases h18237 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u12)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u7)
    · exact False.elim (q5 u9)
    · exact False.elim (q6 u6)
    · exact q7
  have u15 : (¬ p1545) := by
    rcases h19706 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u10)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u13)
    · exact q4
  rcases h20851 with q0 | q1
  · exact False.elim (u14 q0)
  · exact False.elim (u15 q1)

theorem step22834 (p2 p15 p49 p69 p84 p85 p234 p256 p419 p595 p616 p687 p796 p1188 p1189 p1193 p1334 p1443 p1452 : Prop)
    (h22278 : p84 ∨ (¬ p85))
    (h6604 : (¬ p15) ∨ (¬ p69))
    (h16362 : (¬ p15) ∨ (¬ p85) ∨ (¬ p234) ∨ (¬ p796))
    (h22095 : p1188 ∨ p234)
    (h22833 : p616 ∨ (¬ p1188) ∨ p69 ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p687) ∨ (¬ p1334) ∨ (¬ p419) ∨ (¬ p2))
    (h10651 : (¬ p595) ∨ (¬ p616))
    (h17508 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p616) ∨ (¬ p1189) ∨ (¬ p1443) ∨ (¬ p1452))
    (h9388 : (¬ p15) ∨ p595 ∨ (¬ p1193))
    (h21784 : p1189 ∨ p1193) : (¬ p15) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p687) ∨ (¬ p1334) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p796) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))
  have u11 : p84 := by
    rcases h22278 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u12 : (¬ p69) := by
    rcases h6604 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u13 : (¬ p234) := by
    rcases h16362 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u2)
    · exact q2
    · exact False.elim (q3 u7)
  have u14 : p1188 := by
    rcases h22095 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  have u15 : p616 := by
    rcases h22833 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact q0
    · exact False.elim (q1 u14)
    · exact False.elim (u12 q2)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u2)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u4)
    · exact False.elim (q7 u9)
    · exact False.elim (q8 u10)
  have u16 : (¬ p595) := by
    rcases h10651 with q0 | q1
    · exact q0
    · exact False.elim (q1 u15)
  have u17 : (¬ p1189) := by
    rcases h17508 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u11)
    · exact False.elim (q3 u8)
    · exact False.elim (q4 u9)
    · exact False.elim (q5 u15)
    · exact q6
    · exact False.elim (q7 u5)
    · exact False.elim (q8 u6)
  have u18 : (¬ p1193) := by
    rcases h9388 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (u16 q1)
    · exact q2
  rcases h21784 with q0 | q1
  · exact False.elim (u17 q0)
  · exact False.elim (u18 q1)

theorem step22835 (p18 p19 p32 p33 p34 p35 p36 p37 : Prop)
    (h125 : p32 ∨ p33)
    (h126 : p32 ∨ p34)
    (h127 : p32 ∨ p35)
    (h128 : p32 ∨ p36)
    (h129 : p32 ∨ p37)
    (h42 : p18 ∨ p19 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p32 ∨ p19 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p32) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p19) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p33 := by
    rcases h125 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p34 := by
    rcases h126 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p35 := by
    rcases h127 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p36 := by
    rcases h128 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p37 := by
    rcases h129 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h42 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22836 (p18 p19 p31 p33 p34 p35 p36 p37 : Prop)
    (h120 : p31 ∨ p33)
    (h121 : p31 ∨ p34)
    (h122 : p31 ∨ p35)
    (h123 : p31 ∨ p36)
    (h124 : p31 ∨ p37)
    (h42 : p18 ∨ p19 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p31 ∨ p19 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p31) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p19) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p33 := by
    rcases h120 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p34 := by
    rcases h121 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p35 := by
    rcases h122 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p36 := by
    rcases h123 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p37 := by
    rcases h124 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h42 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22837 (p18 p19 p30 p33 p34 p35 p36 p37 : Prop)
    (h115 : p30 ∨ p33)
    (h116 : p30 ∨ p34)
    (h117 : p30 ∨ p35)
    (h118 : p30 ∨ p36)
    (h119 : p30 ∨ p37)
    (h42 : p18 ∨ p19 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p30 ∨ p19 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p30) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p19) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p33 := by
    rcases h115 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p34 := by
    rcases h116 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p35 := by
    rcases h117 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p36 := by
    rcases h118 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p37 := by
    rcases h119 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h42 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22838 (p18 p19 p29 p33 p34 p35 p36 p37 : Prop)
    (h110 : p29 ∨ p33)
    (h111 : p29 ∨ p34)
    (h112 : p29 ∨ p35)
    (h113 : p29 ∨ p36)
    (h114 : p29 ∨ p37)
    (h42 : p18 ∨ p19 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p29 ∨ p19 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p29) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p19) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p33 := by
    rcases h110 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p34 := by
    rcases h111 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p35 := by
    rcases h112 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p36 := by
    rcases h113 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p37 := by
    rcases h114 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h42 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22839 (p18 p19 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 : Prop)
    (h17 : p18 ∨ p19 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32))
    (h105 : p28 ∨ p33)
    (h106 : p28 ∨ p34)
    (h107 : p28 ∨ p35)
    (h108 : p28 ∨ p36)
    (h109 : p28 ∨ p37)
    (h42 : p18 ∨ p19 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : (¬ p29) ∨ (¬ p31) ∨ p18 ∨ p19 ∨ (¬ p30) ∨ (¬ p32) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p29 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p31 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p19) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p30 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p32 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p28) := by
    rcases h17 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u5)
  have u7 : p33 := by
    rcases h105 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p34 := by
    rcases h106 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p35 := by
    rcases h107 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p36 := by
    rcases h108 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p37 := by
    rcases h109 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h42 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22840 (p18 p19 p29 p30 p31 p32 : Prop)
    (h22835 : p32 ∨ p19 ∨ p18)
    (h22836 : p31 ∨ p19 ∨ p18)
    (h22837 : p30 ∨ p19 ∨ p18)
    (h22838 : p29 ∨ p19 ∨ p18)
    (h22839 : (¬ p29) ∨ (¬ p31) ∨ p18 ∨ p19 ∨ (¬ p30) ∨ (¬ p32)) : p19 ∨ p18 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p19) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p18) := fun hu => hn (Or.inr hu)
  have u2 : p32 := by
    rcases h22835 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p31 := by
    rcases h22836 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p30 := by
    rcases h22837 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p29 := by
    rcases h22838 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22839 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step22841 (p595 p616 p1232 p1289 p1293 p1334 p1542 : Prop)
    (h21790 : p616 ∨ p595)
    (h10564 : p616 ∨ (¬ p1232) ∨ (¬ p1293))
    (h17613 : (¬ p595) ∨ (¬ p1232) ∨ (¬ p1289) ∨ (¬ p1334) ∨ (¬ p1542))
    (h22540 : p1289 ∨ p1293) : (¬ p1232) ∨ (¬ p1542) ∨ p616 ∨ (¬ p1334) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p616) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p595 := by
    rcases h21790 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u5 : (¬ p1293) := by
    rcases h10564 with q0 | q1 | q2
    · exact False.elim (u2 q0)
    · exact False.elim (q1 u0)
    · exact q2
  have u6 : (¬ p1289) := by
    rcases h17613 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u0)
    · exact q2
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u1)
  rcases h22540 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step22842 (p85 p161 p457 p461 p495 p1225 p1229 p1452 p1489 : Prop)
    (h16384 : (¬ p85) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1489))
    (h10248 : (¬ p457) ∨ (¬ p495) ∨ (¬ p1229))
    (h21572 : p161 ∨ p1225)
    (h22380 : p461 ∨ p457)
    (h11159 : (¬ p161) ∨ (¬ p461) ∨ (¬ p1452)) : (¬ p1229) ∨ (¬ p495) ∨ (¬ p85) ∨ (¬ p1452) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p1225) := by
    rcases h16384 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u4)
  have u6 : (¬ p457) := by
    rcases h10248 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u0)
  have u7 : p161 := by
    rcases h21572 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u8 : p461 := by
    rcases h22380 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h11159 with q0 | q1 | q2
  · exact False.elim (q0 u7)
  · exact False.elim (q1 u8)
  · exact False.elim (q2 u3)

theorem step22843 (p2 p3 p14 p18 p64 p86 p104 p110 p229 p234 p256 p288 p557 p1061 p1076 : Prop)
    (h17095 : (¬ p2) ∨ (¬ p3) ∨ (¬ p18) ∨ (¬ p234))
    (h21089 : p3 ∨ p557)
    (h12197 : (¬ p104) ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1076))
    (h17198 : (¬ p14) ∨ (¬ p18) ∨ (¬ p557) ∨ (¬ p1061) ∨ (¬ p1076))
    (h22241 : p110 ∨ p104)
    (h21834 : p229 ∨ p14)
    (h17191 : (¬ p2) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p110) ∨ (¬ p229) ∨ (¬ p234) ∨ (¬ p256) ∨ (¬ p288)) : (¬ p18) ∨ (¬ p234) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p288) ∨ (¬ p256) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p3) := by
    rcases h17095 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u8)
    · exact q1
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u1)
  have u10 : p557 := by
    rcases h21089 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  have u11 : (¬ p104) := by
    rcases h12197 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u10)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
  have u12 : (¬ p14) := by
    rcases h17198 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u10)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
  have u13 : p110 := by
    rcases h22241 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u14 : p229 := by
    rcases h21834 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  rcases h17191 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u13)
  · exact False.elim (q4 u14)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u6)

theorem step22844 (p86 p126 p256 p434 p596 p616 p1232 p1287 p1334 p1542 p1545 : Prop)
    (h11936 : (¬ p434) ∨ (¬ p596) ∨ (¬ p1545))
    (h17187 : (¬ p86) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p434) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1334))
    (h20851 : p1542 ∨ p1545)
    (h22841 : (¬ p1232) ∨ (¬ p1542) ∨ p616 ∨ (¬ p1334)) : (¬ p434) ∨ (¬ p1287) ∨ (¬ p1232) ∨ (¬ p596) ∨ (¬ p86) ∨ (¬ p1334) ∨ (¬ p256) ∨ (¬ p126) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p1545) := by
    rcases h11936 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u3)
    · exact q2
  have u9 : (¬ p616) := by
    rcases h17187 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u5)
  have u10 : p1542 := by
    rcases h20851 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h22841 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u10)
  · exact False.elim (u9 q2)
  · exact False.elim (q3 u5)

theorem step22845 (p85 p616 p620 p687 p1232 p1334 p1387 p1394 p1542 p1545 : Prop)
    (h22669 : p620 ∨ p616)
    (h11318 : (¬ p85) ∨ p616 ∨ (¬ p1387))
    (h22841 : (¬ p1232) ∨ (¬ p1542) ∨ p616 ∨ (¬ p1334))
    (h22650 : p1394 ∨ p1387)
    (h20851 : p1542 ∨ p1545)
    (h19706 : (¬ p85) ∨ (¬ p620) ∨ (¬ p687) ∨ (¬ p1394) ∨ (¬ p1545)) : p616 ∨ (¬ p1232) ∨ (¬ p85) ∨ (¬ p687) ∨ (¬ p1334) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p616) := fun hu => hn (Or.inl hu)
  have u1 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p620 := by
    rcases h22669 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : (¬ p1387) := by
    rcases h11318 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact False.elim (u0 q1)
    · exact q2
  have u7 : (¬ p1542) := by
    rcases h22841 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (u0 q2)
    · exact False.elim (q3 u4)
  have u8 : p1394 := by
    rcases h22650 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1545 := by
    rcases h20851 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h19706 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)

theorem step22847 (p1077 p1079 p1085 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6450 : p1085 ∨ p1090)
    (h6451 : p1085 ∨ p1091)
    (h6452 : p1085 ∨ p1092)
    (h6453 : p1085 ∨ p1093)
    (h6454 : p1085 ∨ p1094)
    (h6382 : p1077 ∨ p1079 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1085 ∨ p1079 ∨ p1077 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1085) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1079) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1077) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1090 := by
    rcases h6450 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1091 := by
    rcases h6451 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1092 := by
    rcases h6452 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1093 := by
    rcases h6453 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1094 := by
    rcases h6454 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6382 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22848 (p1077 p1079 p1089 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6470 : p1089 ∨ p1090)
    (h6471 : p1089 ∨ p1091)
    (h6472 : p1089 ∨ p1092)
    (h6473 : p1089 ∨ p1093)
    (h6474 : p1089 ∨ p1094)
    (h6382 : p1077 ∨ p1079 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1089 ∨ p1079 ∨ p1077 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1089) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1079) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1077) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1090 := by
    rcases h6470 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1091 := by
    rcases h6471 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1092 := by
    rcases h6472 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1093 := by
    rcases h6473 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1094 := by
    rcases h6474 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6382 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22849 (p1077 p1079 p1088 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6465 : p1088 ∨ p1090)
    (h6466 : p1088 ∨ p1091)
    (h6467 : p1088 ∨ p1092)
    (h6468 : p1088 ∨ p1093)
    (h6469 : p1088 ∨ p1094)
    (h6382 : p1077 ∨ p1079 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1088 ∨ p1079 ∨ p1077 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1088) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1079) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1077) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1090 := by
    rcases h6465 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1091 := by
    rcases h6466 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1092 := by
    rcases h6467 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1093 := by
    rcases h6468 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1094 := by
    rcases h6469 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6382 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22850 (p1077 p1079 p1087 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6460 : p1087 ∨ p1090)
    (h6461 : p1087 ∨ p1091)
    (h6462 : p1087 ∨ p1092)
    (h6463 : p1087 ∨ p1093)
    (h6464 : p1087 ∨ p1094)
    (h6382 : p1077 ∨ p1079 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : p1087 ∨ p1079 ∨ p1077 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1087) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1079) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1077) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1090 := by
    rcases h6460 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1091 := by
    rcases h6461 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1092 := by
    rcases h6462 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1093 := by
    rcases h6463 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1094 := by
    rcases h6464 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h6382 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22851 (p1077 p1079 p1085 p1086 p1087 p1088 p1089 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6357 : p1077 ∨ p1079 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089))
    (h6455 : p1086 ∨ p1090)
    (h6456 : p1086 ∨ p1091)
    (h6457 : p1086 ∨ p1092)
    (h6458 : p1086 ∨ p1093)
    (h6459 : p1086 ∨ p1094)
    (h6382 : p1077 ∨ p1079 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094)) : (¬ p1087) ∨ (¬ p1085) ∨ p1077 ∨ p1079 ∨ (¬ p1088) ∨ (¬ p1089) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1087 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1085 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1077) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1079) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1088 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1089 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1086) := by
    rcases h6357 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p1090 := by
    rcases h6455 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1091 := by
    rcases h6456 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1092 := by
    rcases h6457 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1093 := by
    rcases h6458 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1094 := by
    rcases h6459 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h6382 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22852 (p1077 p1079 p1085 p1087 p1088 p1089 : Prop)
    (h22847 : p1085 ∨ p1079 ∨ p1077)
    (h22848 : p1089 ∨ p1079 ∨ p1077)
    (h22849 : p1088 ∨ p1079 ∨ p1077)
    (h22850 : p1087 ∨ p1079 ∨ p1077)
    (h22851 : (¬ p1087) ∨ (¬ p1085) ∨ p1077 ∨ p1079 ∨ (¬ p1088) ∨ (¬ p1089)) : p1079 ∨ p1077 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1079) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1077) := fun hu => hn (Or.inr hu)
  have u2 : p1085 := by
    rcases h22847 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1089 := by
    rcases h22848 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1088 := by
    rcases h22849 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1087 := by
    rcases h22850 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22851 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22853 (p835 p840 p845 p848 p849 p850 p851 p852 : Prop)
    (h4905 : p845 ∨ p848)
    (h4906 : p845 ∨ p849)
    (h4907 : p845 ∨ p850)
    (h4908 : p845 ∨ p851)
    (h4909 : p845 ∨ p852)
    (h4827 : p835 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p845 ∨ p835 ∨ p840 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p845) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p835) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p840) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4905 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4906 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4907 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4908 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4909 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4827 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22854 (p835 p840 p844 p848 p849 p850 p851 p852 : Prop)
    (h4900 : p844 ∨ p848)
    (h4901 : p844 ∨ p849)
    (h4902 : p844 ∨ p850)
    (h4903 : p844 ∨ p851)
    (h4904 : p844 ∨ p852)
    (h4827 : p835 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p844 ∨ p835 ∨ p840 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p844) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p835) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p840) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4900 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4901 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4902 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4903 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4904 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4827 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22855 (p835 p840 p843 p848 p849 p850 p851 p852 : Prop)
    (h4895 : p843 ∨ p848)
    (h4896 : p843 ∨ p849)
    (h4897 : p843 ∨ p850)
    (h4898 : p843 ∨ p851)
    (h4899 : p843 ∨ p852)
    (h4827 : p835 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p843 ∨ p835 ∨ p840 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p843) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p835) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p840) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4895 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4896 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4897 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4898 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4899 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4827 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22856 (p835 p840 p847 p848 p849 p850 p851 p852 : Prop)
    (h4915 : p847 ∨ p848)
    (h4916 : p847 ∨ p849)
    (h4917 : p847 ∨ p850)
    (h4918 : p847 ∨ p851)
    (h4919 : p847 ∨ p852)
    (h4827 : p835 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : p847 ∨ p835 ∨ p840 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p847) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p835) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p840) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p848 := by
    rcases h4915 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p849 := by
    rcases h4916 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p850 := by
    rcases h4917 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p851 := by
    rcases h4918 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p852 := by
    rcases h4919 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4827 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22857 (p835 p840 p843 p844 p845 p846 p847 p848 p849 p850 p851 p852 : Prop)
    (h4802 : p835 ∨ p840 ∨ (¬ p843) ∨ (¬ p844) ∨ (¬ p845) ∨ (¬ p846) ∨ (¬ p847))
    (h4910 : p846 ∨ p848)
    (h4911 : p846 ∨ p849)
    (h4912 : p846 ∨ p850)
    (h4913 : p846 ∨ p851)
    (h4914 : p846 ∨ p852)
    (h4827 : p835 ∨ p840 ∨ (¬ p848) ∨ (¬ p849) ∨ (¬ p850) ∨ (¬ p851) ∨ (¬ p852)) : (¬ p847) ∨ (¬ p844) ∨ p840 ∨ p835 ∨ (¬ p843) ∨ (¬ p845) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p847 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p844 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p840) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p835) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p843 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p845 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p846) := by
    rcases h4802 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u5)
    · exact q5
    · exact False.elim (q6 u0)
  have u7 : p848 := by
    rcases h4910 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p849 := by
    rcases h4911 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p850 := by
    rcases h4912 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p851 := by
    rcases h4913 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p852 := by
    rcases h4914 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h4827 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22858 (p835 p840 p843 p844 p845 p847 : Prop)
    (h22853 : p845 ∨ p835 ∨ p840)
    (h22854 : p844 ∨ p835 ∨ p840)
    (h22855 : p843 ∨ p835 ∨ p840)
    (h22856 : p847 ∨ p835 ∨ p840)
    (h22857 : (¬ p847) ∨ (¬ p844) ∨ p840 ∨ p835 ∨ (¬ p843) ∨ (¬ p845)) : p835 ∨ p840 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p835) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p840) := fun hu => hn (Or.inr hu)
  have u2 : p845 := by
    rcases h22853 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p844 := by
    rcases h22854 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p843 := by
    rcases h22855 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p847 := by
    rcases h22856 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22857 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step22859 (p922 p929 p931 p935 p936 p937 p938 p939 : Prop)
    (h5438 : p931 ∨ p935)
    (h5439 : p931 ∨ p936)
    (h5440 : p931 ∨ p937)
    (h5441 : p931 ∨ p938)
    (h5442 : p931 ∨ p939)
    (h5361 : p922 ∨ p929 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p931 ∨ p929 ∨ p922 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p931) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p929) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p922) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5438 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5439 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5440 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5441 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5442 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5361 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22860 (p922 p929 p930 p935 p936 p937 p938 p939 : Prop)
    (h5433 : p930 ∨ p935)
    (h5434 : p930 ∨ p936)
    (h5435 : p930 ∨ p937)
    (h5436 : p930 ∨ p938)
    (h5437 : p930 ∨ p939)
    (h5361 : p922 ∨ p929 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p930 ∨ p929 ∨ p922 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p930) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p929) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p922) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5433 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5434 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5435 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5436 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5437 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5361 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22861 (p922 p929 p934 p935 p936 p937 p938 p939 : Prop)
    (h5453 : p934 ∨ p935)
    (h5454 : p934 ∨ p936)
    (h5455 : p934 ∨ p937)
    (h5456 : p934 ∨ p938)
    (h5457 : p934 ∨ p939)
    (h5361 : p922 ∨ p929 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p934 ∨ p929 ∨ p922 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p934) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p929) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p922) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5453 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5454 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5455 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5456 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5457 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5361 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22862 (p922 p929 p933 p935 p936 p937 p938 p939 : Prop)
    (h5448 : p933 ∨ p935)
    (h5449 : p933 ∨ p936)
    (h5450 : p933 ∨ p937)
    (h5451 : p933 ∨ p938)
    (h5452 : p933 ∨ p939)
    (h5361 : p922 ∨ p929 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p933 ∨ p929 ∨ p922 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p933) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p929) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p922) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p935 := by
    rcases h5448 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p936 := by
    rcases h5449 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p937 := by
    rcases h5450 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p938 := by
    rcases h5451 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p939 := by
    rcases h5452 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5361 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22863 (p922 p929 p930 p931 p932 p933 p934 p935 p936 p937 p938 p939 : Prop)
    (h5336 : p922 ∨ p929 ∨ (¬ p930) ∨ (¬ p931) ∨ (¬ p932) ∨ (¬ p933) ∨ (¬ p934))
    (h5443 : p932 ∨ p935)
    (h5444 : p932 ∨ p936)
    (h5445 : p932 ∨ p937)
    (h5446 : p932 ∨ p938)
    (h5447 : p932 ∨ p939)
    (h5361 : p922 ∨ p929 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : (¬ p933) ∨ (¬ p931) ∨ p922 ∨ p929 ∨ (¬ p934) ∨ (¬ p930) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p933 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p931 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p922) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p929) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p934 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p930 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p932) := by
    rcases h5336 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u1)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u4)
  have u7 : p935 := by
    rcases h5443 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p936 := by
    rcases h5444 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p937 := by
    rcases h5445 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p938 := by
    rcases h5446 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p939 := by
    rcases h5447 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h5361 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22864 (p922 p929 p930 p931 p933 p934 : Prop)
    (h22859 : p931 ∨ p929 ∨ p922)
    (h22860 : p930 ∨ p929 ∨ p922)
    (h22861 : p934 ∨ p929 ∨ p922)
    (h22862 : p933 ∨ p929 ∨ p922)
    (h22863 : (¬ p933) ∨ (¬ p931) ∨ p922 ∨ p929 ∨ (¬ p934) ∨ (¬ p930)) : p929 ∨ p922 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p929) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p922) := fun hu => hn (Or.inr hu)
  have u2 : p931 := by
    rcases h22859 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p930 := by
    rcases h22860 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p934 := by
    rcases h22861 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p933 := by
    rcases h22862 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22863 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22865 (p6 p19 p48 p64 p85 p922 p929 p1096 : Prop)
    (h8759 : (¬ p85) ∨ (¬ p922) ∨ (¬ p1096))
    (h16729 : (¬ p6) ∨ (¬ p19) ∨ (¬ p48) ∨ (¬ p64) ∨ (¬ p929) ∨ (¬ p1096))
    (h22864 : p929 ∨ p922) : (¬ p1096) ∨ (¬ p6) ∨ (¬ p19) ∨ (¬ p48) ∨ (¬ p64) ∨ (¬ p85) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p922) := by
    rcases h8759 with q0 | q1 | q2
    · exact False.elim (q0 u5)
    · exact q1
    · exact False.elim (q2 u0)
  have u7 : (¬ p929) := by
    rcases h16729 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact q4
    · exact False.elim (q5 u0)
  rcases h22864 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)

theorem step22866 (p1250 p1252 p1259 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7557 : p1259 ∨ p1264)
    (h7558 : p1259 ∨ p1265)
    (h7559 : p1259 ∨ p1266)
    (h7560 : p1259 ∨ p1267)
    (h7561 : p1259 ∨ p1268)
    (h7483 : p1250 ∨ p1252 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1259 ∨ p1252 ∨ p1250 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1259) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1252) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1250) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1264 := by
    rcases h7557 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1265 := by
    rcases h7558 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1266 := by
    rcases h7559 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1267 := by
    rcases h7560 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7561 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7483 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22867 (p1250 p1252 p1263 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7577 : p1263 ∨ p1264)
    (h7578 : p1263 ∨ p1265)
    (h7579 : p1263 ∨ p1266)
    (h7580 : p1263 ∨ p1267)
    (h7581 : p1263 ∨ p1268)
    (h7483 : p1250 ∨ p1252 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1263 ∨ p1252 ∨ p1250 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1263) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1252) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1250) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1264 := by
    rcases h7577 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1265 := by
    rcases h7578 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1266 := by
    rcases h7579 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1267 := by
    rcases h7580 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7581 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7483 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22868 (p1250 p1252 p1262 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7572 : p1262 ∨ p1264)
    (h7573 : p1262 ∨ p1265)
    (h7574 : p1262 ∨ p1266)
    (h7575 : p1262 ∨ p1267)
    (h7576 : p1262 ∨ p1268)
    (h7483 : p1250 ∨ p1252 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1262 ∨ p1252 ∨ p1250 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1262) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1252) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1250) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1264 := by
    rcases h7572 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1265 := by
    rcases h7573 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1266 := by
    rcases h7574 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1267 := by
    rcases h7575 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7576 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7483 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22869 (p1250 p1252 p1261 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7567 : p1261 ∨ p1264)
    (h7568 : p1261 ∨ p1265)
    (h7569 : p1261 ∨ p1266)
    (h7570 : p1261 ∨ p1267)
    (h7571 : p1261 ∨ p1268)
    (h7483 : p1250 ∨ p1252 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1261 ∨ p1252 ∨ p1250 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1261) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1252) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1250) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1264 := by
    rcases h7567 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1265 := by
    rcases h7568 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1266 := by
    rcases h7569 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1267 := by
    rcases h7570 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7571 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7483 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22870 (p1250 p1252 p1259 p1260 p1261 p1262 p1263 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7458 : p1250 ∨ p1252 ∨ (¬ p1259) ∨ (¬ p1260) ∨ (¬ p1261) ∨ (¬ p1262) ∨ (¬ p1263))
    (h7562 : p1260 ∨ p1264)
    (h7563 : p1260 ∨ p1265)
    (h7564 : p1260 ∨ p1266)
    (h7565 : p1260 ∨ p1267)
    (h7566 : p1260 ∨ p1268)
    (h7483 : p1250 ∨ p1252 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : (¬ p1261) ∨ (¬ p1263) ∨ p1250 ∨ p1252 ∨ (¬ p1262) ∨ (¬ p1259) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1261 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1263 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1250) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1252) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1259 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1260) := by
    rcases h7458 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u1)
  have u7 : p1264 := by
    rcases h7562 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1265 := by
    rcases h7563 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1266 := by
    rcases h7564 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1267 := by
    rcases h7565 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1268 := by
    rcases h7566 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7483 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22871 (p1250 p1252 p1259 p1261 p1262 p1263 : Prop)
    (h22866 : p1259 ∨ p1252 ∨ p1250)
    (h22867 : p1263 ∨ p1252 ∨ p1250)
    (h22868 : p1262 ∨ p1252 ∨ p1250)
    (h22869 : p1261 ∨ p1252 ∨ p1250)
    (h22870 : (¬ p1261) ∨ (¬ p1263) ∨ p1250 ∨ p1252 ∨ (¬ p1262) ∨ (¬ p1259)) : p1252 ∨ p1250 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1252) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1250) := fun hu => hn (Or.inr hu)
  have u2 : p1259 := by
    rcases h22866 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1263 := by
    rcases h22867 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1262 := by
    rcases h22868 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1261 := by
    rcases h22869 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22870 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step22872 (p44 p50 p54 p56 p57 p58 p59 p60 : Prop)
    (h248 : p54 ∨ p56)
    (h249 : p54 ∨ p57)
    (h250 : p54 ∨ p58)
    (h251 : p54 ∨ p59)
    (h252 : p54 ∨ p60)
    (h167 : p44 ∨ p50 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p54 ∨ p50 ∨ p44 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p54) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p50) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p44) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h248 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h249 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h250 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h251 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h252 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h167 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22873 (p44 p50 p53 p56 p57 p58 p59 p60 : Prop)
    (h243 : p53 ∨ p56)
    (h244 : p53 ∨ p57)
    (h245 : p53 ∨ p58)
    (h246 : p53 ∨ p59)
    (h247 : p53 ∨ p60)
    (h167 : p44 ∨ p50 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p53 ∨ p50 ∨ p44 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p53) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p50) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p44) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h243 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h244 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h245 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h246 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h247 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h167 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22874 (p44 p50 p52 p56 p57 p58 p59 p60 : Prop)
    (h238 : p52 ∨ p56)
    (h239 : p52 ∨ p57)
    (h240 : p52 ∨ p58)
    (h241 : p52 ∨ p59)
    (h242 : p52 ∨ p60)
    (h167 : p44 ∨ p50 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p52 ∨ p50 ∨ p44 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p52) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p50) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p44) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h238 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h239 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h240 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h241 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h242 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h167 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22875 (p44 p50 p51 p56 p57 p58 p59 p60 : Prop)
    (h233 : p51 ∨ p56)
    (h234 : p51 ∨ p57)
    (h235 : p51 ∨ p58)
    (h236 : p51 ∨ p59)
    (h237 : p51 ∨ p60)
    (h167 : p44 ∨ p50 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : p51 ∨ p50 ∨ p44 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p51) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p50) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p44) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p56 := by
    rcases h233 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p57 := by
    rcases h234 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p58 := by
    rcases h235 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p59 := by
    rcases h236 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p60 := by
    rcases h237 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h167 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22876 (p44 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 : Prop)
    (h142 : p44 ∨ p50 ∨ (¬ p51) ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) ∨ (¬ p55))
    (h253 : p55 ∨ p56)
    (h254 : p55 ∨ p57)
    (h255 : p55 ∨ p58)
    (h256 : p55 ∨ p59)
    (h257 : p55 ∨ p60)
    (h167 : p44 ∨ p50 ∨ (¬ p56) ∨ (¬ p57) ∨ (¬ p58) ∨ (¬ p59) ∨ (¬ p60)) : (¬ p51) ∨ p50 ∨ p44 ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p51 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p50) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p44) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p52 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p53 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p54 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p55) := by
    rcases h142 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact q6
  have u7 : p56 := by
    rcases h253 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p57 := by
    rcases h254 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p58 := by
    rcases h255 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p59 := by
    rcases h256 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p60 := by
    rcases h257 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h167 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22877 (p44 p50 p51 p52 p53 p54 : Prop)
    (h22872 : p54 ∨ p50 ∨ p44)
    (h22873 : p53 ∨ p50 ∨ p44)
    (h22874 : p52 ∨ p50 ∨ p44)
    (h22875 : p51 ∨ p50 ∨ p44)
    (h22876 : (¬ p51) ∨ p50 ∨ p44 ∨ (¬ p52) ∨ (¬ p53) ∨ (¬ p54)) : p50 ∨ p44 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p50) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p44) := fun hu => hn (Or.inr hu)
  have u2 : p54 := by
    rcases h22872 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p53 := by
    rcases h22873 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p52 := by
    rcases h22874 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p51 := by
    rcases h22875 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22876 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step22878 (p1252 p1255 p1260 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7562 : p1260 ∨ p1264)
    (h7563 : p1260 ∨ p1265)
    (h7564 : p1260 ∨ p1266)
    (h7565 : p1260 ∨ p1267)
    (h7566 : p1260 ∨ p1268)
    (h7482 : p1252 ∨ p1255 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1260 ∨ p1252 ∨ p1255 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1260) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1252) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1255) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1264 := by
    rcases h7562 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1265 := by
    rcases h7563 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1266 := by
    rcases h7564 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1267 := by
    rcases h7565 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7566 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7482 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22879 (p1252 p1255 p1263 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7577 : p1263 ∨ p1264)
    (h7578 : p1263 ∨ p1265)
    (h7579 : p1263 ∨ p1266)
    (h7580 : p1263 ∨ p1267)
    (h7581 : p1263 ∨ p1268)
    (h7482 : p1252 ∨ p1255 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1263 ∨ p1252 ∨ p1255 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1263) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1252) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1255) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1264 := by
    rcases h7577 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1265 := by
    rcases h7578 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1266 := by
    rcases h7579 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1267 := by
    rcases h7580 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7581 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7482 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22880 (p1252 p1255 p1262 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7572 : p1262 ∨ p1264)
    (h7573 : p1262 ∨ p1265)
    (h7574 : p1262 ∨ p1266)
    (h7575 : p1262 ∨ p1267)
    (h7576 : p1262 ∨ p1268)
    (h7482 : p1252 ∨ p1255 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1262 ∨ p1252 ∨ p1255 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1262) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1252) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1255) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1264 := by
    rcases h7572 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1265 := by
    rcases h7573 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1266 := by
    rcases h7574 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1267 := by
    rcases h7575 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7576 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7482 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22881 (p1252 p1255 p1261 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h7567 : p1261 ∨ p1264)
    (h7568 : p1261 ∨ p1265)
    (h7569 : p1261 ∨ p1266)
    (h7570 : p1261 ∨ p1267)
    (h7571 : p1261 ∨ p1268)
    (h7482 : p1252 ∨ p1255 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1261 ∨ p1252 ∨ p1255 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1261) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1252) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1255) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1264 := by
    rcases h7567 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1265 := by
    rcases h7568 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1266 := by
    rcases h7569 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1267 := by
    rcases h7570 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1268 := by
    rcases h7571 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7482 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22882 (p1252 p1255 p1256 p1259 p1260 p1261 p1262 p1263 p1264 p1265 p1266 p1267 p1268 : Prop)
    (h22878 : p1260 ∨ p1252 ∨ p1255)
    (h22879 : p1263 ∨ p1252 ∨ p1255)
    (h22880 : p1262 ∨ p1252 ∨ p1255)
    (h22881 : p1261 ∨ p1252 ∨ p1255)
    (h7459 : p1252 ∨ p1256 ∨ (¬ p1259) ∨ (¬ p1260) ∨ (¬ p1261) ∨ (¬ p1262) ∨ (¬ p1263))
    (h7557 : p1259 ∨ p1264)
    (h7558 : p1259 ∨ p1265)
    (h7559 : p1259 ∨ p1266)
    (h7560 : p1259 ∨ p1267)
    (h7561 : p1259 ∨ p1268)
    (h7482 : p1252 ∨ p1255 ∨ (¬ p1264) ∨ (¬ p1265) ∨ (¬ p1266) ∨ (¬ p1267) ∨ (¬ p1268)) : p1252 ∨ p1255 ∨ p1256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1252) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1255) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1256) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1260 := by
    rcases h22878 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1263 := by
    rcases h22879 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1262 := by
    rcases h22880 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1261 := by
    rcases h22881 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1259) := by
    rcases h7459 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u4)
  have u8 : p1264 := by
    rcases h7557 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p1265 := by
    rcases h7558 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p1266 := by
    rcases h7559 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p1267 := by
    rcases h7560 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u12 : p1268 := by
    rcases h7561 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h7482 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step22883 (p2 p6 p8 p15 p18 p19 p38 p44 p50 p64 p67 p69 p86 p101 p102 p126 p224 p234 p256 p288 p323 p325 p329 p346 p419 p424 p434 p581 p596 p728 p1035 p1061 p1076 p1187 p1206 p1212 p1232 p1252 p1287 p1328 p1334 p1366 p1443 p1489 : Prop)
    (h12635 : (¬ p419) ∨ (¬ p1328) ∨ (¬ p1366))
    (h21365 : p1334 ∨ p1328)
    (h21316 : p64 ∨ p15)
    (h21946 : p69 ∨ p15)
    (h22771 : (¬ p728) ∨ (¬ p69) ∨ (¬ p1187) ∨ (¬ p8) ∨ (¬ p1334) ∨ (¬ p419))
    (h21531 : p1187 ∨ p234)
    (h10840 : (¬ p2) ∨ (¬ p38) ∨ p1187)
    (h11331 : (¬ p44) ∨ (¬ p234) ∨ p424)
    (h21299 : p67 ∨ p38)
    (h22427 : p1287 ∨ (¬ p419) ∨ (¬ p2) ∨ (¬ p67))
    (h22843 : (¬ p18) ∨ (¬ p234) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p1061) ∨ (¬ p1076) ∨ (¬ p288) ∨ (¬ p256) ∨ (¬ p2))
    (h22840 : p19 ∨ p18)
    (h22844 : (¬ p434) ∨ (¬ p1287) ∨ (¬ p1232) ∨ (¬ p596) ∨ (¬ p86) ∨ (¬ p1334) ∨ (¬ p256) ∨ (¬ p126))
    (h13541 : (¬ p325) ∨ p434 ∨ (¬ p1366))
    (h22877 : p50 ∨ p44)
    (h18838 : (¬ p19) ∨ (¬ p50) ∨ (¬ p1035) ∨ (¬ p1212) ∨ (¬ p1252) ∨ (¬ p1489))
    (h21957 : p1212 ∨ p1206)
    (h16496 : (¬ p102) ∨ (¬ p256) ∨ (¬ p1206) ∨ (¬ p1443))
    (h20340 : (¬ p323) ∨ (¬ p581) ∨ (¬ p1206) ∨ (¬ p1443))
    (h21623 : p101 ∨ p102)
    (h21607 : p329 ∨ p323 ∨ p325)
    (h16370 : (¬ p6) ∨ (¬ p101) ∨ (¬ p224) ∨ (¬ p346))
    (h13807 : (¬ p2) ∨ p6 ∨ (¬ p329)) : p15 ∨ (¬ p1232) ∨ (¬ p596) ∨ (¬ p581) ∨ (¬ p86) ∨ (¬ p728) ∨ (¬ p346) ∨ (¬ p8) ∨ (¬ p224) ∨ (¬ p1252) ∨ (¬ p1035) ∨ (¬ p1061) ∨ (¬ p1366) ∨ (¬ p1076) ∨ (¬ p288) ∨ (¬ p1443) ∨ (¬ p1489) ∨ p424 ∨ (¬ p256) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p15) := fun hu => hn (Or.inl hu)
  have u1 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1252 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : (¬ p424) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))
  have u18 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))
  have u19 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))
  have u20 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))))
  have u21 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))))))))
  have u22 : (¬ p1328) := by
    rcases h12635 with q0 | q1 | q2
    · exact False.elim (q0 u20)
    · exact q1
    · exact False.elim (q2 u12)
  have u23 : p1334 := by
    rcases h21365 with q0 | q1
    · exact q0
    · exact False.elim (u22 q1)
  have u24 : p64 := by
    rcases h21316 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u25 : p69 := by
    rcases h21946 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u26 : (¬ p1187) := by
    rcases h22771 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u25)
    · exact q2
    · exact False.elim (q3 u7)
    · exact False.elim (q4 u23)
    · exact False.elim (q5 u20)
  have u27 : p234 := by
    rcases h21531 with q0 | q1
    · exact False.elim (u26 q0)
    · exact q1
  have u28 : (¬ p38) := by
    rcases h10840 with q0 | q1 | q2
    · exact False.elim (q0 u21)
    · exact q1
    · exact False.elim (u26 q2)
  have u29 : (¬ p44) := by
    rcases h11331 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u27)
    · exact False.elim (u17 q2)
  have u30 : p67 := by
    rcases h21299 with q0 | q1
    · exact q0
    · exact False.elim (u28 q1)
  have u31 : p1287 := by
    rcases h22427 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u20)
    · exact False.elim (q2 u21)
    · exact False.elim (q3 u30)
  have u32 : (¬ p18) := by
    rcases h22843 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact q0
    · exact False.elim (q1 u27)
    · exact False.elim (q2 u24)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u11)
    · exact False.elim (q5 u13)
    · exact False.elim (q6 u14)
    · exact False.elim (q7 u18)
    · exact False.elim (q8 u21)
  have u33 : p19 := by
    rcases h22840 with q0 | q1
    · exact q0
    · exact False.elim (u32 q1)
  have u34 : (¬ p434) := by
    rcases h22844 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact q0
    · exact False.elim (q1 u31)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u23)
    · exact False.elim (q6 u18)
    · exact False.elim (q7 u19)
  have u35 : (¬ p325) := by
    rcases h13541 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u34 q1)
    · exact False.elim (q2 u12)
  have u36 : p50 := by
    rcases h22877 with q0 | q1
    · exact q0
    · exact False.elim (u29 q1)
  have u37 : (¬ p1212) := by
    rcases h18838 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u33)
    · exact False.elim (q1 u36)
    · exact False.elim (q2 u10)
    · exact q3
    · exact False.elim (q4 u9)
    · exact False.elim (q5 u16)
  have u38 : p1206 := by
    rcases h21957 with q0 | q1
    · exact False.elim (u37 q0)
    · exact q1
  have u39 : (¬ p102) := by
    rcases h16496 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u18)
    · exact False.elim (q2 u38)
    · exact False.elim (q3 u15)
  have u40 : (¬ p323) := by
    rcases h20340 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u38)
    · exact False.elim (q3 u15)
  have u41 : p101 := by
    rcases h21623 with q0 | q1
    · exact q0
    · exact False.elim (u39 q1)
  have u42 : p329 := by
    rcases h21607 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u40 q1)
    · exact False.elim (u35 q2)
  have u43 : (¬ p6) := by
    rcases h16370 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u41)
    · exact False.elim (q2 u8)
    · exact False.elim (q3 u6)
  rcases h13807 with q0 | q1 | q2
  · exact False.elim (q0 u21)
  · exact False.elim (u43 q1)
  · exact False.elim (q2 u42)

theorem step22886 (p1227 p1269 p1277 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7687 : p1277 ∨ p1281)
    (h7688 : p1277 ∨ p1282)
    (h7689 : p1277 ∨ p1283)
    (h7690 : p1277 ∨ p1284)
    (h7691 : p1277 ∨ p1285)
    (h7613 : p1227 ∨ p1269 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1277 ∨ p1227 ∨ p1269 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1277) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1227) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1269) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7687 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7688 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7689 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7690 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7691 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7613 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22887 (p1227 p1269 p1276 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7682 : p1276 ∨ p1281)
    (h7683 : p1276 ∨ p1282)
    (h7684 : p1276 ∨ p1283)
    (h7685 : p1276 ∨ p1284)
    (h7686 : p1276 ∨ p1285)
    (h7613 : p1227 ∨ p1269 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1276 ∨ p1227 ∨ p1269 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1276) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1227) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1269) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7682 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7683 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7684 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7685 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7686 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7613 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22888 (p1227 p1269 p1280 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7702 : p1280 ∨ p1281)
    (h7703 : p1280 ∨ p1282)
    (h7704 : p1280 ∨ p1283)
    (h7705 : p1280 ∨ p1284)
    (h7706 : p1280 ∨ p1285)
    (h7613 : p1227 ∨ p1269 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1280 ∨ p1227 ∨ p1269 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1280) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1227) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1269) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7702 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7703 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7704 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7705 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7706 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7613 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22889 (p1227 p1269 p1279 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7697 : p1279 ∨ p1281)
    (h7698 : p1279 ∨ p1282)
    (h7699 : p1279 ∨ p1283)
    (h7700 : p1279 ∨ p1284)
    (h7701 : p1279 ∨ p1285)
    (h7613 : p1227 ∨ p1269 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : p1279 ∨ p1227 ∨ p1269 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1279) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1227) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1269) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1281 := by
    rcases h7697 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1282 := by
    rcases h7698 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1283 := by
    rcases h7699 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1284 := by
    rcases h7700 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1285 := by
    rcases h7701 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7613 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22890 (p1227 p1269 p1276 p1277 p1278 p1279 p1280 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7588 : p1227 ∨ p1269 ∨ (¬ p1276) ∨ (¬ p1277) ∨ (¬ p1278) ∨ (¬ p1279) ∨ (¬ p1280))
    (h7692 : p1278 ∨ p1281)
    (h7693 : p1278 ∨ p1282)
    (h7694 : p1278 ∨ p1283)
    (h7695 : p1278 ∨ p1284)
    (h7696 : p1278 ∨ p1285)
    (h7613 : p1227 ∨ p1269 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285)) : (¬ p1279) ∨ (¬ p1276) ∨ p1269 ∨ p1227 ∨ (¬ p1280) ∨ (¬ p1277) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1279 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1276 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1269) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1227) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1280 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1277 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1278) := by
    rcases h7588 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u5)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u4)
  have u7 : p1281 := by
    rcases h7692 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1282 := by
    rcases h7693 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1283 := by
    rcases h7694 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1284 := by
    rcases h7695 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1285 := by
    rcases h7696 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7613 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22891 (p1227 p1269 p1276 p1277 p1279 p1280 : Prop)
    (h22886 : p1277 ∨ p1227 ∨ p1269)
    (h22887 : p1276 ∨ p1227 ∨ p1269)
    (h22888 : p1280 ∨ p1227 ∨ p1269)
    (h22889 : p1279 ∨ p1227 ∨ p1269)
    (h22890 : (¬ p1279) ∨ (¬ p1276) ∨ p1269 ∨ p1227 ∨ (¬ p1280) ∨ (¬ p1277)) : p1227 ∨ p1269 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1227) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1269) := fun hu => hn (Or.inr hu)
  have u2 : p1277 := by
    rcases h22886 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1276 := by
    rcases h22887 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1280 := by
    rcases h22888 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1279 := by
    rcases h22889 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22890 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step22892 (p138 p141 p142 p144 p145 p146 p147 p148 p149 p150 p151 p152 p153 : Prop)
    (h22637 : p148 ∨ p138 ∨ p142)
    (h22638 : p153 ∨ p138 ∨ p142)
    (h22639 : p152 ∨ p138 ∨ p142)
    (h22640 : p151 ∨ p138 ∨ p142)
    (h22641 : p150 ∨ p138 ∨ p142)
    (h697 : p138 ∨ p141 ∨ (¬ p149) ∨ (¬ p150) ∨ (¬ p151) ∨ (¬ p152) ∨ (¬ p153))
    (h756 : p144 ∨ p149)
    (h761 : p145 ∨ p149)
    (h766 : p146 ∨ p149)
    (h771 : p147 ∨ p149)
    (h673 : p138 ∨ p142 ∨ (¬ p144) ∨ (¬ p145) ∨ (¬ p146) ∨ (¬ p147) ∨ (¬ p148)) : p138 ∨ p142 ∨ p141 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p138) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p142) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p141) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p148 := by
    rcases h22637 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p153 := by
    rcases h22638 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p152 := by
    rcases h22639 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p151 := by
    rcases h22640 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : p150 := by
    rcases h22641 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u8 : (¬ p149) := by
    rcases h697 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u7)
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u4)
  have u9 : p144 := by
    rcases h756 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u10 : p145 := by
    rcases h761 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u11 : p146 := by
    rcases h766 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u12 : p147 := by
    rcases h771 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h673 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u3)

theorem step22893 (p138 p161 p576 p1225 p1227 p1252 p1269 p1489 : Prop)
    (h11740 : (¬ p161) ∨ (¬ p1225))
    (h17469 : (¬ p138) ∨ (¬ p576) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1252) ∨ (¬ p1489))
    (h12910 : p161 ∨ (¬ p1269) ∨ (¬ p1489))
    (h22891 : p1227 ∨ p1269) : (¬ p1225) ∨ (¬ p138) ∨ (¬ p576) ∨ (¬ p1252) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1252 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p161) := by
    rcases h11740 with q0 | q1
    · exact q0
    · exact False.elim (q1 u0)
  have u6 : (¬ p1227) := by
    rcases h17469 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u0)
    · exact q3
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u4)
  have u7 : (¬ p1269) := by
    rcases h12910 with q0 | q1 | q2
    · exact False.elim (u5 q0)
    · exact q1
    · exact False.elim (q2 u4)
  rcases h22891 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u7 q1)

theorem step22894 (p594 p601 p605 p609 p610 p611 p612 p613 : Prop)
    (h3470 : p605 ∨ p609)
    (h3471 : p605 ∨ p610)
    (h3472 : p605 ∨ p611)
    (h3473 : p605 ∨ p612)
    (h3474 : p605 ∨ p613)
    (h3392 : p594 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p605 ∨ p594 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p605) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p594) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3470 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3471 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3472 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3473 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3474 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3392 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22895 (p594 p601 p604 p609 p610 p611 p612 p613 : Prop)
    (h3465 : p604 ∨ p609)
    (h3466 : p604 ∨ p610)
    (h3467 : p604 ∨ p611)
    (h3468 : p604 ∨ p612)
    (h3469 : p604 ∨ p613)
    (h3392 : p594 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p604 ∨ p594 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p604) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p594) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3465 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3466 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3467 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3468 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3469 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3392 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22896 (p594 p601 p608 p609 p610 p611 p612 p613 : Prop)
    (h3485 : p608 ∨ p609)
    (h3486 : p608 ∨ p610)
    (h3487 : p608 ∨ p611)
    (h3488 : p608 ∨ p612)
    (h3489 : p608 ∨ p613)
    (h3392 : p594 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p608 ∨ p594 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p608) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p594) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3485 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3486 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3487 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3488 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3489 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3392 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22897 (p594 p601 p607 p609 p610 p611 p612 p613 : Prop)
    (h3480 : p607 ∨ p609)
    (h3481 : p607 ∨ p610)
    (h3482 : p607 ∨ p611)
    (h3483 : p607 ∨ p612)
    (h3484 : p607 ∨ p613)
    (h3392 : p594 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : p607 ∨ p594 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p607) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p594) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p609 := by
    rcases h3480 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p610 := by
    rcases h3481 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p611 := by
    rcases h3482 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p612 := by
    rcases h3483 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p613 := by
    rcases h3484 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3392 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22898 (p594 p601 p604 p605 p606 p607 p608 p609 p610 p611 p612 p613 : Prop)
    (h3367 : p594 ∨ p601 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608))
    (h3475 : p606 ∨ p609)
    (h3476 : p606 ∨ p610)
    (h3477 : p606 ∨ p611)
    (h3478 : p606 ∨ p612)
    (h3479 : p606 ∨ p613)
    (h3392 : p594 ∨ p601 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613)) : (¬ p607) ∨ (¬ p604) ∨ p601 ∨ p594 ∨ (¬ p608) ∨ (¬ p605) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p607 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p604 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p601) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p594) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p608 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p605 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p606) := by
    rcases h3367 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u5)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u4)
  have u7 : p609 := by
    rcases h3475 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p610 := by
    rcases h3476 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p611 := by
    rcases h3477 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p612 := by
    rcases h3478 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p613 := by
    rcases h3479 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3392 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22899 (p594 p601 p604 p605 p607 p608 : Prop)
    (h22894 : p605 ∨ p594 ∨ p601)
    (h22895 : p604 ∨ p594 ∨ p601)
    (h22896 : p608 ∨ p594 ∨ p601)
    (h22897 : p607 ∨ p594 ∨ p601)
    (h22898 : (¬ p607) ∨ (¬ p604) ∨ p601 ∨ p594 ∨ (¬ p608) ∨ (¬ p605)) : p594 ∨ p601 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p594) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p601) := fun hu => hn (Or.inr hu)
  have u2 : p605 := by
    rcases h22894 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p604 := by
    rcases h22895 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p608 := by
    rcases h22896 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p607 := by
    rcases h22897 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22898 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step22900 (p5 p69 p77 p78 p79 p80 p81 p82 : Prop)
    (h389 : p77 ∨ p78)
    (h390 : p77 ∨ p79)
    (h391 : p77 ∨ p80)
    (h392 : p77 ∨ p81)
    (h393 : p77 ∨ p82)
    (h307 : p5 ∨ p69 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p77 ∨ p5 ∨ p69 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p77) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p5) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p69) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p78 := by
    rcases h389 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p79 := by
    rcases h390 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p80 := by
    rcases h391 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p81 := by
    rcases h392 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p82 := by
    rcases h393 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h307 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22901 (p5 p15 p64 p69 p73 p74 p75 p76 p77 p82 : Prop)
    (h21316 : p64 ∨ p15)
    (h6604 : (¬ p15) ∨ (¬ p69))
    (h22900 : p77 ∨ p5 ∨ p69)
    (h373 : p73 ∨ p82)
    (h378 : p74 ∨ p82)
    (h272 : p5 ∨ p64 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p82 ∨ (¬ p76) ∨ (¬ p75) ∨ p5 ∨ p64 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p82) := fun hu => hn (Or.inl hu)
  have u1 : p76 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p75 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p5) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p64) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p15 := by
    rcases h21316 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u6 : (¬ p69) := by
    rcases h6604 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  have u7 : p77 := by
    rcases h22900 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u3 q1)
    · exact False.elim (u6 q2)
  have u8 : p73 := by
    rcases h373 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p74 := by
    rcases h378 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h272 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step22902 (p5 p15 p64 p69 p73 p74 p75 p76 p77 p81 : Prop)
    (h21316 : p64 ∨ p15)
    (h6604 : (¬ p15) ∨ (¬ p69))
    (h22900 : p77 ∨ p5 ∨ p69)
    (h372 : p73 ∨ p81)
    (h377 : p74 ∨ p81)
    (h272 : p5 ∨ p64 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p81 ∨ (¬ p76) ∨ (¬ p75) ∨ p5 ∨ p64 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p81) := fun hu => hn (Or.inl hu)
  have u1 : p76 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p75 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p5) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p64) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p15 := by
    rcases h21316 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u6 : (¬ p69) := by
    rcases h6604 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  have u7 : p77 := by
    rcases h22900 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u3 q1)
    · exact False.elim (u6 q2)
  have u8 : p73 := by
    rcases h372 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p74 := by
    rcases h377 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h272 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step22903 (p5 p15 p64 p69 p73 p74 p75 p76 p77 p80 : Prop)
    (h21316 : p64 ∨ p15)
    (h6604 : (¬ p15) ∨ (¬ p69))
    (h22900 : p77 ∨ p5 ∨ p69)
    (h371 : p73 ∨ p80)
    (h376 : p74 ∨ p80)
    (h272 : p5 ∨ p64 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p80 ∨ (¬ p76) ∨ (¬ p75) ∨ p5 ∨ p64 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p80) := fun hu => hn (Or.inl hu)
  have u1 : p76 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p75 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p5) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p64) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p15 := by
    rcases h21316 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u6 : (¬ p69) := by
    rcases h6604 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  have u7 : p77 := by
    rcases h22900 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u3 q1)
    · exact False.elim (u6 q2)
  have u8 : p73 := by
    rcases h371 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p74 := by
    rcases h376 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h272 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step22904 (p5 p15 p64 p69 p73 p74 p75 p76 p77 p79 : Prop)
    (h21316 : p64 ∨ p15)
    (h6604 : (¬ p15) ∨ (¬ p69))
    (h22900 : p77 ∨ p5 ∨ p69)
    (h370 : p73 ∨ p79)
    (h375 : p74 ∨ p79)
    (h272 : p5 ∨ p64 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p79 ∨ (¬ p76) ∨ (¬ p75) ∨ p5 ∨ p64 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p79) := fun hu => hn (Or.inl hu)
  have u1 : p76 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p75 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p5) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p64) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p15 := by
    rcases h21316 with q0 | q1
    · exact False.elim (u4 q0)
    · exact q1
  have u6 : (¬ p69) := by
    rcases h6604 with q0 | q1
    · exact False.elim (q0 u5)
    · exact q1
  have u7 : p77 := by
    rcases h22900 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u3 q1)
    · exact False.elim (u6 q2)
  have u8 : p73 := by
    rcases h370 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u9 : p74 := by
    rcases h375 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h272 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step22905 (p5 p15 p64 p69 p73 p74 p75 p76 p77 p78 p79 p80 p81 p82 : Prop)
    (h21316 : p64 ∨ p15)
    (h6604 : (¬ p15) ∨ (¬ p69))
    (h22900 : p77 ∨ p5 ∨ p69)
    (h22901 : p82 ∨ (¬ p76) ∨ (¬ p75) ∨ p5 ∨ p64)
    (h22902 : p81 ∨ (¬ p76) ∨ (¬ p75) ∨ p5 ∨ p64)
    (h22903 : p80 ∨ (¬ p76) ∨ (¬ p75) ∨ p5 ∨ p64)
    (h22904 : p79 ∨ (¬ p76) ∨ (¬ p75) ∨ p5 ∨ p64)
    (h307 : p5 ∨ p69 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82))
    (h369 : p73 ∨ p78)
    (h374 : p74 ∨ p78)
    (h272 : p5 ∨ p64 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : (¬ p76) ∨ (¬ p75) ∨ p5 ∨ p64 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p76 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p75 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p5) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p64) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p15 := by
    rcases h21316 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u5 : (¬ p69) := by
    rcases h6604 with q0 | q1
    · exact False.elim (q0 u4)
    · exact q1
  have u6 : p77 := by
    rcases h22900 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u5 q2)
  have u7 : p82 := by
    rcases h22901 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u1)
    · exact False.elim (u2 q3)
    · exact False.elim (u3 q4)
  have u8 : p81 := by
    rcases h22902 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u1)
    · exact False.elim (u2 q3)
    · exact False.elim (u3 q4)
  have u9 : p80 := by
    rcases h22903 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u1)
    · exact False.elim (u2 q3)
    · exact False.elim (u3 q4)
  have u10 : p79 := by
    rcases h22904 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u1)
    · exact False.elim (u2 q3)
    · exact False.elim (u3 q4)
  have u11 : (¬ p78) := by
    rcases h307 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u5 q1)
    · exact q2
    · exact False.elim (q3 u10)
    · exact False.elim (q4 u9)
    · exact False.elim (q5 u8)
    · exact False.elim (q6 u7)
  have u12 : p73 := by
    rcases h369 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u13 : p74 := by
    rcases h374 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  rcases h272 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u12)
  · exact False.elim (q3 u13)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u6)

theorem step22906 (p5 p64 p76 p78 p79 p80 p81 p82 : Prop)
    (h384 : p76 ∨ p78)
    (h385 : p76 ∨ p79)
    (h386 : p76 ∨ p80)
    (h387 : p76 ∨ p81)
    (h388 : p76 ∨ p82)
    (h297 : p5 ∨ p64 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p76 ∨ p5 ∨ p64 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p76) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p5) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p64) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p78 := by
    rcases h384 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p79 := by
    rcases h385 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p80 := by
    rcases h386 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p81 := by
    rcases h387 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p82 := by
    rcases h388 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h297 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22907 (p5 p64 p75 p76 p78 p79 p80 p81 p82 : Prop)
    (h22905 : (¬ p76) ∨ (¬ p75) ∨ p5 ∨ p64)
    (h379 : p75 ∨ p78)
    (h380 : p75 ∨ p79)
    (h381 : p75 ∨ p80)
    (h382 : p75 ∨ p81)
    (h383 : p75 ∨ p82)
    (h297 : p5 ∨ p64 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : (¬ p76) ∨ p64 ∨ p5 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p76 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p64) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p5) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p75) := by
    rcases h22905 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u4 : p78 := by
    rcases h379 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u5 : p79 := by
    rcases h380 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u6 : p80 := by
    rcases h381 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u7 : p81 := by
    rcases h382 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u8 : p82 := by
    rcases h383 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  rcases h297 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step22908 (p5 p64 p76 : Prop)
    (h22906 : p76 ∨ p5 ∨ p64)
    (h22907 : (¬ p76) ∨ p64 ∨ p5) : p5 ∨ p64 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p5) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p64) := fun hu => hn (Or.inr hu)
  have u2 : p76 := by
    rcases h22906 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22907 with q0 | q1 | q2
  · exact False.elim (q0 u2)
  · exact False.elim (u1 q1)
  · exact False.elim (u0 q2)

theorem step22909 (p2 p5 p64 p84 p89 p90 p160 p188 p228 p256 p419 p576 p581 p1249 p1273 p1353 p1489 p1495 : Prop)
    (h21688 : p576 ∨ p581)
    (h11129 : (¬ p84) ∨ (¬ p256) ∨ p581)
    (h22277 : p89 ∨ p84)
    (h22396 : p90 ∨ p84)
    (h11182 : (¬ p64) ∨ (¬ p89) ∨ p188)
    (h16727 : (¬ p90) ∨ (¬ p160) ∨ (¬ p1249) ∨ (¬ p1353) ∨ (¬ p1489))
    (h21525 : p1273 ∨ p1249)
    (h18235 : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p576) ∨ (¬ p1273) ∨ (¬ p1495))
    (h22908 : p5 ∨ p64) : p581 ∨ (¬ p160) ∨ (¬ p1353) ∨ (¬ p1495) ∨ (¬ p1489) ∨ p188 ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p581) := fun hu => hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1353 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p188) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p576 := by
    rcases h21688 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : (¬ p84) := by
    rcases h11129 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u7)
    · exact False.elim (u0 q2)
  have u12 : p89 := by
    rcases h22277 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u13 : p90 := by
    rcases h22396 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u14 : (¬ p64) := by
    rcases h11182 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u12)
    · exact False.elim (u5 q2)
  have u15 : (¬ p1249) := by
    rcases h16727 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u13)
    · exact False.elim (q1 u1)
    · exact q2
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u4)
  have u16 : p1273 := by
    rcases h21525 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  have u17 : (¬ p5) := by
    rcases h18235 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact False.elim (q0 u9)
    · exact q1
    · exact False.elim (q2 u12)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u7)
    · exact False.elim (q5 u8)
    · exact False.elim (q6 u10)
    · exact False.elim (q7 u16)
    · exact False.elim (q8 u3)
  rcases h22908 with q0 | q1
  · exact False.elim (u17 q0)
  · exact False.elim (u14 q1)

theorem step22911 (p224 p303 p344 p346 p347 p348 p419 p657 p662 p666 p690 p710 p713 p1055 p1061 p1366 : Prop)
    (h11160 : (¬ p1055) ∨ (¬ p1061))
    (h22560 : p346 ∨ p344)
    (h17451 : (¬ p346) ∨ (¬ p419) ∨ (¬ p690) ∨ (¬ p713) ∨ (¬ p1366))
    (h20854 : p710 ∨ p713)
    (h10740 : (¬ p662) ∨ (¬ p710) ∨ p1055)
    (h21721 : p662 ∨ p657)
    (h6747 : (¬ p224) ∨ (¬ p657))
    (h11604 : (¬ p303) ∨ (¬ p348) ∨ (¬ p657))
    (h22413 : p666 ∨ p224)
    (h21054 : p347 ∨ p348 ∨ p344)
    (h17219 : (¬ p303) ∨ (¬ p347) ∨ (¬ p666) ∨ (¬ p710) ∨ (¬ p1061)) : p344 ∨ (¬ p690) ∨ (¬ p1061) ∨ (¬ p1366) ∨ (¬ p303) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p344) := fun hu => hn (Or.inl hu)
  have u1 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1055) := by
    rcases h11160 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u7 : p346 := by
    rcases h22560 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u8 : (¬ p713) := by
    rcases h17451 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u3)
  have u9 : p710 := by
    rcases h20854 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u10 : (¬ p662) := by
    rcases h10740 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u9)
    · exact False.elim (u6 q2)
  have u11 : p657 := by
    rcases h21721 with q0 | q1
    · exact False.elim (u10 q0)
    · exact q1
  have u12 : (¬ p224) := by
    rcases h6747 with q0 | q1
    · exact q0
    · exact False.elim (q1 u11)
  have u13 : (¬ p348) := by
    rcases h11604 with q0 | q1 | q2
    · exact False.elim (q0 u4)
    · exact q1
    · exact False.elim (q2 u11)
  have u14 : p666 := by
    rcases h22413 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u15 : p347 := by
    rcases h21054 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u13 q1)
    · exact False.elim (u0 q2)
  rcases h17219 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u15)
  · exact False.elim (q2 u14)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u2)

theorem step22912 (p256 p286 p288 p344 p657 p664 p840 p983 p1117 p1121 p1489 : Prop)
    (h9337 : (¬ p983) ∨ (¬ p1121) ∨ (¬ p1489))
    (h21537 : p1121 ∨ p1117)
    (h16985 : (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p657))
    (h13505 : (¬ p286) ∨ (¬ p344) ∨ p840)
    (h22831 : p664 ∨ p657)
    (h16465 : (¬ p664) ∨ (¬ p840) ∨ (¬ p983) ∨ (¬ p1117) ∨ (¬ p1489)) : (¬ p344) ∨ (¬ p983) ∨ (¬ p288) ∨ (¬ p286) ∨ (¬ p1489) ∨ (¬ p256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1121) := by
    rcases h9337 with q0 | q1 | q2
    · exact False.elim (q0 u1)
    · exact q1
    · exact False.elim (q2 u4)
  have u7 : p1117 := by
    rcases h21537 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : (¬ p657) := by
    rcases h16985 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u0)
    · exact q3
  have u9 : p840 := by
    rcases h13505 with q0 | q1 | q2
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u0)
    · exact q2
  have u10 : p664 := by
    rcases h22831 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h16465 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u10)
  · exact False.elim (q1 u9)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u4)

theorem step22913 (p2 p15 p43 p49 p63 p85 p256 p419 p687 p796 p1334 p1443 p1452 : Prop)
    (h22211 : p85 ∨ p63)
    (h12953 : (¬ p15) ∨ (¬ p43) ∨ p63)
    (h22834 : (¬ p15) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p687) ∨ (¬ p1334) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p796) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h22271 : p49 ∨ p43) : (¬ p15) ∨ (¬ p687) ∨ p63 ∨ (¬ p1334) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p796) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : p85 := by
    rcases h22211 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u11 : (¬ p43) := by
    rcases h12953 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (u2 q2)
  have u12 : (¬ p49) := by
    rcases h22834 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u10)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
    · exact False.elim (q7 u6)
    · exact False.elim (q8 u7)
    · exact False.elim (q9 u8)
    · exact False.elim (q10 u9)
  rcases h22271 with q0 | q1
  · exact False.elim (u12 q0)
  · exact False.elim (u11 q1)

theorem step22916 (p918 p927 p930 p931 p932 p933 p934 p935 p936 p937 p938 p939 : Prop)
    (h5344 : p918 ∨ p927 ∨ (¬ p930) ∨ (¬ p931) ∨ (¬ p932) ∨ (¬ p933) ∨ (¬ p934))
    (h5443 : p932 ∨ p935)
    (h5444 : p932 ∨ p936)
    (h5445 : p932 ∨ p937)
    (h5446 : p932 ∨ p938)
    (h5447 : p932 ∨ p939)
    (h5369 : p918 ∨ p927 ∨ (¬ p935) ∨ (¬ p936) ∨ (¬ p937) ∨ (¬ p938) ∨ (¬ p939)) : p927 ∨ (¬ p931) ∨ p918 ∨ (¬ p930) ∨ (¬ p933) ∨ (¬ p934) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p927) := fun hu => hn (Or.inl hu)
  have u1 : p931 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p918) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p930 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p933 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p934 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p932) := by
    rcases h5344 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u1)
    · exact q4
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p935 := by
    rcases h5443 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p936 := by
    rcases h5444 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p937 := by
    rcases h5445 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p938 := by
    rcases h5446 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p939 := by
    rcases h5447 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h5369 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22924 (p3 p226 p568 p569 p570 p571 p572 p573 : Prop)
    (h3232 : p568 ∨ p569)
    (h3233 : p568 ∨ p570)
    (h3234 : p568 ∨ p571)
    (h3235 : p568 ∨ p572)
    (h3236 : p568 ∨ p573)
    (h3149 : p3 ∨ p226 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p568 ∨ p3 ∨ p226 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p568) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p569 := by
    rcases h3232 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p570 := by
    rcases h3233 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p571 := by
    rcases h3234 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p572 := by
    rcases h3235 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p573 := by
    rcases h3236 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3149 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22925 (p3 p226 p567 p569 p570 p571 p572 p573 : Prop)
    (h3227 : p567 ∨ p569)
    (h3228 : p567 ∨ p570)
    (h3229 : p567 ∨ p571)
    (h3230 : p567 ∨ p572)
    (h3231 : p567 ∨ p573)
    (h3149 : p3 ∨ p226 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p567 ∨ p3 ∨ p226 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p567) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p569 := by
    rcases h3227 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p570 := by
    rcases h3228 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p571 := by
    rcases h3229 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p572 := by
    rcases h3230 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p573 := by
    rcases h3231 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3149 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22926 (p3 p226 p566 p569 p570 p571 p572 p573 : Prop)
    (h3222 : p566 ∨ p569)
    (h3223 : p566 ∨ p570)
    (h3224 : p566 ∨ p571)
    (h3225 : p566 ∨ p572)
    (h3226 : p566 ∨ p573)
    (h3149 : p3 ∨ p226 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p566 ∨ p3 ∨ p226 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p566) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p569 := by
    rcases h3222 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p570 := by
    rcases h3223 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p571 := by
    rcases h3224 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p572 := by
    rcases h3225 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p573 := by
    rcases h3226 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3149 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22927 (p3 p226 p565 p569 p570 p571 p572 p573 : Prop)
    (h3217 : p565 ∨ p569)
    (h3218 : p565 ∨ p570)
    (h3219 : p565 ∨ p571)
    (h3220 : p565 ∨ p572)
    (h3221 : p565 ∨ p573)
    (h3149 : p3 ∨ p226 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p565 ∨ p3 ∨ p226 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p565) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p569 := by
    rcases h3217 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p570 := by
    rcases h3218 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p571 := by
    rcases h3219 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p572 := by
    rcases h3220 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p573 := by
    rcases h3221 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3149 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22928 (p3 p226 p564 p565 p566 p567 p568 p569 p570 p571 p572 p573 : Prop)
    (h3124 : p3 ∨ p226 ∨ (¬ p564) ∨ (¬ p565) ∨ (¬ p566) ∨ (¬ p567) ∨ (¬ p568))
    (h3212 : p564 ∨ p569)
    (h3213 : p564 ∨ p570)
    (h3214 : p564 ∨ p571)
    (h3215 : p564 ∨ p572)
    (h3216 : p564 ∨ p573)
    (h3149 : p3 ∨ p226 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : (¬ p565) ∨ (¬ p568) ∨ p226 ∨ p3 ∨ (¬ p566) ∨ (¬ p567) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p565 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p568 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p566 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p567 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p564) := by
    rcases h3124 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p569 := by
    rcases h3212 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p570 := by
    rcases h3213 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p571 := by
    rcases h3214 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p572 := by
    rcases h3215 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p573 := by
    rcases h3216 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3149 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22929 (p3 p226 p565 p566 p567 p568 : Prop)
    (h22924 : p568 ∨ p3 ∨ p226)
    (h22925 : p567 ∨ p3 ∨ p226)
    (h22926 : p566 ∨ p3 ∨ p226)
    (h22927 : p565 ∨ p3 ∨ p226)
    (h22928 : (¬ p565) ∨ (¬ p568) ∨ p226 ∨ p3 ∨ (¬ p566) ∨ (¬ p567)) : p3 ∨ p226 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p226) := fun hu => hn (Or.inr hu)
  have u2 : p568 := by
    rcases h22924 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p567 := by
    rcases h22925 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p566 := by
    rcases h22926 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p565 := by
    rcases h22927 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22928 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22930 (p226 p561 p568 p569 p570 p571 p572 p573 : Prop)
    (h3232 : p568 ∨ p569)
    (h3233 : p568 ∨ p570)
    (h3234 : p568 ∨ p571)
    (h3235 : p568 ∨ p572)
    (h3236 : p568 ∨ p573)
    (h3148 : p226 ∨ p561 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p568 ∨ p226 ∨ p561 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p568) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p226) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p561) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p569 := by
    rcases h3232 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p570 := by
    rcases h3233 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p571 := by
    rcases h3234 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p572 := by
    rcases h3235 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p573 := by
    rcases h3236 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3148 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22931 (p226 p561 p564 p569 p570 p571 p572 p573 : Prop)
    (h3212 : p564 ∨ p569)
    (h3213 : p564 ∨ p570)
    (h3214 : p564 ∨ p571)
    (h3215 : p564 ∨ p572)
    (h3216 : p564 ∨ p573)
    (h3148 : p226 ∨ p561 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p564 ∨ p226 ∨ p561 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p564) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p226) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p561) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p569 := by
    rcases h3212 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p570 := by
    rcases h3213 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p571 := by
    rcases h3214 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p572 := by
    rcases h3215 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p573 := by
    rcases h3216 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3148 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22932 (p226 p561 p567 p569 p570 p571 p572 p573 : Prop)
    (h3227 : p567 ∨ p569)
    (h3228 : p567 ∨ p570)
    (h3229 : p567 ∨ p571)
    (h3230 : p567 ∨ p572)
    (h3231 : p567 ∨ p573)
    (h3148 : p226 ∨ p561 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p567 ∨ p226 ∨ p561 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p567) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p226) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p561) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p569 := by
    rcases h3227 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p570 := by
    rcases h3228 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p571 := by
    rcases h3229 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p572 := by
    rcases h3230 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p573 := by
    rcases h3231 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3148 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22933 (p226 p561 p566 p569 p570 p571 p572 p573 : Prop)
    (h3222 : p566 ∨ p569)
    (h3223 : p566 ∨ p570)
    (h3224 : p566 ∨ p571)
    (h3225 : p566 ∨ p572)
    (h3226 : p566 ∨ p573)
    (h3148 : p226 ∨ p561 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : p566 ∨ p226 ∨ p561 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p566) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p226) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p561) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p569 := by
    rcases h3222 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p570 := by
    rcases h3223 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p571 := by
    rcases h3224 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p572 := by
    rcases h3225 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p573 := by
    rcases h3226 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3148 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22934 (p226 p561 p564 p565 p566 p567 p568 p569 p570 p571 p572 p573 : Prop)
    (h3123 : p226 ∨ p561 ∨ (¬ p564) ∨ (¬ p565) ∨ (¬ p566) ∨ (¬ p567) ∨ (¬ p568))
    (h3217 : p565 ∨ p569)
    (h3218 : p565 ∨ p570)
    (h3219 : p565 ∨ p571)
    (h3220 : p565 ∨ p572)
    (h3221 : p565 ∨ p573)
    (h3148 : p226 ∨ p561 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573)) : (¬ p566) ∨ (¬ p568) ∨ p226 ∨ p561 ∨ (¬ p567) ∨ (¬ p564) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p566 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p568 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p226) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p561) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p567 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p564 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p565) := by
    rcases h3123 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u1)
  have u7 : p569 := by
    rcases h3217 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p570 := by
    rcases h3218 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p571 := by
    rcases h3219 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p572 := by
    rcases h3220 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p573 := by
    rcases h3221 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3148 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22935 (p226 p561 p564 p566 p567 p568 : Prop)
    (h22930 : p568 ∨ p226 ∨ p561)
    (h22931 : p564 ∨ p226 ∨ p561)
    (h22932 : p567 ∨ p226 ∨ p561)
    (h22933 : p566 ∨ p226 ∨ p561)
    (h22934 : (¬ p566) ∨ (¬ p568) ∨ p226 ∨ p561 ∨ (¬ p567) ∨ (¬ p564)) : p226 ∨ p561 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p226) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p561) := fun hu => hn (Or.inr hu)
  have u2 : p568 := by
    rcases h22930 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p564 := by
    rcases h22931 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p567 := by
    rcases h22932 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p566 := by
    rcases h22933 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22934 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22936 (p12 p1036 p1045 p1046 p1047 p1048 p1049 p1054 : Prop)
    (h6200 : p1045 ∨ p1054)
    (h6205 : p1046 ∨ p1054)
    (h6210 : p1047 ∨ p1054)
    (h6215 : p1048 ∨ p1054)
    (h6220 : p1049 ∨ p1054)
    (h6108 : p12 ∨ p1036 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : p1054 ∨ p1036 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1054) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1036) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1045 := by
    rcases h6200 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1046 := by
    rcases h6205 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1047 := by
    rcases h6210 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1048 := by
    rcases h6215 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1049 := by
    rcases h6220 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6108 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22937 (p12 p1036 p1045 p1046 p1047 p1048 p1049 p1053 : Prop)
    (h6199 : p1045 ∨ p1053)
    (h6204 : p1046 ∨ p1053)
    (h6209 : p1047 ∨ p1053)
    (h6214 : p1048 ∨ p1053)
    (h6219 : p1049 ∨ p1053)
    (h6108 : p12 ∨ p1036 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : p1053 ∨ p1036 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1053) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1036) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1045 := by
    rcases h6199 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1046 := by
    rcases h6204 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1047 := by
    rcases h6209 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1048 := by
    rcases h6214 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1049 := by
    rcases h6219 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6108 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22938 (p12 p1036 p1045 p1046 p1047 p1048 p1049 p1052 : Prop)
    (h6198 : p1045 ∨ p1052)
    (h6203 : p1046 ∨ p1052)
    (h6208 : p1047 ∨ p1052)
    (h6213 : p1048 ∨ p1052)
    (h6218 : p1049 ∨ p1052)
    (h6108 : p12 ∨ p1036 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : p1052 ∨ p1036 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1052) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1036) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1045 := by
    rcases h6198 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1046 := by
    rcases h6203 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1047 := by
    rcases h6208 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1048 := by
    rcases h6213 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1049 := by
    rcases h6218 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6108 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22939 (p12 p1036 p1045 p1046 p1047 p1048 p1049 p1051 : Prop)
    (h6197 : p1045 ∨ p1051)
    (h6202 : p1046 ∨ p1051)
    (h6207 : p1047 ∨ p1051)
    (h6212 : p1048 ∨ p1051)
    (h6217 : p1049 ∨ p1051)
    (h6108 : p12 ∨ p1036 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : p1051 ∨ p1036 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1051) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1036) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1045 := by
    rcases h6197 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1046 := by
    rcases h6202 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1047 := by
    rcases h6207 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1048 := by
    rcases h6212 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1049 := by
    rcases h6217 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6108 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22940 (p12 p1036 p1045 p1046 p1047 p1048 p1049 p1050 p1051 p1052 p1053 p1054 : Prop)
    (h6133 : p12 ∨ p1036 ∨ (¬ p1050) ∨ (¬ p1051) ∨ (¬ p1052) ∨ (¬ p1053) ∨ (¬ p1054))
    (h6196 : p1045 ∨ p1050)
    (h6201 : p1046 ∨ p1050)
    (h6206 : p1047 ∨ p1050)
    (h6211 : p1048 ∨ p1050)
    (h6216 : p1049 ∨ p1050)
    (h6108 : p12 ∨ p1036 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : (¬ p1051) ∨ (¬ p1054) ∨ p12 ∨ p1036 ∨ (¬ p1052) ∨ (¬ p1053) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1051 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1054 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p12) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1036) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1052 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1053 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1050) := by
    rcases h6133 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p1045 := by
    rcases h6196 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1046 := by
    rcases h6201 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1047 := by
    rcases h6206 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1048 := by
    rcases h6211 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1049 := by
    rcases h6216 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h6108 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22941 (p12 p1036 p1051 p1052 p1053 p1054 : Prop)
    (h22936 : p1054 ∨ p1036 ∨ p12)
    (h22937 : p1053 ∨ p1036 ∨ p12)
    (h22938 : p1052 ∨ p1036 ∨ p12)
    (h22939 : p1051 ∨ p1036 ∨ p12)
    (h22940 : (¬ p1051) ∨ (¬ p1054) ∨ p12 ∨ p1036 ∨ (¬ p1052) ∨ (¬ p1053)) : p1036 ∨ p12 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1036) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p12) := fun hu => hn (Or.inr hu)
  have u2 : p1054 := by
    rcases h22936 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1053 := by
    rcases h22937 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1052 := by
    rcases h22938 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1051 := by
    rcases h22939 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22940 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22942 (p225 p544 p550 p551 p552 p553 p554 p555 : Prop)
    (h3107 : p550 ∨ p551)
    (h3108 : p550 ∨ p552)
    (h3109 : p550 ∨ p553)
    (h3110 : p550 ∨ p554)
    (h3111 : p550 ∨ p555)
    (h3024 : p225 ∨ p544 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : p550 ∨ p544 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p550) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p544) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p551 := by
    rcases h3107 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p552 := by
    rcases h3108 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p553 := by
    rcases h3109 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p554 := by
    rcases h3110 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p555 := by
    rcases h3111 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3024 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22943 (p225 p544 p549 p551 p552 p553 p554 p555 : Prop)
    (h3102 : p549 ∨ p551)
    (h3103 : p549 ∨ p552)
    (h3104 : p549 ∨ p553)
    (h3105 : p549 ∨ p554)
    (h3106 : p549 ∨ p555)
    (h3024 : p225 ∨ p544 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : p549 ∨ p544 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p549) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p544) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p551 := by
    rcases h3102 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p552 := by
    rcases h3103 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p553 := by
    rcases h3104 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p554 := by
    rcases h3105 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p555 := by
    rcases h3106 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3024 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22944 (p225 p544 p548 p551 p552 p553 p554 p555 : Prop)
    (h3097 : p548 ∨ p551)
    (h3098 : p548 ∨ p552)
    (h3099 : p548 ∨ p553)
    (h3100 : p548 ∨ p554)
    (h3101 : p548 ∨ p555)
    (h3024 : p225 ∨ p544 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : p548 ∨ p544 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p548) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p544) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p551 := by
    rcases h3097 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p552 := by
    rcases h3098 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p553 := by
    rcases h3099 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p554 := by
    rcases h3100 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p555 := by
    rcases h3101 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3024 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22945 (p225 p544 p547 p551 p552 p553 p554 p555 : Prop)
    (h3092 : p547 ∨ p551)
    (h3093 : p547 ∨ p552)
    (h3094 : p547 ∨ p553)
    (h3095 : p547 ∨ p554)
    (h3096 : p547 ∨ p555)
    (h3024 : p225 ∨ p544 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : p547 ∨ p544 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p547) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p544) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p225) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p551 := by
    rcases h3092 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p552 := by
    rcases h3093 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p553 := by
    rcases h3094 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p554 := by
    rcases h3095 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p555 := by
    rcases h3096 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3024 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22946 (p225 p544 p546 p547 p548 p549 p550 p551 p552 p553 p554 p555 : Prop)
    (h2999 : p225 ∨ p544 ∨ (¬ p546) ∨ (¬ p547) ∨ (¬ p548) ∨ (¬ p549) ∨ (¬ p550))
    (h3087 : p546 ∨ p551)
    (h3088 : p546 ∨ p552)
    (h3089 : p546 ∨ p553)
    (h3090 : p546 ∨ p554)
    (h3091 : p546 ∨ p555)
    (h3024 : p225 ∨ p544 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : (¬ p547) ∨ p225 ∨ (¬ p550) ∨ (¬ p548) ∨ p544 ∨ (¬ p549) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p547 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p550 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p548 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p544) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p549 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p546) := by
    rcases h2999 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u4 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u2)
  have u7 : p551 := by
    rcases h3087 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p552 := by
    rcases h3088 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p553 := by
    rcases h3089 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p554 := by
    rcases h3090 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p555 := by
    rcases h3091 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3024 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22947 (p225 p544 p547 p548 p549 p550 : Prop)
    (h22942 : p550 ∨ p544 ∨ p225)
    (h22943 : p549 ∨ p544 ∨ p225)
    (h22944 : p548 ∨ p544 ∨ p225)
    (h22945 : p547 ∨ p544 ∨ p225)
    (h22946 : (¬ p547) ∨ p225 ∨ (¬ p550) ∨ (¬ p548) ∨ p544 ∨ (¬ p549)) : p544 ∨ p225 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p544) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p225) := fun hu => hn (Or.inr hu)
  have u2 : p550 := by
    rcases h22942 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p549 := by
    rcases h22943 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p548 := by
    rcases h22944 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p547 := by
    rcases h22945 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22946 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u4)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u3)

theorem step22948 (p104 p110 p225 p344 p345 p346 p438 p544 p728 : Prop)
    (h22560 : p346 ∨ p344)
    (h21358 : p345 ∨ p344)
    (h14153 : (¬ p104) ∨ p225 ∨ (¬ p346))
    (h22241 : p110 ∨ p104)
    (h16643 : (¬ p110) ∨ (¬ p345) ∨ (¬ p438) ∨ (¬ p544) ∨ (¬ p728))
    (h22947 : p544 ∨ p225) : p225 ∨ (¬ p728) ∨ (¬ p438) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p225) := fun hu => hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p346 := by
    rcases h22560 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p345 := by
    rcases h21358 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : (¬ p104) := by
    rcases h14153 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u4)
  have u7 : p110 := by
    rcases h22241 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : (¬ p544) := by
    rcases h16643 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u2)
    · exact q3
    · exact False.elim (q4 u1)
  rcases h22947 with q0 | q1
  · exact False.elim (u8 q0)
  · exact False.elim (u0 q1)

theorem step22949 (p103 p109 p113 p116 p117 p118 p119 p120 : Prop)
    (h630 : p113 ∨ p116)
    (h631 : p113 ∨ p117)
    (h632 : p113 ∨ p118)
    (h633 : p113 ∨ p119)
    (h634 : p113 ∨ p120)
    (h548 : p103 ∨ p109 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p113 ∨ p109 ∨ p103 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p113) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p109) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p103) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h630 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h631 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h632 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h633 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h634 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h548 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22950 (p103 p109 p111 p116 p117 p118 p119 p120 : Prop)
    (h620 : p111 ∨ p116)
    (h621 : p111 ∨ p117)
    (h622 : p111 ∨ p118)
    (h623 : p111 ∨ p119)
    (h624 : p111 ∨ p120)
    (h548 : p103 ∨ p109 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p111 ∨ p109 ∨ p103 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p111) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p109) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p103) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h620 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h621 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h622 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h623 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h624 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h548 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22951 (p103 p109 p114 p116 p117 p118 p119 p120 : Prop)
    (h635 : p114 ∨ p116)
    (h636 : p114 ∨ p117)
    (h637 : p114 ∨ p118)
    (h638 : p114 ∨ p119)
    (h639 : p114 ∨ p120)
    (h548 : p103 ∨ p109 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p114 ∨ p109 ∨ p103 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p114) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p109) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p103) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h635 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h636 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h637 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h638 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h639 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h548 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22952 (p103 p109 p115 p116 p117 p118 p119 p120 : Prop)
    (h640 : p115 ∨ p116)
    (h641 : p115 ∨ p117)
    (h642 : p115 ∨ p118)
    (h643 : p115 ∨ p119)
    (h644 : p115 ∨ p120)
    (h548 : p103 ∨ p109 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : p115 ∨ p109 ∨ p103 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p115) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p109) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p103) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h640 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p117 := by
    rcases h641 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p118 := by
    rcases h642 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p119 := by
    rcases h643 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p120 := by
    rcases h644 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h548 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22953 (p103 p109 p111 p112 p113 p114 p115 p116 p117 p118 p119 p120 : Prop)
    (h523 : p103 ∨ p109 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115))
    (h625 : p112 ∨ p116)
    (h626 : p112 ∨ p117)
    (h627 : p112 ∨ p118)
    (h628 : p112 ∨ p119)
    (h629 : p112 ∨ p120)
    (h548 : p103 ∨ p109 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120)) : (¬ p115) ∨ (¬ p111) ∨ p109 ∨ p103 ∨ (¬ p113) ∨ (¬ p114) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p111 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p109) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p103) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p113 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p114 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p112) := by
    rcases h523 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u0)
  have u7 : p116 := by
    rcases h625 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p117 := by
    rcases h626 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p118 := by
    rcases h627 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p119 := by
    rcases h628 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p120 := by
    rcases h629 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h548 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22954 (p103 p109 p111 p113 p114 p115 : Prop)
    (h22949 : p113 ∨ p109 ∨ p103)
    (h22950 : p111 ∨ p109 ∨ p103)
    (h22951 : p114 ∨ p109 ∨ p103)
    (h22952 : p115 ∨ p109 ∨ p103)
    (h22953 : (¬ p115) ∨ (¬ p111) ∨ p109 ∨ p103 ∨ (¬ p113) ∨ (¬ p114)) : p109 ∨ p103 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p109) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p103) := fun hu => hn (Or.inr hu)
  have u2 : p113 := by
    rcases h22949 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p111 := by
    rcases h22950 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p114 := by
    rcases h22951 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p115 := by
    rcases h22952 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22953 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)

theorem step22955 (p21 p25 p28 p33 p34 p35 p36 p37 : Prop)
    (h105 : p28 ∨ p33)
    (h106 : p28 ∨ p34)
    (h107 : p28 ∨ p35)
    (h108 : p28 ∨ p36)
    (h109 : p28 ∨ p37)
    (h36 : p21 ∨ p25 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p28 ∨ p21 ∨ p25 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p28) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p21) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p25) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p33 := by
    rcases h105 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p34 := by
    rcases h106 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p35 := by
    rcases h107 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p36 := by
    rcases h108 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p37 := by
    rcases h109 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h36 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22956 (p21 p25 p32 p33 p34 p35 p36 p37 : Prop)
    (h125 : p32 ∨ p33)
    (h126 : p32 ∨ p34)
    (h127 : p32 ∨ p35)
    (h128 : p32 ∨ p36)
    (h129 : p32 ∨ p37)
    (h36 : p21 ∨ p25 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p32 ∨ p21 ∨ p25 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p32) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p21) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p25) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p33 := by
    rcases h125 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p34 := by
    rcases h126 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p35 := by
    rcases h127 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p36 := by
    rcases h128 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p37 := by
    rcases h129 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h36 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22957 (p21 p25 p31 p33 p34 p35 p36 p37 : Prop)
    (h120 : p31 ∨ p33)
    (h121 : p31 ∨ p34)
    (h122 : p31 ∨ p35)
    (h123 : p31 ∨ p36)
    (h124 : p31 ∨ p37)
    (h36 : p21 ∨ p25 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p31 ∨ p21 ∨ p25 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p31) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p21) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p25) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p33 := by
    rcases h120 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p34 := by
    rcases h121 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p35 := by
    rcases h122 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p36 := by
    rcases h123 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p37 := by
    rcases h124 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h36 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22958 (p21 p25 p30 p33 p34 p35 p36 p37 : Prop)
    (h115 : p30 ∨ p33)
    (h116 : p30 ∨ p34)
    (h117 : p30 ∨ p35)
    (h118 : p30 ∨ p36)
    (h119 : p30 ∨ p37)
    (h36 : p21 ∨ p25 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p30 ∨ p21 ∨ p25 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p30) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p21) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p25) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p33 := by
    rcases h115 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p34 := by
    rcases h116 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p35 := by
    rcases h117 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p36 := by
    rcases h118 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p37 := by
    rcases h119 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h36 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22959 (p14 p15 p18 p19 p21 p25 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p103 p109 p229 p495 : Prop)
    (h21834 : p229 ∨ p14)
    (h4 : (¬ p18) ∨ (¬ p19))
    (h14747 : (¬ p18) ∨ (¬ p103) ∨ p229)
    (h22954 : p109 ∨ p103)
    (h16540 : (¬ p14) ∨ (¬ p15) ∨ (¬ p21) ∨ (¬ p109) ∨ (¬ p495))
    (h22955 : p28 ∨ p21 ∨ p25)
    (h22956 : p32 ∨ p21 ∨ p25)
    (h22957 : p31 ∨ p21 ∨ p25)
    (h22958 : p30 ∨ p21 ∨ p25)
    (h12 : p19 ∨ p21 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32))
    (h110 : p29 ∨ p33)
    (h111 : p29 ∨ p34)
    (h112 : p29 ∨ p35)
    (h113 : p29 ∨ p36)
    (h114 : p29 ∨ p37)
    (h36 : p21 ∨ p25 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : (¬ p18) ∨ p229 ∨ p25 ∨ (¬ p15) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p25) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p14 := by
    rcases h21834 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u6 : (¬ p19) := by
    rcases h4 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u7 : (¬ p103) := by
    rcases h14747 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (u1 q2)
  have u8 : p109 := by
    rcases h22954 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : (¬ p21) := by
    rcases h16540 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u3)
    · exact q2
    · exact False.elim (q3 u8)
    · exact False.elim (q4 u4)
  have u10 : p28 := by
    rcases h22955 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u2 q2)
  have u11 : p32 := by
    rcases h22956 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u2 q2)
  have u12 : p31 := by
    rcases h22957 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u2 q2)
  have u13 : p30 := by
    rcases h22958 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u2 q2)
  have u14 : (¬ p29) := by
    rcases h12 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u6 q0)
    · exact False.elim (u9 q1)
    · exact False.elim (q2 u10)
    · exact q3
    · exact False.elim (q4 u13)
    · exact False.elim (q5 u12)
    · exact False.elim (q6 u11)
  have u15 : p33 := by
    rcases h110 with q0 | q1
    · exact False.elim (u14 q0)
    · exact q1
  have u16 : p34 := by
    rcases h111 with q0 | q1
    · exact False.elim (u14 q0)
    · exact q1
  have u17 : p35 := by
    rcases h112 with q0 | q1
    · exact False.elim (u14 q0)
    · exact q1
  have u18 : p36 := by
    rcases h113 with q0 | q1
    · exact False.elim (u14 q0)
    · exact q1
  have u19 : p37 := by
    rcases h114 with q0 | q1
    · exact False.elim (u14 q0)
    · exact q1
  rcases h36 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u9 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u15)
  · exact False.elim (q3 u16)
  · exact False.elim (q4 u17)
  · exact False.elim (q5 u18)
  · exact False.elim (q6 u19)

theorem step22960 (p15 p19 p85 p323 p325 p329 p1187 : Prop)
    (h16532 : (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p323))
    (h12233 : (¬ p19) ∨ (¬ p329) ∨ (¬ p1187))
    (h21607 : p329 ∨ p323 ∨ p325) : (¬ p19) ∨ p325 ∨ (¬ p1187) ∨ (¬ p15) ∨ (¬ p85) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p325) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p323) := by
    rcases h16532 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u4)
    · exact q3
  have u6 : (¬ p329) := by
    rcases h12233 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u2)
  rcases h21607 with q0 | q1 | q2
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (u1 q2)

theorem step22961 (p734 p738 p744 p745 p746 p747 p748 p749 : Prop)
    (h4276 : p744 ∨ p745)
    (h4277 : p744 ∨ p746)
    (h4278 : p744 ∨ p747)
    (h4279 : p744 ∨ p748)
    (h4280 : p744 ∨ p749)
    (h4194 : p734 ∨ p738 ∨ (¬ p745) ∨ (¬ p746) ∨ (¬ p747) ∨ (¬ p748) ∨ (¬ p749)) : p744 ∨ p738 ∨ p734 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p744) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p738) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p734) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p745 := by
    rcases h4276 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p746 := by
    rcases h4277 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p747 := by
    rcases h4278 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p748 := by
    rcases h4279 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p749 := by
    rcases h4280 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4194 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22962 (p734 p738 p743 p745 p746 p747 p748 p749 : Prop)
    (h4271 : p743 ∨ p745)
    (h4272 : p743 ∨ p746)
    (h4273 : p743 ∨ p747)
    (h4274 : p743 ∨ p748)
    (h4275 : p743 ∨ p749)
    (h4194 : p734 ∨ p738 ∨ (¬ p745) ∨ (¬ p746) ∨ (¬ p747) ∨ (¬ p748) ∨ (¬ p749)) : p743 ∨ p738 ∨ p734 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p743) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p738) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p734) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p745 := by
    rcases h4271 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p746 := by
    rcases h4272 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p747 := by
    rcases h4273 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p748 := by
    rcases h4274 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p749 := by
    rcases h4275 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4194 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22963 (p734 p738 p742 p745 p746 p747 p748 p749 : Prop)
    (h4266 : p742 ∨ p745)
    (h4267 : p742 ∨ p746)
    (h4268 : p742 ∨ p747)
    (h4269 : p742 ∨ p748)
    (h4270 : p742 ∨ p749)
    (h4194 : p734 ∨ p738 ∨ (¬ p745) ∨ (¬ p746) ∨ (¬ p747) ∨ (¬ p748) ∨ (¬ p749)) : p742 ∨ p738 ∨ p734 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p742) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p738) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p734) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p745 := by
    rcases h4266 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p746 := by
    rcases h4267 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p747 := by
    rcases h4268 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p748 := by
    rcases h4269 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p749 := by
    rcases h4270 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4194 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22964 (p734 p738 p741 p745 p746 p747 p748 p749 : Prop)
    (h4261 : p741 ∨ p745)
    (h4262 : p741 ∨ p746)
    (h4263 : p741 ∨ p747)
    (h4264 : p741 ∨ p748)
    (h4265 : p741 ∨ p749)
    (h4194 : p734 ∨ p738 ∨ (¬ p745) ∨ (¬ p746) ∨ (¬ p747) ∨ (¬ p748) ∨ (¬ p749)) : p741 ∨ p738 ∨ p734 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p741) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p738) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p734) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p745 := by
    rcases h4261 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p746 := by
    rcases h4262 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p747 := by
    rcases h4263 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p748 := by
    rcases h4264 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p749 := by
    rcases h4265 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4194 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22965 (p734 p738 p740 p741 p742 p743 p744 p745 p746 p747 p748 p749 : Prop)
    (h4169 : p734 ∨ p738 ∨ (¬ p740) ∨ (¬ p741) ∨ (¬ p742) ∨ (¬ p743) ∨ (¬ p744))
    (h4256 : p740 ∨ p745)
    (h4257 : p740 ∨ p746)
    (h4258 : p740 ∨ p747)
    (h4259 : p740 ∨ p748)
    (h4260 : p740 ∨ p749)
    (h4194 : p734 ∨ p738 ∨ (¬ p745) ∨ (¬ p746) ∨ (¬ p747) ∨ (¬ p748) ∨ (¬ p749)) : (¬ p741) ∨ (¬ p744) ∨ p734 ∨ p738 ∨ (¬ p742) ∨ (¬ p743) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p741 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p744 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p734) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p738) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p742 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p743 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p740) := by
    rcases h4169 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p745 := by
    rcases h4256 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p746 := by
    rcases h4257 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p747 := by
    rcases h4258 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p748 := by
    rcases h4259 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p749 := by
    rcases h4260 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h4194 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22966 (p734 p738 p741 p742 p743 p744 : Prop)
    (h22961 : p744 ∨ p738 ∨ p734)
    (h22962 : p743 ∨ p738 ∨ p734)
    (h22963 : p742 ∨ p738 ∨ p734)
    (h22964 : p741 ∨ p738 ∨ p734)
    (h22965 : (¬ p741) ∨ (¬ p744) ∨ p734 ∨ p738 ∨ (¬ p742) ∨ (¬ p743)) : p738 ∨ p734 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p738) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p734) := fun hu => hn (Or.inr hu)
  have u2 : p744 := by
    rcases h22961 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p743 := by
    rcases h22962 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p742 := by
    rcases h22963 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p741 := by
    rcases h22964 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22965 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22967 (p898 p902 p911 p912 p913 p914 p915 p916 : Prop)
    (h5321 : p911 ∨ p912)
    (h5322 : p911 ∨ p913)
    (h5323 : p911 ∨ p914)
    (h5324 : p911 ∨ p915)
    (h5325 : p911 ∨ p916)
    (h5226 : p898 ∨ p902 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p911 ∨ p898 ∨ p902 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p911) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p898) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p902) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p912 := by
    rcases h5321 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p913 := by
    rcases h5322 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p914 := by
    rcases h5323 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p915 := by
    rcases h5324 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5325 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5226 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22968 (p898 p902 p910 p912 p913 p914 p915 p916 : Prop)
    (h5316 : p910 ∨ p912)
    (h5317 : p910 ∨ p913)
    (h5318 : p910 ∨ p914)
    (h5319 : p910 ∨ p915)
    (h5320 : p910 ∨ p916)
    (h5226 : p898 ∨ p902 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p910 ∨ p898 ∨ p902 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p910) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p898) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p902) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p912 := by
    rcases h5316 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p913 := by
    rcases h5317 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p914 := by
    rcases h5318 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p915 := by
    rcases h5319 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5320 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5226 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22969 (p898 p902 p909 p912 p913 p914 p915 p916 : Prop)
    (h5311 : p909 ∨ p912)
    (h5312 : p909 ∨ p913)
    (h5313 : p909 ∨ p914)
    (h5314 : p909 ∨ p915)
    (h5315 : p909 ∨ p916)
    (h5226 : p898 ∨ p902 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p909 ∨ p898 ∨ p902 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p909) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p898) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p902) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p912 := by
    rcases h5311 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p913 := by
    rcases h5312 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p914 := by
    rcases h5313 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p915 := by
    rcases h5314 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5315 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5226 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22970 (p898 p902 p908 p912 p913 p914 p915 p916 : Prop)
    (h5306 : p908 ∨ p912)
    (h5307 : p908 ∨ p913)
    (h5308 : p908 ∨ p914)
    (h5309 : p908 ∨ p915)
    (h5310 : p908 ∨ p916)
    (h5226 : p898 ∨ p902 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p908 ∨ p898 ∨ p902 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p908) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p898) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p902) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p912 := by
    rcases h5306 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p913 := by
    rcases h5307 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p914 := by
    rcases h5308 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p915 := by
    rcases h5309 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5310 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5226 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22971 (p898 p902 p907 p908 p909 p910 p911 p912 p913 p914 p915 p916 : Prop)
    (h5201 : p898 ∨ p902 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911))
    (h5301 : p907 ∨ p912)
    (h5302 : p907 ∨ p913)
    (h5303 : p907 ∨ p914)
    (h5304 : p907 ∨ p915)
    (h5305 : p907 ∨ p916)
    (h5226 : p898 ∨ p902 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : (¬ p908) ∨ (¬ p911) ∨ p898 ∨ p902 ∨ (¬ p909) ∨ (¬ p910) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p908 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p911 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p898) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p902) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p909 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p910 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p907) := by
    rcases h5201 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p912 := by
    rcases h5301 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p913 := by
    rcases h5302 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p914 := by
    rcases h5303 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p915 := by
    rcases h5304 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p916 := by
    rcases h5305 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h5226 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22972 (p898 p902 p908 p909 p910 p911 : Prop)
    (h22967 : p911 ∨ p898 ∨ p902)
    (h22968 : p910 ∨ p898 ∨ p902)
    (h22969 : p909 ∨ p898 ∨ p902)
    (h22970 : p908 ∨ p898 ∨ p902)
    (h22971 : (¬ p908) ∨ (¬ p911) ∨ p898 ∨ p902 ∨ (¬ p909) ∨ (¬ p910)) : p898 ∨ p902 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p898) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p902) := fun hu => hn (Or.inr hu)
  have u2 : p911 := by
    rcases h22967 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p910 := by
    rcases h22968 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p909 := by
    rcases h22969 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p908 := by
    rcases h22970 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22971 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22973 (p901 p902 p907 p912 p913 p914 p915 p916 : Prop)
    (h5301 : p907 ∨ p912)
    (h5302 : p907 ∨ p913)
    (h5303 : p907 ∨ p914)
    (h5304 : p907 ∨ p915)
    (h5305 : p907 ∨ p916)
    (h5246 : p901 ∨ p902 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p907 ∨ p901 ∨ p902 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p907) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p901) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p902) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p912 := by
    rcases h5301 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p913 := by
    rcases h5302 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p914 := by
    rcases h5303 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p915 := by
    rcases h5304 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5305 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5246 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22974 (p901 p902 p911 p912 p913 p914 p915 p916 : Prop)
    (h5321 : p911 ∨ p912)
    (h5322 : p911 ∨ p913)
    (h5323 : p911 ∨ p914)
    (h5324 : p911 ∨ p915)
    (h5325 : p911 ∨ p916)
    (h5246 : p901 ∨ p902 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p911 ∨ p901 ∨ p902 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p911) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p901) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p902) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p912 := by
    rcases h5321 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p913 := by
    rcases h5322 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p914 := by
    rcases h5323 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p915 := by
    rcases h5324 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5325 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5246 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22975 (p901 p902 p910 p912 p913 p914 p915 p916 : Prop)
    (h5316 : p910 ∨ p912)
    (h5317 : p910 ∨ p913)
    (h5318 : p910 ∨ p914)
    (h5319 : p910 ∨ p915)
    (h5320 : p910 ∨ p916)
    (h5246 : p901 ∨ p902 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p910 ∨ p901 ∨ p902 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p910) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p901) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p902) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p912 := by
    rcases h5316 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p913 := by
    rcases h5317 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p914 := by
    rcases h5318 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p915 := by
    rcases h5319 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5320 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5246 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22976 (p901 p902 p909 p912 p913 p914 p915 p916 : Prop)
    (h5311 : p909 ∨ p912)
    (h5312 : p909 ∨ p913)
    (h5313 : p909 ∨ p914)
    (h5314 : p909 ∨ p915)
    (h5315 : p909 ∨ p916)
    (h5246 : p901 ∨ p902 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : p909 ∨ p901 ∨ p902 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p909) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p901) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p902) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p912 := by
    rcases h5311 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p913 := by
    rcases h5312 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p914 := by
    rcases h5313 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p915 := by
    rcases h5314 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p916 := by
    rcases h5315 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5246 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22977 (p901 p902 p907 p908 p909 p910 p911 p912 p913 p914 p915 p916 : Prop)
    (h5221 : p901 ∨ p902 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911))
    (h5306 : p908 ∨ p912)
    (h5307 : p908 ∨ p913)
    (h5308 : p908 ∨ p914)
    (h5309 : p908 ∨ p915)
    (h5310 : p908 ∨ p916)
    (h5246 : p901 ∨ p902 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916)) : (¬ p909) ∨ (¬ p907) ∨ p902 ∨ p901 ∨ (¬ p910) ∨ (¬ p911) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p909 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p907 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p902) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p901) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p910 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p911 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p908) := by
    rcases h5221 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p912 := by
    rcases h5306 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p913 := by
    rcases h5307 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p914 := by
    rcases h5308 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p915 := by
    rcases h5309 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p916 := by
    rcases h5310 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h5246 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22978 (p901 p902 p907 p909 p910 p911 : Prop)
    (h22973 : p907 ∨ p901 ∨ p902)
    (h22974 : p911 ∨ p901 ∨ p902)
    (h22975 : p910 ∨ p901 ∨ p902)
    (h22976 : p909 ∨ p901 ∨ p902)
    (h22977 : (¬ p909) ∨ (¬ p907) ∨ p902 ∨ p901 ∨ (¬ p910) ∨ (¬ p911)) : p901 ∨ p902 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p901) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p902) := fun hu => hn (Or.inr hu)
  have u2 : p907 := by
    rcases h22973 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p911 := by
    rcases h22974 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p910 := by
    rcases h22975 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p909 := by
    rcases h22976 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22977 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step22979 (p2 p3 p15 p18 p19 p25 p38 p43 p49 p50 p63 p64 p67 p69 p85 p86 p126 p185 p192 p224 p225 p226 p228 p229 p234 p237 p241 p256 p325 p344 p346 p347 p348 p367 p382 p387 p419 p434 p438 p455 p476 p481 p495 p499 p576 p579 p581 p595 p616 p657 p687 p690 p710 p713 p728 p734 p796 p836 p901 p902 p1187 p1287 p1328 p1334 p1366 p1443 p1452 : Prop)
    (h17969 : (¬ p63) ∨ (¬ p581) ∨ (¬ p1443) ∨ (¬ p1452))
    (h22211 : p85 ∨ p63)
    (h12204 : (¬ p576) ∨ (¬ p581))
    (h20860 : p576 ∨ p579)
    (h13230 : p455 ∨ (¬ p579) ∨ (¬ p1443))
    (h16546 : (¬ p85) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1452))
    (h20942 : p495 ∨ p499)
    (h21852 : p86 ∨ p63)
    (h22560 : p346 ∨ p344)
    (h12635 : (¬ p419) ∨ (¬ p1328) ∨ (¬ p1366))
    (h21365 : p1334 ∨ p1328)
    (h11962 : (¬ p2) ∨ (¬ p192) ∨ p796)
    (h10692 : (¬ p2) ∨ (¬ p481))
    (h22551 : p476 ∨ p481)
    (h12408 : p382 ∨ (¬ p419) ∨ (¬ p476))
    (h10100 : (¬ p367) ∨ (¬ p382) ∨ (¬ p387))
    (h21214 : p228 ∨ p387)
    (h21454 : p237 ∨ (¬ p256) ∨ (¬ p126))
    (h1179 : (¬ p185) ∨ (¬ p237))
    (h21965 : p241 ∨ p185)
    (h21316 : p64 ∨ p15)
    (h6604 : (¬ p15) ∨ (¬ p69))
    (h17354 : (¬ p15) ∨ p50)
    (h12953 : (¬ p15) ∨ (¬ p43) ∨ p63)
    (h16362 : (¬ p15) ∨ (¬ p85) ∨ (¬ p234) ∨ (¬ p796))
    (h10583 : (¬ p15) ∨ (¬ p25) ∨ p499)
    (h22913 : (¬ p15) ∨ (¬ p687) ∨ p63 ∨ (¬ p1334) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p796) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h22515 : p38 ∨ p64 ∨ p69)
    (h13974 : (¬ p50) ∨ p67 ∨ (¬ p192))
    (h22271 : p49 ∨ p43)
    (h21531 : p1187 ∨ p234)
    (h20766 : p690 ∨ p687)
    (h11942 : (¬ p367) ∨ (¬ p434) ∨ p687)
    (h22427 : p1287 ∨ (¬ p419) ∨ (¬ p2) ∨ (¬ p67))
    (h17451 : (¬ p346) ∨ (¬ p419) ∨ (¬ p690) ∨ (¬ p713) ∨ (¬ p1366))
    (h21060 : p438 ∨ p434)
    (h13541 : (¬ p325) ∨ p434 ∨ (¬ p1366))
    (h20854 : p710 ∨ p713)
    (h13411 : (¬ p241) ∨ (¬ p710) ∨ p836)
    (h16503 : (¬ p419) ∨ (¬ p734) ∨ (¬ p836) ∨ (¬ p1366))
    (h20753 : p728 ∨ p734)
    (h12514 : (¬ p348) ∨ (¬ p438) ∨ (¬ p728))
    (h21054 : p347 ∨ p348 ∨ p344)
    (h22948 : p225 ∨ (¬ p728) ∨ (¬ p438) ∨ p344)
    (h22960 : (¬ p19) ∨ p325 ∨ (¬ p1187) ∨ (¬ p15) ∨ (¬ p85))
    (h22840 : p19 ∨ p18)
    (h22959 : (¬ p18) ∨ p229 ∨ p25 ∨ (¬ p15) ∨ (¬ p495))
    (h18531 : (¬ p2) ∨ (¬ p3) ∨ (¬ p229) ∨ (¬ p419))
    (h22929 : p3 ∨ p226)
    (h16378 : (¬ p38) ∨ (¬ p49) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p228) ∨ (¬ p581) ∨ (¬ p1443))
    (h20814 : p224 ∨ p657)
    (h8778 : (¬ p657) ∨ (¬ p902) ∨ (¬ p1287))
    (h18864 : (¬ p86) ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p347) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p1287))
    (h21790 : p616 ∨ p595)
    (h16692 : (¬ p2) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p657) ∨ (¬ p901))
    (h22978 : p901 ∨ p902) : p64 ∨ (¬ p581) ∨ p344 ∨ (¬ p1366) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p192) ∨ (¬ p367) ∨ (¬ p256) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p64) := fun hu => hn (Or.inl hu)
  have u1 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p367 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : (¬ p63) := by
    rcases h17969 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
  have u13 : p85 := by
    rcases h22211 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u14 : (¬ p576) := by
    rcases h12204 with q0 | q1
    · exact q0
    · exact False.elim (q1 u1)
  have u15 : p579 := by
    rcases h20860 with q0 | q1
    · exact False.elim (u14 q0)
    · exact q1
  have u16 : p455 := by
    rcases h13230 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u15)
    · exact False.elim (q2 u4)
  have u17 : (¬ p499) := by
    rcases h16546 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u13)
    · exact False.elim (q1 u16)
    · exact q2
    · exact False.elim (q3 u5)
  have u18 : p495 := by
    rcases h20942 with q0 | q1
    · exact q0
    · exact False.elim (u17 q1)
  have u19 : p86 := by
    rcases h21852 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u20 : p346 := by
    rcases h22560 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u21 : (¬ p1328) := by
    rcases h12635 with q0 | q1 | q2
    · exact False.elim (q0 u10)
    · exact q1
    · exact False.elim (q2 u3)
  have u22 : p1334 := by
    rcases h21365 with q0 | q1
    · exact q0
    · exact False.elim (u21 q1)
  have u23 : p796 := by
    rcases h11962 with q0 | q1 | q2
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u6)
    · exact q2
  have u24 : (¬ p481) := by
    rcases h10692 with q0 | q1
    · exact False.elim (q0 u11)
    · exact q1
  have u25 : p476 := by
    rcases h22551 with q0 | q1
    · exact q0
    · exact False.elim (u24 q1)
  have u26 : p382 := by
    rcases h12408 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u10)
    · exact False.elim (q2 u25)
  have u27 : (¬ p387) := by
    rcases h10100 with q0 | q1 | q2
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u26)
    · exact q2
  have u28 : p228 := by
    rcases h21214 with q0 | q1
    · exact q0
    · exact False.elim (u27 q1)
  have u29 : p237 := by
    rcases h21454 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u8)
    · exact False.elim (q2 u9)
  have u30 : (¬ p185) := by
    rcases h1179 with q0 | q1
    · exact q0
    · exact False.elim (q1 u29)
  have u31 : p241 := by
    rcases h21965 with q0 | q1
    · exact q0
    · exact False.elim (u30 q1)
  have u32 : p15 := by
    rcases h21316 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u33 : (¬ p69) := by
    rcases h6604 with q0 | q1
    · exact False.elim (q0 u32)
    · exact q1
  have u34 : p50 := by
    rcases h17354 with q0 | q1
    · exact False.elim (q0 u32)
    · exact q1
  have u35 : (¬ p43) := by
    rcases h12953 with q0 | q1 | q2
    · exact False.elim (q0 u32)
    · exact q1
    · exact False.elim (u12 q2)
  have u36 : (¬ p234) := by
    rcases h16362 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u32)
    · exact False.elim (q1 u13)
    · exact q2
    · exact False.elim (q3 u23)
  have u37 : (¬ p25) := by
    rcases h10583 with q0 | q1 | q2
    · exact False.elim (q0 u32)
    · exact q1
    · exact False.elim (u17 q2)
  have u38 : (¬ p687) := by
    rcases h22913 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
    · exact False.elim (q0 u32)
    · exact q1
    · exact False.elim (u12 q2)
    · exact False.elim (q3 u22)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u23)
    · exact False.elim (q7 u8)
    · exact False.elim (q8 u10)
    · exact False.elim (q9 u11)
  have u39 : p38 := by
    rcases h22515 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u33 q2)
  have u40 : p67 := by
    rcases h13974 with q0 | q1 | q2
    · exact False.elim (q0 u34)
    · exact q1
    · exact False.elim (q2 u6)
  have u41 : p49 := by
    rcases h22271 with q0 | q1
    · exact q0
    · exact False.elim (u35 q1)
  have u42 : p1187 := by
    rcases h21531 with q0 | q1
    · exact q0
    · exact False.elim (u36 q1)
  have u43 : p690 := by
    rcases h20766 with q0 | q1
    · exact q0
    · exact False.elim (u38 q1)
  have u44 : (¬ p434) := by
    rcases h11942 with q0 | q1 | q2
    · exact False.elim (q0 u7)
    · exact q1
    · exact False.elim (u38 q2)
  have u45 : p1287 := by
    rcases h22427 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u10)
    · exact False.elim (q2 u11)
    · exact False.elim (q3 u40)
  have u46 : (¬ p713) := by
    rcases h17451 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u20)
    · exact False.elim (q1 u10)
    · exact False.elim (q2 u43)
    · exact q3
    · exact False.elim (q4 u3)
  have u47 : p438 := by
    rcases h21060 with q0 | q1
    · exact q0
    · exact False.elim (u44 q1)
  have u48 : (¬ p325) := by
    rcases h13541 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u44 q1)
    · exact False.elim (q2 u3)
  have u49 : p710 := by
    rcases h20854 with q0 | q1
    · exact q0
    · exact False.elim (u46 q1)
  have u50 : p836 := by
    rcases h13411 with q0 | q1 | q2
    · exact False.elim (q0 u31)
    · exact False.elim (q1 u49)
    · exact q2
  have u51 : (¬ p734) := by
    rcases h16503 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u10)
    · exact q1
    · exact False.elim (q2 u50)
    · exact False.elim (q3 u3)
  have u52 : p728 := by
    rcases h20753 with q0 | q1
    · exact q0
    · exact False.elim (u51 q1)
  have u53 : (¬ p348) := by
    rcases h12514 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u47)
    · exact False.elim (q2 u52)
  have u54 : p347 := by
    rcases h21054 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u53 q1)
    · exact False.elim (u2 q2)
  have u55 : p225 := by
    rcases h22948 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u52)
    · exact False.elim (q2 u47)
    · exact False.elim (u2 q3)
  have u56 : (¬ p19) := by
    rcases h22960 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (u48 q1)
    · exact False.elim (q2 u42)
    · exact False.elim (q3 u32)
    · exact False.elim (q4 u13)
  have u57 : p18 := by
    rcases h22840 with q0 | q1
    · exact False.elim (u56 q0)
    · exact q1
  have u58 : p229 := by
    rcases h22959 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u57)
    · exact q1
    · exact False.elim (u37 q2)
    · exact False.elim (q3 u32)
    · exact False.elim (q4 u18)
  have u59 : (¬ p3) := by
    rcases h18531 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u11)
    · exact q1
    · exact False.elim (q2 u58)
    · exact False.elim (q3 u10)
  have u60 : p226 := by
    rcases h22929 with q0 | q1
    · exact False.elim (u59 q0)
    · exact q1
  have u61 : (¬ p224) := by
    rcases h16378 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u39)
    · exact False.elim (q1 u41)
    · exact q2
    · exact False.elim (q3 u55)
    · exact False.elim (q4 u60)
    · exact False.elim (q5 u28)
    · exact False.elim (q6 u1)
    · exact False.elim (q7 u4)
  have u62 : p657 := by
    rcases h20814 with q0 | q1
    · exact False.elim (u61 q0)
    · exact q1
  have u63 : (¬ p902) := by
    rcases h8778 with q0 | q1 | q2
    · exact False.elim (q0 u62)
    · exact q1
    · exact False.elim (q2 u45)
  have u64 : (¬ p616) := by
    rcases h18864 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u19)
    · exact False.elim (q1 u9)
    · exact False.elim (q2 u8)
    · exact False.elim (q3 u54)
    · exact q4
    · exact False.elim (q5 u62)
    · exact False.elim (q6 u45)
  have u65 : p595 := by
    rcases h21790 with q0 | q1
    · exact False.elim (u64 q0)
    · exact q1
  have u66 : (¬ p901) := by
    rcases h16692 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u39)
    · exact False.elim (q2 u41)
    · exact False.elim (q3 u13)
    · exact False.elim (q4 u10)
    · exact False.elim (q5 u65)
    · exact False.elim (q6 u62)
    · exact q7
  rcases h22978 with q0 | q1
  · exact False.elim (u66 q0)
  · exact False.elim (u63 q1)

theorem step22980 (p15 p49 p84 p256 p419 p595 p616 p1189 p1193 p1443 p1452 : Prop)
    (h10651 : (¬ p595) ∨ (¬ p616))
    (h9388 : (¬ p15) ∨ p595 ∨ (¬ p1193))
    (h17508 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p616) ∨ (¬ p1189) ∨ (¬ p1443) ∨ (¬ p1452))
    (h21784 : p1189 ∨ p1193) : (¬ p15) ∨ (¬ p49) ∨ (¬ p616) ∨ (¬ p84) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p256) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p595) := by
    rcases h10651 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u9 : (¬ p1193) := by
    rcases h9388 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (u8 q1)
    · exact q2
  have u10 : (¬ p1189) := by
    rcases h17508 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u7)
    · exact False.elim (q5 u2)
    · exact q6
    · exact False.elim (q7 u4)
    · exact False.elim (q8 u5)
  rcases h21784 with q0 | q1
  · exact False.elim (u10 q0)
  · exact False.elim (u9 q1)

theorem step22981 (p8 p710 p716 p721 p722 p723 p724 p725 : Prop)
    (h4124 : p716 ∨ p721)
    (h4125 : p716 ∨ p722)
    (h4126 : p716 ∨ p723)
    (h4127 : p716 ∨ p724)
    (h4128 : p716 ∨ p725)
    (h4061 : p8 ∨ p710 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : p716 ∨ p710 ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p716) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p710) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p721 := by
    rcases h4124 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p722 := by
    rcases h4125 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p723 := by
    rcases h4126 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p724 := by
    rcases h4127 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p725 := by
    rcases h4128 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4061 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22982 (p8 p710 p720 p721 p722 p723 p724 p725 : Prop)
    (h4144 : p720 ∨ p721)
    (h4145 : p720 ∨ p722)
    (h4146 : p720 ∨ p723)
    (h4147 : p720 ∨ p724)
    (h4148 : p720 ∨ p725)
    (h4061 : p8 ∨ p710 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : p720 ∨ p710 ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p720) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p710) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p721 := by
    rcases h4144 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p722 := by
    rcases h4145 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p723 := by
    rcases h4146 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p724 := by
    rcases h4147 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p725 := by
    rcases h4148 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4061 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22983 (p8 p710 p719 p721 p722 p723 p724 p725 : Prop)
    (h4139 : p719 ∨ p721)
    (h4140 : p719 ∨ p722)
    (h4141 : p719 ∨ p723)
    (h4142 : p719 ∨ p724)
    (h4143 : p719 ∨ p725)
    (h4061 : p8 ∨ p710 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : p719 ∨ p710 ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p719) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p710) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p721 := by
    rcases h4139 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p722 := by
    rcases h4140 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p723 := by
    rcases h4141 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p724 := by
    rcases h4142 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p725 := by
    rcases h4143 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4061 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22984 (p8 p710 p718 p721 p722 p723 p724 p725 : Prop)
    (h4134 : p718 ∨ p721)
    (h4135 : p718 ∨ p722)
    (h4136 : p718 ∨ p723)
    (h4137 : p718 ∨ p724)
    (h4138 : p718 ∨ p725)
    (h4061 : p8 ∨ p710 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : p718 ∨ p710 ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p718) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p710) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p721 := by
    rcases h4134 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p722 := by
    rcases h4135 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p723 := by
    rcases h4136 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p724 := by
    rcases h4137 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p725 := by
    rcases h4138 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4061 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22985 (p8 p710 p716 p717 p718 p719 p720 p721 p722 p723 p724 p725 : Prop)
    (h4036 : p8 ∨ p710 ∨ (¬ p716) ∨ (¬ p717) ∨ (¬ p718) ∨ (¬ p719) ∨ (¬ p720))
    (h4129 : p717 ∨ p721)
    (h4130 : p717 ∨ p722)
    (h4131 : p717 ∨ p723)
    (h4132 : p717 ∨ p724)
    (h4133 : p717 ∨ p725)
    (h4061 : p8 ∨ p710 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725)) : (¬ p718) ∨ (¬ p720) ∨ p8 ∨ p710 ∨ (¬ p716) ∨ (¬ p719) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p718 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p720 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p8) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p710) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p716 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p719 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p717) := by
    rcases h4036 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p721 := by
    rcases h4129 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p722 := by
    rcases h4130 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p723 := by
    rcases h4131 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p724 := by
    rcases h4132 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p725 := by
    rcases h4133 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h4061 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step22986 (p8 p710 p716 p718 p719 p720 : Prop)
    (h22981 : p716 ∨ p710 ∨ p8)
    (h22982 : p720 ∨ p710 ∨ p8)
    (h22983 : p719 ∨ p710 ∨ p8)
    (h22984 : p718 ∨ p710 ∨ p8)
    (h22985 : (¬ p718) ∨ (¬ p720) ∨ p8 ∨ p710 ∨ (¬ p716) ∨ (¬ p719)) : p710 ∨ p8 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p710) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p8) := fun hu => hn (Or.inr hu)
  have u2 : p716 := by
    rcases h22981 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p720 := by
    rcases h22982 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p719 := by
    rcases h22983 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p718 := by
    rcases h22984 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22985 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)

theorem step22987 (p167 p169 p173 p174 p175 p176 p177 p182 : Prop)
    (h894 : p173 ∨ p182)
    (h899 : p174 ∨ p182)
    (h904 : p175 ∨ p182)
    (h909 : p176 ∨ p182)
    (h914 : p177 ∨ p182)
    (h800 : p167 ∨ p169 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p182 ∨ p169 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p182) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p169) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p167) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p173 := by
    rcases h894 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p174 := by
    rcases h899 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p175 := by
    rcases h904 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p176 := by
    rcases h909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p177 := by
    rcases h914 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h800 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22988 (p167 p169 p173 p174 p175 p176 p177 p180 : Prop)
    (h892 : p173 ∨ p180)
    (h897 : p174 ∨ p180)
    (h902 : p175 ∨ p180)
    (h907 : p176 ∨ p180)
    (h912 : p177 ∨ p180)
    (h800 : p167 ∨ p169 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p180 ∨ p169 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p180) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p169) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p167) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p173 := by
    rcases h892 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p174 := by
    rcases h897 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p175 := by
    rcases h902 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p176 := by
    rcases h907 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p177 := by
    rcases h912 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h800 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22989 (p167 p169 p173 p174 p175 p176 p177 p179 : Prop)
    (h891 : p173 ∨ p179)
    (h896 : p174 ∨ p179)
    (h901 : p175 ∨ p179)
    (h906 : p176 ∨ p179)
    (h911 : p177 ∨ p179)
    (h800 : p167 ∨ p169 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p179 ∨ p169 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p179) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p169) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p167) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p173 := by
    rcases h891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p174 := by
    rcases h896 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p175 := by
    rcases h901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p176 := by
    rcases h906 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p177 := by
    rcases h911 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h800 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22990 (p167 p169 p173 p174 p175 p176 p177 p178 p179 p180 p182 : Prop)
    (h21672 : (¬ p179) ∨ (¬ p180) ∨ p167 ∨ p169 ∨ (¬ p178) ∨ (¬ p182))
    (h890 : p173 ∨ p178)
    (h895 : p174 ∨ p178)
    (h900 : p175 ∨ p178)
    (h905 : p176 ∨ p178)
    (h910 : p177 ∨ p178)
    (h800 : p167 ∨ p169 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : (¬ p179) ∨ (¬ p180) ∨ (¬ p182) ∨ p169 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p179 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p180 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p182 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p169) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p167) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p178) := by
    rcases h21672 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u1)
    · exact False.elim (u4 q2)
    · exact False.elim (u3 q3)
    · exact q4
    · exact False.elim (q5 u2)
  have u6 : p173 := by
    rcases h890 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u7 : p174 := by
    rcases h895 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u8 : p175 := by
    rcases h900 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p176 := by
    rcases h905 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p177 := by
    rcases h910 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h800 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)

theorem step22991 (p167 p169 p179 p180 p182 : Prop)
    (h22987 : p182 ∨ p169 ∨ p167)
    (h22988 : p180 ∨ p169 ∨ p167)
    (h22989 : p179 ∨ p169 ∨ p167)
    (h22990 : (¬ p179) ∨ (¬ p180) ∨ (¬ p182) ∨ p169 ∨ p167) : p169 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p169) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p167) := fun hu => hn (Or.inr hu)
  have u2 : p182 := by
    rcases h22987 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p180 := by
    rcases h22988 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p179 := by
    rcases h22989 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22990 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u2)
  · exact False.elim (u0 q3)
  · exact False.elim (u1 q4)

theorem step22992 (p167 p170 p177 p178 p179 p180 p181 p182 : Prop)
    (h910 : p177 ∨ p178)
    (h913 : p177 ∨ p181)
    (h826 : p167 ∨ p170 ∨ (¬ p178) ∨ (¬ p179) ∨ (¬ p180) ∨ (¬ p181) ∨ (¬ p182)) : p177 ∨ (¬ p182) ∨ (¬ p180) ∨ (¬ p179) ∨ p170 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p177) := fun hu => hn (Or.inl hu)
  have u1 : p182 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p180 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p179 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p170) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p167) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p178 := by
    rcases h910 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p181 := by
    rcases h913 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h826 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step22993 (p167 p170 p176 p178 p179 p180 p181 p182 : Prop)
    (h905 : p176 ∨ p178)
    (h908 : p176 ∨ p181)
    (h826 : p167 ∨ p170 ∨ (¬ p178) ∨ (¬ p179) ∨ (¬ p180) ∨ (¬ p181) ∨ (¬ p182)) : p176 ∨ (¬ p182) ∨ (¬ p180) ∨ (¬ p179) ∨ p170 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p176) := fun hu => hn (Or.inl hu)
  have u1 : p182 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p180 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p179 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p170) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p167) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p178 := by
    rcases h905 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p181 := by
    rcases h908 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h826 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step22994 (p167 p170 p175 p178 p179 p180 p181 p182 : Prop)
    (h900 : p175 ∨ p178)
    (h903 : p175 ∨ p181)
    (h826 : p167 ∨ p170 ∨ (¬ p178) ∨ (¬ p179) ∨ (¬ p180) ∨ (¬ p181) ∨ (¬ p182)) : p175 ∨ (¬ p182) ∨ (¬ p180) ∨ (¬ p179) ∨ p170 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p175) := fun hu => hn (Or.inl hu)
  have u1 : p182 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p180 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p179 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p170) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p167) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p178 := by
    rcases h900 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p181 := by
    rcases h903 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h826 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step22995 (p167 p170 p174 p178 p179 p180 p181 p182 : Prop)
    (h895 : p174 ∨ p178)
    (h898 : p174 ∨ p181)
    (h826 : p167 ∨ p170 ∨ (¬ p178) ∨ (¬ p179) ∨ (¬ p180) ∨ (¬ p181) ∨ (¬ p182)) : p174 ∨ (¬ p182) ∨ (¬ p180) ∨ (¬ p179) ∨ p170 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p174) := fun hu => hn (Or.inl hu)
  have u1 : p182 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p180 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p179 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p170) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p167) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : p178 := by
    rcases h895 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p181 := by
    rcases h898 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h826 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step22996 (p167 p170 p173 p174 p175 p176 p177 p178 p179 p180 p181 p182 : Prop)
    (h22992 : p177 ∨ (¬ p182) ∨ (¬ p180) ∨ (¬ p179) ∨ p170 ∨ p167)
    (h22993 : p176 ∨ (¬ p182) ∨ (¬ p180) ∨ (¬ p179) ∨ p170 ∨ p167)
    (h22994 : p175 ∨ (¬ p182) ∨ (¬ p180) ∨ (¬ p179) ∨ p170 ∨ p167)
    (h22995 : p174 ∨ (¬ p182) ∨ (¬ p180) ∨ (¬ p179) ∨ p170 ∨ p167)
    (h801 : p167 ∨ p170 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177))
    (h890 : p173 ∨ p178)
    (h893 : p173 ∨ p181)
    (h826 : p167 ∨ p170 ∨ (¬ p178) ∨ (¬ p179) ∨ (¬ p180) ∨ (¬ p181) ∨ (¬ p182)) : (¬ p182) ∨ (¬ p180) ∨ p167 ∨ (¬ p179) ∨ p170 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p182 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p180 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p167) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p179 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p170) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p177 := by
    rcases h22992 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u3)
    · exact False.elim (u4 q4)
    · exact False.elim (u2 q5)
  have u6 : p176 := by
    rcases h22993 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u3)
    · exact False.elim (u4 q4)
    · exact False.elim (u2 q5)
  have u7 : p175 := by
    rcases h22994 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u3)
    · exact False.elim (u4 q4)
    · exact False.elim (u2 q5)
  have u8 : p174 := by
    rcases h22995 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u3)
    · exact False.elim (u4 q4)
    · exact False.elim (u2 q5)
  have u9 : (¬ p173) := by
    rcases h801 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u4 q1)
    · exact q2
    · exact False.elim (q3 u8)
    · exact False.elim (q4 u7)
    · exact False.elim (q5 u6)
    · exact False.elim (q6 u5)
  have u10 : p178 := by
    rcases h890 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  have u11 : p181 := by
    rcases h893 with q0 | q1
    · exact False.elim (u9 q0)
    · exact q1
  rcases h826 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u0)

theorem step22997 (p167 p170 p173 p174 p175 p176 p177 p182 : Prop)
    (h894 : p173 ∨ p182)
    (h899 : p174 ∨ p182)
    (h904 : p175 ∨ p182)
    (h909 : p176 ∨ p182)
    (h914 : p177 ∨ p182)
    (h801 : p167 ∨ p170 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p182 ∨ p170 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p182) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p170) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p167) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p173 := by
    rcases h894 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p174 := by
    rcases h899 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p175 := by
    rcases h904 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p176 := by
    rcases h909 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p177 := by
    rcases h914 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h801 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22998 (p167 p170 p173 p174 p175 p176 p177 p180 : Prop)
    (h892 : p173 ∨ p180)
    (h897 : p174 ∨ p180)
    (h902 : p175 ∨ p180)
    (h907 : p176 ∨ p180)
    (h912 : p177 ∨ p180)
    (h801 : p167 ∨ p170 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p180 ∨ p170 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p180) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p170) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p167) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p173 := by
    rcases h892 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p174 := by
    rcases h897 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p175 := by
    rcases h902 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p176 := by
    rcases h907 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p177 := by
    rcases h912 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h801 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step22999 (p167 p170 p173 p174 p175 p176 p177 p179 p180 p182 : Prop)
    (h22996 : (¬ p182) ∨ (¬ p180) ∨ p167 ∨ (¬ p179) ∨ p170)
    (h891 : p173 ∨ p179)
    (h896 : p174 ∨ p179)
    (h901 : p175 ∨ p179)
    (h906 : p176 ∨ p179)
    (h911 : p177 ∨ p179)
    (h801 : p167 ∨ p170 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : (¬ p180) ∨ p170 ∨ p167 ∨ (¬ p182) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p180 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p170) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p167) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p182 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p179) := by
    rcases h22996 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u0)
    · exact False.elim (u2 q2)
    · exact q3
    · exact False.elim (u1 q4)
  have u5 : p173 := by
    rcases h891 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u6 : p174 := by
    rcases h896 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u7 : p175 := by
    rcases h901 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u8 : p176 := by
    rcases h906 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u9 : p177 := by
    rcases h911 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h801 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u9)

theorem step23000 (p167 p170 p180 p182 : Prop)
    (h22997 : p182 ∨ p170 ∨ p167)
    (h22998 : p180 ∨ p170 ∨ p167)
    (h22999 : (¬ p180) ∨ p170 ∨ p167 ∨ (¬ p182)) : p170 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p170) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p167) := fun hu => hn (Or.inr hu)
  have u2 : p182 := by
    rcases h22997 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p180 := by
    rcases h22998 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h22999 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)

theorem step23001 (p635 p642 p643 p648 p649 p650 p651 p652 : Prop)
    (h3716 : p643 ∨ p648)
    (h3717 : p643 ∨ p649)
    (h3718 : p643 ∨ p650)
    (h3719 : p643 ∨ p651)
    (h3720 : p643 ∨ p652)
    (h3650 : p635 ∨ p642 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p643 ∨ p642 ∨ p635 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p643) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p642) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p635) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p648 := by
    rcases h3716 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p649 := by
    rcases h3717 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p650 := by
    rcases h3718 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p651 := by
    rcases h3719 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p652 := by
    rcases h3720 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3650 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23002 (p635 p642 p647 p648 p649 p650 p651 p652 : Prop)
    (h3736 : p647 ∨ p648)
    (h3737 : p647 ∨ p649)
    (h3738 : p647 ∨ p650)
    (h3739 : p647 ∨ p651)
    (h3740 : p647 ∨ p652)
    (h3650 : p635 ∨ p642 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p647 ∨ p642 ∨ p635 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p647) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p642) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p635) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p648 := by
    rcases h3736 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p649 := by
    rcases h3737 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p650 := by
    rcases h3738 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p651 := by
    rcases h3739 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p652 := by
    rcases h3740 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3650 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23003 (p635 p642 p646 p648 p649 p650 p651 p652 : Prop)
    (h3731 : p646 ∨ p648)
    (h3732 : p646 ∨ p649)
    (h3733 : p646 ∨ p650)
    (h3734 : p646 ∨ p651)
    (h3735 : p646 ∨ p652)
    (h3650 : p635 ∨ p642 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p646 ∨ p642 ∨ p635 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p646) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p642) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p635) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p648 := by
    rcases h3731 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p649 := by
    rcases h3732 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p650 := by
    rcases h3733 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p651 := by
    rcases h3734 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p652 := by
    rcases h3735 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3650 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23004 (p635 p642 p645 p648 p649 p650 p651 p652 : Prop)
    (h3726 : p645 ∨ p648)
    (h3727 : p645 ∨ p649)
    (h3728 : p645 ∨ p650)
    (h3729 : p645 ∨ p651)
    (h3730 : p645 ∨ p652)
    (h3650 : p635 ∨ p642 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : p645 ∨ p642 ∨ p635 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p645) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p642) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p635) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p648 := by
    rcases h3726 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p649 := by
    rcases h3727 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p650 := by
    rcases h3728 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p651 := by
    rcases h3729 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p652 := by
    rcases h3730 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h3650 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23005 (p635 p642 p643 p644 p645 p646 p647 p648 p649 p650 p651 p652 : Prop)
    (h3625 : p635 ∨ p642 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647))
    (h3721 : p644 ∨ p648)
    (h3722 : p644 ∨ p649)
    (h3723 : p644 ∨ p650)
    (h3724 : p644 ∨ p651)
    (h3725 : p644 ∨ p652)
    (h3650 : p635 ∨ p642 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652)) : (¬ p645) ∨ (¬ p643) ∨ p635 ∨ p642 ∨ (¬ p646) ∨ (¬ p647) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p645 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p643 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p635) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p642) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p646 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p647 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p644) := by
    rcases h3625 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p648 := by
    rcases h3721 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p649 := by
    rcases h3722 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p650 := by
    rcases h3723 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p651 := by
    rcases h3724 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p652 := by
    rcases h3725 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h3650 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step23006 (p635 p642 p643 p645 p646 p647 : Prop)
    (h23001 : p643 ∨ p642 ∨ p635)
    (h23002 : p647 ∨ p642 ∨ p635)
    (h23003 : p646 ∨ p642 ∨ p635)
    (h23004 : p645 ∨ p642 ∨ p635)
    (h23005 : (¬ p645) ∨ (¬ p643) ∨ p635 ∨ p642 ∨ (¬ p646) ∨ (¬ p647)) : p642 ∨ p635 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p642) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p635) := fun hu => hn (Or.inr hu)
  have u2 : p643 := by
    rcases h23001 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p647 := by
    rcases h23002 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p646 := by
    rcases h23003 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p645 := by
    rcases h23004 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h23005 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step23007 (p344 p345 p438 p635 p642 p728 p904 : Prop)
    (h21358 : p345 ∨ p344)
    (h11229 : p344 ∨ (¬ p635) ∨ (¬ p904))
    (h17588 : (¬ p345) ∨ (¬ p438) ∨ (¬ p642) ∨ (¬ p728) ∨ (¬ p904))
    (h23006 : p642 ∨ p635) : (¬ p904) ∨ (¬ p438) ∨ (¬ p728) ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p345 := by
    rcases h21358 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : (¬ p635) := by
    rcases h11229 with q0 | q1 | q2
    · exact False.elim (u3 q0)
    · exact q1
    · exact False.elim (q2 u0)
  have u6 : (¬ p642) := by
    rcases h17588 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u4)
    · exact False.elim (q1 u1)
    · exact q2
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u0)
  rcases h23006 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step23008 (p879 p883 p891 p892 p893 p894 p895 p896 : Prop)
    (h5195 : p891 ∨ p892)
    (h5196 : p891 ∨ p893)
    (h5197 : p891 ∨ p894)
    (h5198 : p891 ∨ p895)
    (h5199 : p891 ∨ p896)
    (h5100 : p879 ∨ p883 ∨ (¬ p892) ∨ (¬ p893) ∨ (¬ p894) ∨ (¬ p895) ∨ (¬ p896)) : p891 ∨ p883 ∨ p879 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p891) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p883) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p879) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p892 := by
    rcases h5195 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p893 := by
    rcases h5196 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p894 := by
    rcases h5197 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p895 := by
    rcases h5198 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p896 := by
    rcases h5199 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23009 (p879 p883 p887 p892 p893 p894 p895 p896 : Prop)
    (h5175 : p887 ∨ p892)
    (h5176 : p887 ∨ p893)
    (h5177 : p887 ∨ p894)
    (h5178 : p887 ∨ p895)
    (h5179 : p887 ∨ p896)
    (h5100 : p879 ∨ p883 ∨ (¬ p892) ∨ (¬ p893) ∨ (¬ p894) ∨ (¬ p895) ∨ (¬ p896)) : p887 ∨ p883 ∨ p879 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p887) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p883) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p879) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p892 := by
    rcases h5175 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p893 := by
    rcases h5176 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p894 := by
    rcases h5177 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p895 := by
    rcases h5178 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p896 := by
    rcases h5179 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23010 (p879 p883 p890 p892 p893 p894 p895 p896 : Prop)
    (h5190 : p890 ∨ p892)
    (h5191 : p890 ∨ p893)
    (h5192 : p890 ∨ p894)
    (h5193 : p890 ∨ p895)
    (h5194 : p890 ∨ p896)
    (h5100 : p879 ∨ p883 ∨ (¬ p892) ∨ (¬ p893) ∨ (¬ p894) ∨ (¬ p895) ∨ (¬ p896)) : p890 ∨ p883 ∨ p879 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p890) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p883) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p879) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p892 := by
    rcases h5190 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p893 := by
    rcases h5191 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p894 := by
    rcases h5192 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p895 := by
    rcases h5193 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p896 := by
    rcases h5194 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23011 (p879 p883 p889 p892 p893 p894 p895 p896 : Prop)
    (h5185 : p889 ∨ p892)
    (h5186 : p889 ∨ p893)
    (h5187 : p889 ∨ p894)
    (h5188 : p889 ∨ p895)
    (h5189 : p889 ∨ p896)
    (h5100 : p879 ∨ p883 ∨ (¬ p892) ∨ (¬ p893) ∨ (¬ p894) ∨ (¬ p895) ∨ (¬ p896)) : p889 ∨ p883 ∨ p879 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p889) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p883) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p879) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p892 := by
    rcases h5185 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p893 := by
    rcases h5186 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p894 := by
    rcases h5187 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p895 := by
    rcases h5188 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p896 := by
    rcases h5189 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23012 (p229 p879 p883 p887 p888 p889 p890 p891 p892 p893 p894 p895 p896 : Prop)
    (h23008 : p891 ∨ p883 ∨ p879)
    (h23009 : p887 ∨ p883 ∨ p879)
    (h23010 : p890 ∨ p883 ∨ p879)
    (h23011 : p889 ∨ p883 ∨ p879)
    (h5085 : p229 ∨ p883 ∨ (¬ p887) ∨ (¬ p888) ∨ (¬ p889) ∨ (¬ p890) ∨ (¬ p891))
    (h5180 : p888 ∨ p892)
    (h5181 : p888 ∨ p893)
    (h5182 : p888 ∨ p894)
    (h5183 : p888 ∨ p895)
    (h5184 : p888 ∨ p896)
    (h5100 : p879 ∨ p883 ∨ (¬ p892) ∨ (¬ p893) ∨ (¬ p894) ∨ (¬ p895) ∨ (¬ p896)) : p883 ∨ p879 ∨ p229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p883) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p879) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p229) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p891 := by
    rcases h23008 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p887 := by
    rcases h23009 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p890 := by
    rcases h23010 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p889 := by
    rcases h23011 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p888) := by
    rcases h5085 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u4)
    · exact q3
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u3)
  have u8 : p892 := by
    rcases h5180 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p893 := by
    rcases h5181 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p894 := by
    rcases h5182 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p895 := by
    rcases h5183 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u12 : p896 := by
    rcases h5184 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h5100 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step23014 (p18 p69 p103 p109 p229 p879 p883 p1096 : Prop)
    (h10795 : (¬ p69) ∨ (¬ p879) ∨ (¬ p1096))
    (h23012 : p883 ∨ p879 ∨ p229)
    (h14747 : (¬ p18) ∨ (¬ p103) ∨ p229)
    (h16687 : (¬ p18) ∨ (¬ p69) ∨ (¬ p109) ∨ (¬ p883) ∨ (¬ p1096))
    (h22954 : p109 ∨ p103) : (¬ p18) ∨ p229 ∨ (¬ p69) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p229) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p879) := by
    rcases h10795 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u3)
  have u5 : p883 := by
    rcases h23012 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u4 q1)
    · exact False.elim (u1 q2)
  have u6 : (¬ p103) := by
    rcases h14747 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (u1 q2)
  have u7 : (¬ p109) := by
    rcases h16687 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u2)
    · exact q2
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u3)
  rcases h22954 with q0 | q1
  · exact False.elim (u7 q0)
  · exact False.elim (u6 q1)

theorem step23017 (p15 p43 p49 p63 p84 p85 p256 p419 p616 p1443 p1452 : Prop)
    (h22211 : p85 ∨ p63)
    (h22278 : p84 ∨ (¬ p85))
    (h12953 : (¬ p15) ∨ (¬ p43) ∨ p63)
    (h22980 : (¬ p15) ∨ (¬ p49) ∨ (¬ p616) ∨ (¬ p84) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p256) ∨ (¬ p419))
    (h22271 : p49 ∨ p43) : (¬ p15) ∨ (¬ p616) ∨ p63 ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p256) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p63) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : p85 := by
    rcases h22211 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u8 : p84 := by
    rcases h22278 with q0 | q1
    · exact q0
    · exact False.elim (q1 u7)
  have u9 : (¬ p43) := by
    rcases h12953 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (u2 q2)
  have u10 : (¬ p49) := by
    rcases h22980 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u8)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
    · exact False.elim (q7 u6)
  rcases h22271 with q0 | q1
  · exact False.elim (u10 q0)
  · exact False.elim (u9 q1)

theorem step23018 (p6 p211 p214 p215 p216 p217 p218 p219 p220 p221 p222 p223 : Prop)
    (h1058 : p6 ∨ p211 ∨ (¬ p214) ∨ (¬ p215) ∨ (¬ p216) ∨ (¬ p217) ∨ (¬ p218))
    (h1147 : p214 ∨ p219)
    (h1148 : p214 ∨ p220)
    (h1149 : p214 ∨ p221)
    (h1150 : p214 ∨ p222)
    (h1151 : p214 ∨ p223)
    (h1083 : p6 ∨ p211 ∨ (¬ p219) ∨ (¬ p220) ∨ (¬ p221) ∨ (¬ p222) ∨ (¬ p223)) : p6 ∨ (¬ p216) ∨ p211 ∨ (¬ p217) ∨ (¬ p218) ∨ (¬ p215) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : p216 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p211) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p217 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p218 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p215 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p214) := by
    rcases h1058 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u4)
  have u7 : p219 := by
    rcases h1147 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p220 := by
    rcases h1148 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p221 := by
    rcases h1149 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p222 := by
    rcases h1150 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p223 := by
    rcases h1151 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h1083 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step23019 (p6 p211 p215 p216 p217 p218 : Prop)
    (h22595 : p218 ∨ p211 ∨ p6)
    (h22596 : p217 ∨ p211 ∨ p6)
    (h22597 : p216 ∨ p211 ∨ p6)
    (h22598 : p215 ∨ p211 ∨ p6)
    (h23018 : p6 ∨ (¬ p216) ∨ p211 ∨ (¬ p217) ∨ (¬ p218) ∨ (¬ p215)) : p6 ∨ p211 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p6) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p211) := fun hu => hn (Or.inr hu)
  have u2 : p218 := by
    rcases h22595 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p217 := by
    rcases h22596 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u4 : p216 := by
    rcases h22597 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u5 : p215 := by
    rcases h22598 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  rcases h23018 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)

theorem step23020 (p2 p18 p19 p38 p67 p134 p419 : Prop)
    (h19889 : (¬ p18) ∨ p67)
    (h21299 : p67 ∨ p38)
    (h22840 : p19 ∨ p18)
    (h18923 : (¬ p2) ∨ (¬ p19) ∨ (¬ p38) ∨ (¬ p134) ∨ (¬ p419)) : p67 ∨ (¬ p134) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p18) := by
    rcases h19889 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p38 := by
    rcases h21299 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p19 := by
    rcases h22840 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  rcases h18923 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u6)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)

theorem step23021 (p2 p3 p15 p18 p19 p25 p38 p43 p49 p63 p69 p85 p102 p224 p225 p226 p228 p229 p234 p256 p419 p455 p495 p499 p576 p579 p581 p595 p616 p796 p1188 p1443 p1452 : Prop)
    (h17969 : (¬ p63) ∨ (¬ p581) ∨ (¬ p1443) ∨ (¬ p1452))
    (h22211 : p85 ∨ p63)
    (h12204 : (¬ p576) ∨ (¬ p581))
    (h20860 : p576 ∨ p579)
    (h13230 : p455 ∨ (¬ p579) ∨ (¬ p1443))
    (h16546 : (¬ p85) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1452))
    (h20942 : p495 ∨ p499)
    (h21946 : p69 ∨ p15)
    (h12953 : (¬ p15) ∨ (¬ p43) ∨ p63)
    (h16362 : (¬ p15) ∨ (¬ p85) ∨ (¬ p234) ∨ (¬ p796))
    (h10583 : (¬ p15) ∨ (¬ p25) ∨ p499)
    (h23017 : (¬ p15) ∨ (¬ p616) ∨ p63 ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p256) ∨ (¬ p419))
    (h16327 : (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p102))
    (h22271 : p49 ∨ p43)
    (h22095 : p1188 ∨ p234)
    (h21790 : p616 ∨ p595)
    (h22840 : p19 ∨ p18)
    (h22684 : p38 ∨ (¬ p595) ∨ (¬ p1188) ∨ p69)
    (h22959 : (¬ p18) ∨ p229 ∨ p25 ∨ (¬ p15) ∨ (¬ p495))
    (h16378 : (¬ p38) ∨ (¬ p49) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p228) ∨ (¬ p581) ∨ (¬ p1443))
    (h18531 : (¬ p2) ∨ (¬ p3) ∨ (¬ p229) ∨ (¬ p419))
    (h22929 : p3 ∨ p226) : p69 ∨ (¬ p225) ∨ (¬ p102) ∨ (¬ p224) ∨ (¬ p581) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p796) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p69) := fun hu => hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : (¬ p63) := by
    rcases h17969 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u6)
  have u13 : p85 := by
    rcases h22211 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u14 : (¬ p576) := by
    rcases h12204 with q0 | q1
    · exact q0
    · exact False.elim (q1 u4)
  have u15 : p579 := by
    rcases h20860 with q0 | q1
    · exact False.elim (u14 q0)
    · exact q1
  have u16 : p455 := by
    rcases h13230 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u15)
    · exact False.elim (q2 u5)
  have u17 : (¬ p499) := by
    rcases h16546 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u13)
    · exact False.elim (q1 u16)
    · exact q2
    · exact False.elim (q3 u6)
  have u18 : p495 := by
    rcases h20942 with q0 | q1
    · exact q0
    · exact False.elim (u17 q1)
  have u19 : p15 := by
    rcases h21946 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u20 : (¬ p43) := by
    rcases h12953 with q0 | q1 | q2
    · exact False.elim (q0 u19)
    · exact q1
    · exact False.elim (u12 q2)
  have u21 : (¬ p234) := by
    rcases h16362 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u19)
    · exact False.elim (q1 u13)
    · exact q2
    · exact False.elim (q3 u7)
  have u22 : (¬ p25) := by
    rcases h10583 with q0 | q1 | q2
    · exact False.elim (q0 u19)
    · exact q1
    · exact False.elim (u17 q2)
  have u23 : (¬ p616) := by
    rcases h23017 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u19)
    · exact q1
    · exact False.elim (u12 q2)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u9)
    · exact False.elim (q6 u10)
  have u24 : (¬ p19) := by
    rcases h16327 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u19)
    · exact q1
    · exact False.elim (q2 u13)
    · exact False.elim (q3 u2)
  have u25 : p49 := by
    rcases h22271 with q0 | q1
    · exact q0
    · exact False.elim (u20 q1)
  have u26 : p1188 := by
    rcases h22095 with q0 | q1
    · exact q0
    · exact False.elim (u21 q1)
  have u27 : p595 := by
    rcases h21790 with q0 | q1
    · exact False.elim (u23 q0)
    · exact q1
  have u28 : p18 := by
    rcases h22840 with q0 | q1
    · exact False.elim (u24 q0)
    · exact q1
  have u29 : p38 := by
    rcases h22684 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u27)
    · exact False.elim (q2 u26)
    · exact False.elim (u0 q3)
  have u30 : p229 := by
    rcases h22959 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u28)
    · exact q1
    · exact False.elim (u22 q2)
    · exact False.elim (q3 u19)
    · exact False.elim (q4 u18)
  have u31 : (¬ p226) := by
    rcases h16378 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u29)
    · exact False.elim (q1 u25)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u1)
    · exact q4
    · exact False.elim (q5 u8)
    · exact False.elim (q6 u4)
    · exact False.elim (q7 u5)
  have u32 : (¬ p3) := by
    rcases h18531 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u11)
    · exact q1
    · exact False.elim (q2 u30)
    · exact False.elim (q3 u10)
  rcases h22929 with q0 | q1
  · exact False.elim (u32 q0)
  · exact False.elim (u31 q1)

theorem step23022 (p2 p6 p18 p19 p44 p48 p63 p64 p69 p85 p101 p102 p160 p224 p225 p228 p229 p256 p344 p346 p419 p422 p438 p455 p495 p499 p532 p576 p579 p581 p657 p664 p728 p734 p796 p836 p840 p860 p861 p897 p904 p964 p983 p1096 p1099 p1117 p1121 p1206 p1212 p1226 p1229 p1233 p1325 p1328 p1331 p1333 p1366 p1443 p1452 p1489 : Prop)
    (h17969 : (¬ p63) ∨ (¬ p581) ∨ (¬ p1443) ∨ (¬ p1452))
    (h22211 : p85 ∨ p63)
    (h12204 : (¬ p576) ∨ (¬ p581))
    (h20860 : p576 ∨ p579)
    (h13230 : p455 ∨ (¬ p579) ∨ (¬ p1443))
    (h16546 : (¬ p85) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1452))
    (h20942 : p495 ∨ p499)
    (h22842 : (¬ p1229) ∨ (¬ p495) ∨ (¬ p85) ∨ (¬ p1452) ∨ (¬ p1489))
    (h21346 : p1233 ∨ p1229)
    (h22560 : p346 ∨ p344)
    (h12635 : (¬ p419) ∨ (¬ p1328) ∨ (¬ p1366))
    (h21200 : p1331 ∨ p1328)
    (h17024 : (¬ p419) ∨ (¬ p796) ∨ (¬ p983) ∨ (¬ p1325))
    (h21656 : p1325 ∨ p1333)
    (h10842 : (¬ p861) ∨ (¬ p1333) ∨ (¬ p1489))
    (h21340 : p860 ∨ p861)
    (h9337 : (¬ p983) ∨ (¬ p1121) ∨ (¬ p1489))
    (h21537 : p1121 ∨ p1117)
    (h20814 : p224 ∨ p657)
    (h22831 : p664 ∨ p657)
    (h16465 : (¬ p664) ∨ (¬ p840) ∨ (¬ p983) ∨ (¬ p1117) ∨ (¬ p1489))
    (h21988 : p840 ∨ p836)
    (h16503 : (¬ p419) ∨ (¬ p734) ∨ (¬ p836) ∨ (¬ p1366))
    (h20753 : p728 ∨ p734)
    (h16645 : (¬ p224) ∨ (¬ p228) ∨ (¬ p532) ∨ (¬ p728) ∨ (¬ p1331))
    (h10737 : p532 ∨ (¬ p964) ∨ (¬ p1226))
    (h21183 : p1226 ∨ p160)
    (h16370 : (¬ p6) ∨ (¬ p101) ∨ (¬ p224) ∨ (¬ p346))
    (h21623 : p101 ∨ p102)
    (h16496 : (¬ p102) ∨ (¬ p256) ∨ (¬ p1206) ∨ (¬ p1443))
    (h21957 : p1212 ∨ p1206)
    (h22948 : p225 ∨ (¬ p728) ∨ (¬ p438) ∨ p344)
    (h23007 : (¬ p904) ∨ (¬ p438) ∨ (¬ p728) ∨ p344)
    (h20784 : p897 ∨ p904)
    (h16916 : (¬ p160) ∨ (¬ p224) ∨ (¬ p860) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1233) ∨ (¬ p1489))
    (h21802 : p1096 ∨ p1099)
    (h23021 : p69 ∨ (¬ p225) ∨ (¬ p102) ∨ (¬ p224) ∨ (¬ p581) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p796) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h16287 : (¬ p69) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p229))
    (h23014 : (¬ p18) ∨ p229 ∨ (¬ p69) ∨ (¬ p1096))
    (h22840 : p19 ∨ p18)
    (h22865 : (¬ p1096) ∨ (¬ p6) ∨ (¬ p19) ∨ (¬ p48) ∨ (¬ p64) ∨ (¬ p85))
    (h15341 : (¬ p19) ∨ (¬ p44) ∨ (¬ p422) ∨ (¬ p1212))
    (h21322 : p48 ∨ p44) : p657 ∨ (¬ p438) ∨ (¬ p64) ∨ (¬ p581) ∨ p344 ∨ (¬ p1366) ∨ (¬ p983) ∨ (¬ p964) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ (¬ p422) ∨ (¬ p796) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p657) := fun hu => hn (Or.inl hu)
  have u1 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p964 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))))
  have u18 : (¬ p63) := by
    rcases h17969 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u8)
    · exact False.elim (q3 u9)
  have u19 : p85 := by
    rcases h22211 with q0 | q1
    · exact q0
    · exact False.elim (u18 q1)
  have u20 : (¬ p576) := by
    rcases h12204 with q0 | q1
    · exact q0
    · exact False.elim (q1 u3)
  have u21 : p579 := by
    rcases h20860 with q0 | q1
    · exact False.elim (u20 q0)
    · exact q1
  have u22 : p455 := by
    rcases h13230 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u21)
    · exact False.elim (q2 u8)
  have u23 : (¬ p499) := by
    rcases h16546 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u19)
    · exact False.elim (q1 u22)
    · exact q2
    · exact False.elim (q3 u9)
  have u24 : p495 := by
    rcases h20942 with q0 | q1
    · exact q0
    · exact False.elim (u23 q1)
  have u25 : (¬ p1229) := by
    rcases h22842 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u24)
    · exact False.elim (q2 u19)
    · exact False.elim (q3 u9)
    · exact False.elim (q4 u10)
  have u26 : p1233 := by
    rcases h21346 with q0 | q1
    · exact q0
    · exact False.elim (u25 q1)
  have u27 : p346 := by
    rcases h22560 with q0 | q1
    · exact q0
    · exact False.elim (u4 q1)
  have u28 : (¬ p1328) := by
    rcases h12635 with q0 | q1 | q2
    · exact False.elim (q0 u16)
    · exact q1
    · exact False.elim (q2 u5)
  have u29 : p1331 := by
    rcases h21200 with q0 | q1
    · exact q0
    · exact False.elim (u28 q1)
  have u30 : (¬ p1325) := by
    rcases h17024 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u16)
    · exact False.elim (q1 u13)
    · exact False.elim (q2 u6)
    · exact q3
  have u31 : p1333 := by
    rcases h21656 with q0 | q1
    · exact False.elim (u30 q0)
    · exact q1
  have u32 : (¬ p861) := by
    rcases h10842 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u31)
    · exact False.elim (q2 u10)
  have u33 : p860 := by
    rcases h21340 with q0 | q1
    · exact q0
    · exact False.elim (u32 q1)
  have u34 : (¬ p1121) := by
    rcases h9337 with q0 | q1 | q2
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (q2 u10)
  have u35 : p1117 := by
    rcases h21537 with q0 | q1
    · exact False.elim (u34 q0)
    · exact q1
  have u36 : p224 := by
    rcases h20814 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u37 : p664 := by
    rcases h22831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u38 : (¬ p840) := by
    rcases h16465 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u37)
    · exact q1
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u35)
    · exact False.elim (q4 u10)
  have u39 : p836 := by
    rcases h21988 with q0 | q1
    · exact False.elim (u38 q0)
    · exact q1
  have u40 : (¬ p734) := by
    rcases h16503 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u16)
    · exact q1
    · exact False.elim (q2 u39)
    · exact False.elim (q3 u5)
  have u41 : p728 := by
    rcases h20753 with q0 | q1
    · exact q0
    · exact False.elim (u40 q1)
  have u42 : (¬ p532) := by
    rcases h16645 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u36)
    · exact False.elim (q1 u14)
    · exact q2
    · exact False.elim (q3 u41)
    · exact False.elim (q4 u29)
  have u43 : (¬ p1226) := by
    rcases h10737 with q0 | q1 | q2
    · exact False.elim (u42 q0)
    · exact False.elim (q1 u7)
    · exact q2
  have u44 : p160 := by
    rcases h21183 with q0 | q1
    · exact False.elim (u43 q0)
    · exact q1
  have u45 : (¬ p101) := by
    rcases h16370 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u11)
    · exact q1
    · exact False.elim (q2 u36)
    · exact False.elim (q3 u27)
  have u46 : p102 := by
    rcases h21623 with q0 | q1
    · exact False.elim (u45 q0)
    · exact q1
  have u47 : (¬ p1206) := by
    rcases h16496 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u46)
    · exact False.elim (q1 u15)
    · exact q2
    · exact False.elim (q3 u8)
  have u48 : p1212 := by
    rcases h21957 with q0 | q1
    · exact q0
    · exact False.elim (u47 q1)
  have u49 : p225 := by
    rcases h22948 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u41)
    · exact False.elim (q2 u1)
    · exact False.elim (u4 q3)
  have u50 : (¬ p904) := by
    rcases h23007 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u41)
    · exact False.elim (u4 q3)
  have u51 : p897 := by
    rcases h20784 with q0 | q1
    · exact q0
    · exact False.elim (u50 q1)
  have u52 : (¬ p1099) := by
    rcases h16916 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u44)
    · exact False.elim (q1 u36)
    · exact False.elim (q2 u33)
    · exact False.elim (q3 u51)
    · exact q4
    · exact False.elim (q5 u26)
    · exact False.elim (q6 u10)
  have u53 : p1096 := by
    rcases h21802 with q0 | q1
    · exact q0
    · exact False.elim (u52 q1)
  have u54 : p69 := by
    rcases h23021 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
    · exact q0
    · exact False.elim (q1 u49)
    · exact False.elim (q2 u46)
    · exact False.elim (q3 u36)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u8)
    · exact False.elim (q6 u9)
    · exact False.elim (q7 u13)
    · exact False.elim (q8 u14)
    · exact False.elim (q9 u15)
    · exact False.elim (q10 u16)
    · exact False.elim (q11 u17)
  have u55 : (¬ p229) := by
    rcases h16287 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u54)
    · exact False.elim (q1 u36)
    · exact False.elim (q2 u49)
    · exact q3
  have u56 : (¬ p18) := by
    rcases h23014 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u55 q1)
    · exact False.elim (q2 u54)
    · exact False.elim (q3 u53)
  have u57 : p19 := by
    rcases h22840 with q0 | q1
    · exact q0
    · exact False.elim (u56 q1)
  have u58 : (¬ p48) := by
    rcases h22865 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u53)
    · exact False.elim (q1 u11)
    · exact False.elim (q2 u57)
    · exact q3
    · exact False.elim (q4 u2)
    · exact False.elim (q5 u19)
  have u59 : (¬ p44) := by
    rcases h15341 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u57)
    · exact q1
    · exact False.elim (q2 u12)
    · exact False.elim (q3 u48)
  rcases h21322 with q0 | q1
  · exact False.elim (u58 q0)
  · exact False.elim (u59 q1)

theorem step23023 (p2 p6 p63 p64 p67 p85 p86 p126 p134 p142 p192 p228 p256 p303 p344 p347 p348 p367 p381 p382 p387 p419 p420 p422 p434 p438 p455 p476 p481 p495 p499 p576 p579 p581 p596 p657 p796 p964 p983 p996 p997 p1140 p1159 p1229 p1232 p1287 p1328 p1334 p1366 p1443 p1452 p1489 : Prop)
    (h12635 : (¬ p419) ∨ (¬ p1328) ∨ (¬ p1366))
    (h21365 : p1334 ∨ p1328)
    (h9328 : (¬ p6) ∨ (¬ p142) ∨ (¬ p192))
    (h22176 : p142 ∨ p134)
    (h23020 : p67 ∨ (¬ p134) ∨ (¬ p419) ∨ (¬ p2))
    (h22427 : p1287 ∨ (¬ p419) ∨ (¬ p2) ∨ (¬ p67))
    (h5837 : (¬ p419) ∨ (¬ p996))
    (h21727 : p997 ∨ p996)
    (h13524 : (¬ p2) ∨ (¬ p997) ∨ (¬ p1140))
    (h21650 : p1159 ∨ p1140)
    (h13779 : (¬ p192) ∨ p422 ∨ (¬ p1159))
    (h11962 : (¬ p2) ∨ (¬ p192) ∨ p796)
    (h10692 : (¬ p2) ∨ (¬ p481))
    (h22551 : p476 ∨ p481)
    (h12408 : p382 ∨ (¬ p419) ∨ (¬ p476))
    (h10100 : (¬ p367) ∨ (¬ p382) ∨ (¬ p387))
    (h21214 : p228 ∨ p387)
    (h20914 : p387 ∨ p381)
    (h7324 : p303 ∨ (¬ p367) ∨ (¬ p382))
    (h12204 : (¬ p576) ∨ (¬ p581))
    (h17969 : (¬ p63) ∨ (¬ p581) ∨ (¬ p1443) ∨ (¬ p1452))
    (h20860 : p576 ∨ p579)
    (h21852 : p86 ∨ p63)
    (h22211 : p85 ∨ p63)
    (h9846 : (¬ p126) ∨ (¬ p420) ∨ (¬ p579))
    (h13230 : p455 ∨ (¬ p579) ∨ (¬ p1443))
    (h22572 : p596 ∨ p420)
    (h16546 : (¬ p85) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1452))
    (h20942 : p495 ∨ p499)
    (h22842 : (¬ p1229) ∨ (¬ p495) ∨ (¬ p85) ∨ (¬ p1452) ∨ (¬ p1489))
    (h22374 : p1229 ∨ p1232)
    (h22979 : p64 ∨ (¬ p581) ∨ p344 ∨ (¬ p1366) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p192) ∨ (¬ p367) ∨ (¬ p256) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p2))
    (h22844 : (¬ p434) ∨ (¬ p1287) ∨ (¬ p1232) ∨ (¬ p596) ∨ (¬ p86) ∨ (¬ p1334) ∨ (¬ p256) ∨ (¬ p126))
    (h21060 : p438 ∨ p434)
    (h23022 : p657 ∨ (¬ p438) ∨ (¬ p64) ∨ (¬ p581) ∨ p344 ∨ (¬ p1366) ∨ (¬ p983) ∨ (¬ p964) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ (¬ p422) ∨ (¬ p796) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h11604 : (¬ p303) ∨ (¬ p348) ∨ (¬ p657))
    (h18862 : (¬ p2) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p256) ∨ (¬ p347) ∨ (¬ p381) ∨ (¬ p419) ∨ (¬ p657) ∨ (¬ p1443))
    (h21054 : p347 ∨ p348 ∨ p344) : (¬ p581) ∨ p344 ∨ (¬ p1366) ∨ (¬ p983) ∨ (¬ p964) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ (¬ p192) ∨ (¬ p367) ∨ (¬ p256) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p344) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p964 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p367 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))
  have u15 : (¬ p1328) := by
    rcases h12635 with q0 | q1 | q2
    · exact False.elim (q0 u13)
    · exact q1
    · exact False.elim (q2 u2)
  have u16 : p1334 := by
    rcases h21365 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  have u17 : (¬ p142) := by
    rcases h9328 with q0 | q1 | q2
    · exact False.elim (q0 u8)
    · exact q1
    · exact False.elim (q2 u9)
  have u18 : p134 := by
    rcases h22176 with q0 | q1
    · exact False.elim (u17 q0)
    · exact q1
  have u19 : p67 := by
    rcases h23020 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u18)
    · exact False.elim (q2 u13)
    · exact False.elim (q3 u14)
  have u20 : p1287 := by
    rcases h22427 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u13)
    · exact False.elim (q2 u14)
    · exact False.elim (q3 u19)
  have u21 : (¬ p996) := by
    rcases h5837 with q0 | q1
    · exact False.elim (q0 u13)
    · exact q1
  have u22 : p997 := by
    rcases h21727 with q0 | q1
    · exact q0
    · exact False.elim (u21 q1)
  have u23 : (¬ p1140) := by
    rcases h13524 with q0 | q1 | q2
    · exact False.elim (q0 u14)
    · exact False.elim (q1 u22)
    · exact q2
  have u24 : p1159 := by
    rcases h21650 with q0 | q1
    · exact q0
    · exact False.elim (u23 q1)
  have u25 : p422 := by
    rcases h13779 with q0 | q1 | q2
    · exact False.elim (q0 u9)
    · exact q1
    · exact False.elim (q2 u24)
  have u26 : p796 := by
    rcases h11962 with q0 | q1 | q2
    · exact False.elim (q0 u14)
    · exact False.elim (q1 u9)
    · exact q2
  have u27 : (¬ p481) := by
    rcases h10692 with q0 | q1
    · exact False.elim (q0 u14)
    · exact q1
  have u28 : p476 := by
    rcases h22551 with q0 | q1
    · exact q0
    · exact False.elim (u27 q1)
  have u29 : p382 := by
    rcases h12408 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u13)
    · exact False.elim (q2 u28)
  have u30 : (¬ p387) := by
    rcases h10100 with q0 | q1 | q2
    · exact False.elim (q0 u10)
    · exact False.elim (q1 u29)
    · exact q2
  have u31 : p228 := by
    rcases h21214 with q0 | q1
    · exact q0
    · exact False.elim (u30 q1)
  have u32 : p381 := by
    rcases h20914 with q0 | q1
    · exact False.elim (u30 q0)
    · exact q1
  have u33 : p303 := by
    rcases h7324 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u10)
    · exact False.elim (q2 u29)
  have u34 : (¬ p576) := by
    rcases h12204 with q0 | q1
    · exact q0
    · exact False.elim (q1 u0)
  have u35 : (¬ p63) := by
    rcases h17969 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u6)
  have u36 : p579 := by
    rcases h20860 with q0 | q1
    · exact False.elim (u34 q0)
    · exact q1
  have u37 : p86 := by
    rcases h21852 with q0 | q1
    · exact q0
    · exact False.elim (u35 q1)
  have u38 : p85 := by
    rcases h22211 with q0 | q1
    · exact q0
    · exact False.elim (u35 q1)
  have u39 : (¬ p420) := by
    rcases h9846 with q0 | q1 | q2
    · exact False.elim (q0 u12)
    · exact q1
    · exact False.elim (q2 u36)
  have u40 : p455 := by
    rcases h13230 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u36)
    · exact False.elim (q2 u5)
  have u41 : p596 := by
    rcases h22572 with q0 | q1
    · exact q0
    · exact False.elim (u39 q1)
  have u42 : (¬ p499) := by
    rcases h16546 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u38)
    · exact False.elim (q1 u40)
    · exact q2
    · exact False.elim (q3 u6)
  have u43 : p495 := by
    rcases h20942 with q0 | q1
    · exact q0
    · exact False.elim (u42 q1)
  have u44 : (¬ p1229) := by
    rcases h22842 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u43)
    · exact False.elim (q2 u38)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u7)
  have u45 : p1232 := by
    rcases h22374 with q0 | q1
    · exact False.elim (u44 q0)
    · exact q1
  have u46 : p64 := by
    rcases h22979 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact False.elim (q6 u9)
    · exact False.elim (q7 u10)
    · exact False.elim (q8 u11)
    · exact False.elim (q9 u12)
    · exact False.elim (q10 u13)
    · exact False.elim (q11 u14)
  have u47 : (¬ p434) := by
    rcases h22844 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact q0
    · exact False.elim (q1 u20)
    · exact False.elim (q2 u45)
    · exact False.elim (q3 u41)
    · exact False.elim (q4 u37)
    · exact False.elim (q5 u16)
    · exact False.elim (q6 u11)
    · exact False.elim (q7 u12)
  have u48 : p438 := by
    rcases h21060 with q0 | q1
    · exact q0
    · exact False.elim (u47 q1)
  have u49 : p657 := by
    rcases h23022 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17
    · exact q0
    · exact False.elim (q1 u48)
    · exact False.elim (q2 u46)
    · exact False.elim (q3 u0)
    · exact False.elim (u1 q4)
    · exact False.elim (q5 u2)
    · exact False.elim (q6 u3)
    · exact False.elim (q7 u4)
    · exact False.elim (q8 u5)
    · exact False.elim (q9 u6)
    · exact False.elim (q10 u7)
    · exact False.elim (q11 u8)
    · exact False.elim (q12 u25)
    · exact False.elim (q13 u26)
    · exact False.elim (q14 u31)
    · exact False.elim (q15 u11)
    · exact False.elim (q16 u13)
    · exact False.elim (q17 u14)
  have u50 : (¬ p348) := by
    rcases h11604 with q0 | q1 | q2
    · exact False.elim (q0 u33)
    · exact q1
    · exact False.elim (q2 u49)
  have u51 : (¬ p347) := by
    rcases h18862 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact False.elim (q0 u14)
    · exact False.elim (q1 u46)
    · exact False.elim (q2 u37)
    · exact False.elim (q3 u11)
    · exact q4
    · exact False.elim (q5 u32)
    · exact False.elim (q6 u13)
    · exact False.elim (q7 u49)
    · exact False.elim (q8 u5)
  rcases h21054 with q0 | q1 | q2
  · exact False.elim (u51 q0)
  · exact False.elim (u50 q1)
  · exact False.elim (u1 q2)

theorem step23024 (p2 p5 p6 p64 p84 p89 p124 p125 p126 p160 p188 p192 p194 p228 p256 p258 p265 p266 p286 p288 p344 p367 p382 p387 p419 p435 p476 p481 p532 p581 p796 p961 p964 p983 p1226 p1325 p1335 p1349 p1353 p1366 p1443 p1452 p1489 p1492 p1495 p1496 p1502 p1503 p1504 p1505 p1506 p1507 p1508 : Prop)
    (h21387 : p188 ∨ p192)
    (h11962 : (¬ p2) ∨ (¬ p192) ∨ p796)
    (h22615 : p194 ∨ p188)
    (h10692 : (¬ p2) ∨ (¬ p481))
    (h22551 : p476 ∨ p481)
    (h12408 : p382 ∨ (¬ p419) ∨ (¬ p476))
    (h13074 : (¬ p125) ∨ (¬ p126) ∨ (¬ p265))
    (h21948 : p367 ∨ p125)
    (h10100 : (¬ p367) ∨ (¬ p382) ∨ (¬ p387))
    (h21214 : p228 ∨ p387)
    (h9173 : p1502 ∨ p1503)
    (h9174 : p1502 ∨ p1504)
    (h9175 : p1502 ∨ p1505)
    (h9176 : p1502 ∨ p1506)
    (h9177 : p1502 ∨ p1507)
    (h22701 : p1502 ∨ p1492 ∨ p1495)
    (h9080 : p1443 ∨ p1492 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507))
    (h9079 : p1492 ∨ p1496 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507))
    (h13190 : (¬ p1452) ∨ (¬ p1495) ∨ p1508)
    (h12820 : (¬ p265) ∨ (¬ p961) ∨ (¬ p1443))
    (h19744 : (¬ p2) ∨ (¬ p124) ∨ (¬ p194) ∨ (¬ p228) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p419) ∨ (¬ p1443))
    (h13598 : (¬ p256) ∨ (¬ p1349) ∨ (¬ p1496))
    (h21239 : p964 ∨ p961)
    (h21140 : p286 ∨ p258)
    (h21668 : p258 ∨ p288)
    (h21157 : p1353 ∨ p1349)
    (h22829 : p983 ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h17024 : (¬ p419) ∨ (¬ p796) ∨ (¬ p983) ∨ (¬ p1325))
    (h21904 : p1335 ∨ p1325)
    (h17511 : (¬ p2) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p1443) ∨ (¬ p1452))
    (h21910 : p1366 ∨ p435)
    (h22912 : (¬ p344) ∨ (¬ p983) ∨ (¬ p288) ∨ (¬ p286) ∨ (¬ p1489) ∨ (¬ p256))
    (h23023 : (¬ p581) ∨ p344 ∨ (¬ p1366) ∨ (¬ p983) ∨ (¬ p964) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ (¬ p192) ∨ (¬ p367) ∨ (¬ p256) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p2))
    (h11129 : (¬ p84) ∨ (¬ p256) ∨ p581)
    (h22909 : p581 ∨ (¬ p160) ∨ (¬ p1353) ∨ (¬ p1495) ∨ (¬ p1489) ∨ p188 ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h22277 : p89 ∨ p84)
    (h21183 : p1226 ∨ p160)
    (h11182 : (¬ p64) ∨ (¬ p89) ∨ p188)
    (h10737 : p532 ∨ (¬ p964) ∨ (¬ p1226))
    (h22908 : p5 ∨ p64)
    (h17166 : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p532) ∨ (¬ p1496) ∨ (¬ p1508)) : p1502 ∨ p1492 ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ p188 ∨ (¬ p256) ∨ (¬ p265) ∨ (¬ p266) ∨ (¬ p126) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1502) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1492) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p188) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))
  have u13 : p192 := by
    rcases h21387 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u14 : p796 := by
    rcases h11962 with q0 | q1 | q2
    · exact False.elim (q0 u12)
    · exact False.elim (q1 u13)
    · exact q2
  have u15 : p194 := by
    rcases h22615 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u16 : (¬ p481) := by
    rcases h10692 with q0 | q1
    · exact False.elim (q0 u12)
    · exact q1
  have u17 : p476 := by
    rcases h22551 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u18 : p382 := by
    rcases h12408 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u11)
    · exact False.elim (q2 u17)
  have u19 : (¬ p125) := by
    rcases h13074 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u9)
    · exact False.elim (q2 u7)
  have u20 : p367 := by
    rcases h21948 with q0 | q1
    · exact q0
    · exact False.elim (u19 q1)
  have u21 : (¬ p387) := by
    rcases h10100 with q0 | q1 | q2
    · exact False.elim (q0 u20)
    · exact False.elim (q1 u18)
    · exact q2
  have u22 : p228 := by
    rcases h21214 with q0 | q1
    · exact q0
    · exact False.elim (u21 q1)
  have u23 : p1503 := by
    rcases h9173 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u24 : p1504 := by
    rcases h9174 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u25 : p1505 := by
    rcases h9175 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u26 : p1506 := by
    rcases h9176 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u27 : p1507 := by
    rcases h9177 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u28 : p1495 := by
    rcases h22701 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact q2
  have u29 : p1443 := by
    rcases h9080 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u23)
    · exact False.elim (q3 u24)
    · exact False.elim (q4 u25)
    · exact False.elim (q5 u26)
    · exact False.elim (q6 u27)
  have u30 : p1496 := by
    rcases h9079 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact q1
    · exact False.elim (q2 u23)
    · exact False.elim (q3 u24)
    · exact False.elim (q4 u25)
    · exact False.elim (q5 u26)
    · exact False.elim (q6 u27)
  have u31 : p1508 := by
    rcases h13190 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u28)
    · exact q2
  have u32 : (¬ p961) := by
    rcases h12820 with q0 | q1 | q2
    · exact False.elim (q0 u7)
    · exact q1
    · exact False.elim (q2 u29)
  have u33 : (¬ p258) := by
    rcases h19744 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u12)
    · exact False.elim (q1 u10)
    · exact False.elim (q2 u15)
    · exact False.elim (q3 u22)
    · exact q4
    · exact False.elim (q5 u8)
    · exact False.elim (q6 u11)
    · exact False.elim (q7 u29)
  have u34 : (¬ p1349) := by
    rcases h13598 with q0 | q1 | q2
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (q2 u30)
  have u35 : p964 := by
    rcases h21239 with q0 | q1
    · exact q0
    · exact False.elim (u32 q1)
  have u36 : p286 := by
    rcases h21140 with q0 | q1
    · exact q0
    · exact False.elim (u33 q1)
  have u37 : p288 := by
    rcases h21668 with q0 | q1
    · exact False.elim (u33 q0)
    · exact q1
  have u38 : p1353 := by
    rcases h21157 with q0 | q1
    · exact q0
    · exact False.elim (u34 q1)
  have u39 : p983 := by
    rcases h22829 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (q1 u29)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u15)
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u11)
    · exact False.elim (q6 u12)
  have u40 : (¬ p1325) := by
    rcases h17024 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u14)
    · exact False.elim (q2 u39)
    · exact q3
  have u41 : p1335 := by
    rcases h21904 with q0 | q1
    · exact q0
    · exact False.elim (u40 q1)
  have u42 : (¬ p435) := by
    rcases h17511 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u12)
    · exact False.elim (q1 u15)
    · exact False.elim (q2 u6)
    · exact q3
    · exact False.elim (q4 u41)
    · exact False.elim (q5 u29)
    · exact False.elim (q6 u2)
  have u43 : p1366 := by
    rcases h21910 with q0 | q1
    · exact q0
    · exact False.elim (u42 q1)
  have u44 : (¬ p344) := by
    rcases h22912 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u39)
    · exact False.elim (q2 u37)
    · exact False.elim (q3 u36)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u6)
  have u45 : (¬ p581) := by
    rcases h23023 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14
    · exact q0
    · exact False.elim (u44 q1)
    · exact False.elim (q2 u43)
    · exact False.elim (q3 u39)
    · exact False.elim (q4 u35)
    · exact False.elim (q5 u29)
    · exact False.elim (q6 u2)
    · exact False.elim (q7 u3)
    · exact False.elim (q8 u4)
    · exact False.elim (q9 u13)
    · exact False.elim (q10 u20)
    · exact False.elim (q11 u6)
    · exact False.elim (q12 u9)
    · exact False.elim (q13 u11)
    · exact False.elim (q14 u12)
  have u46 : (¬ p84) := by
    rcases h11129 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u6)
    · exact False.elim (u45 q2)
  have u47 : (¬ p160) := by
    rcases h22909 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
    · exact False.elim (u45 q0)
    · exact q1
    · exact False.elim (q2 u38)
    · exact False.elim (q3 u28)
    · exact False.elim (q4 u3)
    · exact False.elim (u5 q5)
    · exact False.elim (q6 u22)
    · exact False.elim (q7 u6)
    · exact False.elim (q8 u11)
    · exact False.elim (q9 u12)
  have u48 : p89 := by
    rcases h22277 with q0 | q1
    · exact q0
    · exact False.elim (u46 q1)
  have u49 : p1226 := by
    rcases h21183 with q0 | q1
    · exact q0
    · exact False.elim (u47 q1)
  have u50 : (¬ p64) := by
    rcases h11182 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u48)
    · exact False.elim (u5 q2)
  have u51 : p532 := by
    rcases h10737 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u35)
    · exact False.elim (q2 u49)
  have u52 : p5 := by
    rcases h22908 with q0 | q1
    · exact q0
    · exact False.elim (u50 q1)
  rcases h17166 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u12)
  · exact False.elim (q1 u52)
  · exact False.elim (q2 u48)
  · exact False.elim (q3 u22)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u51)
  · exact False.elim (q7 u30)
  · exact False.elim (q8 u31)

theorem step23025 (p2 p5 p6 p64 p84 p89 p124 p125 p126 p160 p188 p192 p194 p228 p256 p258 p265 p266 p286 p288 p344 p367 p382 p387 p419 p435 p476 p481 p532 p581 p796 p961 p964 p983 p1226 p1325 p1335 p1349 p1353 p1366 p1443 p1452 p1489 p1492 p1495 p1496 p1498 p1499 p1500 p1501 p1502 p1508 : Prop)
    (h23024 : p1502 ∨ p1492 ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ p188 ∨ (¬ p256) ∨ (¬ p265) ∨ (¬ p266) ∨ (¬ p126) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2))
    (h21387 : p188 ∨ p192)
    (h11962 : (¬ p2) ∨ (¬ p192) ∨ p796)
    (h22615 : p194 ∨ p188)
    (h10692 : (¬ p2) ∨ (¬ p481))
    (h22551 : p476 ∨ p481)
    (h12408 : p382 ∨ (¬ p419) ∨ (¬ p476))
    (h13074 : (¬ p125) ∨ (¬ p126) ∨ (¬ p265))
    (h21948 : p367 ∨ p125)
    (h10100 : (¬ p367) ∨ (¬ p382) ∨ (¬ p387))
    (h21214 : p228 ∨ p387)
    (h9054 : p1492 ∨ p1496 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502))
    (h9055 : p1443 ∨ p1492 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502))
    (h9053 : p1492 ∨ p1495 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502))
    (h13598 : (¬ p256) ∨ (¬ p1349) ∨ (¬ p1496))
    (h12820 : (¬ p265) ∨ (¬ p961) ∨ (¬ p1443))
    (h19744 : (¬ p2) ∨ (¬ p124) ∨ (¬ p194) ∨ (¬ p228) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p419) ∨ (¬ p1443))
    (h22829 : p983 ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h13190 : (¬ p1452) ∨ (¬ p1495) ∨ p1508)
    (h21157 : p1353 ∨ p1349)
    (h21239 : p964 ∨ p961)
    (h21140 : p286 ∨ p258)
    (h21668 : p258 ∨ p288)
    (h17024 : (¬ p419) ∨ (¬ p796) ∨ (¬ p983) ∨ (¬ p1325))
    (h22912 : (¬ p344) ∨ (¬ p983) ∨ (¬ p288) ∨ (¬ p286) ∨ (¬ p1489) ∨ (¬ p256))
    (h21904 : p1335 ∨ p1325)
    (h17511 : (¬ p2) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p1443) ∨ (¬ p1452))
    (h21910 : p1366 ∨ p435)
    (h23023 : (¬ p581) ∨ p344 ∨ (¬ p1366) ∨ (¬ p983) ∨ (¬ p964) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ (¬ p192) ∨ (¬ p367) ∨ (¬ p256) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p2))
    (h11129 : (¬ p84) ∨ (¬ p256) ∨ p581)
    (h22909 : p581 ∨ (¬ p160) ∨ (¬ p1353) ∨ (¬ p1495) ∨ (¬ p1489) ∨ p188 ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h22277 : p89 ∨ p84)
    (h21183 : p1226 ∨ p160)
    (h11182 : (¬ p64) ∨ (¬ p89) ∨ p188)
    (h10737 : p532 ∨ (¬ p964) ∨ (¬ p1226))
    (h22908 : p5 ∨ p64)
    (h17166 : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p532) ∨ (¬ p1496) ∨ (¬ p1508)) : (¬ p1501) ∨ (¬ p1500) ∨ (¬ p1499) ∨ (¬ p1498) ∨ p1492 ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ p188 ∨ (¬ p256) ∨ (¬ p265) ∨ (¬ p266) ∨ (¬ p126) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1501 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1492) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : (¬ p188) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))
  have u16 : p1502 := by
    rcases h23024 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
    · exact q0
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u7)
    · exact False.elim (u8 q5)
    · exact False.elim (q6 u9)
    · exact False.elim (q7 u10)
    · exact False.elim (q8 u11)
    · exact False.elim (q9 u12)
    · exact False.elim (q10 u13)
    · exact False.elim (q11 u14)
    · exact False.elim (q12 u15)
  have u17 : p192 := by
    rcases h21387 with q0 | q1
    · exact False.elim (u8 q0)
    · exact q1
  have u18 : p796 := by
    rcases h11962 with q0 | q1 | q2
    · exact False.elim (q0 u15)
    · exact False.elim (q1 u17)
    · exact q2
  have u19 : p194 := by
    rcases h22615 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u20 : (¬ p481) := by
    rcases h10692 with q0 | q1
    · exact False.elim (q0 u15)
    · exact q1
  have u21 : p476 := by
    rcases h22551 with q0 | q1
    · exact q0
    · exact False.elim (u20 q1)
  have u22 : p382 := by
    rcases h12408 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u14)
    · exact False.elim (q2 u21)
  have u23 : (¬ p125) := by
    rcases h13074 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u12)
    · exact False.elim (q2 u10)
  have u24 : p367 := by
    rcases h21948 with q0 | q1
    · exact q0
    · exact False.elim (u23 q1)
  have u25 : (¬ p387) := by
    rcases h10100 with q0 | q1 | q2
    · exact False.elim (q0 u24)
    · exact False.elim (q1 u22)
    · exact q2
  have u26 : p228 := by
    rcases h21214 with q0 | q1
    · exact q0
    · exact False.elim (u25 q1)
  have u27 : p1496 := by
    rcases h9054 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact q1
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u16)
  have u28 : p1443 := by
    rcases h9055 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u16)
  have u29 : p1495 := by
    rcases h9053 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact q1
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u16)
  have u30 : (¬ p1349) := by
    rcases h13598 with q0 | q1 | q2
    · exact False.elim (q0 u9)
    · exact q1
    · exact False.elim (q2 u27)
  have u31 : (¬ p961) := by
    rcases h12820 with q0 | q1 | q2
    · exact False.elim (q0 u10)
    · exact q1
    · exact False.elim (q2 u28)
  have u32 : (¬ p258) := by
    rcases h19744 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u15)
    · exact False.elim (q1 u13)
    · exact False.elim (q2 u19)
    · exact False.elim (q3 u26)
    · exact q4
    · exact False.elim (q5 u11)
    · exact False.elim (q6 u14)
    · exact False.elim (q7 u28)
  have u33 : p983 := by
    rcases h22829 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (q1 u28)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u19)
    · exact False.elim (q4 u9)
    · exact False.elim (q5 u14)
    · exact False.elim (q6 u15)
  have u34 : p1508 := by
    rcases h13190 with q0 | q1 | q2
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u29)
    · exact q2
  have u35 : p1353 := by
    rcases h21157 with q0 | q1
    · exact q0
    · exact False.elim (u30 q1)
  have u36 : p964 := by
    rcases h21239 with q0 | q1
    · exact q0
    · exact False.elim (u31 q1)
  have u37 : p286 := by
    rcases h21140 with q0 | q1
    · exact q0
    · exact False.elim (u32 q1)
  have u38 : p288 := by
    rcases h21668 with q0 | q1
    · exact False.elim (u32 q0)
    · exact q1
  have u39 : (¬ p1325) := by
    rcases h17024 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u14)
    · exact False.elim (q1 u18)
    · exact False.elim (q2 u33)
    · exact q3
  have u40 : (¬ p344) := by
    rcases h22912 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u33)
    · exact False.elim (q2 u38)
    · exact False.elim (q3 u37)
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u9)
  have u41 : p1335 := by
    rcases h21904 with q0 | q1
    · exact q0
    · exact False.elim (u39 q1)
  have u42 : (¬ p435) := by
    rcases h17511 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u15)
    · exact False.elim (q1 u19)
    · exact False.elim (q2 u9)
    · exact q3
    · exact False.elim (q4 u41)
    · exact False.elim (q5 u28)
    · exact False.elim (q6 u5)
  have u43 : p1366 := by
    rcases h21910 with q0 | q1
    · exact q0
    · exact False.elim (u42 q1)
  have u44 : (¬ p581) := by
    rcases h23023 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14
    · exact q0
    · exact False.elim (u40 q1)
    · exact False.elim (q2 u43)
    · exact False.elim (q3 u33)
    · exact False.elim (q4 u36)
    · exact False.elim (q5 u28)
    · exact False.elim (q6 u5)
    · exact False.elim (q7 u6)
    · exact False.elim (q8 u7)
    · exact False.elim (q9 u17)
    · exact False.elim (q10 u24)
    · exact False.elim (q11 u9)
    · exact False.elim (q12 u12)
    · exact False.elim (q13 u14)
    · exact False.elim (q14 u15)
  have u45 : (¬ p84) := by
    rcases h11129 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u9)
    · exact False.elim (u44 q2)
  have u46 : (¬ p160) := by
    rcases h22909 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
    · exact False.elim (u44 q0)
    · exact q1
    · exact False.elim (q2 u35)
    · exact False.elim (q3 u29)
    · exact False.elim (q4 u6)
    · exact False.elim (u8 q5)
    · exact False.elim (q6 u26)
    · exact False.elim (q7 u9)
    · exact False.elim (q8 u14)
    · exact False.elim (q9 u15)
  have u47 : p89 := by
    rcases h22277 with q0 | q1
    · exact q0
    · exact False.elim (u45 q1)
  have u48 : p1226 := by
    rcases h21183 with q0 | q1
    · exact q0
    · exact False.elim (u46 q1)
  have u49 : (¬ p64) := by
    rcases h11182 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u47)
    · exact False.elim (u8 q2)
  have u50 : p532 := by
    rcases h10737 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u36)
    · exact False.elim (q2 u48)
  have u51 : p5 := by
    rcases h22908 with q0 | q1
    · exact q0
    · exact False.elim (u49 q1)
  rcases h17166 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u15)
  · exact False.elim (q1 u51)
  · exact False.elim (q2 u47)
  · exact False.elim (q3 u26)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u14)
  · exact False.elim (q6 u50)
  · exact False.elim (q7 u27)
  · exact False.elim (q8 u34)

theorem step23026 (p2 p5 p6 p64 p84 p89 p124 p125 p126 p160 p188 p192 p194 p228 p256 p258 p265 p266 p286 p288 p344 p367 p382 p387 p419 p435 p476 p481 p532 p581 p796 p961 p964 p983 p1226 p1325 p1335 p1349 p1353 p1366 p1443 p1452 p1489 p1492 p1495 p1496 p1501 p1503 p1504 p1505 p1506 p1507 p1508 : Prop)
    (h21387 : p188 ∨ p192)
    (h11962 : (¬ p2) ∨ (¬ p192) ∨ p796)
    (h22615 : p194 ∨ p188)
    (h10692 : (¬ p2) ∨ (¬ p481))
    (h22551 : p476 ∨ p481)
    (h12408 : p382 ∨ (¬ p419) ∨ (¬ p476))
    (h13074 : (¬ p125) ∨ (¬ p126) ∨ (¬ p265))
    (h21948 : p367 ∨ p125)
    (h10100 : (¬ p367) ∨ (¬ p382) ∨ (¬ p387))
    (h21214 : p228 ∨ p387)
    (h9168 : p1501 ∨ p1503)
    (h9169 : p1501 ∨ p1504)
    (h9170 : p1501 ∨ p1505)
    (h9171 : p1501 ∨ p1506)
    (h9172 : p1501 ∨ p1507)
    (h22702 : p1501 ∨ p1492 ∨ p1495)
    (h9080 : p1443 ∨ p1492 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507))
    (h9079 : p1492 ∨ p1496 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507))
    (h13190 : (¬ p1452) ∨ (¬ p1495) ∨ p1508)
    (h12820 : (¬ p265) ∨ (¬ p961) ∨ (¬ p1443))
    (h19744 : (¬ p2) ∨ (¬ p124) ∨ (¬ p194) ∨ (¬ p228) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p419) ∨ (¬ p1443))
    (h22829 : p983 ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h13598 : (¬ p256) ∨ (¬ p1349) ∨ (¬ p1496))
    (h21239 : p964 ∨ p961)
    (h21140 : p286 ∨ p258)
    (h21668 : p258 ∨ p288)
    (h17024 : (¬ p419) ∨ (¬ p796) ∨ (¬ p983) ∨ (¬ p1325))
    (h22912 : (¬ p344) ∨ (¬ p983) ∨ (¬ p288) ∨ (¬ p286) ∨ (¬ p1489) ∨ (¬ p256))
    (h21157 : p1353 ∨ p1349)
    (h21904 : p1335 ∨ p1325)
    (h17511 : (¬ p2) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p1443) ∨ (¬ p1452))
    (h21910 : p1366 ∨ p435)
    (h23023 : (¬ p581) ∨ p344 ∨ (¬ p1366) ∨ (¬ p983) ∨ (¬ p964) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ (¬ p192) ∨ (¬ p367) ∨ (¬ p256) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p2))
    (h11129 : (¬ p84) ∨ (¬ p256) ∨ p581)
    (h22909 : p581 ∨ (¬ p160) ∨ (¬ p1353) ∨ (¬ p1495) ∨ (¬ p1489) ∨ p188 ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h22277 : p89 ∨ p84)
    (h21183 : p1226 ∨ p160)
    (h11182 : (¬ p64) ∨ (¬ p89) ∨ p188)
    (h10737 : p532 ∨ (¬ p964) ∨ (¬ p1226))
    (h22908 : p5 ∨ p64)
    (h17166 : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p532) ∨ (¬ p1496) ∨ (¬ p1508)) : p1501 ∨ p1492 ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ p188 ∨ (¬ p256) ∨ (¬ p265) ∨ (¬ p266) ∨ (¬ p126) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1501) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1492) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p188) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))
  have u13 : p192 := by
    rcases h21387 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u14 : p796 := by
    rcases h11962 with q0 | q1 | q2
    · exact False.elim (q0 u12)
    · exact False.elim (q1 u13)
    · exact q2
  have u15 : p194 := by
    rcases h22615 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u16 : (¬ p481) := by
    rcases h10692 with q0 | q1
    · exact False.elim (q0 u12)
    · exact q1
  have u17 : p476 := by
    rcases h22551 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u18 : p382 := by
    rcases h12408 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u11)
    · exact False.elim (q2 u17)
  have u19 : (¬ p125) := by
    rcases h13074 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u9)
    · exact False.elim (q2 u7)
  have u20 : p367 := by
    rcases h21948 with q0 | q1
    · exact q0
    · exact False.elim (u19 q1)
  have u21 : (¬ p387) := by
    rcases h10100 with q0 | q1 | q2
    · exact False.elim (q0 u20)
    · exact False.elim (q1 u18)
    · exact q2
  have u22 : p228 := by
    rcases h21214 with q0 | q1
    · exact q0
    · exact False.elim (u21 q1)
  have u23 : p1503 := by
    rcases h9168 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u24 : p1504 := by
    rcases h9169 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u25 : p1505 := by
    rcases h9170 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u26 : p1506 := by
    rcases h9171 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u27 : p1507 := by
    rcases h9172 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u28 : p1495 := by
    rcases h22702 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact q2
  have u29 : p1443 := by
    rcases h9080 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u23)
    · exact False.elim (q3 u24)
    · exact False.elim (q4 u25)
    · exact False.elim (q5 u26)
    · exact False.elim (q6 u27)
  have u30 : p1496 := by
    rcases h9079 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact q1
    · exact False.elim (q2 u23)
    · exact False.elim (q3 u24)
    · exact False.elim (q4 u25)
    · exact False.elim (q5 u26)
    · exact False.elim (q6 u27)
  have u31 : p1508 := by
    rcases h13190 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u28)
    · exact q2
  have u32 : (¬ p961) := by
    rcases h12820 with q0 | q1 | q2
    · exact False.elim (q0 u7)
    · exact q1
    · exact False.elim (q2 u29)
  have u33 : (¬ p258) := by
    rcases h19744 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u12)
    · exact False.elim (q1 u10)
    · exact False.elim (q2 u15)
    · exact False.elim (q3 u22)
    · exact q4
    · exact False.elim (q5 u8)
    · exact False.elim (q6 u11)
    · exact False.elim (q7 u29)
  have u34 : p983 := by
    rcases h22829 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (q1 u29)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u15)
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u11)
    · exact False.elim (q6 u12)
  have u35 : (¬ p1349) := by
    rcases h13598 with q0 | q1 | q2
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (q2 u30)
  have u36 : p964 := by
    rcases h21239 with q0 | q1
    · exact q0
    · exact False.elim (u32 q1)
  have u37 : p286 := by
    rcases h21140 with q0 | q1
    · exact q0
    · exact False.elim (u33 q1)
  have u38 : p288 := by
    rcases h21668 with q0 | q1
    · exact False.elim (u33 q0)
    · exact q1
  have u39 : (¬ p1325) := by
    rcases h17024 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u14)
    · exact False.elim (q2 u34)
    · exact q3
  have u40 : (¬ p344) := by
    rcases h22912 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u34)
    · exact False.elim (q2 u38)
    · exact False.elim (q3 u37)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u6)
  have u41 : p1353 := by
    rcases h21157 with q0 | q1
    · exact q0
    · exact False.elim (u35 q1)
  have u42 : p1335 := by
    rcases h21904 with q0 | q1
    · exact q0
    · exact False.elim (u39 q1)
  have u43 : (¬ p435) := by
    rcases h17511 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u12)
    · exact False.elim (q1 u15)
    · exact False.elim (q2 u6)
    · exact q3
    · exact False.elim (q4 u42)
    · exact False.elim (q5 u29)
    · exact False.elim (q6 u2)
  have u44 : p1366 := by
    rcases h21910 with q0 | q1
    · exact q0
    · exact False.elim (u43 q1)
  have u45 : (¬ p581) := by
    rcases h23023 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14
    · exact q0
    · exact False.elim (u40 q1)
    · exact False.elim (q2 u44)
    · exact False.elim (q3 u34)
    · exact False.elim (q4 u36)
    · exact False.elim (q5 u29)
    · exact False.elim (q6 u2)
    · exact False.elim (q7 u3)
    · exact False.elim (q8 u4)
    · exact False.elim (q9 u13)
    · exact False.elim (q10 u20)
    · exact False.elim (q11 u6)
    · exact False.elim (q12 u9)
    · exact False.elim (q13 u11)
    · exact False.elim (q14 u12)
  have u46 : (¬ p84) := by
    rcases h11129 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u6)
    · exact False.elim (u45 q2)
  have u47 : (¬ p160) := by
    rcases h22909 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
    · exact False.elim (u45 q0)
    · exact q1
    · exact False.elim (q2 u41)
    · exact False.elim (q3 u28)
    · exact False.elim (q4 u3)
    · exact False.elim (u5 q5)
    · exact False.elim (q6 u22)
    · exact False.elim (q7 u6)
    · exact False.elim (q8 u11)
    · exact False.elim (q9 u12)
  have u48 : p89 := by
    rcases h22277 with q0 | q1
    · exact q0
    · exact False.elim (u46 q1)
  have u49 : p1226 := by
    rcases h21183 with q0 | q1
    · exact q0
    · exact False.elim (u47 q1)
  have u50 : (¬ p64) := by
    rcases h11182 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u48)
    · exact False.elim (u5 q2)
  have u51 : p532 := by
    rcases h10737 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u36)
    · exact False.elim (q2 u49)
  have u52 : p5 := by
    rcases h22908 with q0 | q1
    · exact q0
    · exact False.elim (u50 q1)
  rcases h17166 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u12)
  · exact False.elim (q1 u52)
  · exact False.elim (q2 u48)
  · exact False.elim (q3 u22)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u51)
  · exact False.elim (q7 u30)
  · exact False.elim (q8 u31)

theorem step23027 (p2 p5 p6 p64 p84 p89 p124 p125 p126 p160 p188 p192 p194 p228 p256 p258 p265 p266 p286 p288 p344 p367 p382 p387 p419 p435 p476 p481 p532 p581 p796 p961 p964 p983 p1226 p1325 p1335 p1349 p1353 p1366 p1443 p1452 p1489 p1492 p1495 p1496 p1500 p1503 p1504 p1505 p1506 p1507 p1508 : Prop)
    (h21387 : p188 ∨ p192)
    (h11962 : (¬ p2) ∨ (¬ p192) ∨ p796)
    (h22615 : p194 ∨ p188)
    (h10692 : (¬ p2) ∨ (¬ p481))
    (h22551 : p476 ∨ p481)
    (h12408 : p382 ∨ (¬ p419) ∨ (¬ p476))
    (h13074 : (¬ p125) ∨ (¬ p126) ∨ (¬ p265))
    (h21948 : p367 ∨ p125)
    (h10100 : (¬ p367) ∨ (¬ p382) ∨ (¬ p387))
    (h21214 : p228 ∨ p387)
    (h9163 : p1500 ∨ p1503)
    (h9164 : p1500 ∨ p1504)
    (h9165 : p1500 ∨ p1505)
    (h9166 : p1500 ∨ p1506)
    (h9167 : p1500 ∨ p1507)
    (h22703 : p1500 ∨ p1492 ∨ p1495)
    (h9080 : p1443 ∨ p1492 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507))
    (h9079 : p1492 ∨ p1496 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507))
    (h13190 : (¬ p1452) ∨ (¬ p1495) ∨ p1508)
    (h12820 : (¬ p265) ∨ (¬ p961) ∨ (¬ p1443))
    (h19744 : (¬ p2) ∨ (¬ p124) ∨ (¬ p194) ∨ (¬ p228) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p419) ∨ (¬ p1443))
    (h22829 : p983 ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h13598 : (¬ p256) ∨ (¬ p1349) ∨ (¬ p1496))
    (h21239 : p964 ∨ p961)
    (h21140 : p286 ∨ p258)
    (h21668 : p258 ∨ p288)
    (h17024 : (¬ p419) ∨ (¬ p796) ∨ (¬ p983) ∨ (¬ p1325))
    (h22912 : (¬ p344) ∨ (¬ p983) ∨ (¬ p288) ∨ (¬ p286) ∨ (¬ p1489) ∨ (¬ p256))
    (h21157 : p1353 ∨ p1349)
    (h21904 : p1335 ∨ p1325)
    (h17511 : (¬ p2) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p1443) ∨ (¬ p1452))
    (h21910 : p1366 ∨ p435)
    (h23023 : (¬ p581) ∨ p344 ∨ (¬ p1366) ∨ (¬ p983) ∨ (¬ p964) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ (¬ p192) ∨ (¬ p367) ∨ (¬ p256) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p2))
    (h11129 : (¬ p84) ∨ (¬ p256) ∨ p581)
    (h22909 : p581 ∨ (¬ p160) ∨ (¬ p1353) ∨ (¬ p1495) ∨ (¬ p1489) ∨ p188 ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h22277 : p89 ∨ p84)
    (h21183 : p1226 ∨ p160)
    (h11182 : (¬ p64) ∨ (¬ p89) ∨ p188)
    (h10737 : p532 ∨ (¬ p964) ∨ (¬ p1226))
    (h22908 : p5 ∨ p64)
    (h17166 : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p532) ∨ (¬ p1496) ∨ (¬ p1508)) : p1500 ∨ p1492 ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ p188 ∨ (¬ p256) ∨ (¬ p265) ∨ (¬ p266) ∨ (¬ p126) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1500) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1492) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p188) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))
  have u13 : p192 := by
    rcases h21387 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u14 : p796 := by
    rcases h11962 with q0 | q1 | q2
    · exact False.elim (q0 u12)
    · exact False.elim (q1 u13)
    · exact q2
  have u15 : p194 := by
    rcases h22615 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u16 : (¬ p481) := by
    rcases h10692 with q0 | q1
    · exact False.elim (q0 u12)
    · exact q1
  have u17 : p476 := by
    rcases h22551 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u18 : p382 := by
    rcases h12408 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u11)
    · exact False.elim (q2 u17)
  have u19 : (¬ p125) := by
    rcases h13074 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u9)
    · exact False.elim (q2 u7)
  have u20 : p367 := by
    rcases h21948 with q0 | q1
    · exact q0
    · exact False.elim (u19 q1)
  have u21 : (¬ p387) := by
    rcases h10100 with q0 | q1 | q2
    · exact False.elim (q0 u20)
    · exact False.elim (q1 u18)
    · exact q2
  have u22 : p228 := by
    rcases h21214 with q0 | q1
    · exact q0
    · exact False.elim (u21 q1)
  have u23 : p1503 := by
    rcases h9163 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u24 : p1504 := by
    rcases h9164 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u25 : p1505 := by
    rcases h9165 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u26 : p1506 := by
    rcases h9166 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u27 : p1507 := by
    rcases h9167 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u28 : p1495 := by
    rcases h22703 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact q2
  have u29 : p1443 := by
    rcases h9080 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u23)
    · exact False.elim (q3 u24)
    · exact False.elim (q4 u25)
    · exact False.elim (q5 u26)
    · exact False.elim (q6 u27)
  have u30 : p1496 := by
    rcases h9079 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact q1
    · exact False.elim (q2 u23)
    · exact False.elim (q3 u24)
    · exact False.elim (q4 u25)
    · exact False.elim (q5 u26)
    · exact False.elim (q6 u27)
  have u31 : p1508 := by
    rcases h13190 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u28)
    · exact q2
  have u32 : (¬ p961) := by
    rcases h12820 with q0 | q1 | q2
    · exact False.elim (q0 u7)
    · exact q1
    · exact False.elim (q2 u29)
  have u33 : (¬ p258) := by
    rcases h19744 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u12)
    · exact False.elim (q1 u10)
    · exact False.elim (q2 u15)
    · exact False.elim (q3 u22)
    · exact q4
    · exact False.elim (q5 u8)
    · exact False.elim (q6 u11)
    · exact False.elim (q7 u29)
  have u34 : p983 := by
    rcases h22829 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (q1 u29)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u15)
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u11)
    · exact False.elim (q6 u12)
  have u35 : (¬ p1349) := by
    rcases h13598 with q0 | q1 | q2
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (q2 u30)
  have u36 : p964 := by
    rcases h21239 with q0 | q1
    · exact q0
    · exact False.elim (u32 q1)
  have u37 : p286 := by
    rcases h21140 with q0 | q1
    · exact q0
    · exact False.elim (u33 q1)
  have u38 : p288 := by
    rcases h21668 with q0 | q1
    · exact False.elim (u33 q0)
    · exact q1
  have u39 : (¬ p1325) := by
    rcases h17024 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u14)
    · exact False.elim (q2 u34)
    · exact q3
  have u40 : (¬ p344) := by
    rcases h22912 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u34)
    · exact False.elim (q2 u38)
    · exact False.elim (q3 u37)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u6)
  have u41 : p1353 := by
    rcases h21157 with q0 | q1
    · exact q0
    · exact False.elim (u35 q1)
  have u42 : p1335 := by
    rcases h21904 with q0 | q1
    · exact q0
    · exact False.elim (u39 q1)
  have u43 : (¬ p435) := by
    rcases h17511 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u12)
    · exact False.elim (q1 u15)
    · exact False.elim (q2 u6)
    · exact q3
    · exact False.elim (q4 u42)
    · exact False.elim (q5 u29)
    · exact False.elim (q6 u2)
  have u44 : p1366 := by
    rcases h21910 with q0 | q1
    · exact q0
    · exact False.elim (u43 q1)
  have u45 : (¬ p581) := by
    rcases h23023 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14
    · exact q0
    · exact False.elim (u40 q1)
    · exact False.elim (q2 u44)
    · exact False.elim (q3 u34)
    · exact False.elim (q4 u36)
    · exact False.elim (q5 u29)
    · exact False.elim (q6 u2)
    · exact False.elim (q7 u3)
    · exact False.elim (q8 u4)
    · exact False.elim (q9 u13)
    · exact False.elim (q10 u20)
    · exact False.elim (q11 u6)
    · exact False.elim (q12 u9)
    · exact False.elim (q13 u11)
    · exact False.elim (q14 u12)
  have u46 : (¬ p84) := by
    rcases h11129 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u6)
    · exact False.elim (u45 q2)
  have u47 : (¬ p160) := by
    rcases h22909 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
    · exact False.elim (u45 q0)
    · exact q1
    · exact False.elim (q2 u41)
    · exact False.elim (q3 u28)
    · exact False.elim (q4 u3)
    · exact False.elim (u5 q5)
    · exact False.elim (q6 u22)
    · exact False.elim (q7 u6)
    · exact False.elim (q8 u11)
    · exact False.elim (q9 u12)
  have u48 : p89 := by
    rcases h22277 with q0 | q1
    · exact q0
    · exact False.elim (u46 q1)
  have u49 : p1226 := by
    rcases h21183 with q0 | q1
    · exact q0
    · exact False.elim (u47 q1)
  have u50 : (¬ p64) := by
    rcases h11182 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u48)
    · exact False.elim (u5 q2)
  have u51 : p532 := by
    rcases h10737 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u36)
    · exact False.elim (q2 u49)
  have u52 : p5 := by
    rcases h22908 with q0 | q1
    · exact q0
    · exact False.elim (u50 q1)
  rcases h17166 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u12)
  · exact False.elim (q1 u52)
  · exact False.elim (q2 u48)
  · exact False.elim (q3 u22)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u51)
  · exact False.elim (q7 u30)
  · exact False.elim (q8 u31)

theorem step23028 (p2 p5 p6 p64 p84 p89 p124 p125 p126 p160 p188 p192 p194 p228 p256 p258 p265 p266 p286 p288 p344 p367 p382 p387 p419 p435 p476 p481 p532 p581 p796 p961 p964 p983 p1226 p1325 p1335 p1349 p1353 p1366 p1443 p1452 p1489 p1492 p1495 p1496 p1499 p1503 p1504 p1505 p1506 p1507 p1508 : Prop)
    (h21387 : p188 ∨ p192)
    (h11962 : (¬ p2) ∨ (¬ p192) ∨ p796)
    (h22615 : p194 ∨ p188)
    (h10692 : (¬ p2) ∨ (¬ p481))
    (h22551 : p476 ∨ p481)
    (h12408 : p382 ∨ (¬ p419) ∨ (¬ p476))
    (h13074 : (¬ p125) ∨ (¬ p126) ∨ (¬ p265))
    (h21948 : p367 ∨ p125)
    (h10100 : (¬ p367) ∨ (¬ p382) ∨ (¬ p387))
    (h21214 : p228 ∨ p387)
    (h9158 : p1499 ∨ p1503)
    (h9159 : p1499 ∨ p1504)
    (h9160 : p1499 ∨ p1505)
    (h9161 : p1499 ∨ p1506)
    (h9162 : p1499 ∨ p1507)
    (h22704 : p1499 ∨ p1492 ∨ p1495)
    (h9080 : p1443 ∨ p1492 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507))
    (h9079 : p1492 ∨ p1496 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507))
    (h13190 : (¬ p1452) ∨ (¬ p1495) ∨ p1508)
    (h12820 : (¬ p265) ∨ (¬ p961) ∨ (¬ p1443))
    (h19744 : (¬ p2) ∨ (¬ p124) ∨ (¬ p194) ∨ (¬ p228) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p419) ∨ (¬ p1443))
    (h22829 : p983 ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h13598 : (¬ p256) ∨ (¬ p1349) ∨ (¬ p1496))
    (h21239 : p964 ∨ p961)
    (h21140 : p286 ∨ p258)
    (h21668 : p258 ∨ p288)
    (h17024 : (¬ p419) ∨ (¬ p796) ∨ (¬ p983) ∨ (¬ p1325))
    (h22912 : (¬ p344) ∨ (¬ p983) ∨ (¬ p288) ∨ (¬ p286) ∨ (¬ p1489) ∨ (¬ p256))
    (h21157 : p1353 ∨ p1349)
    (h21904 : p1335 ∨ p1325)
    (h17511 : (¬ p2) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p1443) ∨ (¬ p1452))
    (h21910 : p1366 ∨ p435)
    (h23023 : (¬ p581) ∨ p344 ∨ (¬ p1366) ∨ (¬ p983) ∨ (¬ p964) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ (¬ p192) ∨ (¬ p367) ∨ (¬ p256) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p2))
    (h11129 : (¬ p84) ∨ (¬ p256) ∨ p581)
    (h22909 : p581 ∨ (¬ p160) ∨ (¬ p1353) ∨ (¬ p1495) ∨ (¬ p1489) ∨ p188 ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h22277 : p89 ∨ p84)
    (h21183 : p1226 ∨ p160)
    (h11182 : (¬ p64) ∨ (¬ p89) ∨ p188)
    (h10737 : p532 ∨ (¬ p964) ∨ (¬ p1226))
    (h22908 : p5 ∨ p64)
    (h17166 : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p532) ∨ (¬ p1496) ∨ (¬ p1508)) : p1499 ∨ p1492 ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ p188 ∨ (¬ p256) ∨ (¬ p265) ∨ (¬ p266) ∨ (¬ p126) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1499) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1492) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p188) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))
  have u13 : p192 := by
    rcases h21387 with q0 | q1
    · exact False.elim (u5 q0)
    · exact q1
  have u14 : p796 := by
    rcases h11962 with q0 | q1 | q2
    · exact False.elim (q0 u12)
    · exact False.elim (q1 u13)
    · exact q2
  have u15 : p194 := by
    rcases h22615 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u16 : (¬ p481) := by
    rcases h10692 with q0 | q1
    · exact False.elim (q0 u12)
    · exact q1
  have u17 : p476 := by
    rcases h22551 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u18 : p382 := by
    rcases h12408 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u11)
    · exact False.elim (q2 u17)
  have u19 : (¬ p125) := by
    rcases h13074 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u9)
    · exact False.elim (q2 u7)
  have u20 : p367 := by
    rcases h21948 with q0 | q1
    · exact q0
    · exact False.elim (u19 q1)
  have u21 : (¬ p387) := by
    rcases h10100 with q0 | q1 | q2
    · exact False.elim (q0 u20)
    · exact False.elim (q1 u18)
    · exact q2
  have u22 : p228 := by
    rcases h21214 with q0 | q1
    · exact q0
    · exact False.elim (u21 q1)
  have u23 : p1503 := by
    rcases h9158 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u24 : p1504 := by
    rcases h9159 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u25 : p1505 := by
    rcases h9160 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u26 : p1506 := by
    rcases h9161 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u27 : p1507 := by
    rcases h9162 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u28 : p1495 := by
    rcases h22704 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact q2
  have u29 : p1443 := by
    rcases h9080 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u23)
    · exact False.elim (q3 u24)
    · exact False.elim (q4 u25)
    · exact False.elim (q5 u26)
    · exact False.elim (q6 u27)
  have u30 : p1496 := by
    rcases h9079 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact q1
    · exact False.elim (q2 u23)
    · exact False.elim (q3 u24)
    · exact False.elim (q4 u25)
    · exact False.elim (q5 u26)
    · exact False.elim (q6 u27)
  have u31 : p1508 := by
    rcases h13190 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u28)
    · exact q2
  have u32 : (¬ p961) := by
    rcases h12820 with q0 | q1 | q2
    · exact False.elim (q0 u7)
    · exact q1
    · exact False.elim (q2 u29)
  have u33 : (¬ p258) := by
    rcases h19744 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u12)
    · exact False.elim (q1 u10)
    · exact False.elim (q2 u15)
    · exact False.elim (q3 u22)
    · exact q4
    · exact False.elim (q5 u8)
    · exact False.elim (q6 u11)
    · exact False.elim (q7 u29)
  have u34 : p983 := by
    rcases h22829 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (q1 u29)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u15)
    · exact False.elim (q4 u6)
    · exact False.elim (q5 u11)
    · exact False.elim (q6 u12)
  have u35 : (¬ p1349) := by
    rcases h13598 with q0 | q1 | q2
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (q2 u30)
  have u36 : p964 := by
    rcases h21239 with q0 | q1
    · exact q0
    · exact False.elim (u32 q1)
  have u37 : p286 := by
    rcases h21140 with q0 | q1
    · exact q0
    · exact False.elim (u33 q1)
  have u38 : p288 := by
    rcases h21668 with q0 | q1
    · exact False.elim (u33 q0)
    · exact q1
  have u39 : (¬ p1325) := by
    rcases h17024 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u14)
    · exact False.elim (q2 u34)
    · exact q3
  have u40 : (¬ p344) := by
    rcases h22912 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u34)
    · exact False.elim (q2 u38)
    · exact False.elim (q3 u37)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u6)
  have u41 : p1353 := by
    rcases h21157 with q0 | q1
    · exact q0
    · exact False.elim (u35 q1)
  have u42 : p1335 := by
    rcases h21904 with q0 | q1
    · exact q0
    · exact False.elim (u39 q1)
  have u43 : (¬ p435) := by
    rcases h17511 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u12)
    · exact False.elim (q1 u15)
    · exact False.elim (q2 u6)
    · exact q3
    · exact False.elim (q4 u42)
    · exact False.elim (q5 u29)
    · exact False.elim (q6 u2)
  have u44 : p1366 := by
    rcases h21910 with q0 | q1
    · exact q0
    · exact False.elim (u43 q1)
  have u45 : (¬ p581) := by
    rcases h23023 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14
    · exact q0
    · exact False.elim (u40 q1)
    · exact False.elim (q2 u44)
    · exact False.elim (q3 u34)
    · exact False.elim (q4 u36)
    · exact False.elim (q5 u29)
    · exact False.elim (q6 u2)
    · exact False.elim (q7 u3)
    · exact False.elim (q8 u4)
    · exact False.elim (q9 u13)
    · exact False.elim (q10 u20)
    · exact False.elim (q11 u6)
    · exact False.elim (q12 u9)
    · exact False.elim (q13 u11)
    · exact False.elim (q14 u12)
  have u46 : (¬ p84) := by
    rcases h11129 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u6)
    · exact False.elim (u45 q2)
  have u47 : (¬ p160) := by
    rcases h22909 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
    · exact False.elim (u45 q0)
    · exact q1
    · exact False.elim (q2 u41)
    · exact False.elim (q3 u28)
    · exact False.elim (q4 u3)
    · exact False.elim (u5 q5)
    · exact False.elim (q6 u22)
    · exact False.elim (q7 u6)
    · exact False.elim (q8 u11)
    · exact False.elim (q9 u12)
  have u48 : p89 := by
    rcases h22277 with q0 | q1
    · exact q0
    · exact False.elim (u46 q1)
  have u49 : p1226 := by
    rcases h21183 with q0 | q1
    · exact q0
    · exact False.elim (u47 q1)
  have u50 : (¬ p64) := by
    rcases h11182 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u48)
    · exact False.elim (u5 q2)
  have u51 : p532 := by
    rcases h10737 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u36)
    · exact False.elim (q2 u49)
  have u52 : p5 := by
    rcases h22908 with q0 | q1
    · exact q0
    · exact False.elim (u50 q1)
  rcases h17166 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u12)
  · exact False.elim (q1 u52)
  · exact False.elim (q2 u48)
  · exact False.elim (q3 u22)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u51)
  · exact False.elim (q7 u30)
  · exact False.elim (q8 u31)

theorem step23029 (p2 p5 p6 p17 p64 p84 p89 p124 p125 p126 p160 p188 p192 p194 p211 p227 p228 p256 p258 p265 p266 p286 p288 p344 p367 p382 p387 p419 p435 p476 p481 p532 p581 p796 p961 p964 p983 p1226 p1325 p1335 p1349 p1353 p1366 p1443 p1452 p1489 p1492 p1495 p1496 p1498 p1499 p1500 p1501 p1503 p1504 p1505 p1506 p1507 p1508 : Prop)
    (h10692 : (¬ p2) ∨ (¬ p481))
    (h22551 : p476 ∨ p481)
    (h12408 : p382 ∨ (¬ p419) ∨ (¬ p476))
    (h21151 : p17 ∨ p265)
    (h13074 : (¬ p125) ∨ (¬ p126) ∨ (¬ p265))
    (h21948 : p367 ∨ p125)
    (h10100 : (¬ p367) ∨ (¬ p382) ∨ (¬ p387))
    (h21214 : p228 ∨ p387)
    (h18534 : (¬ p2) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p228) ∨ (¬ p419))
    (h23019 : p6 ∨ p211)
    (h11559 : (¬ p188) ∨ p211 ∨ (¬ p266))
    (h21387 : p188 ∨ p192)
    (h11962 : (¬ p2) ∨ (¬ p192) ∨ p796)
    (h22615 : p194 ∨ p188)
    (h21276 : p256 ∨ p17)
    (h16416 : (¬ p126) ∨ (¬ p227) ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p1492))
    (h23026 : p1501 ∨ p1492 ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ p188 ∨ (¬ p256) ∨ (¬ p265) ∨ (¬ p266) ∨ (¬ p126) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2))
    (h23027 : p1500 ∨ p1492 ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ p188 ∨ (¬ p256) ∨ (¬ p265) ∨ (¬ p266) ∨ (¬ p126) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2))
    (h23028 : p1499 ∨ p1492 ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ p188 ∨ (¬ p256) ∨ (¬ p265) ∨ (¬ p266) ∨ (¬ p126) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2))
    (h23025 : (¬ p1501) ∨ (¬ p1500) ∨ (¬ p1499) ∨ (¬ p1498) ∨ p1492 ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ p188 ∨ (¬ p256) ∨ (¬ p265) ∨ (¬ p266) ∨ (¬ p126) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2))
    (h9153 : p1498 ∨ p1503)
    (h9154 : p1498 ∨ p1504)
    (h9155 : p1498 ∨ p1505)
    (h9156 : p1498 ∨ p1506)
    (h9157 : p1498 ∨ p1507)
    (h9080 : p1443 ∨ p1492 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507))
    (h9079 : p1492 ∨ p1496 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507))
    (h9078 : p1492 ∨ p1495 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507))
    (h12820 : (¬ p265) ∨ (¬ p961) ∨ (¬ p1443))
    (h19744 : (¬ p2) ∨ (¬ p124) ∨ (¬ p194) ∨ (¬ p228) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p419) ∨ (¬ p1443))
    (h22829 : p983 ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h13598 : (¬ p256) ∨ (¬ p1349) ∨ (¬ p1496))
    (h13190 : (¬ p1452) ∨ (¬ p1495) ∨ p1508)
    (h21239 : p964 ∨ p961)
    (h21140 : p286 ∨ p258)
    (h21668 : p258 ∨ p288)
    (h17024 : (¬ p419) ∨ (¬ p796) ∨ (¬ p983) ∨ (¬ p1325))
    (h22912 : (¬ p344) ∨ (¬ p983) ∨ (¬ p288) ∨ (¬ p286) ∨ (¬ p1489) ∨ (¬ p256))
    (h21157 : p1353 ∨ p1349)
    (h21904 : p1335 ∨ p1325)
    (h17511 : (¬ p2) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p435) ∨ (¬ p1335) ∨ (¬ p1443) ∨ (¬ p1452))
    (h21910 : p1366 ∨ p435)
    (h23023 : (¬ p581) ∨ p344 ∨ (¬ p1366) ∨ (¬ p983) ∨ (¬ p964) ∨ (¬ p1443) ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p6) ∨ (¬ p192) ∨ (¬ p367) ∨ (¬ p256) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p2))
    (h11129 : (¬ p84) ∨ (¬ p256) ∨ p581)
    (h22909 : p581 ∨ (¬ p160) ∨ (¬ p1353) ∨ (¬ p1495) ∨ (¬ p1489) ∨ p188 ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p2))
    (h22277 : p89 ∨ p84)
    (h21183 : p1226 ∨ p160)
    (h11182 : (¬ p64) ∨ (¬ p89) ∨ p188)
    (h10737 : p532 ∨ (¬ p964) ∨ (¬ p1226))
    (h22908 : p5 ∨ p64)
    (h17166 : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p532) ∨ (¬ p1496) ∨ (¬ p1508)) : (¬ p1452) ∨ (¬ p1489) ∨ p17 ∨ (¬ p266) ∨ (¬ p227) ∨ (¬ p126) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p481) := by
    rcases h10692 with q0 | q1
    · exact False.elim (q0 u8)
    · exact q1
  have u10 : p476 := by
    rcases h22551 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u11 : p382 := by
    rcases h12408 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u10)
  have u12 : p265 := by
    rcases h21151 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u13 : (¬ p125) := by
    rcases h13074 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u12)
  have u14 : p367 := by
    rcases h21948 with q0 | q1
    · exact q0
    · exact False.elim (u13 q1)
  have u15 : (¬ p387) := by
    rcases h10100 with q0 | q1 | q2
    · exact False.elim (q0 u14)
    · exact False.elim (q1 u11)
    · exact q2
  have u16 : p228 := by
    rcases h21214 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  have u17 : (¬ p211) := by
    rcases h18534 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u8)
    · exact q1
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u16)
    · exact False.elim (q4 u7)
  have u18 : p6 := by
    rcases h23019 with q0 | q1
    · exact q0
    · exact False.elim (u17 q1)
  have u19 : (¬ p188) := by
    rcases h11559 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u17 q1)
    · exact False.elim (q2 u3)
  have u20 : p192 := by
    rcases h21387 with q0 | q1
    · exact False.elim (u19 q0)
    · exact q1
  have u21 : p796 := by
    rcases h11962 with q0 | q1 | q2
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u20)
    · exact q2
  have u22 : p194 := by
    rcases h22615 with q0 | q1
    · exact q0
    · exact False.elim (u19 q1)
  have u23 : p256 := by
    rcases h21276 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u24 : (¬ p1492) := by
    rcases h16416 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u1)
    · exact q4
  have u25 : p1501 := by
    rcases h23026 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
    · exact q0
    · exact False.elim (u24 q1)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u18)
    · exact False.elim (u19 q5)
    · exact False.elim (q6 u23)
    · exact False.elim (q7 u12)
    · exact False.elim (q8 u3)
    · exact False.elim (q9 u5)
    · exact False.elim (q10 u6)
    · exact False.elim (q11 u7)
    · exact False.elim (q12 u8)
  have u26 : p1500 := by
    rcases h23027 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
    · exact q0
    · exact False.elim (u24 q1)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u18)
    · exact False.elim (u19 q5)
    · exact False.elim (q6 u23)
    · exact False.elim (q7 u12)
    · exact False.elim (q8 u3)
    · exact False.elim (q9 u5)
    · exact False.elim (q10 u6)
    · exact False.elim (q11 u7)
    · exact False.elim (q12 u8)
  have u27 : p1499 := by
    rcases h23028 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12
    · exact q0
    · exact False.elim (u24 q1)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u18)
    · exact False.elim (u19 q5)
    · exact False.elim (q6 u23)
    · exact False.elim (q7 u12)
    · exact False.elim (q8 u3)
    · exact False.elim (q9 u5)
    · exact False.elim (q10 u6)
    · exact False.elim (q11 u7)
    · exact False.elim (q12 u8)
  have u28 : (¬ p1498) := by
    rcases h23025 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15
    · exact False.elim (q0 u25)
    · exact False.elim (q1 u26)
    · exact False.elim (q2 u27)
    · exact q3
    · exact False.elim (u24 q4)
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u1)
    · exact False.elim (q7 u18)
    · exact False.elim (u19 q8)
    · exact False.elim (q9 u23)
    · exact False.elim (q10 u12)
    · exact False.elim (q11 u3)
    · exact False.elim (q12 u5)
    · exact False.elim (q13 u6)
    · exact False.elim (q14 u7)
    · exact False.elim (q15 u8)
  have u29 : p1503 := by
    rcases h9153 with q0 | q1
    · exact False.elim (u28 q0)
    · exact q1
  have u30 : p1504 := by
    rcases h9154 with q0 | q1
    · exact False.elim (u28 q0)
    · exact q1
  have u31 : p1505 := by
    rcases h9155 with q0 | q1
    · exact False.elim (u28 q0)
    · exact q1
  have u32 : p1506 := by
    rcases h9156 with q0 | q1
    · exact False.elim (u28 q0)
    · exact q1
  have u33 : p1507 := by
    rcases h9157 with q0 | q1
    · exact False.elim (u28 q0)
    · exact q1
  have u34 : p1443 := by
    rcases h9080 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (u24 q1)
    · exact False.elim (q2 u29)
    · exact False.elim (q3 u30)
    · exact False.elim (q4 u31)
    · exact False.elim (q5 u32)
    · exact False.elim (q6 u33)
  have u35 : p1496 := by
    rcases h9079 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u24 q0)
    · exact q1
    · exact False.elim (q2 u29)
    · exact False.elim (q3 u30)
    · exact False.elim (q4 u31)
    · exact False.elim (q5 u32)
    · exact False.elim (q6 u33)
  have u36 : p1495 := by
    rcases h9078 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u24 q0)
    · exact q1
    · exact False.elim (q2 u29)
    · exact False.elim (q3 u30)
    · exact False.elim (q4 u31)
    · exact False.elim (q5 u32)
    · exact False.elim (q6 u33)
  have u37 : (¬ p961) := by
    rcases h12820 with q0 | q1 | q2
    · exact False.elim (q0 u12)
    · exact q1
    · exact False.elim (q2 u34)
  have u38 : (¬ p258) := by
    rcases h19744 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u6)
    · exact False.elim (q2 u22)
    · exact False.elim (q3 u16)
    · exact q4
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u7)
    · exact False.elim (q7 u34)
  have u39 : p983 := by
    rcases h22829 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact q0
    · exact False.elim (q1 u34)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u22)
    · exact False.elim (q4 u23)
    · exact False.elim (q5 u7)
    · exact False.elim (q6 u8)
  have u40 : (¬ p1349) := by
    rcases h13598 with q0 | q1 | q2
    · exact False.elim (q0 u23)
    · exact q1
    · exact False.elim (q2 u35)
  have u41 : p1508 := by
    rcases h13190 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u36)
    · exact q2
  have u42 : p964 := by
    rcases h21239 with q0 | q1
    · exact q0
    · exact False.elim (u37 q1)
  have u43 : p286 := by
    rcases h21140 with q0 | q1
    · exact q0
    · exact False.elim (u38 q1)
  have u44 : p288 := by
    rcases h21668 with q0 | q1
    · exact False.elim (u38 q0)
    · exact q1
  have u45 : (¬ p1325) := by
    rcases h17024 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u21)
    · exact False.elim (q2 u39)
    · exact q3
  have u46 : (¬ p344) := by
    rcases h22912 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u39)
    · exact False.elim (q2 u44)
    · exact False.elim (q3 u43)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u23)
  have u47 : p1353 := by
    rcases h21157 with q0 | q1
    · exact q0
    · exact False.elim (u40 q1)
  have u48 : p1335 := by
    rcases h21904 with q0 | q1
    · exact q0
    · exact False.elim (u45 q1)
  have u49 : (¬ p435) := by
    rcases h17511 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u22)
    · exact False.elim (q2 u23)
    · exact q3
    · exact False.elim (q4 u48)
    · exact False.elim (q5 u34)
    · exact False.elim (q6 u0)
  have u50 : p1366 := by
    rcases h21910 with q0 | q1
    · exact q0
    · exact False.elim (u49 q1)
  have u51 : (¬ p581) := by
    rcases h23023 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14
    · exact q0
    · exact False.elim (u46 q1)
    · exact False.elim (q2 u50)
    · exact False.elim (q3 u39)
    · exact False.elim (q4 u42)
    · exact False.elim (q5 u34)
    · exact False.elim (q6 u0)
    · exact False.elim (q7 u1)
    · exact False.elim (q8 u18)
    · exact False.elim (q9 u20)
    · exact False.elim (q10 u14)
    · exact False.elim (q11 u23)
    · exact False.elim (q12 u5)
    · exact False.elim (q13 u7)
    · exact False.elim (q14 u8)
  have u52 : (¬ p84) := by
    rcases h11129 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u23)
    · exact False.elim (u51 q2)
  have u53 : (¬ p160) := by
    rcases h22909 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
    · exact False.elim (u51 q0)
    · exact q1
    · exact False.elim (q2 u47)
    · exact False.elim (q3 u36)
    · exact False.elim (q4 u1)
    · exact False.elim (u19 q5)
    · exact False.elim (q6 u16)
    · exact False.elim (q7 u23)
    · exact False.elim (q8 u7)
    · exact False.elim (q9 u8)
  have u54 : p89 := by
    rcases h22277 with q0 | q1
    · exact q0
    · exact False.elim (u52 q1)
  have u55 : p1226 := by
    rcases h21183 with q0 | q1
    · exact q0
    · exact False.elim (u53 q1)
  have u56 : (¬ p64) := by
    rcases h11182 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u54)
    · exact False.elim (u19 q2)
  have u57 : p532 := by
    rcases h10737 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u42)
    · exact False.elim (q2 u55)
  have u58 : p5 := by
    rcases h22908 with q0 | q1
    · exact q0
    · exact False.elim (u56 q1)
  rcases h17166 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u58)
  · exact False.elim (q2 u54)
  · exact False.elim (q3 u16)
  · exact False.elim (q4 u23)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u57)
  · exact False.elim (q7 u35)
  · exact False.elim (q8 u41)

theorem step23030 (p1443 p1492 p1498 p1499 p1500 p1501 p1502 p1507 : Prop)
    (h9157 : p1498 ∨ p1507)
    (h9162 : p1499 ∨ p1507)
    (h9167 : p1500 ∨ p1507)
    (h9172 : p1501 ∨ p1507)
    (h9177 : p1502 ∨ p1507)
    (h9055 : p1443 ∨ p1492 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502)) : p1507 ∨ p1492 ∨ p1443 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1507) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1492) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1443) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1498 := by
    rcases h9157 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1499 := by
    rcases h9162 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1500 := by
    rcases h9167 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1501 := by
    rcases h9172 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1502 := by
    rcases h9177 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9055 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23031 (p1443 p1492 p1498 p1499 p1500 p1501 p1502 p1506 : Prop)
    (h9156 : p1498 ∨ p1506)
    (h9161 : p1499 ∨ p1506)
    (h9166 : p1500 ∨ p1506)
    (h9171 : p1501 ∨ p1506)
    (h9176 : p1502 ∨ p1506)
    (h9055 : p1443 ∨ p1492 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502)) : p1506 ∨ p1492 ∨ p1443 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1506) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1492) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1443) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1498 := by
    rcases h9156 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1499 := by
    rcases h9161 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1500 := by
    rcases h9166 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1501 := by
    rcases h9171 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1502 := by
    rcases h9176 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9055 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23032 (p1443 p1492 p1498 p1499 p1500 p1501 p1502 p1505 : Prop)
    (h9155 : p1498 ∨ p1505)
    (h9160 : p1499 ∨ p1505)
    (h9165 : p1500 ∨ p1505)
    (h9170 : p1501 ∨ p1505)
    (h9175 : p1502 ∨ p1505)
    (h9055 : p1443 ∨ p1492 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502)) : p1505 ∨ p1492 ∨ p1443 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1505) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1492) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1443) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1498 := by
    rcases h9155 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1499 := by
    rcases h9160 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1500 := by
    rcases h9165 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1501 := by
    rcases h9170 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1502 := by
    rcases h9175 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9055 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23033 (p1443 p1492 p1498 p1499 p1500 p1501 p1502 p1504 : Prop)
    (h9154 : p1498 ∨ p1504)
    (h9159 : p1499 ∨ p1504)
    (h9164 : p1500 ∨ p1504)
    (h9169 : p1501 ∨ p1504)
    (h9174 : p1502 ∨ p1504)
    (h9055 : p1443 ∨ p1492 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502)) : p1504 ∨ p1492 ∨ p1443 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1504) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1492) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1443) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1498 := by
    rcases h9154 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1499 := by
    rcases h9159 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1500 := by
    rcases h9164 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1501 := by
    rcases h9169 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1502 := by
    rcases h9174 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9055 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23034 (p1443 p1492 p1498 p1499 p1500 p1501 p1502 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9080 : p1443 ∨ p1492 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507))
    (h9153 : p1498 ∨ p1503)
    (h9158 : p1499 ∨ p1503)
    (h9163 : p1500 ∨ p1503)
    (h9168 : p1501 ∨ p1503)
    (h9173 : p1502 ∨ p1503)
    (h9055 : p1443 ∨ p1492 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502)) : (¬ p1504) ∨ (¬ p1505) ∨ p1443 ∨ p1492 ∨ (¬ p1507) ∨ (¬ p1506) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1504 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1505 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1443) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1492) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1507 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1506 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1503) := by
    rcases h9080 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u4)
  have u7 : p1498 := by
    rcases h9153 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1499 := by
    rcases h9158 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1500 := by
    rcases h9163 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1501 := by
    rcases h9168 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1502 := by
    rcases h9173 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h9055 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step23035 (p1443 p1492 p1504 p1505 p1506 p1507 : Prop)
    (h23030 : p1507 ∨ p1492 ∨ p1443)
    (h23031 : p1506 ∨ p1492 ∨ p1443)
    (h23032 : p1505 ∨ p1492 ∨ p1443)
    (h23033 : p1504 ∨ p1492 ∨ p1443)
    (h23034 : (¬ p1504) ∨ (¬ p1505) ∨ p1443 ∨ p1492 ∨ (¬ p1507) ∨ (¬ p1506)) : p1492 ∨ p1443 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1492) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1443) := fun hu => hn (Or.inr hu)
  have u2 : p1507 := by
    rcases h23030 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1506 := by
    rcases h23031 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1505 := by
    rcases h23032 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1504 := by
    rcases h23033 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h23034 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step23037 (p19 p20 p28 p33 p34 p35 p36 p37 : Prop)
    (h105 : p28 ∨ p33)
    (h106 : p28 ∨ p34)
    (h107 : p28 ∨ p35)
    (h108 : p28 ∨ p36)
    (h109 : p28 ∨ p37)
    (h32 : p19 ∨ p20 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p28 ∨ p20 ∨ p19 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p28) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p20) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p19) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p33 := by
    rcases h105 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p34 := by
    rcases h106 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p35 := by
    rcases h107 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p36 := by
    rcases h108 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p37 := by
    rcases h109 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h32 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23038 (p19 p20 p32 p33 p34 p35 p36 p37 : Prop)
    (h125 : p32 ∨ p33)
    (h126 : p32 ∨ p34)
    (h127 : p32 ∨ p35)
    (h128 : p32 ∨ p36)
    (h129 : p32 ∨ p37)
    (h32 : p19 ∨ p20 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p32 ∨ p20 ∨ p19 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p32) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p20) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p19) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p33 := by
    rcases h125 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p34 := by
    rcases h126 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p35 := by
    rcases h127 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p36 := by
    rcases h128 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p37 := by
    rcases h129 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h32 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23039 (p19 p20 p31 p33 p34 p35 p36 p37 : Prop)
    (h120 : p31 ∨ p33)
    (h121 : p31 ∨ p34)
    (h122 : p31 ∨ p35)
    (h123 : p31 ∨ p36)
    (h124 : p31 ∨ p37)
    (h32 : p19 ∨ p20 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p31 ∨ p20 ∨ p19 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p31) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p20) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p19) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p33 := by
    rcases h120 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p34 := by
    rcases h121 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p35 := by
    rcases h122 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p36 := by
    rcases h123 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p37 := by
    rcases h124 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h32 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23040 (p19 p20 p30 p33 p34 p35 p36 p37 : Prop)
    (h115 : p30 ∨ p33)
    (h116 : p30 ∨ p34)
    (h117 : p30 ∨ p35)
    (h118 : p30 ∨ p36)
    (h119 : p30 ∨ p37)
    (h32 : p19 ∨ p20 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : p30 ∨ p20 ∨ p19 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p30) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p20) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p19) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p33 := by
    rcases h115 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p34 := by
    rcases h116 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p35 := by
    rcases h117 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p36 := by
    rcases h118 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p37 := by
    rcases h119 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h32 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23041 (p19 p20 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 : Prop)
    (h7 : p19 ∨ p20 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32))
    (h110 : p29 ∨ p33)
    (h111 : p29 ∨ p34)
    (h112 : p29 ∨ p35)
    (h113 : p29 ∨ p36)
    (h114 : p29 ∨ p37)
    (h32 : p19 ∨ p20 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : (¬ p30) ∨ (¬ p31) ∨ p19 ∨ (¬ p32) ∨ p20 ∨ (¬ p28) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p30 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p31 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p19) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p32 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p20) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p28 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p29) := by
    rcases h7 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u4 q1)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u3)
  have u7 : p33 := by
    rcases h110 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p34 := by
    rcases h111 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p35 := by
    rcases h112 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p36 := by
    rcases h113 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p37 := by
    rcases h114 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h32 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step23042 (p19 p20 p28 p30 p31 p32 : Prop)
    (h23037 : p28 ∨ p20 ∨ p19)
    (h23038 : p32 ∨ p20 ∨ p19)
    (h23039 : p31 ∨ p20 ∨ p19)
    (h23040 : p30 ∨ p20 ∨ p19)
    (h23041 : (¬ p30) ∨ (¬ p31) ∨ p19 ∨ (¬ p32) ∨ p20 ∨ (¬ p28)) : p20 ∨ p19 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p20) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p19) := fun hu => hn (Or.inr hu)
  have u2 : p28 := by
    rcases h23037 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p32 := by
    rcases h23038 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p31 := by
    rcases h23039 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p30 := by
    rcases h23040 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h23041 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u2)

theorem step23044 (p533 p983 p990 p991 p992 p993 p994 p995 : Prop)
    (h5832 : p990 ∨ p991)
    (h5833 : p990 ∨ p992)
    (h5834 : p990 ∨ p993)
    (h5835 : p990 ∨ p994)
    (h5836 : p990 ∨ p995)
    (h5759 : p533 ∨ p983 ∨ (¬ p991) ∨ (¬ p992) ∨ (¬ p993) ∨ (¬ p994) ∨ (¬ p995)) : p990 ∨ p533 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p990) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p533) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p991 := by
    rcases h5832 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p992 := by
    rcases h5833 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p993 := by
    rcases h5834 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p994 := by
    rcases h5835 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p995 := by
    rcases h5836 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5759 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23045 (p533 p983 p989 p991 p992 p993 p994 p995 : Prop)
    (h5827 : p989 ∨ p991)
    (h5828 : p989 ∨ p992)
    (h5829 : p989 ∨ p993)
    (h5830 : p989 ∨ p994)
    (h5831 : p989 ∨ p995)
    (h5759 : p533 ∨ p983 ∨ (¬ p991) ∨ (¬ p992) ∨ (¬ p993) ∨ (¬ p994) ∨ (¬ p995)) : p989 ∨ p533 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p989) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p533) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p991 := by
    rcases h5827 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p992 := by
    rcases h5828 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p993 := by
    rcases h5829 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p994 := by
    rcases h5830 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p995 := by
    rcases h5831 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5759 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23046 (p533 p983 p988 p991 p992 p993 p994 p995 : Prop)
    (h5822 : p988 ∨ p991)
    (h5823 : p988 ∨ p992)
    (h5824 : p988 ∨ p993)
    (h5825 : p988 ∨ p994)
    (h5826 : p988 ∨ p995)
    (h5759 : p533 ∨ p983 ∨ (¬ p991) ∨ (¬ p992) ∨ (¬ p993) ∨ (¬ p994) ∨ (¬ p995)) : p988 ∨ p533 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p988) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p533) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p991 := by
    rcases h5822 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p992 := by
    rcases h5823 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p993 := by
    rcases h5824 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p994 := by
    rcases h5825 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p995 := by
    rcases h5826 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5759 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23047 (p533 p983 p987 p991 p992 p993 p994 p995 : Prop)
    (h5817 : p987 ∨ p991)
    (h5818 : p987 ∨ p992)
    (h5819 : p987 ∨ p993)
    (h5820 : p987 ∨ p994)
    (h5821 : p987 ∨ p995)
    (h5759 : p533 ∨ p983 ∨ (¬ p991) ∨ (¬ p992) ∨ (¬ p993) ∨ (¬ p994) ∨ (¬ p995)) : p987 ∨ p533 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p987) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p533) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p991 := by
    rcases h5817 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p992 := by
    rcases h5818 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p993 := by
    rcases h5819 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p994 := by
    rcases h5820 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p995 := by
    rcases h5821 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5759 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23048 (p533 p983 p986 p987 p988 p989 p990 p991 p992 p993 p994 p995 : Prop)
    (h5734 : p533 ∨ p983 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990))
    (h5812 : p986 ∨ p991)
    (h5813 : p986 ∨ p992)
    (h5814 : p986 ∨ p993)
    (h5815 : p986 ∨ p994)
    (h5816 : p986 ∨ p995)
    (h5759 : p533 ∨ p983 ∨ (¬ p991) ∨ (¬ p992) ∨ (¬ p993) ∨ (¬ p994) ∨ (¬ p995)) : (¬ p987) ∨ (¬ p990) ∨ p983 ∨ p533 ∨ (¬ p988) ∨ (¬ p989) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p987 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p990 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p533) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p988 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p989 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p986) := by
    rcases h5734 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact q2
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u1)
  have u7 : p991 := by
    rcases h5812 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p992 := by
    rcases h5813 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p993 := by
    rcases h5814 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p994 := by
    rcases h5815 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p995 := by
    rcases h5816 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h5759 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step23049 (p533 p983 p987 p988 p989 p990 : Prop)
    (h23044 : p990 ∨ p533 ∨ p983)
    (h23045 : p989 ∨ p533 ∨ p983)
    (h23046 : p988 ∨ p533 ∨ p983)
    (h23047 : p987 ∨ p533 ∨ p983)
    (h23048 : (¬ p987) ∨ (¬ p990) ∨ p983 ∨ p533 ∨ (¬ p988) ∨ (¬ p989)) : p533 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p533) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p983) := fun hu => hn (Or.inr hu)
  have u2 : p990 := by
    rcases h23044 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p989 := by
    rcases h23045 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p988 := by
    rcases h23046 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p987 := by
    rcases h23047 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h23048 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step23050 (p727 p737 p740 p745 p746 p747 p748 p749 : Prop)
    (h4256 : p740 ∨ p745)
    (h4257 : p740 ∨ p746)
    (h4258 : p740 ∨ p747)
    (h4259 : p740 ∨ p748)
    (h4260 : p740 ∨ p749)
    (h4197 : p727 ∨ p737 ∨ (¬ p745) ∨ (¬ p746) ∨ (¬ p747) ∨ (¬ p748) ∨ (¬ p749)) : p740 ∨ p727 ∨ p737 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p740) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p727) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p737) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p745 := by
    rcases h4256 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p746 := by
    rcases h4257 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p747 := by
    rcases h4258 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p748 := by
    rcases h4259 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p749 := by
    rcases h4260 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4197 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23051 (p727 p737 p744 p745 p746 p747 p748 p749 : Prop)
    (h4276 : p744 ∨ p745)
    (h4277 : p744 ∨ p746)
    (h4278 : p744 ∨ p747)
    (h4279 : p744 ∨ p748)
    (h4280 : p744 ∨ p749)
    (h4197 : p727 ∨ p737 ∨ (¬ p745) ∨ (¬ p746) ∨ (¬ p747) ∨ (¬ p748) ∨ (¬ p749)) : p744 ∨ p727 ∨ p737 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p744) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p727) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p737) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p745 := by
    rcases h4276 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p746 := by
    rcases h4277 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p747 := by
    rcases h4278 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p748 := by
    rcases h4279 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p749 := by
    rcases h4280 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4197 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23052 (p727 p737 p743 p745 p746 p747 p748 p749 : Prop)
    (h4271 : p743 ∨ p745)
    (h4272 : p743 ∨ p746)
    (h4273 : p743 ∨ p747)
    (h4274 : p743 ∨ p748)
    (h4275 : p743 ∨ p749)
    (h4197 : p727 ∨ p737 ∨ (¬ p745) ∨ (¬ p746) ∨ (¬ p747) ∨ (¬ p748) ∨ (¬ p749)) : p743 ∨ p727 ∨ p737 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p743) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p727) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p737) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p745 := by
    rcases h4271 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p746 := by
    rcases h4272 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p747 := by
    rcases h4273 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p748 := by
    rcases h4274 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p749 := by
    rcases h4275 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4197 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23053 (p727 p737 p742 p745 p746 p747 p748 p749 : Prop)
    (h4266 : p742 ∨ p745)
    (h4267 : p742 ∨ p746)
    (h4268 : p742 ∨ p747)
    (h4269 : p742 ∨ p748)
    (h4270 : p742 ∨ p749)
    (h4197 : p727 ∨ p737 ∨ (¬ p745) ∨ (¬ p746) ∨ (¬ p747) ∨ (¬ p748) ∨ (¬ p749)) : p742 ∨ p727 ∨ p737 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p742) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p727) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p737) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p745 := by
    rcases h4266 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p746 := by
    rcases h4267 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p747 := by
    rcases h4268 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p748 := by
    rcases h4269 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p749 := by
    rcases h4270 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h4197 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23054 (p727 p737 p740 p741 p742 p743 p744 p745 p746 p747 p748 p749 : Prop)
    (h4172 : p727 ∨ p737 ∨ (¬ p740) ∨ (¬ p741) ∨ (¬ p742) ∨ (¬ p743) ∨ (¬ p744))
    (h4261 : p741 ∨ p745)
    (h4262 : p741 ∨ p746)
    (h4263 : p741 ∨ p747)
    (h4264 : p741 ∨ p748)
    (h4265 : p741 ∨ p749)
    (h4197 : p727 ∨ p737 ∨ (¬ p745) ∨ (¬ p746) ∨ (¬ p747) ∨ (¬ p748) ∨ (¬ p749)) : (¬ p742) ∨ p727 ∨ p737 ∨ (¬ p743) ∨ (¬ p744) ∨ (¬ p740) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p742 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p727) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p737) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p743 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p744 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p740 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p741) := by
    rcases h4172 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u4)
  have u7 : p745 := by
    rcases h4261 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p746 := by
    rcases h4262 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p747 := by
    rcases h4263 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p748 := by
    rcases h4264 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p749 := by
    rcases h4265 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h4197 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step23055 (p727 p737 p740 p742 p743 p744 : Prop)
    (h23050 : p740 ∨ p727 ∨ p737)
    (h23051 : p744 ∨ p727 ∨ p737)
    (h23052 : p743 ∨ p727 ∨ p737)
    (h23053 : p742 ∨ p727 ∨ p737)
    (h23054 : (¬ p742) ∨ p727 ∨ p737 ∨ (¬ p743) ∨ (¬ p744) ∨ (¬ p740)) : p727 ∨ p737 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p727) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p737) := fun hu => hn (Or.inr hu)
  have u2 : p740 := by
    rcases h23050 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p744 := by
    rcases h23051 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p743 := by
    rcases h23052 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p742 := by
    rcases h23053 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h23054 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step23056 (p15 p21 p49 p84 p101 p108 p237 p258 p495 p499 p534 p583 p633 p634 p639 p726 p727 p840 p880 p940 p1096 p1099 : Prop)
    (h20942 : p495 ∨ p499)
    (h22748 : p583 ∨ (¬ p21))
    (h8733 : (¬ p21) ∨ (¬ p101) ∨ (¬ p633))
    (h22658 : p108 ∨ p101)
    (h22745 : (¬ p726) ∨ (¬ p534) ∨ (¬ p258) ∨ (¬ p108))
    (h21095 : p940 ∨ p534)
    (h17211 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p237) ∨ (¬ p727) ∨ (¬ p840) ∨ (¬ p880) ∨ (¬ p940) ∨ (¬ p1099))
    (h21802 : p1096 ∨ p1099)
    (h10764 : p499 ∨ (¬ p634) ∨ (¬ p1096))
    (h16411 : (¬ p258) ∨ (¬ p495) ∨ (¬ p583) ∨ (¬ p639) ∨ (¬ p1096))
    (h20840 : p639 ∨ p634) : (¬ p21) ∨ (¬ p727) ∨ (¬ p726) ∨ p499 ∨ (¬ p633) ∨ (¬ p880) ∨ (¬ p49) ∨ (¬ p15) ∨ (¬ p84) ∨ (¬ p840) ∨ (¬ p258) ∨ (¬ p237) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p499) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : p495 := by
    rcases h20942 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u13 : p583 := by
    rcases h22748 with q0 | q1
    · exact q0
    · exact False.elim (q1 u0)
  have u14 : (¬ p101) := by
    rcases h8733 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u4)
  have u15 : p108 := by
    rcases h22658 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  have u16 : (¬ p534) := by
    rcases h22745 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u10)
    · exact False.elim (q3 u15)
  have u17 : p940 := by
    rcases h21095 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u18 : (¬ p1099) := by
    rcases h17211 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u6)
    · exact False.elim (q2 u8)
    · exact False.elim (q3 u11)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u9)
    · exact False.elim (q6 u5)
    · exact False.elim (q7 u17)
    · exact q8
  have u19 : p1096 := by
    rcases h21802 with q0 | q1
    · exact q0
    · exact False.elim (u18 q1)
  have u20 : (¬ p634) := by
    rcases h10764 with q0 | q1 | q2
    · exact False.elim (u3 q0)
    · exact q1
    · exact False.elim (q2 u19)
  have u21 : (¬ p639) := by
    rcases h16411 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u10)
    · exact False.elim (q1 u12)
    · exact False.elim (q2 u13)
    · exact q3
    · exact False.elim (q4 u19)
  rcases h20840 with q0 | q1
  · exact False.elim (u21 q0)
  · exact False.elim (u20 q1)

theorem step23057 (p2 p5 p11 p15 p19 p21 p25 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p49 p84 p85 p124 p126 p161 p237 p258 p266 p344 p419 p495 p499 p533 p616 p633 p726 p727 p737 p756 p840 p880 p1225 p1229 p1232 p1289 p1293 p1325 : Prop)
    (h19747 : (¬ p2) ∨ (¬ p5) ∨ (¬ p344) ∨ (¬ p419) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1325))
    (h20942 : p495 ∨ p499)
    (h10583 : (¬ p15) ∨ (¬ p25) ∨ p499)
    (h22643 : (¬ p1229) ∨ (¬ p11) ∨ (¬ p126) ∨ (¬ p495) ∨ (¬ p85))
    (h22374 : p1229 ∨ p1232)
    (h10564 : p616 ∨ (¬ p1232) ∨ (¬ p1293))
    (h22540 : p1289 ∨ p1293)
    (h9341 : (¬ p1225) ∨ (¬ p1289) ∨ (¬ p1325))
    (h21572 : p161 ∨ p1225)
    (h18198 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p124) ∨ (¬ p161) ∨ (¬ p266) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1232))
    (h21112 : p726 ∨ p756)
    (h12183 : (¬ p344) ∨ (¬ p737) ∨ p756)
    (h23055 : p727 ∨ p737)
    (h23056 : (¬ p21) ∨ (¬ p727) ∨ (¬ p726) ∨ p499 ∨ (¬ p633) ∨ (¬ p880) ∨ (¬ p49) ∨ (¬ p15) ∨ (¬ p84) ∨ (¬ p840) ∨ (¬ p258) ∨ (¬ p237))
    (h12 : p19 ∨ p21 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32))
    (h110 : p29 ∨ p33)
    (h111 : p29 ∨ p34)
    (h112 : p29 ∨ p35)
    (h113 : p29 ∨ p36)
    (h114 : p29 ∨ p37)
    (h36 : p21 ∨ p25 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : (¬ p633) ∨ (¬ p28) ∨ (¬ p32) ∨ (¬ p31) ∨ (¬ p30) ∨ (¬ p880) ∨ (¬ p49) ∨ p19 ∨ (¬ p85) ∨ p616 ∨ (¬ p5) ∨ (¬ p15) ∨ (¬ p84) ∨ (¬ p533) ∨ (¬ p1325) ∨ (¬ p840) ∨ (¬ p258) ∨ (¬ p11) ∨ (¬ p344) ∨ (¬ p237) ∨ (¬ p266) ∨ (¬ p126) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p28 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p32 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p31 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p30 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p19) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : (¬ p616) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))
  have u18 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))
  have u19 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))
  have u20 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))))
  have u21 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))))
  have u22 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))))))
  have u23 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))))))
  have u24 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))))))))))))
  have u25 : (¬ p499) := by
    rcases h19747 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u24)
    · exact False.elim (q1 u10)
    · exact False.elim (q2 u18)
    · exact False.elim (q3 u23)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u14)
  have u26 : p495 := by
    rcases h20942 with q0 | q1
    · exact q0
    · exact False.elim (u25 q1)
  have u27 : (¬ p25) := by
    rcases h10583 with q0 | q1 | q2
    · exact False.elim (q0 u11)
    · exact q1
    · exact False.elim (u25 q2)
  have u28 : (¬ p1229) := by
    rcases h22643 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u17)
    · exact False.elim (q2 u21)
    · exact False.elim (q3 u26)
    · exact False.elim (q4 u8)
  have u29 : p1232 := by
    rcases h22374 with q0 | q1
    · exact False.elim (u28 q0)
    · exact q1
  have u30 : (¬ p1293) := by
    rcases h10564 with q0 | q1 | q2
    · exact False.elim (u9 q0)
    · exact False.elim (q1 u29)
    · exact q2
  have u31 : p1289 := by
    rcases h22540 with q0 | q1
    · exact q0
    · exact False.elim (u30 q1)
  have u32 : (¬ p1225) := by
    rcases h9341 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u31)
    · exact False.elim (q2 u14)
  have u33 : p161 := by
    rcases h21572 with q0 | q1
    · exact q0
    · exact False.elim (u32 q1)
  have u34 : (¬ p756) := by
    rcases h18198 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u6)
    · exact False.elim (q2 u12)
    · exact False.elim (q3 u22)
    · exact False.elim (q4 u33)
    · exact False.elim (q5 u20)
    · exact False.elim (q6 u13)
    · exact q7
    · exact False.elim (q8 u29)
  have u35 : p726 := by
    rcases h21112 with q0 | q1
    · exact q0
    · exact False.elim (u34 q1)
  have u36 : (¬ p737) := by
    rcases h12183 with q0 | q1 | q2
    · exact False.elim (q0 u18)
    · exact q1
    · exact False.elim (u34 q2)
  have u37 : p727 := by
    rcases h23055 with q0 | q1
    · exact q0
    · exact False.elim (u36 q1)
  have u38 : (¬ p21) := by
    rcases h23056 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
    · exact q0
    · exact False.elim (q1 u37)
    · exact False.elim (q2 u35)
    · exact False.elim (u25 q3)
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u6)
    · exact False.elim (q7 u11)
    · exact False.elim (q8 u12)
    · exact False.elim (q9 u15)
    · exact False.elim (q10 u16)
    · exact False.elim (q11 u19)
  have u39 : (¬ p29) := by
    rcases h12 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u7 q0)
    · exact False.elim (u38 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u2)
  have u40 : p33 := by
    rcases h110 with q0 | q1
    · exact False.elim (u39 q0)
    · exact q1
  have u41 : p34 := by
    rcases h111 with q0 | q1
    · exact False.elim (u39 q0)
    · exact q1
  have u42 : p35 := by
    rcases h112 with q0 | q1
    · exact False.elim (u39 q0)
    · exact q1
  have u43 : p36 := by
    rcases h113 with q0 | q1
    · exact False.elim (u39 q0)
    · exact q1
  have u44 : p37 := by
    rcases h114 with q0 | q1
    · exact False.elim (u39 q0)
    · exact q1
  rcases h36 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u38 q0)
  · exact False.elim (u27 q1)
  · exact False.elim (q2 u40)
  · exact False.elim (q3 u41)
  · exact False.elim (q4 u42)
  · exact False.elim (q5 u43)
  · exact False.elim (q6 u44)

theorem step23058 (p20 p49 p85 p124 p304 p350 p421 p495 p498 p595 p596 p636 : Prop)
    (h21106 : p124 ∨ p304)
    (h11284 : p304 ∨ (¬ p421) ∨ (¬ p636))
    (h16675 : (¬ p20) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p124) ∨ (¬ p498) ∨ (¬ p636))
    (h19255 : (¬ p350) ∨ (¬ p495) ∨ (¬ p595) ∨ (¬ p596) ∨ (¬ p636))
    (h20871 : p495 ∨ p498 ∨ p421) : (¬ p636) ∨ (¬ p20) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p595) ∨ (¬ p596) ∨ (¬ p350) ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : p124 := by
    rcases h21106 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : (¬ p421) := by
    rcases h11284 with q0 | q1 | q2
    · exact False.elim (u7 q0)
    · exact q1
    · exact False.elim (q2 u0)
  have u10 : (¬ p498) := by
    rcases h16675 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u8)
    · exact q4
    · exact False.elim (q5 u0)
  have u11 : (¬ p495) := by
    rcases h19255 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
  rcases h20871 with q0 | q1 | q2
  · exact False.elim (u11 q0)
  · exact False.elim (u10 q1)
  · exact False.elim (u9 q2)

theorem step23059 (p2 p5 p11 p14 p15 p19 p20 p21 p25 p28 p30 p31 p32 p38 p43 p49 p63 p64 p67 p69 p84 p85 p124 p126 p134 p161 p226 p237 p258 p266 p304 p344 p345 p350 p419 p495 p499 p533 p595 p596 p616 p633 p636 p726 p727 p737 p756 p840 p880 p928 p1225 p1229 p1232 p1287 p1289 p1293 p1325 : Prop)
    (h9410 : (¬ p126) ∨ (¬ p258) ∨ (¬ p345))
    (h21667 : p350 ∨ p345)
    (h23020 : p67 ∨ (¬ p134) ∨ (¬ p419) ∨ (¬ p2))
    (h22427 : p1287 ∨ (¬ p419) ∨ (¬ p2) ∨ (¬ p67))
    (h21106 : p124 ∨ p304)
    (h21316 : p64 ∨ p15)
    (h22908 : p5 ∨ p64)
    (h6604 : (¬ p15) ∨ (¬ p69))
    (h16477 : (¬ p15) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1325))
    (h18494 : (¬ p2) ∨ (¬ p5) ∨ (¬ p63) ∨ (¬ p419) ∨ (¬ p840) ∨ (¬ p928) ∨ (¬ p1325))
    (h22515 : p38 ∨ p64 ∨ p69)
    (h21790 : p616 ∨ p595)
    (h22211 : p85 ∨ p63)
    (h12953 : (¬ p15) ∨ (¬ p43) ∨ p63)
    (h18923 : (¬ p2) ∨ (¬ p19) ∨ (¬ p38) ∨ (¬ p134) ∨ (¬ p419))
    (h11954 : (¬ p14) ∨ (¬ p38) ∨ (¬ p226))
    (h22271 : p49 ∨ p43)
    (h20711 : p880 ∨ p14)
    (h23042 : p20 ∨ p19)
    (h23058 : (¬ p636) ∨ (¬ p20) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p595) ∨ (¬ p596) ∨ (¬ p350) ∨ p304)
    (h21879 : p636 ∨ p633)
    (h19747 : (¬ p2) ∨ (¬ p5) ∨ (¬ p344) ∨ (¬ p419) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1325))
    (h20942 : p495 ∨ p499)
    (h10583 : (¬ p15) ∨ (¬ p25) ∨ p499)
    (h22643 : (¬ p1229) ∨ (¬ p11) ∨ (¬ p126) ∨ (¬ p495) ∨ (¬ p85))
    (h22374 : p1229 ∨ p1232)
    (h10564 : p616 ∨ (¬ p1232) ∨ (¬ p1293))
    (h22540 : p1289 ∨ p1293)
    (h9341 : (¬ p1225) ∨ (¬ p1289) ∨ (¬ p1325))
    (h21572 : p161 ∨ p1225)
    (h18198 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p124) ∨ (¬ p161) ∨ (¬ p266) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1232))
    (h21112 : p726 ∨ p756)
    (h12183 : (¬ p344) ∨ (¬ p737) ∨ p756)
    (h23055 : p727 ∨ p737)
    (h23056 : (¬ p21) ∨ (¬ p727) ∨ (¬ p726) ∨ p499 ∨ (¬ p633) ∨ (¬ p880) ∨ (¬ p49) ∨ (¬ p15) ∨ (¬ p84) ∨ (¬ p840) ∨ (¬ p258) ∨ (¬ p237))
    (h22955 : p28 ∨ p21 ∨ p25)
    (h22956 : p32 ∨ p21 ∨ p25)
    (h22957 : p31 ∨ p21 ∨ p25)
    (h22958 : p30 ∨ p21 ∨ p25)
    (h23057 : (¬ p633) ∨ (¬ p28) ∨ (¬ p32) ∨ (¬ p31) ∨ (¬ p30) ∨ (¬ p880) ∨ (¬ p49) ∨ p19 ∨ (¬ p85) ∨ p616 ∨ (¬ p5) ∨ (¬ p15) ∨ (¬ p84) ∨ (¬ p533) ∨ (¬ p1325) ∨ (¬ p840) ∨ (¬ p258) ∨ (¬ p11) ∨ (¬ p344) ∨ (¬ p237) ∨ (¬ p266) ∨ (¬ p126) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2)) : p64 ∨ (¬ p84) ∨ (¬ p533) ∨ (¬ p928) ∨ (¬ p596) ∨ (¬ p226) ∨ (¬ p1325) ∨ (¬ p840) ∨ (¬ p258) ∨ (¬ p11) ∨ (¬ p344) ∨ (¬ p134) ∨ (¬ p237) ∨ (¬ p266) ∨ (¬ p126) ∨ p304 ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p64) := fun hu => hn (Or.inl hu)
  have u1 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))))
  have u18 : (¬ p345) := by
    rcases h9410 with q0 | q1 | q2
    · exact False.elim (q0 u14)
    · exact False.elim (q1 u8)
    · exact q2
  have u19 : p350 := by
    rcases h21667 with q0 | q1
    · exact q0
    · exact False.elim (u18 q1)
  have u20 : p67 := by
    rcases h23020 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u11)
    · exact False.elim (q2 u16)
    · exact False.elim (q3 u17)
  have u21 : p1287 := by
    rcases h22427 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u16)
    · exact False.elim (q2 u17)
    · exact False.elim (q3 u20)
  have u22 : p124 := by
    rcases h21106 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  have u23 : p15 := by
    rcases h21316 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u24 : p5 := by
    rcases h22908 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u25 : (¬ p69) := by
    rcases h6604 with q0 | q1
    · exact False.elim (q0 u23)
    · exact q1
  have u26 : (¬ p616) := by
    rcases h16477 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u23)
    · exact q1
    · exact False.elim (q2 u21)
    · exact False.elim (q3 u6)
  have u27 : (¬ p63) := by
    rcases h18494 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u17)
    · exact False.elim (q1 u24)
    · exact q2
    · exact False.elim (q3 u16)
    · exact False.elim (q4 u7)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u6)
  have u28 : p38 := by
    rcases h22515 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u25 q2)
  have u29 : p595 := by
    rcases h21790 with q0 | q1
    · exact False.elim (u26 q0)
    · exact q1
  have u30 : p85 := by
    rcases h22211 with q0 | q1
    · exact q0
    · exact False.elim (u27 q1)
  have u31 : (¬ p43) := by
    rcases h12953 with q0 | q1 | q2
    · exact False.elim (q0 u23)
    · exact q1
    · exact False.elim (u27 q2)
  have u32 : (¬ p19) := by
    rcases h18923 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u17)
    · exact q1
    · exact False.elim (q2 u28)
    · exact False.elim (q3 u11)
    · exact False.elim (q4 u16)
  have u33 : (¬ p14) := by
    rcases h11954 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u28)
    · exact False.elim (q2 u5)
  have u34 : p49 := by
    rcases h22271 with q0 | q1
    · exact q0
    · exact False.elim (u31 q1)
  have u35 : p880 := by
    rcases h20711 with q0 | q1
    · exact q0
    · exact False.elim (u33 q1)
  have u36 : p20 := by
    rcases h23042 with q0 | q1
    · exact q0
    · exact False.elim (u32 q1)
  have u37 : (¬ p636) := by
    rcases h23058 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact q0
    · exact False.elim (q1 u36)
    · exact False.elim (q2 u34)
    · exact False.elim (q3 u30)
    · exact False.elim (q4 u29)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u19)
    · exact False.elim (u15 q7)
  have u38 : p633 := by
    rcases h21879 with q0 | q1
    · exact False.elim (u37 q0)
    · exact q1
  have u39 : (¬ p499) := by
    rcases h19747 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u17)
    · exact False.elim (q1 u24)
    · exact False.elim (q2 u10)
    · exact False.elim (q3 u16)
    · exact q4
    · exact False.elim (q5 u38)
    · exact False.elim (q6 u6)
  have u40 : p495 := by
    rcases h20942 with q0 | q1
    · exact q0
    · exact False.elim (u39 q1)
  have u41 : (¬ p25) := by
    rcases h10583 with q0 | q1 | q2
    · exact False.elim (q0 u23)
    · exact q1
    · exact False.elim (u39 q2)
  have u42 : (¬ p1229) := by
    rcases h22643 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u9)
    · exact False.elim (q2 u14)
    · exact False.elim (q3 u40)
    · exact False.elim (q4 u30)
  have u43 : p1232 := by
    rcases h22374 with q0 | q1
    · exact False.elim (u42 q0)
    · exact q1
  have u44 : (¬ p1293) := by
    rcases h10564 with q0 | q1 | q2
    · exact False.elim (u26 q0)
    · exact False.elim (q1 u43)
    · exact q2
  have u45 : p1289 := by
    rcases h22540 with q0 | q1
    · exact q0
    · exact False.elim (u44 q1)
  have u46 : (¬ p1225) := by
    rcases h9341 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u45)
    · exact False.elim (q2 u6)
  have u47 : p161 := by
    rcases h21572 with q0 | q1
    · exact q0
    · exact False.elim (u46 q1)
  have u48 : (¬ p756) := by
    rcases h18198 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact False.elim (q0 u23)
    · exact False.elim (q1 u34)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u22)
    · exact False.elim (q4 u47)
    · exact False.elim (q5 u13)
    · exact False.elim (q6 u2)
    · exact q7
    · exact False.elim (q8 u43)
  have u49 : p726 := by
    rcases h21112 with q0 | q1
    · exact q0
    · exact False.elim (u48 q1)
  have u50 : (¬ p737) := by
    rcases h12183 with q0 | q1 | q2
    · exact False.elim (q0 u10)
    · exact q1
    · exact False.elim (u48 q2)
  have u51 : p727 := by
    rcases h23055 with q0 | q1
    · exact q0
    · exact False.elim (u50 q1)
  have u52 : (¬ p21) := by
    rcases h23056 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
    · exact q0
    · exact False.elim (q1 u51)
    · exact False.elim (q2 u49)
    · exact False.elim (u39 q3)
    · exact False.elim (q4 u38)
    · exact False.elim (q5 u35)
    · exact False.elim (q6 u34)
    · exact False.elim (q7 u23)
    · exact False.elim (q8 u1)
    · exact False.elim (q9 u7)
    · exact False.elim (q10 u8)
    · exact False.elim (q11 u12)
  have u53 : p28 := by
    rcases h22955 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u52 q1)
    · exact False.elim (u41 q2)
  have u54 : p32 := by
    rcases h22956 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u52 q1)
    · exact False.elim (u41 q2)
  have u55 : p31 := by
    rcases h22957 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u52 q1)
    · exact False.elim (u41 q2)
  have u56 : p30 := by
    rcases h22958 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u52 q1)
    · exact False.elim (u41 q2)
  rcases h23057 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17 | q18 | q19 | q20 | q21 | q22 | q23 | q24
  · exact False.elim (q0 u38)
  · exact False.elim (q1 u53)
  · exact False.elim (q2 u54)
  · exact False.elim (q3 u55)
  · exact False.elim (q4 u56)
  · exact False.elim (q5 u35)
  · exact False.elim (q6 u34)
  · exact False.elim (u32 q7)
  · exact False.elim (q8 u30)
  · exact False.elim (u26 q9)
  · exact False.elim (q10 u24)
  · exact False.elim (q11 u23)
  · exact False.elim (q12 u1)
  · exact False.elim (q13 u2)
  · exact False.elim (q14 u6)
  · exact False.elim (q15 u7)
  · exact False.elim (q16 u8)
  · exact False.elim (q17 u9)
  · exact False.elim (q18 u10)
  · exact False.elim (q19 u12)
  · exact False.elim (q20 u13)
  · exact False.elim (q21 u14)
  · exact False.elim (q22 u22)
  · exact False.elim (q23 u16)
  · exact False.elim (q24 u17)

theorem step23060 (p14 p15 p19 p20 p21 p25 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p49 p63 p84 p85 p124 p126 p161 p237 p258 p266 p304 p323 p344 p345 p350 p499 p533 p544 p581 p595 p596 p616 p633 p636 p726 p727 p737 p756 p840 p880 p1225 p1232 p1289 p1293 p1325 : Prop)
    (h21790 : p616 ∨ p595)
    (h9410 : (¬ p126) ∨ (¬ p258) ∨ (¬ p345))
    (h21667 : p350 ∨ p345)
    (h21106 : p124 ∨ p304)
    (h18247 : (¬ p63) ∨ (¬ p126) ∨ (¬ p581) ∨ (¬ p1232))
    (h10564 : p616 ∨ (¬ p1232) ∨ (¬ p1293))
    (h22211 : p85 ∨ p63)
    (h22540 : p1289 ∨ p1293)
    (h16532 : (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p323))
    (h16534 : (¬ p14) ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p544))
    (h9341 : (¬ p1225) ∨ (¬ p1289) ∨ (¬ p1325))
    (h23042 : p20 ∨ p19)
    (h20711 : p880 ∨ p14)
    (h21572 : p161 ∨ p1225)
    (h23058 : (¬ p636) ∨ (¬ p20) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p595) ∨ (¬ p596) ∨ (¬ p350) ∨ p304)
    (h18198 : (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p124) ∨ (¬ p161) ∨ (¬ p266) ∨ (¬ p533) ∨ (¬ p756) ∨ (¬ p1232))
    (h21879 : p636 ∨ p633)
    (h21112 : p726 ∨ p756)
    (h12183 : (¬ p344) ∨ (¬ p737) ∨ p756)
    (h16627 : (¬ p85) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633))
    (h23055 : p727 ∨ p737)
    (h10583 : (¬ p15) ∨ (¬ p25) ∨ p499)
    (h23056 : (¬ p21) ∨ (¬ p727) ∨ (¬ p726) ∨ p499 ∨ (¬ p633) ∨ (¬ p880) ∨ (¬ p49) ∨ (¬ p15) ∨ (¬ p84) ∨ (¬ p840) ∨ (¬ p258) ∨ (¬ p237))
    (h22957 : p31 ∨ p21 ∨ p25)
    (h22955 : p28 ∨ p21 ∨ p25)
    (h22956 : p32 ∨ p21 ∨ p25)
    (h22958 : p30 ∨ p21 ∨ p25)
    (h12 : p19 ∨ p21 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32))
    (h110 : p29 ∨ p33)
    (h111 : p29 ∨ p34)
    (h112 : p29 ∨ p35)
    (h113 : p29 ∨ p36)
    (h114 : p29 ∨ p37)
    (h36 : p21 ∨ p25 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : (¬ p1232) ∨ p616 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p533) ∨ (¬ p596) ∨ (¬ p581) ∨ (¬ p323) ∨ (¬ p544) ∨ (¬ p1325) ∨ (¬ p840) ∨ (¬ p258) ∨ (¬ p344) ∨ (¬ p237) ∨ (¬ p266) ∨ (¬ p126) ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p616) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))))
  have u18 : p595 := by
    rcases h21790 with q0 | q1
    · exact False.elim (u1 q0)
    · exact q1
  have u19 : (¬ p345) := by
    rcases h9410 with q0 | q1 | q2
    · exact False.elim (q0 u16)
    · exact False.elim (q1 u12)
    · exact q2
  have u20 : p350 := by
    rcases h21667 with q0 | q1
    · exact q0
    · exact False.elim (u19 q1)
  have u21 : p124 := by
    rcases h21106 with q0 | q1
    · exact q0
    · exact False.elim (u17 q1)
  have u22 : (¬ p63) := by
    rcases h18247 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u16)
    · exact False.elim (q2 u7)
    · exact False.elim (q3 u0)
  have u23 : (¬ p1293) := by
    rcases h10564 with q0 | q1 | q2
    · exact False.elim (u1 q0)
    · exact False.elim (q1 u0)
    · exact q2
  have u24 : p85 := by
    rcases h22211 with q0 | q1
    · exact q0
    · exact False.elim (u22 q1)
  have u25 : p1289 := by
    rcases h22540 with q0 | q1
    · exact q0
    · exact False.elim (u23 q1)
  have u26 : (¬ p19) := by
    rcases h16532 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u24)
    · exact False.elim (q3 u8)
  have u27 : (¬ p14) := by
    rcases h16534 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u24)
    · exact False.elim (q3 u9)
  have u28 : (¬ p1225) := by
    rcases h9341 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u25)
    · exact False.elim (q2 u10)
  have u29 : p20 := by
    rcases h23042 with q0 | q1
    · exact q0
    · exact False.elim (u26 q1)
  have u30 : p880 := by
    rcases h20711 with q0 | q1
    · exact q0
    · exact False.elim (u27 q1)
  have u31 : p161 := by
    rcases h21572 with q0 | q1
    · exact q0
    · exact False.elim (u28 q1)
  have u32 : (¬ p636) := by
    rcases h23058 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact q0
    · exact False.elim (q1 u29)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u24)
    · exact False.elim (q4 u18)
    · exact False.elim (q5 u6)
    · exact False.elim (q6 u20)
    · exact False.elim (u17 q7)
  have u33 : (¬ p756) := by
    rcases h18198 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact False.elim (q0 u2)
    · exact False.elim (q1 u3)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u21)
    · exact False.elim (q4 u31)
    · exact False.elim (q5 u15)
    · exact False.elim (q6 u5)
    · exact q7
    · exact False.elim (q8 u0)
  have u34 : p633 := by
    rcases h21879 with q0 | q1
    · exact False.elim (u32 q0)
    · exact q1
  have u35 : p726 := by
    rcases h21112 with q0 | q1
    · exact q0
    · exact False.elim (u33 q1)
  have u36 : (¬ p737) := by
    rcases h12183 with q0 | q1 | q2
    · exact False.elim (q0 u13)
    · exact q1
    · exact False.elim (u33 q2)
  have u37 : (¬ p499) := by
    rcases h16627 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u24)
    · exact False.elim (q1 u13)
    · exact q2
    · exact False.elim (q3 u34)
  have u38 : p727 := by
    rcases h23055 with q0 | q1
    · exact q0
    · exact False.elim (u36 q1)
  have u39 : (¬ p25) := by
    rcases h10583 with q0 | q1 | q2
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (u37 q2)
  have u40 : (¬ p21) := by
    rcases h23056 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
    · exact q0
    · exact False.elim (q1 u38)
    · exact False.elim (q2 u35)
    · exact False.elim (u37 q3)
    · exact False.elim (q4 u34)
    · exact False.elim (q5 u30)
    · exact False.elim (q6 u3)
    · exact False.elim (q7 u2)
    · exact False.elim (q8 u4)
    · exact False.elim (q9 u11)
    · exact False.elim (q10 u12)
    · exact False.elim (q11 u14)
  have u41 : p31 := by
    rcases h22957 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u40 q1)
    · exact False.elim (u39 q2)
  have u42 : p28 := by
    rcases h22955 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u40 q1)
    · exact False.elim (u39 q2)
  have u43 : p32 := by
    rcases h22956 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u40 q1)
    · exact False.elim (u39 q2)
  have u44 : p30 := by
    rcases h22958 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u40 q1)
    · exact False.elim (u39 q2)
  have u45 : (¬ p29) := by
    rcases h12 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u26 q0)
    · exact False.elim (u40 q1)
    · exact False.elim (q2 u42)
    · exact q3
    · exact False.elim (q4 u44)
    · exact False.elim (q5 u41)
    · exact False.elim (q6 u43)
  have u46 : p33 := by
    rcases h110 with q0 | q1
    · exact False.elim (u45 q0)
    · exact q1
  have u47 : p34 := by
    rcases h111 with q0 | q1
    · exact False.elim (u45 q0)
    · exact q1
  have u48 : p35 := by
    rcases h112 with q0 | q1
    · exact False.elim (u45 q0)
    · exact q1
  have u49 : p36 := by
    rcases h113 with q0 | q1
    · exact False.elim (u45 q0)
    · exact q1
  have u50 : p37 := by
    rcases h114 with q0 | q1
    · exact False.elim (u45 q0)
    · exact q1
  rcases h36 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u40 q0)
  · exact False.elim (u39 q1)
  · exact False.elim (q2 u46)
  · exact False.elim (q3 u47)
  · exact False.elim (q4 u48)
  · exact False.elim (q5 u49)
  · exact False.elim (q6 u50)

theorem step23062 (p11 p15 p19 p20 p49 p85 p126 p304 p323 p344 p350 p495 p499 p595 p596 p633 p636 p1229 : Prop)
    (h16532 : (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p323))
    (h22643 : (¬ p1229) ∨ (¬ p11) ∨ (¬ p126) ∨ (¬ p495) ∨ (¬ p85))
    (h23042 : p20 ∨ p19)
    (h20942 : p495 ∨ p499)
    (h23058 : (¬ p636) ∨ (¬ p20) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p595) ∨ (¬ p596) ∨ (¬ p350) ∨ p304)
    (h16627 : (¬ p85) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633))
    (h21879 : p636 ∨ p633) : (¬ p85) ∨ (¬ p1229) ∨ (¬ p595) ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p596) ∨ (¬ p323) ∨ (¬ p350) ∨ (¬ p11) ∨ (¬ p344) ∨ (¬ p126) ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : (¬ p19) := by
    rcases h16532 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u3)
    · exact q1
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u6)
  have u13 : (¬ p495) := by
    rcases h22643 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u8)
    · exact False.elim (q2 u10)
    · exact q3
    · exact False.elim (q4 u0)
  have u14 : p20 := by
    rcases h23042 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u15 : p499 := by
    rcases h20942 with q0 | q1
    · exact False.elim (u13 q0)
    · exact q1
  have u16 : (¬ p636) := by
    rcases h23058 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact q0
    · exact False.elim (q1 u14)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u2)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u7)
    · exact False.elim (u11 q7)
  have u17 : (¬ p633) := by
    rcases h16627 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u9)
    · exact False.elim (q2 u15)
    · exact q3
  rcases h21879 with q0 | q1
  · exact False.elim (u16 q0)
  · exact False.elim (u17 q1)

theorem step23063 (p5 p68 p73 p74 p75 p76 p77 p82 : Prop)
    (h373 : p73 ∨ p82)
    (h378 : p74 ∨ p82)
    (h383 : p75 ∨ p82)
    (h277 : p5 ∨ p68 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p82 ∨ (¬ p76) ∨ p68 ∨ (¬ p77) ∨ p5 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p82) := fun hu => hn (Or.inl hu)
  have u1 : p76 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p68) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p77 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p5) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p73 := by
    rcases h373 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p74 := by
    rcases h378 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p75 := by
    rcases h383 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h277 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u3)

theorem step23064 (p5 p68 p73 p74 p75 p76 p77 p81 : Prop)
    (h372 : p73 ∨ p81)
    (h377 : p74 ∨ p81)
    (h382 : p75 ∨ p81)
    (h277 : p5 ∨ p68 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p81 ∨ (¬ p76) ∨ p68 ∨ (¬ p77) ∨ p5 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p81) := fun hu => hn (Or.inl hu)
  have u1 : p76 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p68) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p77 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p5) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p73 := by
    rcases h372 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p74 := by
    rcases h377 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p75 := by
    rcases h382 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h277 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u3)

theorem step23065 (p5 p68 p73 p74 p75 p76 p77 p80 : Prop)
    (h371 : p73 ∨ p80)
    (h376 : p74 ∨ p80)
    (h381 : p75 ∨ p80)
    (h277 : p5 ∨ p68 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p80 ∨ (¬ p76) ∨ p68 ∨ (¬ p77) ∨ p5 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p80) := fun hu => hn (Or.inl hu)
  have u1 : p76 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p68) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p77 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p5) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p73 := by
    rcases h371 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p74 := by
    rcases h376 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p75 := by
    rcases h381 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h277 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u3)

theorem step23066 (p5 p68 p73 p74 p75 p76 p77 p79 : Prop)
    (h370 : p73 ∨ p79)
    (h375 : p74 ∨ p79)
    (h380 : p75 ∨ p79)
    (h277 : p5 ∨ p68 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p79 ∨ (¬ p76) ∨ p68 ∨ (¬ p77) ∨ p5 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p79) := fun hu => hn (Or.inl hu)
  have u1 : p76 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p68) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p77 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p5) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p73 := by
    rcases h370 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p74 := by
    rcases h375 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p75 := by
    rcases h380 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h277 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u3)

theorem step23067 (p5 p68 p69 p73 p74 p75 p76 p77 p78 p79 p80 p81 p82 : Prop)
    (h22900 : p77 ∨ p5 ∨ p69)
    (h23063 : p82 ∨ (¬ p76) ∨ p68 ∨ (¬ p77) ∨ p5)
    (h23064 : p81 ∨ (¬ p76) ∨ p68 ∨ (¬ p77) ∨ p5)
    (h23065 : p80 ∨ (¬ p76) ∨ p68 ∨ (¬ p77) ∨ p5)
    (h23066 : p79 ∨ (¬ p76) ∨ p68 ∨ (¬ p77) ∨ p5)
    (h307 : p5 ∨ p69 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82))
    (h369 : p73 ∨ p78)
    (h374 : p74 ∨ p78)
    (h379 : p75 ∨ p78)
    (h277 : p5 ∨ p68 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : (¬ p76) ∨ p68 ∨ p5 ∨ p69 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p76 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p68) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p5) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p69) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p77 := by
    rcases h22900 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u2 q1)
    · exact False.elim (u3 q2)
  have u5 : p82 := by
    rcases h23063 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (q3 u4)
    · exact False.elim (u2 q4)
  have u6 : p81 := by
    rcases h23064 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (q3 u4)
    · exact False.elim (u2 q4)
  have u7 : p80 := by
    rcases h23065 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (q3 u4)
    · exact False.elim (u2 q4)
  have u8 : p79 := by
    rcases h23066 with q0 | q1 | q2 | q3 | q4
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (q3 u4)
    · exact False.elim (u2 q4)
  have u9 : (¬ p78) := by
    rcases h307 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact q2
    · exact False.elim (q3 u8)
    · exact False.elim (q4 u7)
    · exact False.elim (q5 u6)
    · exact False.elim (q6 u5)
  have u10 : p73 := by
    rcases h369 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u11 : p74 := by
    rcases h374 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  have u12 : p75 := by
    rcases h379 with q0 | q1
    · exact q0
    · exact False.elim (u9 q1)
  rcases h277 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u10)
  · exact False.elim (q3 u11)
  · exact False.elim (q4 u12)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u4)

theorem step23068 (p5 p68 p69 p76 p78 p79 p80 p81 p82 : Prop)
    (h23067 : (¬ p76) ∨ p68 ∨ p5 ∨ p69)
    (h384 : p76 ∨ p78)
    (h385 : p76 ∨ p79)
    (h386 : p76 ∨ p80)
    (h387 : p76 ∨ p81)
    (h388 : p76 ∨ p82)
    (h302 : p5 ∨ p68 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82)) : p68 ∨ p69 ∨ p5 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p68) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p69) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p5) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p76) := by
    rcases h23067 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u4 : p78 := by
    rcases h384 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u5 : p79 := by
    rcases h385 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u6 : p80 := by
    rcases h386 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u7 : p81 := by
    rcases h387 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u8 : p82 := by
    rcases h388 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  rcases h302 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step23069 (p2 p5 p11 p15 p39 p49 p63 p64 p68 p69 p84 p85 p126 p234 p237 p258 p266 p304 p323 p344 p345 p350 p419 p533 p544 p581 p595 p596 p616 p840 p1188 p1229 p1232 p1287 p1325 : Prop)
    (h9410 : (¬ p126) ∨ (¬ p258) ∨ (¬ p345))
    (h21667 : p350 ∨ p345)
    (h6604 : (¬ p15) ∨ (¬ p69))
    (h16477 : (¬ p15) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1325))
    (h21790 : p616 ∨ p595)
    (h23060 : (¬ p1232) ∨ p616 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p84) ∨ (¬ p533) ∨ (¬ p596) ∨ (¬ p581) ∨ (¬ p323) ∨ (¬ p544) ∨ (¬ p1325) ∨ (¬ p840) ∨ (¬ p258) ∨ (¬ p344) ∨ (¬ p237) ∨ (¬ p266) ∨ (¬ p126) ∨ p304)
    (h22374 : p1229 ∨ p1232)
    (h23062 : (¬ p85) ∨ (¬ p1229) ∨ (¬ p595) ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p596) ∨ (¬ p323) ∨ (¬ p350) ∨ (¬ p11) ∨ (¬ p344) ∨ (¬ p126) ∨ p304)
    (h22211 : p85 ∨ p63)
    (h18250 : (¬ p2) ∨ (¬ p5) ∨ (¬ p63) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p581) ∨ (¬ p1325))
    (h20442 : (¬ p2) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p64) ∨ (¬ p234))
    (h22095 : p1188 ∨ p234)
    (h10823 : (¬ p64) ∨ (¬ p68) ∨ (¬ p595) ∨ (¬ p1188))
    (h23068 : p68 ∨ p69 ∨ p5) : (¬ p15) ∨ (¬ p49) ∨ (¬ p64) ∨ (¬ p84) ∨ (¬ p533) ∨ (¬ p596) ∨ (¬ p581) ∨ (¬ p39) ∨ (¬ p323) ∨ (¬ p544) ∨ (¬ p1325) ∨ (¬ p840) ∨ (¬ p258) ∨ (¬ p11) ∨ (¬ p344) ∨ (¬ p1287) ∨ (¬ p237) ∨ (¬ p266) ∨ (¬ p126) ∨ p304 ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))
  have u17 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))
  have u18 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))
  have u19 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))))))
  have u20 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))))))))
  have u21 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))))))))))))
  have u22 : (¬ p345) := by
    rcases h9410 with q0 | q1 | q2
    · exact False.elim (q0 u18)
    · exact False.elim (q1 u12)
    · exact q2
  have u23 : p350 := by
    rcases h21667 with q0 | q1
    · exact q0
    · exact False.elim (u22 q1)
  have u24 : (¬ p69) := by
    rcases h6604 with q0 | q1
    · exact False.elim (q0 u0)
    · exact q1
  have u25 : (¬ p616) := by
    rcases h16477 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u15)
    · exact False.elim (q3 u10)
  have u26 : p595 := by
    rcases h21790 with q0 | q1
    · exact False.elim (u25 q0)
    · exact q1
  have u27 : (¬ p1232) := by
    rcases h23060 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17
    · exact q0
    · exact False.elim (u25 q1)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
    · exact False.elim (q7 u6)
    · exact False.elim (q8 u8)
    · exact False.elim (q9 u9)
    · exact False.elim (q10 u10)
    · exact False.elim (q11 u11)
    · exact False.elim (q12 u12)
    · exact False.elim (q13 u14)
    · exact False.elim (q14 u16)
    · exact False.elim (q15 u17)
    · exact False.elim (q16 u18)
    · exact False.elim (u19 q17)
  have u28 : p1229 := by
    rcases h22374 with q0 | q1
    · exact q0
    · exact False.elim (u27 q1)
  have u29 : (¬ p85) := by
    rcases h23062 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
    · exact q0
    · exact False.elim (q1 u28)
    · exact False.elim (q2 u26)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u8)
    · exact False.elim (q7 u23)
    · exact False.elim (q8 u13)
    · exact False.elim (q9 u14)
    · exact False.elim (q10 u18)
    · exact False.elim (u19 q11)
  have u30 : p63 := by
    rcases h22211 with q0 | q1
    · exact False.elim (u29 q0)
    · exact q1
  have u31 : (¬ p5) := by
    rcases h18250 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u21)
    · exact q1
    · exact False.elim (q2 u30)
    · exact False.elim (q3 u18)
    · exact False.elim (q4 u20)
    · exact False.elim (q5 u6)
    · exact False.elim (q6 u10)
  have u32 : (¬ p234) := by
    rcases h20442 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u21)
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u30)
    · exact False.elim (q3 u2)
    · exact q4
  have u33 : p1188 := by
    rcases h22095 with q0 | q1
    · exact q0
    · exact False.elim (u32 q1)
  have u34 : (¬ p68) := by
    rcases h10823 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u26)
    · exact False.elim (q3 u33)
  rcases h23068 with q0 | q1 | q2
  · exact False.elim (u34 q0)
  · exact False.elim (u24 q1)
  · exact False.elim (u31 q2)

theorem step23070 (p18 p25 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 : Prop)
    (h16 : p18 ∨ p25 ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ p31) ∨ (¬ p32))
    (h110 : p29 ∨ p33)
    (h111 : p29 ∨ p34)
    (h112 : p29 ∨ p35)
    (h113 : p29 ∨ p36)
    (h114 : p29 ∨ p37)
    (h41 : p18 ∨ p25 ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p36) ∨ (¬ p37)) : (¬ p30) ∨ (¬ p31) ∨ p25 ∨ p18 ∨ (¬ p32) ∨ (¬ p28) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p30 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p31 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p25) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p18) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p32 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p28 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p29) := by
    rcases h16 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u5)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u4)
  have u7 : p33 := by
    rcases h110 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p34 := by
    rcases h111 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p35 := by
    rcases h112 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p36 := by
    rcases h113 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p37 := by
    rcases h114 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h41 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step23071 (p2 p5 p6 p18 p19 p21 p25 p28 p30 p31 p32 p44 p50 p63 p64 p69 p86 p101 p102 p124 p134 p136 p142 p188 p192 p211 p234 p258 p266 p419 p421 p424 p499 p595 p600 p796 p840 p928 p1187 p1192 p1325 : Prop)
    (h11559 : (¬ p188) ∨ p211 ∨ (¬ p266))
    (h21387 : p188 ∨ p192)
    (h23019 : p6 ∨ p211)
    (h9328 : (¬ p6) ∨ (¬ p142) ∨ (¬ p192))
    (h22176 : p142 ∨ p134)
    (h21927 : p136 ∨ p142)
    (h11962 : (¬ p2) ∨ (¬ p192) ∨ p796)
    (h11964 : (¬ p2) ∨ (¬ p192) ∨ (¬ p424))
    (h16623 : p5 ∨ (¬ p69))
    (h17164 : (¬ p69) ∨ (¬ p419) ∨ (¬ p1187) ∨ (¬ p1325))
    (h18494 : (¬ p2) ∨ (¬ p5) ∨ (¬ p63) ∨ (¬ p419) ∨ (¬ p840) ∨ (¬ p928) ∨ (¬ p1325))
    (h20796 : p1192 ∨ p1187)
    (h21531 : p1187 ∨ p234)
    (h21852 : p86 ∨ p63)
    (h22821 : (¬ p234) ∨ (¬ p124) ∨ (¬ p2) ∨ (¬ p18) ∨ (¬ p64) ∨ (¬ p86) ∨ (¬ p258) ∨ (¬ p266))
    (h11331 : (¬ p44) ∨ (¬ p234) ∨ p424)
    (h22840 : p19 ∨ p18)
    (h22877 : p50 ∨ p44)
    (h16817 : (¬ p19) ∨ (¬ p50) ∨ (¬ p102) ∨ (¬ p136) ∨ (¬ p258))
    (h16757 : (¬ p50) ∨ (¬ p69) ∨ (¬ p595) ∨ (¬ p796) ∨ (¬ p1192))
    (h21623 : p101 ∨ p102)
    (h10590 : (¬ p499) ∨ p595 ∨ (¬ p600))
    (h20878 : p421 ∨ p499)
    (h9710 : (¬ p21) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p421))
    (h16814 : (¬ p25) ∨ (¬ p50) ∨ (¬ p101) ∨ (¬ p124) ∨ (¬ p134) ∨ (¬ p421))
    (h22955 : p28 ∨ p21 ∨ p25)
    (h22956 : p32 ∨ p21 ∨ p25)
    (h22958 : p30 ∨ p21 ∨ p25)
    (h22957 : p31 ∨ p21 ∨ p25)
    (h23070 : (¬ p30) ∨ (¬ p31) ∨ p25 ∨ p18 ∨ (¬ p32) ∨ (¬ p28)) : (¬ p69) ∨ (¬ p64) ∨ (¬ p928) ∨ (¬ p600) ∨ (¬ p1325) ∨ (¬ p840) ∨ (¬ p258) ∨ p211 ∨ (¬ p266) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p211) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))))
  have u12 : (¬ p188) := by
    rcases h11559 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u7 q1)
    · exact False.elim (q2 u8)
  have u13 : p192 := by
    rcases h21387 with q0 | q1
    · exact False.elim (u12 q0)
    · exact q1
  have u14 : p6 := by
    rcases h23019 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u15 : (¬ p142) := by
    rcases h9328 with q0 | q1 | q2
    · exact False.elim (q0 u14)
    · exact q1
    · exact False.elim (q2 u13)
  have u16 : p134 := by
    rcases h22176 with q0 | q1
    · exact False.elim (u15 q0)
    · exact q1
  have u17 : p136 := by
    rcases h21927 with q0 | q1
    · exact q0
    · exact False.elim (u15 q1)
  have u18 : p796 := by
    rcases h11962 with q0 | q1 | q2
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u13)
    · exact q2
  have u19 : (¬ p424) := by
    rcases h11964 with q0 | q1 | q2
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u13)
    · exact q2
  have u20 : p5 := by
    rcases h16623 with q0 | q1
    · exact q0
    · exact False.elim (q1 u0)
  have u21 : (¬ p1187) := by
    rcases h17164 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u10)
    · exact q2
    · exact False.elim (q3 u4)
  have u22 : (¬ p63) := by
    rcases h18494 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u11)
    · exact False.elim (q1 u20)
    · exact q2
    · exact False.elim (q3 u10)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u2)
    · exact False.elim (q6 u4)
  have u23 : p1192 := by
    rcases h20796 with q0 | q1
    · exact q0
    · exact False.elim (u21 q1)
  have u24 : p234 := by
    rcases h21531 with q0 | q1
    · exact False.elim (u21 q0)
    · exact q1
  have u25 : p86 := by
    rcases h21852 with q0 | q1
    · exact q0
    · exact False.elim (u22 q1)
  have u26 : (¬ p18) := by
    rcases h22821 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u24)
    · exact False.elim (q1 u9)
    · exact False.elim (q2 u11)
    · exact q3
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u25)
    · exact False.elim (q6 u6)
    · exact False.elim (q7 u8)
  have u27 : (¬ p44) := by
    rcases h11331 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u24)
    · exact False.elim (u19 q2)
  have u28 : p19 := by
    rcases h22840 with q0 | q1
    · exact q0
    · exact False.elim (u26 q1)
  have u29 : p50 := by
    rcases h22877 with q0 | q1
    · exact q0
    · exact False.elim (u27 q1)
  have u30 : (¬ p102) := by
    rcases h16817 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u28)
    · exact False.elim (q1 u29)
    · exact q2
    · exact False.elim (q3 u17)
    · exact False.elim (q4 u6)
  have u31 : (¬ p595) := by
    rcases h16757 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u29)
    · exact False.elim (q1 u0)
    · exact q2
    · exact False.elim (q3 u18)
    · exact False.elim (q4 u23)
  have u32 : p101 := by
    rcases h21623 with q0 | q1
    · exact q0
    · exact False.elim (u30 q1)
  have u33 : (¬ p499) := by
    rcases h10590 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u31 q1)
    · exact False.elim (q2 u3)
  have u34 : p421 := by
    rcases h20878 with q0 | q1
    · exact q0
    · exact False.elim (u33 q1)
  have u35 : (¬ p21) := by
    rcases h9710 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u32)
    · exact False.elim (q2 u9)
    · exact False.elim (q3 u34)
  have u36 : (¬ p25) := by
    rcases h16814 with q0 | q1 | q2 | q3 | q4 | q5
    · exact q0
    · exact False.elim (q1 u29)
    · exact False.elim (q2 u32)
    · exact False.elim (q3 u9)
    · exact False.elim (q4 u16)
    · exact False.elim (q5 u34)
  have u37 : p28 := by
    rcases h22955 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u35 q1)
    · exact False.elim (u36 q2)
  have u38 : p32 := by
    rcases h22956 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u35 q1)
    · exact False.elim (u36 q2)
  have u39 : p30 := by
    rcases h22958 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u35 q1)
    · exact False.elim (u36 q2)
  have u40 : p31 := by
    rcases h22957 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u35 q1)
    · exact False.elim (u36 q2)
  rcases h23070 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u39)
  · exact False.elim (q1 u40)
  · exact False.elim (u36 q2)
  · exact False.elim (u26 q3)
  · exact False.elim (q4 u38)
  · exact False.elim (q5 u37)

theorem step23072 (p1 p2 p5 p6 p11 p15 p39 p41 p43 p45 p49 p63 p64 p67 p68 p69 p84 p124 p126 p134 p142 p188 p192 p194 p211 p225 p226 p234 p237 p258 p266 p304 p323 p344 p419 p533 p540 p544 p581 p595 p596 p600 p616 p796 p840 p918 p928 p983 p1188 p1287 p1325 : Prop)
    (h11559 : (¬ p188) ∨ p211 ∨ (¬ p266))
    (h21387 : p188 ∨ p192)
    (h11962 : (¬ p2) ∨ (¬ p192) ∨ p796)
    (h17024 : (¬ p419) ∨ (¬ p796) ∨ (¬ p983) ∨ (¬ p1325))
    (h23049 : p533 ∨ p983)
    (h17502 : (¬ p126) ∨ (¬ p237) ∨ (¬ p581) ∨ (¬ p918))
    (h22025 : p918 ∨ p928)
    (h22615 : p194 ∨ p188)
    (h17168 : (¬ p2) ∨ (¬ p194) ∨ (¬ p237) ∨ (¬ p540) ∨ (¬ p840))
    (h21071 : p540 ∨ p544)
    (h11784 : (¬ p225) ∨ (¬ p544))
    (h21617 : p1 ∨ p225)
    (h11951 : (¬ p1) ∨ (¬ p2) ∨ p226)
    (h18276 : (¬ p2) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p419) ∨ (¬ p1325))
    (h21444 : p41 ∨ p45)
    (h21001 : p39 ∨ (¬ p41))
    (h23019 : p6 ∨ p211)
    (h9328 : (¬ p6) ∨ (¬ p142) ∨ (¬ p192))
    (h22176 : p142 ∨ p134)
    (h23020 : p67 ∨ (¬ p134) ∨ (¬ p419) ∨ (¬ p2))
    (h22427 : p1287 ∨ (¬ p419) ∨ (¬ p2) ∨ (¬ p67))
    (h21106 : p124 ∨ p304)
    (h23059 : p64 ∨ (¬ p84) ∨ (¬ p533) ∨ (¬ p928) ∨ (¬ p596) ∨ (¬ p226) ∨ (¬ p1325) ∨ (¬ p840) ∨ (¬ p258) ∨ (¬ p11) ∨ (¬ p344) ∨ (¬ p134) ∨ (¬ p237) ∨ (¬ p266) ∨ (¬ p126) ∨ p304 ∨ (¬ p419) ∨ (¬ p2))
    (h23071 : (¬ p69) ∨ (¬ p64) ∨ (¬ p928) ∨ (¬ p600) ∨ (¬ p1325) ∨ (¬ p840) ∨ (¬ p258) ∨ p211 ∨ (¬ p266) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2))
    (h21946 : p69 ∨ p15)
    (h16477 : (¬ p15) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1325))
    (h23069 : (¬ p15) ∨ (¬ p49) ∨ (¬ p64) ∨ (¬ p84) ∨ (¬ p533) ∨ (¬ p596) ∨ (¬ p581) ∨ (¬ p39) ∨ (¬ p323) ∨ (¬ p544) ∨ (¬ p1325) ∨ (¬ p840) ∨ (¬ p258) ∨ (¬ p11) ∨ (¬ p344) ∨ (¬ p1287) ∨ (¬ p237) ∨ (¬ p266) ∨ (¬ p126) ∨ p304 ∨ (¬ p419) ∨ (¬ p2))
    (h21790 : p616 ∨ p595)
    (h22271 : p49 ∨ p43)
    (h12953 : (¬ p15) ∨ (¬ p43) ∨ p63)
    (h18250 : (¬ p2) ∨ (¬ p5) ∨ (¬ p63) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p581) ∨ (¬ p1325))
    (h20442 : (¬ p2) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p64) ∨ (¬ p234))
    (h23068 : p68 ∨ p69 ∨ p5)
    (h22095 : p1188 ∨ p234)
    (h10823 : (¬ p64) ∨ (¬ p68) ∨ (¬ p595) ∨ (¬ p1188)) : (¬ p84) ∨ (¬ p596) ∨ (¬ p600) ∨ (¬ p581) ∨ (¬ p323) ∨ (¬ p1325) ∨ (¬ p840) ∨ (¬ p258) ∨ (¬ p11) ∨ (¬ p344) ∨ p211 ∨ (¬ p237) ∨ (¬ p266) ∨ (¬ p126) ∨ p304 ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p600 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))
  have u10 : (¬ p211) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))
  have u11 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))
  have u12 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))
  have u13 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))
  have u14 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))))))))
  have u15 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))))))))))
  have u16 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))))))))))
  have u17 : (¬ p188) := by
    rcases h11559 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u10 q1)
    · exact False.elim (q2 u12)
  have u18 : p192 := by
    rcases h21387 with q0 | q1
    · exact False.elim (u17 q0)
    · exact q1
  have u19 : p796 := by
    rcases h11962 with q0 | q1 | q2
    · exact False.elim (q0 u16)
    · exact False.elim (q1 u18)
    · exact q2
  have u20 : (¬ p983) := by
    rcases h17024 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u15)
    · exact False.elim (q1 u19)
    · exact q2
    · exact False.elim (q3 u5)
  have u21 : p533 := by
    rcases h23049 with q0 | q1
    · exact q0
    · exact False.elim (u20 q1)
  have u22 : (¬ p918) := by
    rcases h17502 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u13)
    · exact False.elim (q1 u11)
    · exact False.elim (q2 u3)
    · exact q3
  have u23 : p928 := by
    rcases h22025 with q0 | q1
    · exact False.elim (u22 q0)
    · exact q1
  have u24 : p194 := by
    rcases h22615 with q0 | q1
    · exact q0
    · exact False.elim (u17 q1)
  have u25 : (¬ p540) := by
    rcases h17168 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u16)
    · exact False.elim (q1 u24)
    · exact False.elim (q2 u11)
    · exact q3
    · exact False.elim (q4 u6)
  have u26 : p544 := by
    rcases h21071 with q0 | q1
    · exact False.elim (u25 q0)
    · exact q1
  have u27 : (¬ p225) := by
    rcases h11784 with q0 | q1
    · exact q0
    · exact False.elim (q1 u26)
  have u28 : p1 := by
    rcases h21617 with q0 | q1
    · exact q0
    · exact False.elim (u27 q1)
  have u29 : p226 := by
    rcases h11951 with q0 | q1 | q2
    · exact False.elim (q0 u28)
    · exact False.elim (q1 u16)
    · exact q2
  have u30 : (¬ p45) := by
    rcases h18276 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u16)
    · exact q1
    · exact False.elim (q2 u18)
    · exact False.elim (q3 u15)
    · exact False.elim (q4 u5)
  have u31 : p41 := by
    rcases h21444 with q0 | q1
    · exact q0
    · exact False.elim (u30 q1)
  have u32 : p39 := by
    rcases h21001 with q0 | q1
    · exact q0
    · exact False.elim (q1 u31)
  have u33 : p6 := by
    rcases h23019 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u34 : (¬ p142) := by
    rcases h9328 with q0 | q1 | q2
    · exact False.elim (q0 u33)
    · exact q1
    · exact False.elim (q2 u18)
  have u35 : p134 := by
    rcases h22176 with q0 | q1
    · exact False.elim (u34 q0)
    · exact q1
  have u36 : p67 := by
    rcases h23020 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u35)
    · exact False.elim (q2 u15)
    · exact False.elim (q3 u16)
  have u37 : p1287 := by
    rcases h22427 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u15)
    · exact False.elim (q2 u16)
    · exact False.elim (q3 u36)
  have u38 : p124 := by
    rcases h21106 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  have u39 : p64 := by
    rcases h23059 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u21)
    · exact False.elim (q3 u23)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u29)
    · exact False.elim (q6 u5)
    · exact False.elim (q7 u6)
    · exact False.elim (q8 u7)
    · exact False.elim (q9 u8)
    · exact False.elim (q10 u9)
    · exact False.elim (q11 u35)
    · exact False.elim (q12 u11)
    · exact False.elim (q13 u12)
    · exact False.elim (q14 u13)
    · exact False.elim (u14 q15)
    · exact False.elim (q16 u15)
    · exact False.elim (q17 u16)
  have u40 : (¬ p69) := by
    rcases h23071 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
    · exact q0
    · exact False.elim (q1 u39)
    · exact False.elim (q2 u23)
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact False.elim (q6 u7)
    · exact False.elim (u10 q7)
    · exact False.elim (q8 u12)
    · exact False.elim (q9 u38)
    · exact False.elim (q10 u15)
    · exact False.elim (q11 u16)
  have u41 : p15 := by
    rcases h21946 with q0 | q1
    · exact False.elim (u40 q0)
    · exact q1
  have u42 : (¬ p616) := by
    rcases h16477 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u41)
    · exact q1
    · exact False.elim (q2 u37)
    · exact False.elim (q3 u5)
  have u43 : (¬ p49) := by
    rcases h23069 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16 | q17 | q18 | q19 | q20 | q21
    · exact False.elim (q0 u41)
    · exact q1
    · exact False.elim (q2 u39)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u21)
    · exact False.elim (q5 u1)
    · exact False.elim (q6 u3)
    · exact False.elim (q7 u32)
    · exact False.elim (q8 u4)
    · exact False.elim (q9 u26)
    · exact False.elim (q10 u5)
    · exact False.elim (q11 u6)
    · exact False.elim (q12 u7)
    · exact False.elim (q13 u8)
    · exact False.elim (q14 u9)
    · exact False.elim (q15 u37)
    · exact False.elim (q16 u11)
    · exact False.elim (q17 u12)
    · exact False.elim (q18 u13)
    · exact False.elim (u14 q19)
    · exact False.elim (q20 u15)
    · exact False.elim (q21 u16)
  have u44 : p595 := by
    rcases h21790 with q0 | q1
    · exact False.elim (u42 q0)
    · exact q1
  have u45 : p43 := by
    rcases h22271 with q0 | q1
    · exact False.elim (u43 q0)
    · exact q1
  have u46 : p63 := by
    rcases h12953 with q0 | q1 | q2
    · exact False.elim (q0 u41)
    · exact False.elim (q1 u45)
    · exact q2
  have u47 : (¬ p5) := by
    rcases h18250 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u16)
    · exact q1
    · exact False.elim (q2 u46)
    · exact False.elim (q3 u13)
    · exact False.elim (q4 u15)
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u5)
  have u48 : (¬ p234) := by
    rcases h20442 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u16)
    · exact False.elim (q1 u32)
    · exact False.elim (q2 u46)
    · exact False.elim (q3 u39)
    · exact q4
  have u49 : p68 := by
    rcases h23068 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u40 q1)
    · exact False.elim (u47 q2)
  have u50 : p1188 := by
    rcases h22095 with q0 | q1
    · exact q0
    · exact False.elim (u48 q1)
  rcases h10823 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u39)
  · exact False.elim (q1 u49)
  · exact False.elim (q2 u44)
  · exact False.elim (q3 u50)

theorem step23073 (p2 p5 p6 p10 p11 p17 p41 p45 p63 p64 p84 p85 p89 p124 p125 p126 p134 p142 p160 p188 p192 p211 p227 p228 p237 p256 p258 p262 p265 p266 p268 p283 p288 p303 p304 p323 p344 p367 p382 p387 p419 p420 p476 p481 p532 p576 p579 p581 p596 p600 p836 p840 p961 p964 p1226 p1325 p1333 p1443 : Prop)
    (h10692 : (¬ p2) ∨ (¬ p481))
    (h22551 : p476 ∨ p481)
    (h12408 : p382 ∨ (¬ p419) ∨ (¬ p476))
    (h21151 : p17 ∨ p265)
    (h13074 : (¬ p125) ∨ (¬ p126) ∨ (¬ p265))
    (h21948 : p367 ∨ p125)
    (h10100 : (¬ p367) ∨ (¬ p382) ∨ (¬ p387))
    (h21214 : p228 ∨ p387)
    (h18534 : (¬ p2) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p228) ∨ (¬ p419))
    (h11559 : (¬ p188) ∨ p211 ∨ (¬ p266))
    (h21387 : p188 ∨ p192)
    (h23019 : p6 ∨ p211)
    (h9328 : (¬ p6) ∨ (¬ p142) ∨ (¬ p192))
    (h22176 : p142 ∨ p134)
    (h7324 : p303 ∨ (¬ p367) ∨ (¬ p382))
    (h21276 : p256 ∨ p17)
    (h21454 : p237 ∨ (¬ p256) ∨ (¬ p126))
    (h21106 : p124 ∨ p304)
    (h21227 : p1443 ∨ p11)
    (h13673 : (¬ p227) ∨ (¬ p262) ∨ p1443)
    (h16590 : (¬ p11) ∨ (¬ p227) ∨ (¬ p288) ∨ (¬ p344))
    (h21031 : (¬ p11) ∨ (¬ p160) ∨ (¬ p126) ∨ (¬ p532))
    (h22251 : p268 ∨ p262 ∨ p17)
    (h21668 : p258 ∨ p288)
    (h21864 : p283 ∨ p288)
    (h21183 : p1226 ∨ p160)
    (h19743 : (¬ p124) ∨ (¬ p258) ∨ (¬ p532) ∨ (¬ p961))
    (h18074 : (¬ p124) ∨ (¬ p268) ∨ (¬ p283) ∨ (¬ p344) ∨ (¬ p836))
    (h21239 : p964 ∨ p961)
    (h21988 : p840 ∨ p836)
    (h16587 : (¬ p11) ∨ (¬ p126) ∨ (¬ p964) ∨ (¬ p1226) ∨ (¬ p1333))
    (h21656 : p1325 ∨ p1333)
    (h18276 : (¬ p2) ∨ (¬ p45) ∨ (¬ p192) ∨ (¬ p419) ∨ (¬ p1325))
    (h16996 : (¬ p10) ∨ (¬ p134) ∨ (¬ p303) ∨ (¬ p1325))
    (h21444 : p41 ∨ p45)
    (h21681 : p323 ∨ p10)
    (h18239 : (¬ p11) ∨ (¬ p41) ∨ (¬ p227) ∨ (¬ p576))
    (h20860 : p576 ∨ p579)
    (h21688 : p576 ∨ p581)
    (h9846 : (¬ p126) ∨ (¬ p420) ∨ (¬ p579))
    (h20956 : p600 ∨ p420)
    (h22572 : p596 ∨ p420)
    (h23072 : (¬ p84) ∨ (¬ p596) ∨ (¬ p600) ∨ (¬ p581) ∨ (¬ p323) ∨ (¬ p1325) ∨ (¬ p840) ∨ (¬ p258) ∨ (¬ p11) ∨ (¬ p344) ∨ p211 ∨ (¬ p237) ∨ (¬ p266) ∨ (¬ p126) ∨ p304 ∨ (¬ p419) ∨ (¬ p2))
    (h22277 : p89 ∨ p84)
    (h22278 : p84 ∨ (¬ p85))
    (h11182 : (¬ p64) ∨ (¬ p89) ∨ p188)
    (h22211 : p85 ∨ p63)
    (h22908 : p5 ∨ p64)
    (h18250 : (¬ p2) ∨ (¬ p5) ∨ (¬ p63) ∨ (¬ p126) ∨ (¬ p419) ∨ (¬ p581) ∨ (¬ p1325)) : p1443 ∨ (¬ p344) ∨ (¬ p532) ∨ p17 ∨ (¬ p266) ∨ (¬ p227) ∨ (¬ p126) ∨ p304 ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1443) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p481) := by
    rcases h10692 with q0 | q1
    · exact False.elim (q0 u9)
    · exact q1
  have u11 : p476 := by
    rcases h22551 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u12 : p382 := by
    rcases h12408 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u8)
    · exact False.elim (q2 u11)
  have u13 : p265 := by
    rcases h21151 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u14 : (¬ p125) := by
    rcases h13074 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u6)
    · exact False.elim (q2 u13)
  have u15 : p367 := by
    rcases h21948 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  have u16 : (¬ p387) := by
    rcases h10100 with q0 | q1 | q2
    · exact False.elim (q0 u15)
    · exact False.elim (q1 u12)
    · exact q2
  have u17 : p228 := by
    rcases h21214 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u18 : (¬ p211) := by
    rcases h18534 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u9)
    · exact q1
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u17)
    · exact False.elim (q4 u8)
  have u19 : (¬ p188) := by
    rcases h11559 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u18 q1)
    · exact False.elim (q2 u4)
  have u20 : p192 := by
    rcases h21387 with q0 | q1
    · exact False.elim (u19 q0)
    · exact q1
  have u21 : p6 := by
    rcases h23019 with q0 | q1
    · exact q0
    · exact False.elim (u18 q1)
  have u22 : (¬ p142) := by
    rcases h9328 with q0 | q1 | q2
    · exact False.elim (q0 u21)
    · exact q1
    · exact False.elim (q2 u20)
  have u23 : p134 := by
    rcases h22176 with q0 | q1
    · exact False.elim (u22 q0)
    · exact q1
  have u24 : p303 := by
    rcases h7324 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u15)
    · exact False.elim (q2 u12)
  have u25 : p256 := by
    rcases h21276 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u26 : p237 := by
    rcases h21454 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u25)
    · exact False.elim (q2 u6)
  have u27 : p124 := by
    rcases h21106 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u28 : p11 := by
    rcases h21227 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u29 : (¬ p262) := by
    rcases h13673 with q0 | q1 | q2
    · exact False.elim (q0 u5)
    · exact q1
    · exact False.elim (u0 q2)
  have u30 : (¬ p288) := by
    rcases h16590 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u28)
    · exact False.elim (q1 u5)
    · exact q2
    · exact False.elim (q3 u1)
  have u31 : (¬ p160) := by
    rcases h21031 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u28)
    · exact q1
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u2)
  have u32 : p268 := by
    rcases h22251 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u29 q1)
    · exact False.elim (u3 q2)
  have u33 : p258 := by
    rcases h21668 with q0 | q1
    · exact q0
    · exact False.elim (u30 q1)
  have u34 : p283 := by
    rcases h21864 with q0 | q1
    · exact q0
    · exact False.elim (u30 q1)
  have u35 : p1226 := by
    rcases h21183 with q0 | q1
    · exact q0
    · exact False.elim (u31 q1)
  have u36 : (¬ p961) := by
    rcases h19743 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u27)
    · exact False.elim (q1 u33)
    · exact False.elim (q2 u2)
    · exact q3
  have u37 : (¬ p836) := by
    rcases h18074 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u27)
    · exact False.elim (q1 u32)
    · exact False.elim (q2 u34)
    · exact False.elim (q3 u1)
    · exact q4
  have u38 : p964 := by
    rcases h21239 with q0 | q1
    · exact q0
    · exact False.elim (u36 q1)
  have u39 : p840 := by
    rcases h21988 with q0 | q1
    · exact q0
    · exact False.elim (u37 q1)
  have u40 : (¬ p1333) := by
    rcases h16587 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u28)
    · exact False.elim (q1 u6)
    · exact False.elim (q2 u38)
    · exact False.elim (q3 u35)
    · exact q4
  have u41 : p1325 := by
    rcases h21656 with q0 | q1
    · exact q0
    · exact False.elim (u40 q1)
  have u42 : (¬ p45) := by
    rcases h18276 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u9)
    · exact q1
    · exact False.elim (q2 u20)
    · exact False.elim (q3 u8)
    · exact False.elim (q4 u41)
  have u43 : (¬ p10) := by
    rcases h16996 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u23)
    · exact False.elim (q2 u24)
    · exact False.elim (q3 u41)
  have u44 : p41 := by
    rcases h21444 with q0 | q1
    · exact q0
    · exact False.elim (u42 q1)
  have u45 : p323 := by
    rcases h21681 with q0 | q1
    · exact q0
    · exact False.elim (u43 q1)
  have u46 : (¬ p576) := by
    rcases h18239 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u28)
    · exact False.elim (q1 u44)
    · exact False.elim (q2 u5)
    · exact q3
  have u47 : p579 := by
    rcases h20860 with q0 | q1
    · exact False.elim (u46 q0)
    · exact q1
  have u48 : p581 := by
    rcases h21688 with q0 | q1
    · exact False.elim (u46 q0)
    · exact q1
  have u49 : (¬ p420) := by
    rcases h9846 with q0 | q1 | q2
    · exact False.elim (q0 u6)
    · exact q1
    · exact False.elim (q2 u47)
  have u50 : p600 := by
    rcases h20956 with q0 | q1
    · exact q0
    · exact False.elim (u49 q1)
  have u51 : p596 := by
    rcases h22572 with q0 | q1
    · exact q0
    · exact False.elim (u49 q1)
  have u52 : (¬ p84) := by
    rcases h23072 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11 | q12 | q13 | q14 | q15 | q16
    · exact q0
    · exact False.elim (q1 u51)
    · exact False.elim (q2 u50)
    · exact False.elim (q3 u48)
    · exact False.elim (q4 u45)
    · exact False.elim (q5 u41)
    · exact False.elim (q6 u39)
    · exact False.elim (q7 u33)
    · exact False.elim (q8 u28)
    · exact False.elim (q9 u1)
    · exact False.elim (u18 q10)
    · exact False.elim (q11 u26)
    · exact False.elim (q12 u4)
    · exact False.elim (q13 u6)
    · exact False.elim (u7 q14)
    · exact False.elim (q15 u8)
    · exact False.elim (q16 u9)
  have u53 : p89 := by
    rcases h22277 with q0 | q1
    · exact q0
    · exact False.elim (u52 q1)
  have u54 : (¬ p85) := by
    rcases h22278 with q0 | q1
    · exact False.elim (u52 q0)
    · exact q1
  have u55 : (¬ p64) := by
    rcases h11182 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u53)
    · exact False.elim (u19 q2)
  have u56 : p63 := by
    rcases h22211 with q0 | q1
    · exact False.elim (u54 q0)
    · exact q1
  have u57 : p5 := by
    rcases h22908 with q0 | q1
    · exact q0
    · exact False.elim (u55 q1)
  rcases h18250 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u9)
  · exact False.elim (q1 u57)
  · exact False.elim (q2 u56)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u48)
  · exact False.elim (q6 u41)

theorem step23074 (p978 p983 p986 p991 p992 p993 p994 p995 : Prop)
    (h5812 : p986 ∨ p991)
    (h5813 : p986 ∨ p992)
    (h5814 : p986 ∨ p993)
    (h5815 : p986 ∨ p994)
    (h5816 : p986 ∨ p995)
    (h5739 : p978 ∨ p983 ∨ (¬ p991) ∨ (¬ p992) ∨ (¬ p993) ∨ (¬ p994) ∨ (¬ p995)) : p986 ∨ p978 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p986) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p978) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p991 := by
    rcases h5812 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p992 := by
    rcases h5813 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p993 := by
    rcases h5814 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p994 := by
    rcases h5815 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p995 := by
    rcases h5816 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5739 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23075 (p978 p983 p990 p991 p992 p993 p994 p995 : Prop)
    (h5832 : p990 ∨ p991)
    (h5833 : p990 ∨ p992)
    (h5834 : p990 ∨ p993)
    (h5835 : p990 ∨ p994)
    (h5836 : p990 ∨ p995)
    (h5739 : p978 ∨ p983 ∨ (¬ p991) ∨ (¬ p992) ∨ (¬ p993) ∨ (¬ p994) ∨ (¬ p995)) : p990 ∨ p978 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p990) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p978) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p991 := by
    rcases h5832 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p992 := by
    rcases h5833 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p993 := by
    rcases h5834 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p994 := by
    rcases h5835 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p995 := by
    rcases h5836 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5739 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23076 (p978 p983 p989 p991 p992 p993 p994 p995 : Prop)
    (h5827 : p989 ∨ p991)
    (h5828 : p989 ∨ p992)
    (h5829 : p989 ∨ p993)
    (h5830 : p989 ∨ p994)
    (h5831 : p989 ∨ p995)
    (h5739 : p978 ∨ p983 ∨ (¬ p991) ∨ (¬ p992) ∨ (¬ p993) ∨ (¬ p994) ∨ (¬ p995)) : p989 ∨ p978 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p989) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p978) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p991 := by
    rcases h5827 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p992 := by
    rcases h5828 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p993 := by
    rcases h5829 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p994 := by
    rcases h5830 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p995 := by
    rcases h5831 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5739 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23077 (p978 p983 p988 p991 p992 p993 p994 p995 : Prop)
    (h5822 : p988 ∨ p991)
    (h5823 : p988 ∨ p992)
    (h5824 : p988 ∨ p993)
    (h5825 : p988 ∨ p994)
    (h5826 : p988 ∨ p995)
    (h5739 : p978 ∨ p983 ∨ (¬ p991) ∨ (¬ p992) ∨ (¬ p993) ∨ (¬ p994) ∨ (¬ p995)) : p988 ∨ p978 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p988) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p978) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p991 := by
    rcases h5822 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p992 := by
    rcases h5823 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p993 := by
    rcases h5824 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p994 := by
    rcases h5825 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p995 := by
    rcases h5826 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h5739 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23078 (p978 p983 p986 p987 p988 p989 p990 p991 p992 p993 p994 p995 : Prop)
    (h5714 : p978 ∨ p983 ∨ (¬ p986) ∨ (¬ p987) ∨ (¬ p988) ∨ (¬ p989) ∨ (¬ p990))
    (h5817 : p987 ∨ p991)
    (h5818 : p987 ∨ p992)
    (h5819 : p987 ∨ p993)
    (h5820 : p987 ∨ p994)
    (h5821 : p987 ∨ p995)
    (h5739 : p978 ∨ p983 ∨ (¬ p991) ∨ (¬ p992) ∨ (¬ p993) ∨ (¬ p994) ∨ (¬ p995)) : (¬ p988) ∨ (¬ p986) ∨ p983 ∨ p978 ∨ (¬ p989) ∨ (¬ p990) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p988 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p986 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p983) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p978) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p989 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p990 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p987) := by
    rcases h5714 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
  have u7 : p991 := by
    rcases h5817 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p992 := by
    rcases h5818 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p993 := by
    rcases h5819 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p994 := by
    rcases h5820 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p995 := by
    rcases h5821 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h5739 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step23079 (p978 p983 p986 p988 p989 p990 : Prop)
    (h23074 : p986 ∨ p978 ∨ p983)
    (h23075 : p990 ∨ p978 ∨ p983)
    (h23076 : p989 ∨ p978 ∨ p983)
    (h23077 : p988 ∨ p978 ∨ p983)
    (h23078 : (¬ p988) ∨ (¬ p986) ∨ p983 ∨ p978 ∨ (¬ p989) ∨ (¬ p990)) : p978 ∨ p983 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p978) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p983) := fun hu => hn (Or.inr hu)
  have u2 : p986 := by
    rcases h23074 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p990 := by
    rcases h23075 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p989 := by
    rcases h23076 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p988 := by
    rcases h23077 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h23078 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step23080 (p1036 p1042 p1045 p1046 p1047 p1048 p1049 p1050 : Prop)
    (h6196 : p1045 ∨ p1050)
    (h6201 : p1046 ∨ p1050)
    (h6206 : p1047 ∨ p1050)
    (h6211 : p1048 ∨ p1050)
    (h6216 : p1049 ∨ p1050)
    (h6107 : p1036 ∨ p1042 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : p1050 ∨ p1042 ∨ p1036 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1050) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1042) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1036) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1045 := by
    rcases h6196 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1046 := by
    rcases h6201 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1047 := by
    rcases h6206 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1048 := by
    rcases h6211 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1049 := by
    rcases h6216 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6107 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23081 (p1036 p1042 p1045 p1046 p1047 p1048 p1049 p1054 : Prop)
    (h6200 : p1045 ∨ p1054)
    (h6205 : p1046 ∨ p1054)
    (h6210 : p1047 ∨ p1054)
    (h6215 : p1048 ∨ p1054)
    (h6220 : p1049 ∨ p1054)
    (h6107 : p1036 ∨ p1042 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : p1054 ∨ p1042 ∨ p1036 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1054) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1042) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1036) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1045 := by
    rcases h6200 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1046 := by
    rcases h6205 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1047 := by
    rcases h6210 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1048 := by
    rcases h6215 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1049 := by
    rcases h6220 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6107 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23082 (p1036 p1042 p1045 p1046 p1047 p1048 p1049 p1053 : Prop)
    (h6199 : p1045 ∨ p1053)
    (h6204 : p1046 ∨ p1053)
    (h6209 : p1047 ∨ p1053)
    (h6214 : p1048 ∨ p1053)
    (h6219 : p1049 ∨ p1053)
    (h6107 : p1036 ∨ p1042 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : p1053 ∨ p1042 ∨ p1036 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1053) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1042) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1036) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1045 := by
    rcases h6199 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1046 := by
    rcases h6204 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1047 := by
    rcases h6209 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1048 := by
    rcases h6214 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1049 := by
    rcases h6219 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6107 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23083 (p1036 p1042 p1045 p1046 p1047 p1048 p1049 p1052 : Prop)
    (h6198 : p1045 ∨ p1052)
    (h6203 : p1046 ∨ p1052)
    (h6208 : p1047 ∨ p1052)
    (h6213 : p1048 ∨ p1052)
    (h6218 : p1049 ∨ p1052)
    (h6107 : p1036 ∨ p1042 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : p1052 ∨ p1042 ∨ p1036 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1052) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1042) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1036) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1045 := by
    rcases h6198 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1046 := by
    rcases h6203 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1047 := by
    rcases h6208 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1048 := by
    rcases h6213 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1049 := by
    rcases h6218 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6107 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23084 (p104 p110 p980 p1035 p1036 p1038 p1042 p1045 p1046 p1047 p1048 p1049 p1050 p1051 p1052 p1053 p1054 p1060 p1076 p1226 : Prop)
    (h14910 : (¬ p104) ∨ p1036 ∨ (¬ p1076))
    (h22241 : p110 ∨ p104)
    (h12793 : (¬ p980) ∨ (¬ p1035) ∨ (¬ p1038))
    (h16890 : (¬ p110) ∨ (¬ p1035) ∨ (¬ p1042) ∨ (¬ p1060) ∨ (¬ p1076) ∨ (¬ p1226))
    (h23080 : p1050 ∨ p1042 ∨ p1036)
    (h23081 : p1054 ∨ p1042 ∨ p1036)
    (h23082 : p1053 ∨ p1042 ∨ p1036)
    (h23083 : p1052 ∨ p1042 ∨ p1036)
    (h6127 : p1038 ∨ p1042 ∨ (¬ p1050) ∨ (¬ p1051) ∨ (¬ p1052) ∨ (¬ p1053) ∨ (¬ p1054))
    (h6197 : p1045 ∨ p1051)
    (h6202 : p1046 ∨ p1051)
    (h6207 : p1047 ∨ p1051)
    (h6212 : p1048 ∨ p1051)
    (h6217 : p1049 ∨ p1051)
    (h6107 : p1036 ∨ p1042 ∨ (¬ p1045) ∨ (¬ p1046) ∨ (¬ p1047) ∨ (¬ p1048) ∨ (¬ p1049)) : (¬ p1035) ∨ (¬ p1226) ∨ (¬ p1060) ∨ p1036 ∨ (¬ p1076) ∨ (¬ p980) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1060 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1036) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p104) := by
    rcases h14910 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
  have u7 : p110 := by
    rcases h22241 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : (¬ p1038) := by
    rcases h12793 with q0 | q1 | q2
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u0)
    · exact q2
  have u9 : (¬ p1042) := by
    rcases h16890 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u7)
    · exact False.elim (q1 u0)
    · exact q2
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u1)
  have u10 : p1050 := by
    rcases h23080 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u3 q2)
  have u11 : p1054 := by
    rcases h23081 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u3 q2)
  have u12 : p1053 := by
    rcases h23082 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u3 q2)
  have u13 : p1052 := by
    rcases h23083 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u9 q1)
    · exact False.elim (u3 q2)
  have u14 : (¬ p1051) := by
    rcases h6127 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u8 q0)
    · exact False.elim (u9 q1)
    · exact False.elim (q2 u10)
    · exact q3
    · exact False.elim (q4 u13)
    · exact False.elim (q5 u12)
    · exact False.elim (q6 u11)
  have u15 : p1045 := by
    rcases h6197 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  have u16 : p1046 := by
    rcases h6202 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  have u17 : p1047 := by
    rcases h6207 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  have u18 : p1048 := by
    rcases h6212 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  have u19 : p1049 := by
    rcases h6217 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  rcases h6107 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u15)
  · exact False.elim (q3 u16)
  · exact False.elim (q4 u17)
  · exact False.elim (q5 u18)
  · exact False.elim (q6 u19)

theorem step23085 (p1306 p1310 p1315 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7945 : p1315 ∨ p1319)
    (h7946 : p1315 ∨ p1320)
    (h7947 : p1315 ∨ p1321)
    (h7948 : p1315 ∨ p1322)
    (h7949 : p1315 ∨ p1323)
    (h7865 : p1306 ∨ p1310 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : p1315 ∨ p1310 ∨ p1306 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1315) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1310) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1306) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1319 := by
    rcases h7945 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1320 := by
    rcases h7946 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1321 := by
    rcases h7947 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1322 := by
    rcases h7948 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1323 := by
    rcases h7949 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7865 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23086 (p1306 p1310 p1314 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7940 : p1314 ∨ p1319)
    (h7941 : p1314 ∨ p1320)
    (h7942 : p1314 ∨ p1321)
    (h7943 : p1314 ∨ p1322)
    (h7944 : p1314 ∨ p1323)
    (h7865 : p1306 ∨ p1310 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : p1314 ∨ p1310 ∨ p1306 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1314) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1310) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1306) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1319 := by
    rcases h7940 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1320 := by
    rcases h7941 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1321 := by
    rcases h7942 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1322 := by
    rcases h7943 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1323 := by
    rcases h7944 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7865 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23087 (p1306 p1310 p1318 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7960 : p1318 ∨ p1319)
    (h7961 : p1318 ∨ p1320)
    (h7962 : p1318 ∨ p1321)
    (h7963 : p1318 ∨ p1322)
    (h7964 : p1318 ∨ p1323)
    (h7865 : p1306 ∨ p1310 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : p1318 ∨ p1310 ∨ p1306 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1318) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1310) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1306) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1319 := by
    rcases h7960 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1320 := by
    rcases h7961 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1321 := by
    rcases h7962 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1322 := by
    rcases h7963 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1323 := by
    rcases h7964 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7865 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23088 (p1306 p1310 p1317 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7955 : p1317 ∨ p1319)
    (h7956 : p1317 ∨ p1320)
    (h7957 : p1317 ∨ p1321)
    (h7958 : p1317 ∨ p1322)
    (h7959 : p1317 ∨ p1323)
    (h7865 : p1306 ∨ p1310 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : p1317 ∨ p1310 ∨ p1306 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1317) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1310) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1306) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1319 := by
    rcases h7955 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1320 := by
    rcases h7956 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1321 := by
    rcases h7957 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1322 := by
    rcases h7958 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1323 := by
    rcases h7959 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7865 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step23089 (p1306 p1310 p1314 p1315 p1316 p1317 p1318 p1319 p1320 p1321 p1322 p1323 : Prop)
    (h7840 : p1306 ∨ p1310 ∨ (¬ p1314) ∨ (¬ p1315) ∨ (¬ p1316) ∨ (¬ p1317) ∨ (¬ p1318))
    (h7950 : p1316 ∨ p1319)
    (h7951 : p1316 ∨ p1320)
    (h7952 : p1316 ∨ p1321)
    (h7953 : p1316 ∨ p1322)
    (h7954 : p1316 ∨ p1323)
    (h7865 : p1306 ∨ p1310 ∨ (¬ p1319) ∨ (¬ p1320) ∨ (¬ p1321) ∨ (¬ p1322) ∨ (¬ p1323)) : (¬ p1317) ∨ (¬ p1315) ∨ p1306 ∨ p1310 ∨ (¬ p1318) ∨ (¬ p1314) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1317 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1315 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1306) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1310) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1318 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1314 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1316) := by
    rcases h7840 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u1)
    · exact q4
    · exact False.elim (q5 u0)
    · exact False.elim (q6 u4)
  have u7 : p1319 := by
    rcases h7950 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1320 := by
    rcases h7951 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1321 := by
    rcases h7952 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1322 := by
    rcases h7953 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1323 := by
    rcases h7954 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h7865 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step23090 (p1306 p1310 p1314 p1315 p1317 p1318 : Prop)
    (h23085 : p1315 ∨ p1310 ∨ p1306)
    (h23086 : p1314 ∨ p1310 ∨ p1306)
    (h23087 : p1318 ∨ p1310 ∨ p1306)
    (h23088 : p1317 ∨ p1310 ∨ p1306)
    (h23089 : (¬ p1317) ∨ (¬ p1315) ∨ p1306 ∨ p1310 ∨ (¬ p1318) ∨ (¬ p1314)) : p1310 ∨ p1306 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1310) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1306) := fun hu => hn (Or.inr hu)
  have u2 : p1315 := by
    rcases h23085 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1314 := by
    rcases h23086 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1318 := by
    rcases h23087 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1317 := by
    rcases h23088 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h23089 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u3)

theorem step23091 (p63 p84 p85 p86 p161 p237 p256 p286 p288 p344 p581 p635 p642 p840 p897 p904 p918 p926 p928 p980 p1074 p1076 p1095 p1096 p1099 p1115 p1116 p1225 p1229 p1232 p1306 p1310 p1333 : Prop)
    (h13505 : (¬ p286) ∨ (¬ p344) ∨ p840)
    (h8726 : (¬ p84) ∨ (¬ p237) ∨ (¬ p918))
    (h11129 : (¬ p84) ∨ (¬ p256) ∨ p581)
    (h21470 : p926 ∨ p918)
    (h22025 : p918 ∨ p928)
    (h17217 : (¬ p63) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p581))
    (h10259 : (¬ p840) ∨ (¬ p897) ∨ (¬ p926))
    (h16273 : (¬ p344) ∨ (¬ p928) ∨ (¬ p1076) ∨ (¬ p1116))
    (h21852 : p86 ∨ p63)
    (h22211 : p85 ∨ p63)
    (h20784 : p897 ∨ p904)
    (h21858 : p1115 ∨ p1116)
    (h18745 : (¬ p904) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1333))
    (h16589 : (¬ p286) ∨ (¬ p344) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1225))
    (h22311 : p1074 ∨ p1095)
    (h21572 : p161 ∨ p1225)
    (h16445 : (¬ p85) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1096))
    (h6476 : (¬ p635) ∨ (¬ p1076) ∨ (¬ p1095))
    (h17437 : (¬ p86) ∨ (¬ p161) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p1232) ∨ (¬ p1333))
    (h21802 : p1096 ∨ p1099)
    (h23006 : p642 ∨ p635)
    (h22374 : p1229 ∨ p1232)
    (h8736 : (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1306))
    (h16318 : (¬ p642) ∨ (¬ p1076) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1310))
    (h23090 : p1310 ∨ p1306) : (¬ p84) ∨ (¬ p1076) ∨ (¬ p980) ∨ (¬ p1333) ∨ (¬ p288) ∨ (¬ p286) ∨ (¬ p344) ∨ (¬ p237) ∨ (¬ p256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p84 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p840 := by
    rcases h13505 with q0 | q1 | q2
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u6)
    · exact q2
  have u10 : (¬ p918) := by
    rcases h8726 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u7)
    · exact q2
  have u11 : p581 := by
    rcases h11129 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u8)
    · exact q2
  have u12 : p926 := by
    rcases h21470 with q0 | q1
    · exact q0
    · exact False.elim (u10 q1)
  have u13 : p928 := by
    rcases h22025 with q0 | q1
    · exact False.elim (u10 q0)
    · exact q1
  have u14 : (¬ p63) := by
    rcases h17217 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u6)
    · exact False.elim (q3 u11)
  have u15 : (¬ p897) := by
    rcases h10259 with q0 | q1 | q2
    · exact False.elim (q0 u9)
    · exact q1
    · exact False.elim (q2 u12)
  have u16 : (¬ p1116) := by
    rcases h16273 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u6)
    · exact False.elim (q1 u13)
    · exact False.elim (q2 u1)
    · exact q3
  have u17 : p86 := by
    rcases h21852 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  have u18 : p85 := by
    rcases h22211 with q0 | q1
    · exact q0
    · exact False.elim (u14 q1)
  have u19 : p904 := by
    rcases h20784 with q0 | q1
    · exact False.elim (u15 q0)
    · exact q1
  have u20 : p1115 := by
    rcases h21858 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u21 : (¬ p1074) := by
    rcases h18745 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u19)
    · exact False.elim (q1 u2)
    · exact q2
    · exact False.elim (q3 u3)
  have u22 : (¬ p1225) := by
    rcases h16589 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u5)
    · exact False.elim (q1 u6)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u20)
    · exact q4
  have u23 : p1095 := by
    rcases h22311 with q0 | q1
    · exact False.elim (u21 q0)
    · exact q1
  have u24 : p161 := by
    rcases h21572 with q0 | q1
    · exact q0
    · exact False.elim (u22 q1)
  have u25 : (¬ p1096) := by
    rcases h16445 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u18)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u23)
    · exact q3
  have u26 : (¬ p635) := by
    rcases h6476 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u23)
  have u27 : (¬ p1232) := by
    rcases h17437 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u17)
    · exact False.elim (q1 u24)
    · exact False.elim (q2 u8)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u3)
  have u28 : p1099 := by
    rcases h21802 with q0 | q1
    · exact False.elim (u25 q0)
    · exact q1
  have u29 : p642 := by
    rcases h23006 with q0 | q1
    · exact q0
    · exact False.elim (u26 q1)
  have u30 : p1229 := by
    rcases h22374 with q0 | q1
    · exact q0
    · exact False.elim (u27 q1)
  have u31 : (¬ p1306) := by
    rcases h8736 with q0 | q1 | q2
    · exact False.elim (q0 u28)
    · exact False.elim (q1 u30)
    · exact q2
  have u32 : (¬ p1310) := by
    rcases h16318 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u29)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u28)
    · exact False.elim (q3 u30)
    · exact q4
  rcases h23090 with q0 | q1
  · exact False.elim (u32 q0)
  · exact False.elim (u31 q1)

theorem step23092 (p2 p5 p17 p41 p45 p63 p64 p84 p85 p89 p90 p124 p125 p126 p188 p192 p194 p211 p227 p228 p237 p256 p258 p265 p266 p286 p288 p304 p309 p344 p367 p382 p387 p406 p419 p476 p481 p532 p576 p581 p657 p665 p710 p713 p860 p861 p918 p928 p980 p983 p1076 p1077 p1249 p1273 p1325 p1333 p1443 p1452 p1489 : Prop)
    (h21106 : p124 ∨ p304)
    (h23029 : (¬ p1452) ∨ (¬ p1489) ∨ p17 ∨ (¬ p266) ∨ (¬ p227) ∨ (¬ p126) ∨ (¬ p124) ∨ (¬ p419) ∨ (¬ p2))
    (h21329 : p1452 ∨ p532)
    (h10692 : (¬ p2) ∨ (¬ p481))
    (h22551 : p476 ∨ p481)
    (h12408 : p382 ∨ (¬ p419) ∨ (¬ p476))
    (h21151 : p17 ∨ p265)
    (h13074 : (¬ p125) ∨ (¬ p126) ∨ (¬ p265))
    (h21948 : p367 ∨ p125)
    (h10100 : (¬ p367) ∨ (¬ p382) ∨ (¬ p387))
    (h21214 : p228 ∨ p387)
    (h18534 : (¬ p2) ∨ (¬ p211) ∨ (¬ p227) ∨ (¬ p228) ∨ (¬ p419))
    (h11559 : (¬ p188) ∨ p211 ∨ (¬ p266))
    (h22615 : p194 ∨ p188)
    (h21387 : p188 ∨ p192)
    (h21276 : p256 ∨ p17)
    (h21454 : p237 ∨ (¬ p256) ∨ (¬ p126))
    (h22249 : p309 ∨ p304)
    (h2601 : (¬ p406) ∨ (¬ p419) ∨ (¬ p476))
    (h9310 : (¬ p309) ∨ (¬ p344) ∨ (¬ p710))
    (h20854 : p710 ∨ p713)
    (h10666 : p406 ∨ (¬ p657) ∨ (¬ p713))
    (h22069 : p665 ∨ p657)
    (h23073 : p1443 ∨ (¬ p344) ∨ (¬ p532) ∨ p17 ∨ (¬ p266) ∨ (¬ p227) ∨ (¬ p126) ∨ p304 ∨ (¬ p419) ∨ (¬ p2))
    (h19744 : (¬ p2) ∨ (¬ p124) ∨ (¬ p194) ∨ (¬ p228) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p419) ∨ (¬ p1443))
    (h21140 : p286 ∨ p258)
    (h21668 : p258 ∨ p288)
    (h16581 : (¬ p2) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p419) ∨ (¬ p1325))
    (h22912 : (¬ p344) ∨ (¬ p983) ∨ (¬ p288) ∨ (¬ p286) ∨ (¬ p1489) ∨ (¬ p256))
    (h16566 : (¬ p2) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p1077))
    (h21656 : p1325 ∨ p1333)
    (h20687 : p980 ∨ p983)
    (h21482 : p1077 ∨ p1076)
    (h10842 : (¬ p861) ∨ (¬ p1333) ∨ (¬ p1489))
    (h21340 : p860 ∨ p861)
    (h23091 : (¬ p84) ∨ (¬ p1076) ∨ (¬ p980) ∨ (¬ p1333) ∨ (¬ p288) ∨ (¬ p286) ∨ (¬ p344) ∨ (¬ p237) ∨ (¬ p256))
    (h22277 : p89 ∨ p84)
    (h22278 : p84 ∨ (¬ p85))
    (h22396 : p90 ∨ p84)
    (h11182 : (¬ p64) ∨ (¬ p89) ∨ p188)
    (h22211 : p85 ∨ p63)
    (h18316 : (¬ p2) ∨ (¬ p45) ∨ (¬ p90) ∨ (¬ p192) ∨ (¬ p228) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p1443))
    (h22908 : p5 ∨ p64)
    (h17217 : (¬ p63) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p581))
    (h21444 : p41 ∨ p45)
    (h21688 : p576 ∨ p581)
    (h18317 : (¬ p41) ∨ (¬ p1249) ∨ (¬ p1333) ∨ (¬ p1489))
    (h18225 : (¬ p256) ∨ (¬ p286) ∨ (¬ p344) ∨ (¬ p576) ∨ (¬ p928))
    (h21525 : p1273 ∨ p1249)
    (h22025 : p918 ∨ p928)
    (h18361 : (¬ p2) ∨ (¬ p5) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p419) ∨ (¬ p860) ∨ (¬ p918) ∨ (¬ p1273)) : (¬ p344) ∨ (¬ p1489) ∨ p17 ∨ (¬ p266) ∨ (¬ p227) ∨ (¬ p126) ∨ p304 ∨ (¬ p419) ∨ (¬ p2) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : p124 := by
    rcases h21106 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : (¬ p1452) := by
    rcases h23029 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact q0
    · exact False.elim (q1 u1)
    · exact False.elim (u2 q2)
    · exact False.elim (q3 u3)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u9)
    · exact False.elim (q7 u7)
    · exact False.elim (q8 u8)
  have u11 : p532 := by
    rcases h21329 with q0 | q1
    · exact False.elim (u10 q0)
    · exact q1
  have u12 : (¬ p481) := by
    rcases h10692 with q0 | q1
    · exact False.elim (q0 u8)
    · exact q1
  have u13 : p476 := by
    rcases h22551 with q0 | q1
    · exact q0
    · exact False.elim (u12 q1)
  have u14 : p382 := by
    rcases h12408 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u13)
  have u15 : p265 := by
    rcases h21151 with q0 | q1
    · exact False.elim (u2 q0)
    · exact q1
  have u16 : (¬ p125) := by
    rcases h13074 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u5)
    · exact False.elim (q2 u15)
  have u17 : p367 := by
    rcases h21948 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u18 : (¬ p387) := by
    rcases h10100 with q0 | q1 | q2
    · exact False.elim (q0 u17)
    · exact False.elim (q1 u14)
    · exact q2
  have u19 : p228 := by
    rcases h21214 with q0 | q1
    · exact q0
    · exact False.elim (u18 q1)
  have u20 : (¬ p211) := by
    rcases h18534 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u8)
    · exact q1
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u19)
    · exact False.elim (q4 u7)
  have u21 : (¬ p188) := by
    rcases h11559 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u20 q1)
    · exact False.elim (q2 u3)
  have u22 : p194 := by
    rcases h22615 with q0 | q1
    · exact q0
    · exact False.elim (u21 q1)
  have u23 : p192 := by
    rcases h21387 with q0 | q1
    · exact False.elim (u21 q0)
    · exact q1
  have u24 : p256 := by
    rcases h21276 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u25 : p237 := by
    rcases h21454 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u24)
    · exact False.elim (q2 u5)
  have u26 : p309 := by
    rcases h22249 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u27 : (¬ p406) := by
    rcases h2601 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u7)
    · exact False.elim (q2 u13)
  have u28 : (¬ p710) := by
    rcases h9310 with q0 | q1 | q2
    · exact False.elim (q0 u26)
    · exact False.elim (q1 u0)
    · exact q2
  have u29 : p713 := by
    rcases h20854 with q0 | q1
    · exact False.elim (u28 q0)
    · exact q1
  have u30 : (¬ p657) := by
    rcases h10666 with q0 | q1 | q2
    · exact False.elim (u27 q0)
    · exact q1
    · exact False.elim (q2 u29)
  have u31 : p665 := by
    rcases h22069 with q0 | q1
    · exact q0
    · exact False.elim (u30 q1)
  have u32 : p1443 := by
    rcases h23073 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u11)
    · exact False.elim (u2 q3)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u5)
    · exact False.elim (u6 q7)
    · exact False.elim (q8 u7)
    · exact False.elim (q9 u8)
  have u33 : (¬ p258) := by
    rcases h19744 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u9)
    · exact False.elim (q2 u22)
    · exact False.elim (q3 u19)
    · exact q4
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u7)
    · exact False.elim (q7 u32)
  have u34 : p286 := by
    rcases h21140 with q0 | q1
    · exact q0
    · exact False.elim (u33 q1)
  have u35 : p288 := by
    rcases h21668 with q0 | q1
    · exact False.elim (u33 q0)
    · exact q1
  have u36 : (¬ p1325) := by
    rcases h16581 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u22)
    · exact False.elim (q2 u24)
    · exact False.elim (q3 u35)
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u7)
    · exact q6
  have u37 : (¬ p983) := by
    rcases h22912 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (q0 u0)
    · exact q1
    · exact False.elim (q2 u35)
    · exact False.elim (q3 u34)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u24)
  have u38 : (¬ p1077) := by
    rcases h16566 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (q0 u8)
    · exact False.elim (q1 u22)
    · exact False.elim (q2 u24)
    · exact False.elim (q3 u35)
    · exact False.elim (q4 u7)
    · exact False.elim (q5 u31)
    · exact q6
  have u39 : p1333 := by
    rcases h21656 with q0 | q1
    · exact False.elim (u36 q0)
    · exact q1
  have u40 : p980 := by
    rcases h20687 with q0 | q1
    · exact q0
    · exact False.elim (u37 q1)
  have u41 : p1076 := by
    rcases h21482 with q0 | q1
    · exact False.elim (u38 q0)
    · exact q1
  have u42 : (¬ p861) := by
    rcases h10842 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u39)
    · exact False.elim (q2 u1)
  have u43 : p860 := by
    rcases h21340 with q0 | q1
    · exact q0
    · exact False.elim (u42 q1)
  have u44 : (¬ p84) := by
    rcases h23091 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
    · exact q0
    · exact False.elim (q1 u41)
    · exact False.elim (q2 u40)
    · exact False.elim (q3 u39)
    · exact False.elim (q4 u35)
    · exact False.elim (q5 u34)
    · exact False.elim (q6 u0)
    · exact False.elim (q7 u25)
    · exact False.elim (q8 u24)
  have u45 : p89 := by
    rcases h22277 with q0 | q1
    · exact q0
    · exact False.elim (u44 q1)
  have u46 : (¬ p85) := by
    rcases h22278 with q0 | q1
    · exact False.elim (u44 q0)
    · exact q1
  have u47 : p90 := by
    rcases h22396 with q0 | q1
    · exact q0
    · exact False.elim (u44 q1)
  have u48 : (¬ p64) := by
    rcases h11182 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u45)
    · exact False.elim (u21 q2)
  have u49 : p63 := by
    rcases h22211 with q0 | q1
    · exact False.elim (u46 q0)
    · exact q1
  have u50 : (¬ p45) := by
    rcases h18316 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
    · exact False.elim (q0 u8)
    · exact q1
    · exact False.elim (q2 u47)
    · exact False.elim (q3 u23)
    · exact False.elim (q4 u19)
    · exact False.elim (q5 u24)
    · exact False.elim (q6 u7)
    · exact False.elim (q7 u32)
  have u51 : p5 := by
    rcases h22908 with q0 | q1
    · exact q0
    · exact False.elim (u48 q1)
  have u52 : (¬ p581) := by
    rcases h17217 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u49)
    · exact False.elim (q1 u35)
    · exact False.elim (q2 u0)
    · exact q3
  have u53 : p41 := by
    rcases h21444 with q0 | q1
    · exact q0
    · exact False.elim (u50 q1)
  have u54 : p576 := by
    rcases h21688 with q0 | q1
    · exact q0
    · exact False.elim (u52 q1)
  have u55 : (¬ p1249) := by
    rcases h18317 with q0 | q1 | q2 | q3
    · exact False.elim (q0 u53)
    · exact q1
    · exact False.elim (q2 u39)
    · exact False.elim (q3 u1)
  have u56 : (¬ p928) := by
    rcases h18225 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u24)
    · exact False.elim (q1 u34)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u54)
    · exact q4
  have u57 : p1273 := by
    rcases h21525 with q0 | q1
    · exact q0
    · exact False.elim (u55 q1)
  have u58 : p918 := by
    rcases h22025 with q0 | q1
    · exact q0
    · exact False.elim (u56 q1)
  rcases h18361 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u8)
  · exact False.elim (q1 u51)
  · exact False.elim (q2 u45)
  · exact False.elim (q3 u25)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u43)
  · exact False.elim (q6 u58)
  · exact False.elim (q7 u57)

#print axioms step23092

end NineRUPTrial
