import Erdos261Finite

set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace Erdos261Finite

theorem cert_4 : Represents 4 2 :=
  segment 4 4 2 8 0 (by rfl) (zero_represents 8)

theorem cert_5 : Represents 3 1 :=
  segment 1 3 1 4 2 (by rfl) cert_4

theorem cert_8 : Represents 5 3 :=
  segment 1 5 3 6 0 (by rfl) (zero_represents 6)

theorem cert_11 : Represents 12 10 :=
  segment 2 12 10 14 0 (by rfl) (zero_represents 14)

theorem cert_13 : Represents 10 8 :=
  segment 2 10 8 12 10 (by rfl) cert_11

theorem cert_15 : Represents 8 2 :=
  segment 2 8 2 10 8 (by rfl) cert_13

theorem cert_17 : Represents 6 4 :=
  segment 2 6 4 8 2 (by rfl) cert_15

theorem cert_19 : Represents 7 5 :=
  segment 1 7 5 8 2 (by rfl) cert_15

theorem cert_28 : Represents 16 2 :=
  segment 8 16 2 24 0 (by rfl) (zero_represents 24)

theorem cert_30 : Represents 14 8 :=
  segment 2 14 8 16 2 (by rfl) cert_28

theorem cert_36 : Represents 8 6 :=
  segment 6 8 6 14 8 (by rfl) cert_30

theorem cert_39 : Represents 30 8 :=
  segment 2 30 8 32 0 (by rfl) (zero_represents 32)

theorem cert_45 : Represents 24 8 :=
  segment 6 24 8 30 8 (by rfl) cert_39

theorem cert_49 : Represents 20 18 :=
  segment 4 20 18 24 8 (by rfl) cert_45

theorem cert_60 : Represents 9 7 :=
  segment 11 9 7 20 18 (by rfl) cert_49

theorem cert_112 : Represents 342 320 :=
  segment 50 342 320 392 0 (by rfl) (zero_represents 392)

theorem cert_150 : Represents 304 106 :=
  segment 38 304 106 342 320 (by rfl) cert_112

theorem cert_160 : Represents 294 168 :=
  segment 10 294 168 304 106 (by rfl) cert_150

theorem cert_196 : Represents 258 256 :=
  segment 36 258 256 294 168 (by rfl) cert_160

theorem cert_204 : Represents 250 174 :=
  segment 8 250 174 258 256 (by rfl) cert_196

theorem cert_208 : Represents 246 104 :=
  segment 4 246 104 250 174 (by rfl) cert_204

theorem cert_220 : Represents 234 118 :=
  segment 12 234 118 246 104 (by rfl) cert_208

theorem cert_222 : Represents 232 146 :=
  segment 2 232 146 234 118 (by rfl) cert_220

theorem cert_230 : Represents 224 162 :=
  segment 8 224 162 232 146 (by rfl) cert_222

theorem cert_270 : Represents 184 64 :=
  segment 40 184 64 224 162 (by rfl) cert_230

theorem cert_278 : Represents 176 56 :=
  segment 8 176 56 184 64 (by rfl) cert_270

theorem cert_294 : Represents 160 130 :=
  segment 16 160 130 176 56 (by rfl) cert_278

theorem cert_300 : Represents 154 46 :=
  segment 6 154 46 160 130 (by rfl) cert_294

theorem cert_312 : Represents 142 136 :=
  segment 12 142 136 154 46 (by rfl) cert_300

theorem cert_320 : Represents 134 56 :=
  segment 8 134 56 142 136 (by rfl) cert_312

theorem cert_336 : Represents 118 72 :=
  segment 16 118 72 134 56 (by rfl) cert_320

theorem cert_342 : Represents 112 106 :=
  segment 6 112 106 118 72 (by rfl) cert_336

theorem cert_350 : Represents 104 82 :=
  segment 8 104 82 112 106 (by rfl) cert_342

theorem cert_356 : Represents 98 62 :=
  segment 6 98 62 104 82 (by rfl) cert_350

theorem cert_358 : Represents 96 40 :=
  segment 2 96 40 98 62 (by rfl) cert_356

theorem cert_376 : Represents 78 40 :=
  segment 18 78 40 96 40 (by rfl) cert_358

theorem cert_390 : Represents 64 10 :=
  segment 14 64 10 78 40 (by rfl) cert_376

theorem cert_406 : Represents 48 8 :=
  segment 16 48 8 64 10 (by rfl) cert_390

theorem cert_422 : Represents 32 2 :=
  segment 16 32 2 48 8 (by rfl) cert_406

theorem cert_424 : Represents 30 24 :=
  segment 2 30 24 32 2 (by rfl) cert_422

theorem cert_430 : Represents 24 18 :=
  segment 6 24 18 30 24 (by rfl) cert_424

theorem cert_432 : Represents 22 16 :=
  segment 2 22 16 24 18 (by rfl) cert_430

theorem cert_438 : Represents 16 10 :=
  segment 6 16 10 22 16 (by rfl) cert_432

theorem cert_443 : Represents 11 9 :=
  segment 5 11 9 16 10 (by rfl) cert_438

theorem cert_446 : Represents 13 11 :=
  segment 1 13 11 14 8 (by rfl) cert_30

theorem cert_449 : Represents 14 12 :=
  segment 2 14 12 16 2 (by rfl) cert_28

theorem cert_451 : Represents 15 13 :=
  segment 1 15 13 16 10 (by rfl) cert_438

theorem cert_458 : Represents 16 14 :=
  segment 6 16 14 22 0 (by rfl) (zero_represents 22)

theorem cert_461 : Represents 30 16 :=
  segment 2 30 16 32 2 (by rfl) cert_422

theorem cert_474 : Represents 17 15 :=
  segment 13 17 15 30 16 (by rfl) cert_461

theorem cert_481 : Represents 18 16 :=
  segment 6 18 16 24 8 (by rfl) cert_45

theorem cert_488 : Represents 24 10 :=
  segment 6 24 10 30 8 (by rfl) cert_39

theorem cert_493 : Represents 19 17 :=
  segment 5 19 17 24 10 (by rfl) cert_488

theorem cert_496 : Represents 21 19 :=
  segment 1 21 19 22 16 (by rfl) cert_432

theorem cert_499 : Represents 22 20 :=
  segment 2 22 20 24 10 (by rfl) cert_488

theorem cert_501 : Represents 23 21 :=
  segment 1 23 21 24 18 (by rfl) cert_430

theorem cert_524 : Represents 42 22 :=
  segment 22 42 22 64 10 (by rfl) cert_390

theorem cert_526 : Represents 40 26 :=
  segment 2 40 26 42 22 (by rfl) cert_524

theorem cert_534 : Represents 32 26 :=
  segment 8 32 26 40 26 (by rfl) cert_526

theorem cert_542 : Represents 24 22 :=
  segment 8 24 22 32 26 (by rfl) cert_534

theorem cert_545 : Represents 28 26 :=
  segment 2 28 26 30 16 (by rfl) cert_461

theorem cert_548 : Represents 25 23 :=
  segment 3 25 23 28 26 (by rfl) cert_545

theorem cert_577 : Represents 42 40 :=
  segment 28 42 40 70 0 (by rfl) (zero_represents 70)

theorem cert_579 : Represents 40 10 :=
  segment 2 40 10 42 40 (by rfl) cert_577

theorem cert_585 : Represents 34 6 :=
  segment 6 34 6 40 10 (by rfl) cert_579

theorem cert_593 : Represents 26 24 :=
  segment 8 26 24 34 6 (by rfl) cert_585

theorem cert_597 : Represents 27 25 :=
  segment 3 27 25 30 0 (by rfl) (zero_represents 30)

theorem cert_600 : Represents 29 27 :=
  segment 1 29 27 30 24 (by rfl) cert_424

theorem cert_605 : Represents 30 28 :=
  segment 4 30 28 34 6 (by rfl) cert_585

theorem cert_607 : Represents 31 29 :=
  segment 1 31 29 32 26 (by rfl) cert_534

theorem cert_610 : Represents 232 88 :=
  segment 2 232 88 234 118 (by rfl) cert_220

theorem cert_648 : Represents 194 30 :=
  segment 38 194 30 232 88 (by rfl) cert_610

theorem cert_658 : Represents 184 122 :=
  segment 10 184 122 194 30 (by rfl) cert_648

theorem cert_662 : Represents 180 178 :=
  segment 4 180 178 184 122 (by rfl) cert_658

theorem cert_674 : Represents 168 18 :=
  segment 12 168 18 180 178 (by rfl) cert_662

theorem cert_682 : Represents 160 32 :=
  segment 8 160 32 168 18 (by rfl) cert_674

theorem cert_688 : Represents 154 110 :=
  segment 6 154 110 160 32 (by rfl) cert_682

theorem cert_712 : Represents 130 6 :=
  segment 24 130 6 154 110 (by rfl) cert_688

theorem cert_736 : Represents 106 86 :=
  segment 24 106 86 130 6 (by rfl) cert_712

theorem cert_740 : Represents 102 96 :=
  segment 4 102 96 106 86 (by rfl) cert_736

theorem cert_764 : Represents 78 48 :=
  segment 24 78 48 102 96 (by rfl) cert_740

theorem cert_768 : Represents 74 22 :=
  segment 4 74 22 78 48 (by rfl) cert_764

theorem cert_770 : Represents 72 42 :=
  segment 2 72 42 74 22 (by rfl) cert_768

theorem cert_780 : Represents 62 24 :=
  segment 10 62 24 72 42 (by rfl) cert_770

theorem cert_786 : Represents 56 50 :=
  segment 6 56 50 62 24 (by rfl) cert_780

theorem cert_790 : Represents 52 50 :=
  segment 4 52 50 56 50 (by rfl) cert_786

theorem cert_794 : Represents 48 34 :=
  segment 4 48 34 52 50 (by rfl) cert_790

theorem cert_798 : Represents 44 42 :=
  segment 4 44 42 48 34 (by rfl) cert_794

theorem cert_810 : Represents 32 30 :=
  segment 12 32 30 44 42 (by rfl) cert_798

theorem cert_819 : Represents 38 24 :=
  segment 8 38 24 46 0 (by rfl) (zero_represents 46)

theorem cert_824 : Represents 33 31 :=
  segment 5 33 31 38 24 (by rfl) cert_819

theorem cert_833 : Represents 34 32 :=
  segment 8 34 32 42 22 (by rfl) cert_524

theorem cert_855 : Represents 35 33 :=
  segment 21 35 33 56 0 (by rfl) (zero_represents 56)

theorem cert_858 : Represents 36 34 :=
  segment 2 36 34 38 24 (by rfl) cert_819

theorem cert_862 : Represents 37 35 :=
  segment 3 37 35 40 10 (by rfl) cert_579

theorem cert_865 : Represents 38 36 :=
  segment 2 38 36 40 26 (by rfl) cert_526

theorem cert_874 : Represents 134 40 :=
  segment 8 134 40 142 0 (by rfl) (zero_represents 142)

theorem cert_878 : Represents 130 126 :=
  segment 4 130 126 134 40 (by rfl) cert_874

theorem cert_902 : Represents 106 22 :=
  segment 24 106 22 130 126 (by rfl) cert_878

theorem cert_920 : Represents 88 58 :=
  segment 18 88 58 106 22 (by rfl) cert_902

theorem cert_936 : Represents 72 32 :=
  segment 16 72 32 88 58 (by rfl) cert_920

theorem cert_944 : Represents 64 34 :=
  segment 8 64 34 72 32 (by rfl) cert_936

theorem cert_946 : Represents 62 40 :=
  segment 2 62 40 64 34 (by rfl) cert_944

theorem cert_962 : Represents 46 16 :=
  segment 16 46 16 62 40 (by rfl) cert_946

theorem cert_969 : Represents 39 37 :=
  segment 7 39 37 46 16 (by rfl) cert_962

theorem cert_978 : Represents 40 38 :=
  segment 8 40 38 48 8 (by rfl) cert_406

theorem cert_983 : Represents 58 14 :=
  segment 4 58 14 62 40 (by rfl) cert_946

theorem cert_985 : Represents 56 18 :=
  segment 2 56 18 58 14 (by rfl) cert_983

theorem cert_1000 : Represents 41 39 :=
  segment 15 41 39 56 18 (by rfl) cert_985

theorem cert_1005 : Represents 43 41 :=
  segment 3 43 41 46 16 (by rfl) cert_962

theorem cert_1013 : Represents 72 10 :=
  segment 6 72 10 78 40 (by rfl) cert_376

theorem cert_1021 : Represents 64 56 :=
  segment 8 64 56 72 10 (by rfl) cert_1013

theorem cert_1029 : Represents 56 42 :=
  segment 8 56 42 64 56 (by rfl) cert_1021

theorem cert_1040 : Represents 45 43 :=
  segment 11 45 43 56 42 (by rfl) cert_1029

theorem cert_1043 : Represents 46 44 :=
  segment 2 46 44 48 34 (by rfl) cert_794

theorem cert_1061 : Represents 47 45 :=
  segment 17 47 45 64 56 (by rfl) cert_1021

theorem cert_1072 : Represents 48 46 :=
  segment 10 48 46 58 14 (by rfl) cert_983

theorem cert_1077 : Represents 58 46 :=
  segment 4 58 46 62 24 (by rfl) cert_780

theorem cert_1079 : Represents 56 26 :=
  segment 2 56 26 58 46 (by rfl) cert_1077

theorem cert_1086 : Represents 49 47 :=
  segment 7 49 47 56 26 (by rfl) cert_1079

theorem cert_1093 : Represents 50 48 :=
  segment 6 50 48 56 18 (by rfl) cert_985

theorem cert_1101 : Represents 51 49 :=
  segment 7 51 49 58 46 (by rfl) cert_1077

theorem cert_1106 : Represents 53 51 :=
  segment 3 53 51 56 26 (by rfl) cert_1079

theorem cert_1109 : Represents 54 52 :=
  segment 2 54 52 56 42 (by rfl) cert_1029

theorem cert_1111 : Represents 55 53 :=
  segment 1 55 53 56 50 (by rfl) cert_786

theorem cert_1126 : Represents 74 72 :=
  segment 14 74 72 88 0 (by rfl) (zero_represents 88)

theorem cert_1128 : Represents 72 18 :=
  segment 2 72 18 74 72 (by rfl) cert_1126

theorem cert_1136 : Represents 64 2 :=
  segment 8 64 2 72 18 (by rfl) cert_1128

theorem cert_1140 : Represents 60 58 :=
  segment 4 60 58 64 2 (by rfl) cert_1136

theorem cert_1144 : Represents 56 54 :=
  segment 4 56 54 60 58 (by rfl) cert_1140

theorem cert_1401 : Represents 11974 702 :=
  segment 256 11974 702 12230 0 (by rfl) (zero_represents 12230)

theorem cert_1577 : Represents 11798 3120 :=
  segment 176 11798 3120 11974 702 (by rfl) cert_1401

theorem cert_1833 : Represents 11542 7176 :=
  segment 256 11542 7176 11798 3120 (by rfl) cert_1577

theorem cert_2089 : Represents 11286 5918 :=
  segment 256 11286 5918 11542 7176 (by rfl) cert_1833

theorem cert_2345 : Represents 11030 3586 :=
  segment 256 11030 3586 11286 5918 (by rfl) cert_2089

theorem cert_2425 : Represents 10950 8808 :=
  segment 80 10950 8808 11030 3586 (by rfl) cert_2345

theorem cert_2681 : Represents 10694 1178 :=
  segment 256 10694 1178 10950 8808 (by rfl) cert_2425

theorem cert_2937 : Represents 10438 7326 :=
  segment 256 10438 7326 10694 1178 (by rfl) cert_2681

theorem cert_3005 : Represents 10370 3198 :=
  segment 68 10370 3198 10438 7326 (by rfl) cert_2937

theorem cert_3261 : Represents 10114 5222 :=
  segment 256 10114 5222 10370 3198 (by rfl) cert_3005

theorem cert_3297 : Represents 10078 6712 :=
  segment 36 10078 6712 10114 5222 (by rfl) cert_3261

theorem cert_3305 : Represents 10070 9744 :=
  segment 8 10070 9744 10078 6712 (by rfl) cert_3297

theorem cert_3335 : Represents 10040 6810 :=
  segment 30 10040 6810 10070 9744 (by rfl) cert_3305

theorem cert_3461 : Represents 9914 5774 :=
  segment 126 9914 5774 10040 6810 (by rfl) cert_3335

theorem cert_3519 : Represents 9856 2152 :=
  segment 58 9856 2152 9914 5774 (by rfl) cert_3461

theorem cert_3549 : Represents 9826 806 :=
  segment 30 9826 806 9856 2152 (by rfl) cert_3519

theorem cert_3677 : Represents 9698 806 :=
  segment 128 9698 806 9826 806 (by rfl) cert_3549

theorem cert_3829 : Represents 9546 7446 :=
  segment 152 9546 7446 9698 806 (by rfl) cert_3677

theorem cert_3873 : Represents 9502 3080 :=
  segment 44 9502 3080 9546 7446 (by rfl) cert_3829

theorem cert_3905 : Represents 9470 1800 :=
  segment 32 9470 1800 9502 3080 (by rfl) cert_3873

theorem cert_3965 : Represents 9410 6302 :=
  segment 60 9410 6302 9470 1800 (by rfl) cert_3905

theorem cert_4015 : Represents 9360 4378 :=
  segment 50 9360 4378 9410 6302 (by rfl) cert_3965

theorem cert_4089 : Represents 9286 3712 :=
  segment 74 9286 3712 9360 4378 (by rfl) cert_4015

theorem cert_4121 : Represents 9254 9000 :=
  segment 32 9254 9000 9286 3712 (by rfl) cert_4089

theorem cert_4255 : Represents 9120 1826 :=
  segment 134 9120 1826 9254 9000 (by rfl) cert_4121

theorem cert_4257 : Represents 9118 5016 :=
  segment 2 9118 5016 9120 1826 (by rfl) cert_4255

theorem cert_4495 : Represents 8880 6312 :=
  segment 238 8880 6312 9118 5016 (by rfl) cert_4257

theorem cert_4503 : Represents 8872 6264 :=
  segment 8 8872 6264 8880 6312 (by rfl) cert_4495

theorem cert_4511 : Represents 8864 5600 :=
  segment 8 8864 5600 8872 6264 (by rfl) cert_4503

theorem cert_4597 : Represents 8778 2582 :=
  segment 86 8778 2582 8864 5600 (by rfl) cert_4511

theorem cert_4639 : Represents 8736 5570 :=
  segment 42 8736 5570 8778 2582 (by rfl) cert_4597

theorem cert_4887 : Represents 8488 6360 :=
  segment 248 8488 6360 8736 5570 (by rfl) cert_4639

theorem cert_4905 : Represents 8470 8464 :=
  segment 18 8470 8464 8488 6360 (by rfl) cert_4887

theorem cert_4925 : Represents 8450 6270 :=
  segment 20 8450 6270 8470 8464 (by rfl) cert_4905

theorem cert_4937 : Represents 8438 1168 :=
  segment 12 8438 1168 8450 6270 (by rfl) cert_4925

theorem cert_5193 : Represents 8182 760 :=
  segment 256 8182 760 8438 1168 (by rfl) cert_4937

theorem cert_5239 : Represents 8136 4786 :=
  segment 46 8136 4786 8182 760 (by rfl) cert_5193

theorem cert_5327 : Represents 8048 5928 :=
  segment 88 8048 5928 8136 4786 (by rfl) cert_5239

theorem cert_5463 : Represents 7912 5674 :=
  segment 136 7912 5674 8048 5928 (by rfl) cert_5327

theorem cert_5511 : Represents 7864 5088 :=
  segment 48 7864 5088 7912 5674 (by rfl) cert_5463

theorem cert_5735 : Represents 7640 6376 :=
  segment 224 7640 6376 7864 5088 (by rfl) cert_5511

theorem cert_5831 : Represents 7544 186 :=
  segment 96 7544 186 7640 6376 (by rfl) cert_5735

theorem cert_6081 : Represents 7294 6136 :=
  segment 250 7294 6136 7544 186 (by rfl) cert_5831

theorem cert_6119 : Represents 7256 416 :=
  segment 38 7256 416 7294 6136 (by rfl) cert_6081

theorem cert_6143 : Represents 7232 4378 :=
  segment 24 7232 4378 7256 416 (by rfl) cert_6119

theorem cert_6333 : Represents 7042 4606 :=
  segment 190 7042 4606 7232 4378 (by rfl) cert_6143

theorem cert_6359 : Represents 7016 5216 :=
  segment 26 7016 5216 7042 4606 (by rfl) cert_6333

theorem cert_6375 : Represents 7000 2112 :=
  segment 16 7000 2112 7016 5216 (by rfl) cert_6359

theorem cert_6423 : Represents 6952 5034 :=
  segment 48 6952 5034 7000 2112 (by rfl) cert_6375

theorem cert_6473 : Represents 6902 1816 :=
  segment 50 6902 1816 6952 5034 (by rfl) cert_6423

theorem cert_6535 : Represents 6840 5408 :=
  segment 62 6840 5408 6902 1816 (by rfl) cert_6473

theorem cert_6687 : Represents 6688 2432 :=
  segment 152 6688 2432 6840 5408 (by rfl) cert_6535

theorem cert_6757 : Represents 6618 3310 :=
  segment 70 6618 3310 6688 2432 (by rfl) cert_6687

theorem cert_6855 : Represents 6520 1106 :=
  segment 98 6520 1106 6618 3310 (by rfl) cert_6757

theorem cert_7111 : Represents 6264 2864 :=
  segment 256 6264 2864 6520 1106 (by rfl) cert_6855

theorem cert_7151 : Represents 6224 2330 :=
  segment 40 6224 2330 6264 2864 (by rfl) cert_7111

theorem cert_7157 : Represents 6218 4118 :=
  segment 6 6218 4118 6224 2330 (by rfl) cert_7151

theorem cert_7317 : Represents 6058 3030 :=
  segment 160 6058 3030 6218 4118 (by rfl) cert_7157

theorem cert_7359 : Represents 6016 2938 :=
  segment 42 6016 2938 6058 3030 (by rfl) cert_7317

theorem cert_7447 : Represents 5928 1618 :=
  segment 88 5928 1618 6016 2938 (by rfl) cert_7359

theorem cert_7487 : Represents 5888 4256 :=
  segment 40 5888 4256 5928 1618 (by rfl) cert_7447

theorem cert_7639 : Represents 5736 5336 :=
  segment 152 5736 5336 5888 4256 (by rfl) cert_7487

theorem cert_7645 : Represents 5730 1606 :=
  segment 6 5730 1606 5736 5336 (by rfl) cert_7639

theorem cert_7703 : Represents 5672 586 :=
  segment 58 5672 586 5730 1606 (by rfl) cert_7645

theorem cert_7735 : Represents 5640 4504 :=
  segment 32 5640 4504 5672 586 (by rfl) cert_7703

theorem cert_7775 : Represents 5600 546 :=
  segment 40 5600 546 5640 4504 (by rfl) cert_7735

theorem cert_7895 : Represents 5480 376 :=
  segment 120 5480 376 5600 546 (by rfl) cert_7775

theorem cert_7905 : Represents 5470 5344 :=
  segment 10 5470 5344 5480 376 (by rfl) cert_7895

theorem cert_7919 : Represents 5456 4360 :=
  segment 14 5456 4360 5470 5344 (by rfl) cert_7905

theorem cert_7967 : Represents 5408 3840 :=
  segment 48 5408 3840 5456 4360 (by rfl) cert_7919

theorem cert_8127 : Represents 5248 3552 :=
  segment 160 5248 3552 5408 3840 (by rfl) cert_7967

theorem cert_8241 : Represents 5134 3648 :=
  segment 114 5134 3648 5248 3552 (by rfl) cert_8127

theorem cert_8319 : Represents 5056 986 :=
  segment 78 5056 986 5134 3648 (by rfl) cert_8241

theorem cert_8383 : Represents 4992 4576 :=
  segment 64 4992 4576 5056 986 (by rfl) cert_8319

theorem cert_8417 : Represents 4958 3440 :=
  segment 34 4958 3440 4992 4576 (by rfl) cert_8383

theorem cert_8449 : Represents 4926 3168 :=
  segment 32 4926 3168 4958 3440 (by rfl) cert_8417

theorem cert_8607 : Represents 4768 3168 :=
  segment 158 4768 3168 4926 3168 (by rfl) cert_8449

theorem cert_8721 : Represents 4654 2904 :=
  segment 114 4654 2904 4768 3168 (by rfl) cert_8607

theorem cert_8765 : Represents 4610 1406 :=
  segment 44 4610 1406 4654 2904 (by rfl) cert_8721

theorem cert_8767 : Represents 4608 2656 :=
  segment 2 4608 2656 4610 1406 (by rfl) cert_8765

theorem cert_8807 : Represents 4568 1946 :=
  segment 40 4568 1946 4608 2656 (by rfl) cert_8767

theorem cert_8935 : Represents 4440 3642 :=
  segment 128 4440 3642 4568 1946 (by rfl) cert_8807

theorem cert_8937 : Represents 4438 4240 :=
  segment 2 4438 4240 4440 3642 (by rfl) cert_8935

theorem cert_8949 : Represents 4426 2326 :=
  segment 12 4426 2326 4438 4240 (by rfl) cert_8937

theorem cert_9045 : Represents 4330 3990 :=
  segment 96 4330 3990 4426 2326 (by rfl) cert_8949

theorem cert_9185 : Represents 4190 2792 :=
  segment 140 4190 2792 4330 3990 (by rfl) cert_9045

theorem cert_9279 : Represents 4096 1378 :=
  segment 94 4096 1378 4190 2792 (by rfl) cert_9185

theorem cert_9303 : Represents 4072 3562 :=
  segment 24 4072 3562 4096 1378 (by rfl) cert_9279

theorem cert_9319 : Represents 4056 4018 :=
  segment 16 4056 4018 4072 3562 (by rfl) cert_9303

theorem cert_9327 : Represents 4048 4034 :=
  segment 8 4048 4034 4056 4018 (by rfl) cert_9319

theorem cert_9375 : Represents 4000 2016 :=
  segment 48 4000 2016 4048 4034 (by rfl) cert_9327

theorem cert_9405 : Represents 3970 1926 :=
  segment 30 3970 1926 4000 2016 (by rfl) cert_9375

theorem cert_9407 : Represents 3968 2466 :=
  segment 2 3968 2466 3970 1926 (by rfl) cert_9405

theorem cert_9481 : Represents 3894 1832 :=
  segment 74 3894 1832 3968 2466 (by rfl) cert_9407

theorem cert_9545 : Represents 3830 744 :=
  segment 64 3830 744 3894 1832 (by rfl) cert_9481

theorem cert_9561 : Represents 3814 3784 :=
  segment 16 3814 3784 3830 744 (by rfl) cert_9545

theorem cert_9605 : Represents 3770 3118 :=
  segment 44 3770 3118 3814 3784 (by rfl) cert_9561

theorem cert_9609 : Represents 3766 1608 :=
  segment 4 3766 1608 3770 3118 (by rfl) cert_9605

theorem cert_9631 : Represents 3744 490 :=
  segment 22 3744 490 3766 1608 (by rfl) cert_9609

theorem cert_9663 : Represents 3712 3328 :=
  segment 32 3712 3328 3744 490 (by rfl) cert_9631

theorem cert_9669 : Represents 3706 110 :=
  segment 6 3706 110 3712 3328 (by rfl) cert_9663

theorem cert_9767 : Represents 3608 1562 :=
  segment 98 3608 1562 3706 110 (by rfl) cert_9669

theorem cert_9831 : Represents 3544 2152 :=
  segment 64 3544 2152 3608 1562 (by rfl) cert_9767

theorem cert_10087 : Represents 3288 562 :=
  segment 256 3288 562 3544 2152 (by rfl) cert_9831

theorem cert_10133 : Represents 3242 2262 :=
  segment 46 3242 2262 3288 562 (by rfl) cert_10087

theorem cert_10161 : Represents 3214 2192 :=
  segment 28 3214 2192 3242 2262 (by rfl) cert_10133

theorem cert_10273 : Represents 3102 2984 :=
  segment 112 3102 2984 3214 2192 (by rfl) cert_10161

theorem cert_10305 : Represents 3070 1024 :=
  segment 32 3070 1024 3102 2984 (by rfl) cert_10273

theorem cert_10353 : Represents 3022 2896 :=
  segment 48 3022 2896 3070 1024 (by rfl) cert_10305

theorem cert_10397 : Represents 2978 1734 :=
  segment 44 2978 1734 3022 2896 (by rfl) cert_10353

theorem cert_10433 : Represents 2942 1472 :=
  segment 36 2942 1472 2978 1734 (by rfl) cert_10397

theorem cert_10463 : Represents 2912 354 :=
  segment 30 2912 354 2942 1472 (by rfl) cert_10433

theorem cert_10487 : Represents 2888 234 :=
  segment 24 2888 234 2912 354 (by rfl) cert_10463

theorem cert_10519 : Represents 2856 800 :=
  segment 32 2856 800 2888 234 (by rfl) cert_10487

theorem cert_10615 : Represents 2760 298 :=
  segment 96 2760 298 2856 800 (by rfl) cert_10519

theorem cert_10623 : Represents 2752 1314 :=
  segment 8 2752 1314 2760 298 (by rfl) cert_10615

theorem cert_10741 : Represents 2634 406 :=
  segment 118 2634 406 2752 1314 (by rfl) cert_10623

theorem cert_10753 : Represents 2622 1520 :=
  segment 12 2622 1520 2634 406 (by rfl) cert_10741

theorem cert_10789 : Represents 2586 142 :=
  segment 36 2586 142 2622 1520 (by rfl) cert_10753

theorem cert_10815 : Represents 2560 2154 :=
  segment 26 2560 2154 2586 142 (by rfl) cert_10789

theorem cert_10821 : Represents 2554 2190 :=
  segment 6 2554 2190 2560 2154 (by rfl) cert_10815

theorem cert_10879 : Represents 2496 1792 :=
  segment 58 2496 1792 2554 2190 (by rfl) cert_10821

theorem cert_10909 : Represents 2466 1086 :=
  segment 30 2466 1086 2496 1792 (by rfl) cert_10879

theorem cert_10969 : Represents 2406 1384 :=
  segment 60 2406 1384 2466 1086 (by rfl) cert_10909

theorem cert_10983 : Represents 2392 890 :=
  segment 14 2392 890 2406 1384 (by rfl) cert_10969

theorem cert_11037 : Represents 2338 1606 :=
  segment 54 2338 1606 2392 890 (by rfl) cert_10983

theorem cert_11087 : Represents 2288 2058 :=
  segment 50 2288 2058 2338 1606 (by rfl) cert_11037

theorem cert_11143 : Represents 2232 186 :=
  segment 56 2232 186 2288 2058 (by rfl) cert_11087

theorem cert_11157 : Represents 2218 374 :=
  segment 14 2218 374 2232 186 (by rfl) cert_11143

theorem cert_11325 : Represents 2050 1574 :=
  segment 168 2050 1574 2218 374 (by rfl) cert_11157

theorem cert_11361 : Represents 2014 864 :=
  segment 36 2014 864 2050 1574 (by rfl) cert_11325

theorem cert_11455 : Represents 1920 514 :=
  segment 94 1920 514 2014 864 (by rfl) cert_11361

theorem cert_11527 : Represents 1848 1600 :=
  segment 72 1848 1600 1920 514 (by rfl) cert_11455

theorem cert_11599 : Represents 1776 824 :=
  segment 72 1776 824 1848 1600 (by rfl) cert_11527

theorem cert_11615 : Represents 1760 8 :=
  segment 16 1760 8 1776 824 (by rfl) cert_11599

theorem cert_11647 : Represents 1728 72 :=
  segment 32 1728 72 1760 8 (by rfl) cert_11615

theorem cert_11677 : Represents 1698 478 :=
  segment 30 1698 478 1728 72 (by rfl) cert_11647

theorem cert_11709 : Represents 1666 1022 :=
  segment 32 1666 1022 1698 478 (by rfl) cert_11677

theorem cert_11729 : Represents 1646 560 :=
  segment 20 1646 560 1666 1022 (by rfl) cert_11709

theorem cert_11743 : Represents 1632 506 :=
  segment 14 1632 506 1646 560 (by rfl) cert_11729

theorem cert_11807 : Represents 1568 610 :=
  segment 64 1568 610 1632 506 (by rfl) cert_11743

theorem cert_11873 : Represents 1502 752 :=
  segment 66 1502 752 1568 610 (by rfl) cert_11807

theorem cert_11889 : Represents 1486 1000 :=
  segment 16 1486 1000 1502 752 (by rfl) cert_11873

theorem cert_11975 : Represents 1400 1274 :=
  segment 86 1400 1274 1486 1000 (by rfl) cert_11889

theorem cert_11977 : Represents 1398 1368 :=
  segment 2 1398 1368 1400 1274 (by rfl) cert_11975

theorem cert_12017 : Represents 1358 1024 :=
  segment 40 1358 1024 1398 1368 (by rfl) cert_11977

theorem cert_12033 : Represents 1342 96 :=
  segment 16 1342 96 1358 1024 (by rfl) cert_12017

theorem cert_12037 : Represents 1338 1262 :=
  segment 4 1338 1262 1342 96 (by rfl) cert_12033

theorem cert_12105 : Represents 1270 1264 :=
  segment 68 1270 1264 1338 1262 (by rfl) cert_12037

theorem cert_12119 : Represents 1256 672 :=
  segment 14 1256 672 1270 1264 (by rfl) cert_12105

theorem cert_12159 : Represents 1216 1090 :=
  segment 40 1216 1090 1256 672 (by rfl) cert_12119

theorem cert_12185 : Represents 1190 200 :=
  segment 26 1190 200 1216 1090 (by rfl) cert_12159

theorem cert_12223 : Represents 1152 1056 :=
  segment 38 1152 1056 1190 200 (by rfl) cert_12185

theorem cert_12239 : Represents 1136 392 :=
  segment 16 1136 392 1152 1056 (by rfl) cert_12223

theorem cert_12311 : Represents 1064 920 :=
  segment 72 1064 920 1136 392 (by rfl) cert_12239

theorem cert_12327 : Represents 1048 250 :=
  segment 16 1048 250 1064 920 (by rfl) cert_12311

theorem cert_12359 : Represents 1016 384 :=
  segment 32 1016 384 1048 250 (by rfl) cert_12327

theorem cert_12439 : Represents 936 536 :=
  segment 80 936 536 1016 384 (by rfl) cert_12359

theorem cert_12469 : Represents 906 278 :=
  segment 30 906 278 936 536 (by rfl) cert_12439

theorem cert_12481 : Represents 894 392 :=
  segment 12 894 392 906 278 (by rfl) cert_12469

theorem cert_12513 : Represents 862 512 :=
  segment 32 862 512 894 392 (by rfl) cert_12481

theorem cert_12549 : Represents 826 622 :=
  segment 36 826 622 862 512 (by rfl) cert_12513

theorem cert_12647 : Represents 728 690 :=
  segment 98 728 690 826 622 (by rfl) cert_12549

theorem cert_12703 : Represents 672 610 :=
  segment 56 672 610 728 690 (by rfl) cert_12647

theorem cert_12707 : Represents 668 666 :=
  segment 4 668 666 672 610 (by rfl) cert_12703

theorem cert_12735 : Represents 640 514 :=
  segment 28 640 514 668 666 (by rfl) cert_12707

theorem cert_12737 : Represents 638 608 :=
  segment 2 638 608 640 514 (by rfl) cert_12735

theorem cert_12761 : Represents 614 408 :=
  segment 24 614 408 638 608 (by rfl) cert_12737

theorem cert_12783 : Represents 592 152 :=
  segment 22 592 152 614 408 (by rfl) cert_12761

theorem cert_12789 : Represents 586 342 :=
  segment 6 586 342 592 152 (by rfl) cert_12783

theorem cert_12797 : Represents 578 350 :=
  segment 8 578 350 586 342 (by rfl) cert_12789

theorem cert_12799 : Represents 576 232 :=
  segment 2 576 232 578 350 (by rfl) cert_12797

theorem cert_12865 : Represents 510 136 :=
  segment 66 510 136 576 232 (by rfl) cert_12799

theorem cert_12879 : Represents 496 154 :=
  segment 14 496 154 510 136 (by rfl) cert_12865

theorem cert_12897 : Represents 478 424 :=
  segment 18 478 424 496 154 (by rfl) cert_12879

theorem cert_12903 : Represents 472 384 :=
  segment 6 472 384 478 424 (by rfl) cert_12897

theorem cert_12919 : Represents 456 120 :=
  segment 16 456 120 472 384 (by rfl) cert_12903

theorem cert_12925 : Represents 450 94 :=
  segment 6 450 94 456 120 (by rfl) cert_12919

theorem cert_12945 : Represents 430 216 :=
  segment 20 430 216 450 94 (by rfl) cert_12925

theorem cert_12991 : Represents 384 330 :=
  segment 46 384 330 430 216 (by rfl) cert_12945

theorem cert_13087 : Represents 288 34 :=
  segment 96 288 34 384 330 (by rfl) cert_12991

theorem cert_13103 : Represents 272 138 :=
  segment 16 272 138 288 34 (by rfl) cert_13087

theorem cert_13121 : Represents 254 240 :=
  segment 18 254 240 272 138 (by rfl) cert_13103

theorem cert_13125 : Represents 250 78 :=
  segment 4 250 78 254 240 (by rfl) cert_13121

theorem cert_13129 : Represents 246 144 :=
  segment 4 246 144 250 78 (by rfl) cert_13125

theorem cert_13159 : Represents 216 50 :=
  segment 30 216 50 246 144 (by rfl) cert_13129

theorem cert_13161 : Represents 214 120 :=
  segment 2 214 120 216 50 (by rfl) cert_13159

theorem cert_13189 : Represents 186 46 :=
  segment 28 186 46 214 120 (by rfl) cert_13161

theorem cert_13201 : Represents 174 8 :=
  segment 12 174 8 186 46 (by rfl) cert_13189

theorem cert_13215 : Represents 160 66 :=
  segment 14 160 66 174 8 (by rfl) cert_13201

theorem cert_13239 : Represents 136 56 :=
  segment 24 136 56 160 66 (by rfl) cert_13215

theorem cert_13241 : Represents 134 48 :=
  segment 2 134 48 136 56 (by rfl) cert_13239

theorem cert_13247 : Represents 128 104 :=
  segment 6 128 104 134 48 (by rfl) cert_13241

theorem cert_13277 : Represents 98 30 :=
  segment 30 98 30 128 104 (by rfl) cert_13247

theorem cert_13285 : Represents 90 14 :=
  segment 8 90 14 98 30 (by rfl) cert_13277

theorem cert_13318 : Represents 57 55 :=
  segment 33 57 55 90 14 (by rfl) cert_13285

theorem cert_13323 : Represents 58 56 :=
  segment 4 58 56 62 0 (by rfl) (zero_represents 62)

theorem cert_13329 : Represents 59 57 :=
  segment 5 59 57 64 2 (by rfl) cert_1136

theorem cert_13334 : Represents 61 59 :=
  segment 3 61 59 64 34 (by rfl) cert_944

theorem cert_13337 : Represents 70 64 :=
  segment 2 70 64 72 42 (by rfl) cert_770

theorem cert_13345 : Represents 62 60 :=
  segment 8 62 60 70 64 (by rfl) cert_13337

theorem cert_13348 : Represents 70 40 :=
  segment 2 70 40 72 18 (by rfl) cert_1128

theorem cert_13355 : Represents 63 61 :=
  segment 7 63 61 70 40 (by rfl) cert_13348

theorem cert_13366 : Represents 64 62 :=
  segment 10 64 62 74 22 (by rfl) cert_768

theorem cert_13385 : Represents 78 64 :=
  segment 18 78 64 96 40 (by rfl) cert_358

theorem cert_13398 : Represents 65 63 :=
  segment 13 65 63 78 64 (by rfl) cert_13385

theorem cert_13405 : Represents 66 64 :=
  segment 6 66 64 72 32 (by rfl) cert_936

theorem cert_13409 : Represents 67 65 :=
  segment 3 67 65 70 40 (by rfl) cert_13348

theorem cert_13414 : Represents 68 66 :=
  segment 4 68 66 72 10 (by rfl) cert_1013

theorem cert_13416 : Represents 69 67 :=
  segment 1 69 67 70 64 (by rfl) cert_13337

theorem cert_13445 : Represents 70 68 :=
  segment 28 70 68 98 62 (by rfl) cert_356

theorem cert_13518 : Represents 174 168 :=
  segment 72 174 168 246 104 (by rfl) cert_208

theorem cert_13532 : Represents 160 96 :=
  segment 14 160 96 174 168 (by rfl) cert_13518

theorem cert_13564 : Represents 128 26 :=
  segment 32 128 26 160 96 (by rfl) cert_13532

theorem cert_13588 : Represents 104 96 :=
  segment 24 104 96 128 26 (by rfl) cert_13564

theorem cert_13594 : Represents 98 70 :=
  segment 6 98 70 104 96 (by rfl) cert_13588

theorem cert_13602 : Represents 90 78 :=
  segment 8 90 78 98 70 (by rfl) cert_13594

theorem cert_13621 : Represents 71 69 :=
  segment 19 71 69 90 78 (by rfl) cert_13602

theorem cert_13640 : Represents 88 82 :=
  segment 18 88 82 106 22 (by rfl) cert_902

theorem cert_13648 : Represents 80 66 :=
  segment 8 80 66 88 82 (by rfl) cert_13640

theorem cert_13656 : Represents 72 70 :=
  segment 8 72 70 80 66 (by rfl) cert_13648

theorem cert_13673 : Represents 88 50 :=
  segment 16 88 50 104 0 (by rfl) (zero_represents 104)

theorem cert_13688 : Represents 73 71 :=
  segment 15 73 71 88 50 (by rfl) cert_13673

theorem cert_13693 : Represents 75 73 :=
  segment 3 75 73 78 48 (by rfl) cert_764

theorem cert_13696 : Represents 76 74 :=
  segment 2 76 74 78 64 (by rfl) cert_13385

theorem cert_13710 : Represents 77 75 :=
  segment 13 77 75 90 78 (by rfl) cert_13602

theorem cert_13713 : Represents 78 76 :=
  segment 2 78 76 80 66 (by rfl) cert_13648

theorem cert_13729 : Represents 79 77 :=
  segment 15 79 77 94 0 (by rfl) (zero_represents 94)

theorem cert_13748 : Represents 88 8 :=
  segment 18 88 8 106 86 (by rfl) cert_736

theorem cert_13756 : Represents 80 78 :=
  segment 8 80 78 88 8 (by rfl) cert_13748

theorem cert_13777 : Represents 134 80 :=
  segment 20 134 80 154 110 (by rfl) cert_688

theorem cert_13793 : Represents 118 48 :=
  segment 16 118 48 134 80 (by rfl) cert_13777

theorem cert_13813 : Represents 98 38 :=
  segment 20 98 38 118 48 (by rfl) cert_13793

theorem cert_13815 : Represents 96 58 :=
  segment 2 96 58 98 38 (by rfl) cert_13813

theorem cert_13830 : Represents 81 79 :=
  segment 15 81 79 96 58 (by rfl) cert_13815

theorem cert_13837 : Represents 82 80 :=
  segment 6 82 80 88 8 (by rfl) cert_13748

theorem cert_13843 : Represents 83 81 :=
  segment 5 83 81 88 50 (by rfl) cert_13673

theorem cert_13850 : Represents 84 82 :=
  segment 6 84 82 90 14 (by rfl) cert_13285

theorem cert_13854 : Represents 85 83 :=
  segment 3 85 83 88 58 (by rfl) cert_920

theorem cert_13859 : Represents 94 80 :=
  segment 4 94 80 98 38 (by rfl) cert_13813

theorem cert_13867 : Represents 86 84 :=
  segment 8 86 84 94 80 (by rfl) cert_13859

theorem cert_13869 : Represents 87 85 :=
  segment 1 87 85 88 82 (by rfl) cert_13640

theorem cert_13892 : Represents 106 54 :=
  segment 22 106 54 128 26 (by rfl) cert_13564

theorem cert_13910 : Represents 88 86 :=
  segment 18 88 86 106 54 (by rfl) cert_13892

theorem cert_13918 : Represents 89 87 :=
  segment 7 89 87 96 58 (by rfl) cert_13815

theorem cert_13927 : Represents 90 88 :=
  segment 8 90 88 98 30 (by rfl) cert_13277

theorem cert_13930 : Represents 96 66 :=
  segment 2 96 66 98 70 (by rfl) cert_13594

theorem cert_13935 : Represents 91 89 :=
  segment 5 91 89 96 66 (by rfl) cert_13930

theorem cert_13938 : Represents 92 90 :=
  segment 2 92 90 94 80 (by rfl) cert_13859

theorem cert_13942 : Represents 93 91 :=
  segment 3 93 91 96 66 (by rfl) cert_13930

theorem cert_13965 : Represents 112 104 :=
  segment 22 112 104 134 80 (by rfl) cert_13777

theorem cert_13973 : Represents 104 90 :=
  segment 8 104 90 112 104 (by rfl) cert_13965

theorem cert_13983 : Represents 94 92 :=
  segment 10 94 92 104 90 (by rfl) cert_13973

theorem cert_13995 : Represents 95 93 :=
  segment 11 95 93 106 54 (by rfl) cert_13892

theorem cert_14004 : Represents 96 94 :=
  segment 8 96 94 104 96 (by rfl) cert_13588

theorem cert_14026 : Represents 97 95 :=
  segment 21 97 95 118 72 (by rfl) cert_336

theorem cert_14037 : Represents 174 48 :=
  segment 10 174 48 184 122 (by rfl) cert_658

theorem cert_14051 : Represents 160 152 :=
  segment 14 160 152 174 48 (by rfl) cert_14037

theorem cert_14081 : Represents 130 128 :=
  segment 30 130 128 160 152 (by rfl) cert_14051

theorem cert_14113 : Represents 98 96 :=
  segment 32 98 96 130 128 (by rfl) cert_14081

theorem cert_14119 : Represents 99 97 :=
  segment 5 99 97 104 82 (by rfl) cert_350

theorem cert_14132 : Represents 100 98 :=
  segment 12 100 98 112 104 (by rfl) cert_13965

theorem cert_14134 : Represents 101 99 :=
  segment 1 101 99 102 96 (by rfl) cert_740

theorem cert_14137 : Represents 102 100 :=
  segment 2 102 100 104 90 (by rfl) cert_13973

theorem cert_14154 : Represents 1486 488 :=
  segment 16 1486 488 1502 752 (by rfl) cert_11873

theorem cert_14230 : Represents 1410 422 :=
  segment 76 1410 422 1486 488 (by rfl) cert_14154

theorem cert_14240 : Represents 1400 128 :=
  segment 10 1400 128 1410 422 (by rfl) cert_14230

theorem cert_14288 : Represents 1352 1338 :=
  segment 48 1352 1338 1400 128 (by rfl) cert_14240

theorem cert_14298 : Represents 1342 1248 :=
  segment 10 1342 1248 1352 1338 (by rfl) cert_14288

theorem cert_14360 : Represents 1280 522 :=
  segment 62 1280 522 1342 1248 (by rfl) cert_14298

theorem cert_14384 : Represents 1256 586 :=
  segment 24 1256 586 1280 522 (by rfl) cert_14360

theorem cert_14434 : Represents 1206 808 :=
  segment 50 1206 808 1256 586 (by rfl) cert_14384

theorem cert_14488 : Represents 1152 98 :=
  segment 54 1152 98 1206 808 (by rfl) cert_14434

theorem cert_14504 : Represents 1136 746 :=
  segment 16 1136 746 1152 98 (by rfl) cert_14488

theorem cert_14528 : Represents 1112 90 :=
  segment 24 1112 90 1136 746 (by rfl) cert_14504

theorem cert_14576 : Represents 1064 146 :=
  segment 48 1064 146 1112 90 (by rfl) cert_14528

theorem cert_14592 : Represents 1048 800 :=
  segment 16 1048 800 1064 146 (by rfl) cert_14576

theorem cert_14624 : Represents 1016 634 :=
  segment 32 1016 634 1048 800 (by rfl) cert_14592

theorem cert_14632 : Represents 1008 504 :=
  segment 8 1008 504 1016 634 (by rfl) cert_14624

theorem cert_14704 : Represents 936 402 :=
  segment 72 936 402 1008 504 (by rfl) cert_14632

theorem cert_14734 : Represents 906 630 :=
  segment 30 906 630 936 402 (by rfl) cert_14704

theorem cert_14778 : Represents 862 352 :=
  segment 44 862 352 906 630 (by rfl) cert_14734

theorem cert_14814 : Represents 826 206 :=
  segment 36 826 206 862 352 (by rfl) cert_14778

theorem cert_14856 : Represents 784 760 :=
  segment 42 784 760 826 206 (by rfl) cert_14814

theorem cert_14912 : Represents 728 40 :=
  segment 56 728 40 784 760 (by rfl) cert_14856

theorem cert_14930 : Represents 710 456 :=
  segment 18 710 456 728 40 (by rfl) cert_14912

theorem cert_15000 : Represents 640 128 :=
  segment 70 640 128 710 456 (by rfl) cert_14930

theorem cert_15034 : Represents 606 352 :=
  segment 34 606 352 640 128 (by rfl) cert_15000

theorem cert_15062 : Represents 578 230 :=
  segment 28 578 230 606 352 (by rfl) cert_15034

theorem cert_15090 : Represents 550 296 :=
  segment 28 550 296 578 230 (by rfl) cert_15062

theorem cert_15100 : Represents 540 538 :=
  segment 10 540 538 550 296 (by rfl) cert_15090

theorem cert_15122 : Represents 518 24 :=
  segment 22 518 24 540 538 (by rfl) cert_15100

theorem cert_15128 : Represents 512 482 :=
  segment 6 512 482 518 24 (by rfl) cert_15122

theorem cert_15130 : Represents 510 376 :=
  segment 2 510 376 512 482 (by rfl) cert_15128

theorem cert_15138 : Represents 502 456 :=
  segment 8 502 456 510 376 (by rfl) cert_15130

theorem cert_15158 : Represents 482 326 :=
  segment 20 482 326 502 456 (by rfl) cert_15138

theorem cert_15176 : Represents 464 88 :=
  segment 18 464 88 482 326 (by rfl) cert_15158

theorem cert_15198 : Represents 442 110 :=
  segment 22 442 110 464 88 (by rfl) cert_15176

theorem cert_15218 : Represents 422 368 :=
  segment 20 422 368 442 110 (by rfl) cert_15198

theorem cert_15226 : Represents 414 8 :=
  segment 8 414 8 422 368 (by rfl) cert_15218

theorem cert_15264 : Represents 376 274 :=
  segment 38 376 274 414 8 (by rfl) cert_15226

theorem cert_15278 : Represents 362 360 :=
  segment 14 362 360 376 274 (by rfl) cert_15264

theorem cert_15296 : Represents 344 8 :=
  segment 18 344 8 362 360 (by rfl) cert_15278

theorem cert_15304 : Represents 336 322 :=
  segment 8 336 322 344 8 (by rfl) cert_15296

theorem cert_15330 : Represents 310 248 :=
  segment 26 310 248 336 322 (by rfl) cert_15304

theorem cert_15346 : Represents 294 96 :=
  segment 16 294 96 310 248 (by rfl) cert_15330

theorem cert_15352 : Represents 288 74 :=
  segment 6 288 74 294 96 (by rfl) cert_15346

theorem cert_15358 : Represents 282 174 :=
  segment 6 282 174 288 74 (by rfl) cert_15352

theorem cert_15360 : Represents 280 114 :=
  segment 2 280 114 282 174 (by rfl) cert_15358

theorem cert_15362 : Represents 278 168 :=
  segment 2 278 168 280 114 (by rfl) cert_15360

theorem cert_15370 : Represents 270 216 :=
  segment 8 270 216 278 168 (by rfl) cert_15362

theorem cert_15374 : Represents 266 214 :=
  segment 4 266 214 270 216 (by rfl) cert_15370

theorem cert_15376 : Represents 264 120 :=
  segment 2 264 120 266 214 (by rfl) cert_15374

theorem cert_15382 : Represents 258 6 :=
  segment 6 258 6 264 120 (by rfl) cert_15376

theorem cert_15410 : Represents 230 200 :=
  segment 28 230 200 258 6 (by rfl) cert_15382

theorem cert_15422 : Represents 218 142 :=
  segment 12 218 142 230 200 (by rfl) cert_15410

theorem cert_15438 : Represents 202 150 :=
  segment 16 202 150 218 142 (by rfl) cert_15422

theorem cert_15442 : Represents 198 184 :=
  segment 4 198 184 202 150 (by rfl) cert_15438

theorem cert_15446 : Represents 194 158 :=
  segment 4 194 158 198 184 (by rfl) cert_15442

theorem cert_15448 : Represents 192 136 :=
  segment 2 192 136 194 158 (by rfl) cert_15446

theorem cert_15456 : Represents 184 50 :=
  segment 8 184 50 192 136 (by rfl) cert_15448

theorem cert_15490 : Represents 150 120 :=
  segment 34 150 120 184 50 (by rfl) cert_15456

theorem cert_15506 : Represents 134 24 :=
  segment 16 134 24 150 120 (by rfl) cert_15490

theorem cert_15522 : Represents 118 104 :=
  segment 16 118 104 134 24 (by rfl) cert_15506

theorem cert_15537 : Represents 103 101 :=
  segment 15 103 101 118 104 (by rfl) cert_15522

theorem cert_15546 : Represents 120 90 :=
  segment 8 120 90 128 0 (by rfl) (zero_represents 128)

theorem cert_15562 : Represents 104 102 :=
  segment 16 104 102 120 90 (by rfl) cert_15546

theorem cert_15576 : Represents 105 103 :=
  segment 13 105 103 118 48 (by rfl) cert_13793

theorem cert_15581 : Represents 126 16 :=
  segment 4 126 16 130 126 (by rfl) cert_878

theorem cert_15601 : Represents 106 104 :=
  segment 20 106 104 126 16 (by rfl) cert_15581

theorem cert_15626 : Represents 296 210 :=
  segment 24 296 210 320 0 (by rfl) (zero_represents 320)

theorem cert_15642 : Represents 280 168 :=
  segment 16 280 168 296 210 (by rfl) cert_15626

theorem cert_15644 : Represents 278 112 :=
  segment 2 278 112 280 168 (by rfl) cert_15642

theorem cert_15652 : Represents 270 56 :=
  segment 8 270 56 278 112 (by rfl) cert_15644

theorem cert_15656 : Represents 266 54 :=
  segment 4 266 54 270 56 (by rfl) cert_15652

theorem cert_15658 : Represents 264 146 :=
  segment 2 264 146 266 54 (by rfl) cert_15656

theorem cert_15664 : Represents 258 254 :=
  segment 6 258 254 264 146 (by rfl) cert_15658

theorem cert_15668 : Represents 254 112 :=
  segment 4 254 112 258 254 (by rfl) cert_15664

theorem cert_15720 : Represents 202 54 :=
  segment 52 202 54 254 112 (by rfl) cert_15668

theorem cert_15728 : Represents 194 38 :=
  segment 8 194 38 202 54 (by rfl) cert_15720

theorem cert_15730 : Represents 192 58 :=
  segment 2 192 58 194 38 (by rfl) cert_15728

theorem cert_15738 : Represents 184 136 :=
  segment 8 184 136 192 58 (by rfl) cert_15730

theorem cert_15760 : Represents 162 160 :=
  segment 22 162 160 184 136 (by rfl) cert_15738

theorem cert_15780 : Represents 142 56 :=
  segment 20 142 56 162 160 (by rfl) cert_15760

theorem cert_15800 : Represents 122 14 :=
  segment 20 122 14 142 56 (by rfl) cert_15780

theorem cert_15810 : Represents 112 98 :=
  segment 10 112 98 122 14 (by rfl) cert_15800

theorem cert_15815 : Represents 107 105 :=
  segment 5 107 105 112 98 (by rfl) cert_15810

theorem cert_15818 : Represents 116 114 :=
  segment 2 116 114 118 104 (by rfl) cert_15522

theorem cert_15826 : Represents 108 106 :=
  segment 8 108 106 116 114 (by rfl) cert_15818

theorem cert_15846 : Represents 109 107 :=
  segment 19 109 107 128 104 (by rfl) cert_13247

theorem cert_15849 : Represents 110 108 :=
  segment 2 110 108 112 98 (by rfl) cert_15810

theorem cert_15851 : Represents 111 109 :=
  segment 1 111 109 112 106 (by rfl) cert_342

theorem cert_15862 : Represents 112 110 :=
  segment 10 112 110 122 14 (by rfl) cert_15800

theorem cert_15876 : Represents 113 111 :=
  segment 13 113 111 126 16 (by rfl) cert_15581

theorem cert_15897 : Represents 114 112 :=
  segment 20 114 112 134 56 (by rfl) cert_320

theorem cert_15904 : Represents 124 122 :=
  segment 6 124 122 130 6 (by rfl) cert_712

theorem cert_15908 : Represents 120 114 :=
  segment 4 120 114 124 122 (by rfl) cert_15904

theorem cert_15913 : Represents 115 113 :=
  segment 5 115 113 120 114 (by rfl) cert_15908

theorem cert_15918 : Represents 117 115 :=
  segment 3 117 115 120 90 (by rfl) cert_15546

theorem cert_15927 : Represents 176 162 :=
  segment 8 176 162 184 64 (by rfl) cert_270

theorem cert_15943 : Represents 160 10 :=
  segment 16 160 10 176 162 (by rfl) cert_15927

theorem cert_15959 : Represents 144 130 :=
  segment 16 144 130 160 10 (by rfl) cert_15943

theorem cert_15961 : Represents 142 104 :=
  segment 2 142 104 144 130 (by rfl) cert_15959

theorem cert_15975 : Represents 128 98 :=
  segment 14 128 98 142 104 (by rfl) cert_15961

theorem cert_15985 : Represents 118 116 :=
  segment 10 118 116 128 98 (by rfl) cert_15975

theorem cert_15987 : Represents 119 117 :=
  segment 1 119 117 120 114 (by rfl) cert_15908

theorem cert_16002 : Represents 120 118 :=
  segment 14 120 118 134 48 (by rfl) cert_13241

theorem cert_16008 : Represents 121 119 :=
  segment 5 121 119 126 0 (by rfl) (zero_represents 126)

theorem cert_16019 : Represents 184 18 :=
  segment 10 184 18 194 158 (by rfl) cert_15446

theorem cert_16029 : Represents 174 120 :=
  segment 10 174 120 184 18 (by rfl) cert_16019

end Erdos261Finite
