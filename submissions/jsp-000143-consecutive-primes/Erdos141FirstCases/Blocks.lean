/- Copyright 2026 James-16. Apache 2.0. Developed with OpenAI Codex assistance. -/
import Erdos141FirstCases.Block
import Lean.Elab.Tactic.Omega
namespace Erdos141FirstCases
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def factors_0 : List ℕ := [0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 53, 2, 3, 2, 5, 2, 61, 2, 3, 2, 17, 2, 13, 2, 3, 2, 137, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 31, 2, 73, 2, 3, 2, 5, 2, 19, 2, 3, 2, 41, 2, 11, 2, 3, 2, 7, 2, 29, 2, 3, 2]
theorem block_0 : BlockCertificate 0 factors_0 := by
  unfold BlockCertificate
  decide +kernel

def factors_1 : List ℕ := [103, 2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 43, 2, 71, 2, 3, 2, 67, 2, 17, 2, 3, 2, 139, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 151, 2, 3, 2, 59, 2, 7, 2, 3, 2, 29, 2, 11, 2, 3, 2, 17, 2, 5, 2]
theorem block_1 : BlockCertificate 64 factors_1 := by
  unfold BlockCertificate
  decide +kernel

def factors_2 : List ℕ := [3, 2, 89, 2, 0, 2, 3, 2, 5, 2, 83, 2, 3, 2, 7, 2, 37, 2, 3, 2, 179, 2, 127, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 43, 2, 3, 2, 23, 2, 163, 2, 3, 2, 13121, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 109, 2]
theorem block_2 : BlockCertificate 128 factors_2 := by
  unfold BlockCertificate
  decide +kernel

def factors_3 : List ℕ := [17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 173, 2, 149, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 4271, 2, 3, 2, 13, 2, 29, 2, 3, 2, 19, 2, 7, 2, 3, 2, 601, 2, 5, 2, 3, 2, 263, 2, 11, 2, 3, 2]
theorem block_3 : BlockCertificate 192 factors_3 := by
  unfold BlockCertificate
  decide +kernel

def factors_4 : List ℕ := [5, 2, 13, 2, 3, 2, 61, 2, 23, 2, 3, 2, 7, 2, 103, 2, 3, 2, 11, 2, 5, 2, 3, 2, 79, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 29, 2, 17, 2, 3, 2, 41, 2, 0, 2, 3, 2, 83, 2, 5, 2, 3, 2, 7, 2, 251, 2, 3, 2, 5, 2, 11, 2]
theorem block_4 : BlockCertificate 256 factors_4 := by
  unfold BlockCertificate
  decide +kernel

def factors_5 : List ℕ := [3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 53, 2, 3, 2, 73, 2, 5, 2, 3, 2, 11, 2, 167, 2, 3, 2, 5, 2, 59, 2, 3, 2, 7, 2, 0, 2, 3, 2, 157, 2, 47, 2, 3, 2, 563, 2, 5, 2, 3, 2, 97, 2, 139, 2, 3, 2, 5, 2, 181, 2, 3, 2, 113, 2]
theorem block_5 : BlockCertificate 320 factors_5 := by
  unfold BlockCertificate
  decide +kernel

def factors_6 : List ℕ := [11, 2, 3, 2, 13, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 223, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 13, 2, 3, 2, 191, 2, 0, 2, 3, 2, 367, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 79, 2, 3, 2, 487, 2, 0, 2, 3, 2]
theorem block_6 : BlockCertificate 384 factors_6 := by
  unfold BlockCertificate
  decide +kernel

def factors_7 : List ℕ := [23, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 2741, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 31, 2, 3, 2, 7, 2, 73, 2, 3, 2, 3329, 2, 5, 2, 3, 2, 67, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 149, 2, 19, 2, 3, 2, 0, 2, 71, 2]
theorem block_7 : BlockCertificate 448 factors_7 := by
  unfold BlockCertificate
  decide +kernel

def factors_8 : List ℕ := [3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 11597, 2, 3, 2, 5, 2, 107, 2, 3, 2, 17, 2, 7, 2, 3, 2, 11, 2, 23, 2, 3, 2, 13, 2, 5, 2, 3, 2, 241, 2, 739, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 97, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2]
theorem block_8 : BlockCertificate 512 factors_8 := by
  unfold BlockCertificate
  decide +kernel

def factors_9 : List ℕ := [5, 2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 37, 2, 3, 2, 193, 2, 0, 2, 3, 2, 31, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 613, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 67, 2, 3, 2, 61, 2, 0, 2, 3, 2, 17, 2, 5, 2, 3, 2]
theorem block_9 : BlockCertificate 576 factors_9 := by
  unfold BlockCertificate
  decide +kernel

def factors_10 : List ℕ := [29, 2, 47, 2, 3, 2, 5, 2, 11, 2, 3, 2, 71, 2, 32183, 2, 3, 2, 127, 2, 7, 2, 3, 2, 89, 2, 5, 2, 3, 2, 11, 2, 157, 2, 3, 2, 5, 2, 23, 2, 3, 2, 103, 2, 43, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 13, 2, 7, 2]
theorem block_10 : BlockCertificate 640 factors_10 := by
  unfold BlockCertificate
  decide +kernel

def factors_11 : List ℕ := [3, 2, 5, 2, 41, 2, 3, 2, 151, 2, 11, 2, 3, 2, 4679, 2, 313, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 107, 2, 7, 2, 3, 2, 2347, 2, 61, 2, 3, 2, 53, 2, 5, 2, 3, 2, 281, 2, 0, 2, 3, 2, 5, 2]
theorem block_11 : BlockCertificate 704 factors_11 := by
  unfold BlockCertificate
  decide +kernel

def factors_12 : List ℕ := [0, 2, 3, 2, 7, 2, 20963, 2, 3, 2, 13, 2, 11, 2, 3, 2, 31, 2, 5, 2, 3, 2, 41, 2, 131, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 13, 2, 3, 2, 19, 2, 37, 2, 3, 2, 7, 2, 5, 2, 3, 2, 59, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2]
theorem block_12 : BlockCertificate 768 factors_12 := by
  unfold BlockCertificate
  decide +kernel

def factors_13 : List ℕ := [0, 2, 113, 2, 3, 2, 17, 2, 0, 2, 3, 2, 109, 2, 5, 2, 3, 2, 137, 2, 937, 2, 3, 2, 5, 2, 227, 2, 3, 2, 23, 2, 179, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 103, 2, 3, 2, 67, 2, 173, 2]
theorem block_13 : BlockCertificate 832 factors_13 := by
  unfold BlockCertificate
  decide +kernel

def factors_14 : List ℕ := [3, 2, 7, 2, 3499, 2, 3, 2, 1009, 2, 5, 2, 3, 2, 269, 2, 7, 2, 3, 2, 5, 2, 73, 2, 3, 2, 19, 2, 47, 2, 3, 2, 139, 2, 29, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 97, 2, 7, 2, 3, 2, 37, 2]
theorem block_14 : BlockCertificate 896 factors_14 := by
  unfold BlockCertificate
  decide +kernel

def factors_15 : List ℕ := [13, 2, 3, 2, 4871, 2, 5, 2, 3, 2, 31, 2, 2699, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 29, 2, 397, 2, 3, 2, 61, 2, 5, 2, 3, 2, 11, 2, 101, 2, 3, 2, 5, 2, 17, 2, 3, 2, 13, 2, 151, 2, 3, 2, 47, 2, 89, 2, 3, 2]
theorem block_15 : BlockCertificate 960 factors_15 := by
  unfold BlockCertificate
  decide +kernel

def factors_16 : List ℕ := [7, 2, 5, 2, 3, 2, 27259, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 11, 2, 3, 2, 431, 2, 0, 2, 3, 2, 131, 2, 5, 2, 3, 2, 113, 2, 109, 2, 3, 2, 5, 2, 0, 2, 3, 2, 53, 2, 19, 2, 3, 2, 71, 2, 7, 2, 3, 2, 0, 2, 5, 2]
theorem block_16 : BlockCertificate 1024 factors_16 := by
  unfold BlockCertificate
  decide +kernel

def factors_17 : List ℕ := [3, 2, 13, 2, 23, 2, 3, 2, 5, 2, 149, 2, 3, 2, 181, 2, 29, 2, 3, 2, 7, 2, 11, 2, 3, 2, 43, 2, 5, 2, 3, 2, 3253, 2, 7, 2, 3, 2, 5, 2, 331, 2, 3, 2, 11, 2, 83, 2, 3, 2, 23, 2, 2693, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2]
theorem block_17 : BlockCertificate 1088 factors_17 := by
  unfold BlockCertificate
  decide +kernel

def factors_18 : List ℕ := [163, 2, 3, 2, 5, 2, 367, 2, 3, 2, 29, 2, 7, 2, 3, 2, 13, 2, 107, 2, 3, 2, 59, 2, 5, 2, 3, 2, 37, 2, 191, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 13, 2, 3, 2, 11, 2, 41, 2, 3, 2, 101, 2, 5, 2, 3, 2, 73, 2, 17, 2, 3, 2]
theorem block_18 : BlockCertificate 1152 factors_18 := by
  unfold BlockCertificate
  decide +kernel

def factors_19 : List ℕ := [5, 2, 31, 2, 3, 2, 179, 2, 1949, 2, 3, 2, 79, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 173, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11801, 2, 37, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 29, 2]
theorem block_19 : BlockCertificate 1216 factors_19 := by
  unfold BlockCertificate
  decide +kernel

def factors_20 : List ℕ := [3, 2, 41, 2, 53, 2, 3, 2, 26891, 2, 7, 2, 3, 2, 67, 2, 5, 2, 3, 2, 47, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 227, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 10771, 2, 3, 2, 31, 2]
theorem block_20 : BlockCertificate 1280 factors_20 := by
  unfold BlockCertificate
  decide +kernel

def factors_21 : List ℕ := [167, 2, 3, 2, 17, 2, 13, 2, 3, 2, 239, 2, 5, 2, 3, 2, 7, 2, 71, 2, 3, 2, 5, 2, 23, 2, 3, 2, 43, 2, 7, 2, 3, 2, 19, 2, 2389, 2, 3, 2, 107, 2, 5, 2, 3, 2, 53, 2, 0, 2, 3, 2, 5, 2, 137, 2, 3, 2, 7, 2, 31, 2, 3, 2]
theorem block_21 : BlockCertificate 1344 factors_21 := by
  unfold BlockCertificate
  decide +kernel

def factors_22 : List ℕ := [0, 2, 59, 2, 3, 2, 23, 2, 5, 2, 3, 2, 127, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 631, 2, 3, 2, 257, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 181, 2, 3, 2, 503, 2, 0, 2]
theorem block_22 : BlockCertificate 1408 factors_22 := by
  unfold BlockCertificate
  decide +kernel

def factors_23 : List ℕ := [3, 2, 4603, 2, 5, 2, 3, 2, 13, 2, 61, 2, 3, 2, 5, 2, 47, 2, 3, 2, 19, 2, 0, 2, 3, 2, 109, 2, 7, 2, 3, 2, 71, 2, 5, 2, 3, 2, 29, 2, 113, 2, 3, 2, 5, 2, 17, 2, 3, 2, 10169, 2, 26783, 2, 3, 2, 7, 2, 19, 2, 3, 2, 97, 2]
theorem block_23 : BlockCertificate 1472 factors_23 := by
  unfold BlockCertificate
  decide +kernel

def factors_24 : List ℕ := [5, 2, 3, 2, 311, 2, 7, 2, 3, 2, 5, 2, 317, 2, 3, 2, 17, 2, 89, 2, 3, 2, 13, 2, 0, 2, 3, 2, 191, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 131, 2, 3, 2, 47, 2, 7, 2, 3, 2, 42013, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2]
theorem block_24 : BlockCertificate 1536 factors_24 := by
  unfold BlockCertificate
  decide +kernel

def factors_25 : List ℕ := [0, 2, 53, 2, 3, 2, 5, 2, 101, 2, 3, 2, 7, 2, 157, 2, 3, 2, 151, 2, 17, 2, 3, 2, 37, 2, 5, 2, 3, 2, 43, 2, 83, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 19, 2, 3, 2, 73, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 13, 2]
theorem block_25 : BlockCertificate 1600 factors_25 := by
  unfold BlockCertificate
  decide +kernel

def factors_26 : List ℕ := [3, 2, 5, 2, 7, 2, 3, 2, 137, 2, 127, 2, 3, 2, 167, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 23, 2, 41, 2, 3, 2, 5, 2, 37, 2, 3, 2, 79, 2, 11, 2, 3, 2, 53, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 17, 2, 3, 2, 5, 2]
theorem block_26 : BlockCertificate 1664 factors_26 := by
  unfold BlockCertificate
  decide +kernel

def factors_27 : List ℕ := [97, 2, 3, 2, 89, 2, 907, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 193, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 139, 2, 59, 2, 3, 2, 38333, 2, 11, 2, 3, 2, 41, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 71, 2, 3, 2]
theorem block_27 : BlockCertificate 1728 factors_27 := by
  unfold BlockCertificate
  decide +kernel

def factors_28 : List ℕ := [11, 2, 7, 2, 3, 2, 83, 2, 29, 2, 3, 2, 163, 2, 5, 2, 3, 2, 101, 2, 107, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 17, 2, 3, 2, 23, 2, 67, 2, 3, 2, 19, 2, 5, 2, 3, 2, 131, 2, 1933, 2, 3, 2, 5, 2, 61, 2, 3, 2, 5779, 2, 521, 2]
theorem block_28 : BlockCertificate 1792 factors_28 := by
  unfold BlockCertificate
  decide +kernel

def factors_29 : List ℕ := [3, 2, 11, 2, 79, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 59, 2, 281, 2, 3, 2, 43, 2, 0]
theorem block_29 : BlockCertificate 1856 factors_29 := by
  unfold BlockCertificate
  decide +kernel

theorem composite_between (r : ℕ) (hr : r < 1891) (hmod : r % 210 ≠ 0) :
    ¬ Nat.Prime (start + r) := by
  by_cases h0 : r < 64
  · have he : 0 + (r - 0) = r := by omega
    have hc := composite_from_block 0 factors_0 block_0 (r - 0)
      (by change r - 0 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h1 : r < 128
  · have he : 64 + (r - 64) = r := by omega
    have hc := composite_from_block 64 factors_1 block_1 (r - 64)
      (by change r - 64 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h2 : r < 192
  · have he : 128 + (r - 128) = r := by omega
    have hc := composite_from_block 128 factors_2 block_2 (r - 128)
      (by change r - 128 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h3 : r < 256
  · have he : 192 + (r - 192) = r := by omega
    have hc := composite_from_block 192 factors_3 block_3 (r - 192)
      (by change r - 192 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h4 : r < 320
  · have he : 256 + (r - 256) = r := by omega
    have hc := composite_from_block 256 factors_4 block_4 (r - 256)
      (by change r - 256 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h5 : r < 384
  · have he : 320 + (r - 320) = r := by omega
    have hc := composite_from_block 320 factors_5 block_5 (r - 320)
      (by change r - 320 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h6 : r < 448
  · have he : 384 + (r - 384) = r := by omega
    have hc := composite_from_block 384 factors_6 block_6 (r - 384)
      (by change r - 384 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h7 : r < 512
  · have he : 448 + (r - 448) = r := by omega
    have hc := composite_from_block 448 factors_7 block_7 (r - 448)
      (by change r - 448 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h8 : r < 576
  · have he : 512 + (r - 512) = r := by omega
    have hc := composite_from_block 512 factors_8 block_8 (r - 512)
      (by change r - 512 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h9 : r < 640
  · have he : 576 + (r - 576) = r := by omega
    have hc := composite_from_block 576 factors_9 block_9 (r - 576)
      (by change r - 576 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h10 : r < 704
  · have he : 640 + (r - 640) = r := by omega
    have hc := composite_from_block 640 factors_10 block_10 (r - 640)
      (by change r - 640 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h11 : r < 768
  · have he : 704 + (r - 704) = r := by omega
    have hc := composite_from_block 704 factors_11 block_11 (r - 704)
      (by change r - 704 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h12 : r < 832
  · have he : 768 + (r - 768) = r := by omega
    have hc := composite_from_block 768 factors_12 block_12 (r - 768)
      (by change r - 768 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h13 : r < 896
  · have he : 832 + (r - 832) = r := by omega
    have hc := composite_from_block 832 factors_13 block_13 (r - 832)
      (by change r - 832 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h14 : r < 960
  · have he : 896 + (r - 896) = r := by omega
    have hc := composite_from_block 896 factors_14 block_14 (r - 896)
      (by change r - 896 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h15 : r < 1024
  · have he : 960 + (r - 960) = r := by omega
    have hc := composite_from_block 960 factors_15 block_15 (r - 960)
      (by change r - 960 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h16 : r < 1088
  · have he : 1024 + (r - 1024) = r := by omega
    have hc := composite_from_block 1024 factors_16 block_16 (r - 1024)
      (by change r - 1024 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h17 : r < 1152
  · have he : 1088 + (r - 1088) = r := by omega
    have hc := composite_from_block 1088 factors_17 block_17 (r - 1088)
      (by change r - 1088 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h18 : r < 1216
  · have he : 1152 + (r - 1152) = r := by omega
    have hc := composite_from_block 1152 factors_18 block_18 (r - 1152)
      (by change r - 1152 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h19 : r < 1280
  · have he : 1216 + (r - 1216) = r := by omega
    have hc := composite_from_block 1216 factors_19 block_19 (r - 1216)
      (by change r - 1216 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h20 : r < 1344
  · have he : 1280 + (r - 1280) = r := by omega
    have hc := composite_from_block 1280 factors_20 block_20 (r - 1280)
      (by change r - 1280 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h21 : r < 1408
  · have he : 1344 + (r - 1344) = r := by omega
    have hc := composite_from_block 1344 factors_21 block_21 (r - 1344)
      (by change r - 1344 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h22 : r < 1472
  · have he : 1408 + (r - 1408) = r := by omega
    have hc := composite_from_block 1408 factors_22 block_22 (r - 1408)
      (by change r - 1408 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h23 : r < 1536
  · have he : 1472 + (r - 1472) = r := by omega
    have hc := composite_from_block 1472 factors_23 block_23 (r - 1472)
      (by change r - 1472 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h24 : r < 1600
  · have he : 1536 + (r - 1536) = r := by omega
    have hc := composite_from_block 1536 factors_24 block_24 (r - 1536)
      (by change r - 1536 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h25 : r < 1664
  · have he : 1600 + (r - 1600) = r := by omega
    have hc := composite_from_block 1600 factors_25 block_25 (r - 1600)
      (by change r - 1600 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h26 : r < 1728
  · have he : 1664 + (r - 1664) = r := by omega
    have hc := composite_from_block 1664 factors_26 block_26 (r - 1664)
      (by change r - 1664 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h27 : r < 1792
  · have he : 1728 + (r - 1728) = r := by omega
    have hc := composite_from_block 1728 factors_27 block_27 (r - 1728)
      (by change r - 1728 < 64; omega) (by omega)
    simpa only [he] using hc
  by_cases h28 : r < 1856
  · have he : 1792 + (r - 1792) = r := by omega
    have hc := composite_from_block 1792 factors_28 block_28 (r - 1792)
      (by change r - 1792 < 64; omega) (by omega)
    simpa only [he] using hc
  have he : 1856 + (r - 1856) = r := by omega
  have hc := composite_from_block 1856 factors_29 block_29 (r - 1856)
    (by change r - 1856 < 35; omega) (by omega)
  simpa only [he] using hc

end Erdos141FirstCases
