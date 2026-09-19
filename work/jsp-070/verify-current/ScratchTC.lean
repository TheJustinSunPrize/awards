import Mathlib

/- Typeclass sanity for ℝ under PosMulMono-based product lemmas -/
example : PosMulMono ℝ := by infer_instance
example : ZeroLEOneClass ℝ := by infer_instance

/- Pattern A/F (sites 3005/3015/3025/3044/3093): products of norms, ≤ 1.
   `(x e.1 - x e.2)` is exactly what the real call sites have. -/
example {ℓ : ℕ} (s : Finset (Fin ℓ × Fin ℓ)) (F : (Fin ℓ × Fin ℓ) → ℂ → ℂ)
    (hF : ∀ e z, ‖F e z‖ ≤ 1) (x : Fin ℓ → ℂ) :
    ∏ e ∈ s, ‖F e (x e.1 - x e.2)‖ ≤ 1 := by
  exact Finset.prod_le_one₀ (fun e _he => by positivity) (fun e _he => hF e (x e.1 - x e.2))

/- Pattern B (site 9120): products with nonneg in context -/
example {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    (hg_nonneg : ∀ i ∈ s, 0 ≤ g i) (hg_le : ∀ i ∈ s, g i ≤ 1) :
    ∏ i ∈ s, g i ≤ 1 := by
  exact Finset.prod_le_one₀ hg_nonneg hg_le

/- Pattern C (sites 9171/9370/9380): products of absolute values vs constant 2 -/
example {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf_abs : ∀ z, |f z| ≤ 2) :
    ∏ e ∈ s, |f e| ≤ ∏ _e ∈ s, (2 : ℝ) := by
  exact Finset.prod_le_prod₀ (fun e _he => abs_nonneg (f e)) (fun e _he => hf_abs e)

/- Pattern D (sites 9296/9305/9466/9760/9949): pointwise nonneg + ≤ 1 -/
example {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf_nonneg : ∀ e, 0 ≤ f e) (hf_le : ∀ e, f e ≤ 1) :
    ∏ e ∈ s, f e ≤ 1 := by
  exact Finset.prod_le_one₀ (fun e _he => hf_nonneg e) (fun e _he => hf_le e)

/- Pattern E (site 9955): nonneg via linarith from hf_le, ≤ 1 via linarith -/
example {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf_le : ∀ z, f z ≤ 1) (hf_nonneg : ∀ z, 0 ≤ f z) :
    ∏ e ∈ s, (1 - f e) ≤ 1 := by
  exact Finset.prod_le_one₀
    (fun e _he => by linarith [hf_le e])
    (fun e _he => by linarith [hf_le e, hf_nonneg e])