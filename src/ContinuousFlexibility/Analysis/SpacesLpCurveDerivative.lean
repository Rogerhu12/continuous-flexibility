module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Derivatives of dominated curves in the actual `L²` space

A locally uniform square-integrable bound on the pointwise derivatives
allows differentiation of the actual `L²` classes. The proof uses the
pointwise difference quotient, the mean value theorem, and dominated
convergence for its squared residual. No continuity of the derivative is
assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal RealInnerProductSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The squared norm of the actual real `L²` class is the stated integral. -/
theorem spaces_lp_norm_sq_toLp {f : α → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq (hf.toLp f), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Dominated convergence in the real `L²` norm, with a bound on the
pointwise residual. The index may be any countably generated filter. -/
theorem spaces_tendsto_toLp_of_dominated {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι → α → ℝ} {f : α → ℝ}
    (hF : ∀ i, MemLp (F i) 2 μ) (hf : MemLp f 2 μ)
    {g : α → ℝ} (hg : MemLp g 2 μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, |F i x - f x| ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    Tendsto (fun i => (hF i).toLp (F i)) l (𝓝 (hf.toLp f)) := by
  have hmeas : ∀ᶠ i in l, AEStronglyMeasurable (fun x => (F i x - f x) ^ 2) μ :=
    Eventually.of_forall fun i => ((hF i).sub hf).aestronglyMeasurable.pow 2
  have hbound₂ : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖(F i x - f x) ^ 2‖ ≤ g x ^ 2 := by
    filter_upwards [hbound] with i hi
    filter_upwards [hi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      (F i x - f x) ^ 2 = |F i x - f x| ^ 2 := (sq_abs _).symm
      _ ≤ g x ^ 2 := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hx)).mpr hx
  have hlim₂ : ∀ᵐ x ∂μ,
      Tendsto (fun i => (F i x - f x) ^ 2) l (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      (hx.sub (tendsto_const_nhds :
        Tendsto (fun _ : ι => f x) l (𝓝 (f x)))).pow 2
  have hi : Tendsto (fun i => ∫ x, (F i x - f x) ^ 2 ∂μ) l (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence (fun x => g x ^ 2)
        hmeas hbound₂ hg.integrable_sq hlim₂)
  have he (i : ι) : ‖(hF i).toLp (F i) - hf.toLp f‖ ^ 2 =
      ∫ x, (F i x - f x) ^ 2 ∂μ := by
    rw [← MemLp.toLp_sub (hF i) hf]
    exact spaces_lp_norm_sq_toLp ((hF i).sub hf)
  have hn₂ : Tendsto (fun i => ‖(hF i).toLp (F i) - hf.toLp f‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    simpa only [he] using hi
  have hn : Tendsto (fun i => ‖(hF i).toLp (F i) - hf.toLp f‖) l (𝓝 (0 : ℝ)) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hn₂
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  exact (tendsto_iff_dist_tendsto_zero).mpr (by simpa only [dist_eq_norm] using hn)

private theorem spaces_slope_bound_of_deriv_bound
    {f df : ℝ → ℝ} {t₀ δ g t : ℝ} (hδ : 0 < δ)
    (hderiv : ∀ s ∈ Ioo (t₀ - δ) (t₀ + δ), HasDerivAt f (df s) s)
    (hbound : ∀ s ∈ Ioo (t₀ - δ) (t₀ + δ), |df s| ≤ g)
    (ht : t ∈ Ioo (t₀ - δ) (t₀ + δ)) (hne : t ≠ t₀) :
    |slope f t₀ t| ≤ g := by
  have h₀ : t₀ ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
  have hd : ‖f t - f t₀‖ ≤ g * ‖t - t₀‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hderiv s hs).hasDerivWithinAt)
      (fun s hs => by simpa only [Real.norm_eq_abs] using hbound s hs)
      (convex_Ioo _ _) h₀ ht
  rw [slope_def_field, abs_div]
  apply (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hne))).mpr
  simpa only [Real.norm_eq_abs] using hd

/-- A locally dominated pointwise derivative is the derivative of the
actual real `L²` curve. The bound is only required on one open interval. -/
theorem spaces_hasDerivAt_toLp_of_dominated_deriv
    {f df : ℝ → α → ℝ} (hf : ∀ t, MemLp (f t) 2 μ) {t₀ δ : ℝ}
    (hd₀ : MemLp (df t₀) 2 μ) (hδ : 0 < δ) {g : α → ℝ} (hg : MemLp g 2 μ)
    (hderiv : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
      HasDerivAt (fun s => f s x) (df t x) t)
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), |df t x| ≤ g x) :
    HasDerivAt (fun t => (hf t).toLp (f t)) (hd₀.toLp (df t₀)) t₀ := by
  let q (t : ℝ) (x : α) : ℝ := slope (fun s => f s x) t₀ t
  have hq (t : ℝ) : MemLp (q t) 2 μ := by
    have he : q t = (t - t₀)⁻¹ • (f t - f t₀) := by
      funext x
      simp only [q, slope_def_module, Pi.smul_apply, Pi.sub_apply]
    rw [he]
    exact ((hf t).sub (hf t₀)).const_smul (t - t₀)⁻¹
  have h₀ : t₀ ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun t => q t x) (𝓝[≠] t₀) (𝓝 (df t₀ x)) := by
    filter_upwards [hderiv] with x hx
    exact (hx t₀ h₀).tendsto_slope
  have hnear : ∀ᶠ t in 𝓝[≠] t₀, t ∈ Ioo (t₀ - δ) (t₀ + δ) := by
    have hn : ∀ᶠ t in 𝓝 t₀, t ∈ Ioo (t₀ - δ) (t₀ + δ) := Ioo_mem_nhds h₀.1 h₀.2
    exact hn.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ t in 𝓝[≠] t₀, t ≠ t₀ := by
    exact (self_mem_nhdsWithin : ({t₀} : Set ℝ)ᶜ ∈ 𝓝[≠] t₀)
  have hb : ∀ᶠ t in 𝓝[≠] t₀, ∀ᵐ x ∂μ, |q t x - df t₀ x| ≤ (2 : ℝ) * g x := by
    filter_upwards [hnear, hne] with t ht htne
    filter_upwards [hderiv, hbound] with x hdx hbx
    have hqg : |q t x| ≤ g x := spaces_slope_bound_of_deriv_bound hδ hdx hbx ht htne
    calc
      |q t x - df t₀ x| ≤ |q t x| + |df t₀ x| := abs_sub _ _
      _ ≤ g x + g x := add_le_add hqg (hbx t₀ h₀)
      _ = _ := by ring
  have htend := spaces_tendsto_toLp_of_dominated hq hd₀ (hg.const_mul 2) hb hlim
  have he (t : ℝ) : slope (fun s => (hf s).toLp (f s)) t₀ t = (hq t).toLp (q t) := by
    rw [slope_def_module]
    change (t - t₀)⁻¹ • ((hf t).toLp (f t) - (hf t₀).toLp (f t₀)) =
      (hq t).toLp (q t)
    rw [← MemLp.toLp_sub (hf t) (hf t₀), ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Eventually.of_forall fun x => by
      simp only [Pi.smul_apply, Pi.sub_apply, q, slope_def_module]
  apply hasDerivAt_iff_tendsto_slope.mpr
  change Tendsto (fun t => slope (fun s => (hf s).toLp (f s)) t₀ t)
    (𝓝[≠] t₀) (𝓝 (hd₀.toLp (df t₀)))
  simpa only [he] using htend

end ContinuousFlexibility.Analysis
