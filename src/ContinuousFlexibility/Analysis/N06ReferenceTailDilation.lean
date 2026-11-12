import ContinuousFlexibility.Analysis.N06MorseRootCurvature
import ContinuousFlexibility.Radial.ReferenceDilation
import ContinuousFlexibility.Analysis.RootCharacteristicFactor

/-!
# Actual second derivatives on the dilated R08 tails

R08 retains the profile identity `W (R * r) = H * R * w r` on each
selected open tail. Differentiating that genuine germ twice transports
the ordinary root curvature with factor `H / R`. The model roots beyond
the selected seam lie strictly in that same open tail, so one constant
works for both dilations and every retained root.

The original model realization and the actual tail identity remain
explicit. They are certificates of a chosen construction and are not
asserted to follow from the erased `RadialReference.property` alone.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The existing first-derivative transport, applied to its actual local
derivative identity, gives the ordinary second derivative. -/
theorem n06_second_deriv_radius_pullback_of_germ
    {f g : ℝ → ℝ} {R a r : ℝ} (hR : R ≠ 0)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (heq : (fun s => g (R * s)) =ᶠ[𝓝 r] (fun s => a * f s)) :
    deriv (deriv g) (R * r) = (a / R ^ 2) * deriv (deriv f) r := by
  have hfirst : (fun s => deriv g (R * s)) =ᶠ[𝓝 r]
      (fun s => (a / R) * deriv f s) := by
    filter_upwards [heq.eventuallyEq_nhds] with s hs
    exact deriv_radius_pullback_of_germ hR
      (hf.differentiable (by simp) s) (hg.differentiable (by simp) (R * s)) hs
  have hfd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  calc
    _ = ((a / R) / R) * deriv (deriv f) r :=
      deriv_radius_pullback_of_germ hR
        (hfd.differentiable (by simp) r) (hgd.differentiable (by simp) (R * r)) hfirst
    _ = _ := by rw [div_div, ← pow_two]

/-- The physical R08 normalization has precisely the curvature factor
`H / R`; the actual profile of the final reference is retained. -/
theorem n06_reference_tail_second_deriv
    {D E : ReferenceData} {R H r : ℝ} (hR : R ≠ 0)
    (hD : ContDiff ℝ ∞ D.w) (hE : ContDiff ℝ ∞ E.w)
    (heq : (fun s => E.w (R * s)) =ᶠ[𝓝 r]
      (fun s => H * R * D.w s)) :
    deriv (deriv E.w) (R * r) = (H / R) * deriv (deriv D.w) r := by
  rw [n06_second_deriv_radius_pullback_of_germ hR hD hE heq]
  field_simp [hR]
  <;> ring

/-- The same actual tail germ transports the divided derivative. This
identifies a genuine factor for the final profile, rather than merely
assigning a value to its formal root coefficient. -/
theorem n06_reference_tail_divided_deriv
    {w W g : ℝ → ℝ} {R H r ι x : ℝ} (hR : R ≠ 0)
    (hw : ContDiff ℝ ∞ w) (hW : ContDiff ℝ ∞ W)
    (hfactor : ∀ t : ℝ, -deriv w (r + ι * t) = t * g t)
    (heq : (fun s => W (R * s)) =ᶠ[𝓝 (r + ι * (x / R))]
      (fun s => H * R * w s)) :
    -deriv W (R * r + ι * x) = x * ((H / R) * g (x / R)) := by
  have hd := deriv_radius_pullback_of_germ hR
    (hw.differentiable (by simp) (r + ι * (x / R)))
    (hW.differentiable (by simp) (R * (r + ι * (x / R)))) heq
  have harg : R * (r + ι * (x / R)) = R * r + ι * x := by
    field_simp [hR]
    <;> ring
  rw [harg, mul_div_cancel_right₀ H hR] at hd
  rw [hd]
  calc
    -(H * deriv w (r + ι * (x / R))) = H * (-deriv w (r + ι * (x / R))) := by ring
    _ = H * ((x / R) * g (x / R)) := by rw [hfactor]
    _ = _ := by ring

/-- The actual positive speed factor has radius weight `R^(-3/2)`.
The independent height dilation cancels from this exact formula. -/
theorem n06_referenceRootSpeedFactor_radius_height_change
    {w W g : ℝ → ℝ} {R H r ι t : ℝ}
    (hR : 0 < R) (hH : 0 < H)
    (hprofile : W (R * (r + ι * t)) = H * R * w (r + ι * t)) :
    referenceRootSpeedFactor W (fun x => (H / R) * g (x / R))
        (R * r) ι (R * t) =
      referenceRootSpeedFactor w g r ι t / (R * Real.sqrt R) := by
  have harg : R * r + ι * (R * t) = R * (r + ι * t) := by ring
  have hrad : (H * R * w (r + ι * t)) * ((H / R) * g t) /
      (R * (r + ι * t)) = (H ^ 2 / R) *
        (w (r + ι * t) * g t / (r + ι * t)) := by
    by_cases hu : r + ι * t = 0
    · simp only [hu, mul_zero, div_zero]
    · field_simp [hR.ne', hu]
      <;> ring
  simp only [referenceRootSpeedFactor, rootProfileRadicand, harg,
    hprofile, mul_div_cancel_left₀ t hR.ne']
  rw [hrad, Real.sqrt_mul (div_nonneg (sq_nonneg H) hR.le),
    Real.sqrt_div (sq_nonneg H), Real.sqrt_sq hH.le]
  by_cases hw : w (r + ι * t) = 0
  · simp only [hw, mul_zero, div_zero, zero_div]
  · field_simp [hH.ne', hR.ne', (Real.sqrt_pos.mpr hR).ne', hw]
    <;> ring

/-- Either actual model root lies strictly beyond any earlier retained
seam. In particular the prepared R08 entry does not cut a root germ. -/
theorem n06_morseRealization_root_mem_tail
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool)
    {start n : ℕ} (hstart : T.index ≤ start) (hn : start ≤ n) {x : ℝ}
    (hx : morseRho (morseChainA T n) (morseChainB T n) x = 0) :
    T.radius side n x ∈ radialTailInterval D side (morseChainSeam T side start) := by
  have hnT : T.index ≤ n := hstart.trans hn
  have hxi := n06_morseRealization_root_mem_Ioo hreal side hnT hx
  have hxc : x ∈ Icc (T.leftX side n) (T.rightX side n) := ⟨hxi.1.le, hxi.2.le⟩
  have hcore := hreal.radius_mem_core side n hnT x hxc
  have hmodel (m : ℕ) (hm : T.index ≤ m) :
      T.radius side m (T.leftX side m) < T.radius side m (T.rightX side m) := by
    have hlt := (hreal.2.2.1 side m hm).2.1
    exact hreal.radius_strictMonoOn side m hm
      (left_mem_Icc.mpr hlt.le) (right_mem_Icc.mpr hlt.le) hlt
  have hstep (m : ℕ) (hm : T.index ≤ m) :
      if side then morseChainSeam T side m < morseChainSeam T side (m + 1)
      else morseChainSeam T side (m + 1) < morseChainSeam T side m := by
    have hj := hreal.join_data side m hm
    have hjoin := hj.1
    rw [hj.2.1, hj.2.2.1] at hjoin
    cases side with
    | false => exact hjoin.trans (hmodel m hm)
    | true => exact (hmodel m hm).trans hjoin
  have hout :
      if side then morseChainSeam T side start ≤ morseChainSeam T side n
      else morseChainSeam T side n ≤ morseChainSeam T side start := by
    clear hcore hxc hxi hnT hx
    induction n, hn using Nat.le_induction with
    | base => cases side <;> exact le_rfl
    | succ m hm ih =>
      have hs := hstep m (hstart.trans hm)
      cases side with
      | false => exact hs.le.trans ih
      | true => exact ih.trans hs.le
  have hinterval := (hreal.2.2.1 side n hnT).2.1
  cases side with
  | false =>
    have hroot := hreal.radius_strictMonoOn false n hnT hxc
      (right_mem_Icc.mpr hinterval.le) hxi.2
    exact ⟨hcore.1, hroot.trans_le hout⟩
  | true =>
    have hroot := hreal.radius_strictMonoOn true n hnT
      (left_mem_Icc.mpr hinterval.le) hxc hxi.1
    exact ⟨hout.trans_lt hroot, hcore.2⟩

/-- Both independent R08 tail dilations retain the actual uniform
root-curvature lower bound on the same final physical profile. The
only transfer premise is the original open-tail profile identity. -/
theorem n06_morseRealization_scaled_tail_root_curvature_lower
    {T : MorseChainData} {σ : ℕ → ℝ} {D E : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (hE : ContDiff ℝ ∞ E.w) (R H : Bool → ℝ)
    (hR : ∀ side, 0 < R side) (hH : ∀ side, 0 < H side)
    {start : ℕ} (hstart : T.index ≤ start)
    (hprofile : ∀ (side : Bool) r,
      r ∈ radialTailInterval D side (morseChainSeam T side start) →
      E.w (R side * r) = H side * R side * D.w r) :
    ∃ c : ℝ, 0 < c ∧ ∀ (side : Bool) (n : ℕ), start ≤ n → ∀ x : ℝ,
      morseRho (morseChainA T n) (morseChainB T n) x = 0 →
      c * radialE n ^ (-12 : ℝ) ≤
        |deriv (deriv E.w) (R side * T.radius side n x)| := by
  obtain ⟨c₀, hc₀, hcurv⟩ := n06_morseRealization_root_curvature_lower hreal hσ
  let q : ℝ := min (H false / R false) (H true / R true)
  have hq : 0 < q := lt_min (div_pos (hH false) (hR false))
    (div_pos (hH true) (hR true))
  have hqside (side : Bool) : q ≤ H side / R side := by
    cases side
    · exact min_le_left _ _
    · exact min_le_right _ _
  refine ⟨q * c₀, mul_pos hq hc₀, ?_⟩
  intro side n hn x hx
  have hr := n06_morseRealization_root_mem_tail hreal side hstart hn hx
  have hopen : IsOpen (radialTailInterval D side (morseChainSeam T side start)) := by
    cases side <;> exact isOpen_Ioo
  have heq : (fun s => E.w (R side * s)) =ᶠ[𝓝 (T.radius side n x)]
      (fun s => H side * R side * D.w s) := by
    filter_upwards [hopen.mem_nhds hr] with s hs
    exact hprofile side s hs
  rw [n06_reference_tail_second_deriv (hR side).ne' hreal.geometry.2.2.1.1 hE heq,
    abs_mul, abs_of_pos (div_pos (hH side) (hR side))]
  calc
    (q * c₀) * radialE n ^ (-12 : ℝ) = q * (c₀ * radialE n ^ (-12 : ℝ)) := by ring
    _ ≤ (H side / R side) * (c₀ * radialE n ^ (-12 : ℝ)) :=
      mul_le_mul_of_nonneg_right (hqside side)
        (mul_nonneg hc₀.le (Real.rpow_nonneg (Real.exp_pos _).le _))
    _ ≤ (H side / R side) * |deriv (deriv D.w) (T.radius side n x)| :=
      mul_le_mul_of_nonneg_left (hcurv side n (hstart.trans hn) x hx)
        (div_pos (hH side) (hR side)).le

end ContinuousFlexibility.Analysis
