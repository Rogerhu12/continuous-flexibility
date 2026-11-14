module

public import ContinuousFlexibility.Analysis.N01cMorseOpticalEnvelope
public import ContinuousFlexibility.Analysis.N01cMorseComponentClassification
public import ContinuousFlexibility.Analysis.N01cOpticalPointCover
public import ContinuousFlexibility.Radial.OpenComponentTransport

/-!
# Actual scaled Morse components retain their optical lower bound

The original profile identity is differentiated; radial dilation changes
the ratio Q0/distance by the inverse cube of its scale. The actual cell
pullback and finite index floor retain the coefficient weight.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- A pointwise optical distance bound transported by an actual profile
dilation. The height dilation cancels and the radius dilation costs R³. -/
theorem n01c_opticalLower_dilation
    {W w : ℝ → ℝ} {R H l u r c weight : ℝ}
    (hR : 0 < R) (hH : H ≠ 0) (hr : r ≠ 0) (hwr : w r ≠ 0)
    (hW : DifferentiableAt ℝ W (R * r)) (hw : DifferentiableAt ℝ w r)
    (he : (fun t => W (R * t)) =ᶠ[𝓝 r] (fun t => (H * R) * w t))
    (hlower : c * weight * min (r - l) (u - r) ≤ -deriv w r / (r * w r)) :
    (c / R ^ 3) * weight * min (R * r - R * l) (R * u - R * r) ≤
      -deriv W (R * r) / ((R * r) * W (R * r)) := by
  rw [n01c_opticalRatio_dilation hW hw hR.ne' hH hr hwr he]
  have hd : min (R * r - R * l) (R * u - R * r) =
      R * min (r - l) (u - r) := by
    rw [← mul_sub, ← mul_sub, ← mul_min_of_nonneg _ _ hR.le]
  rw [hd]
  have hid : (c / R ^ 3) * weight * (R * min (r - l) (u - r)) =
      (c * weight * min (r - l) (u - r)) / R ^ 2 := by
    field_simp [hR.ne']
    <;> ring
  rw [hid]
  exact div_le_div_of_nonneg_right hlower (sq_nonneg R)

/-- Every negative point of an actual rescaled tail belongs to its whole
scaled Morse component and receives the uniform optical lower bound.
The model bound is the already-proved whole-component Morse estimate. -/
theorem n01c_scaledMorse_opticalModelAt
    {T : MorseChainData} {σ : ℕ → ℝ} {D E : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (hlarge : 100 ≤ T.index) (side : Bool)
    {start floor : ℕ} (hstart : T.index ≤ start)
    {R H K : ℝ} (hR : 0 < R) (hH : 0 < H) (hK : 0 < K)
    (hE : RadialProfileGeometry E)
    (hcore : ∀ s ∈ radialTailInterval D side (morseChainSeam T side start),
      R * s ∈ radialCore E)
    (hprofile : ∀ s ∈ radialTailInterval D side (morseChainSeam T side start),
      E.w (R * s) = H * R * D.w s)
    (hcells : ∀ m s, s ∈ radialTailInterval D side (morseChainSeam T side start) →
      s ∈ D.cells m → R * s ∈ E.cells m)
    (hindex : ∀ m, E.cellIndex m = max (D.cellIndex m) floor)
    (hoptical : ∀ side : Bool, ∀ n : ℕ, T.index ≤ n → 100 ≤ n → ∀ r : ℝ,
      r ∈ Ioo
        (T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
        (T.radius side n (morseChainRightTurn T n)) →
      K⁻¹ * radialE n ^ (-K) *
        min (r - T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
          (T.radius side n (morseChainRightTurn T n) - r) ≤
        -deriv D.w r / (r * D.w r))
    {r : ℝ} (hr : r ∈ radialTailInterval D side (morseChainSeam T side start))
    (hneg : deriv D.w r < 0) :
    N01cOpticalModelAt E (K⁻¹ / R ^ 3) K (R * r) := by
  obtain ⟨n, hnStart, hrI, hclosed⟩ :=
    n01c_morse_negative_tail_model_component hreal hσ side hstart hr hneg
  have hn : T.index ≤ n := hstart.trans hnStart
  let l : ℝ := T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n))
  let u : ℝ := T.radius side n (morseChainRightTurn T n)
  have hmodel := morseRealization_model_return hreal hσ side hn
  have hcomponent : NegativeRadialComponent D l u := hmodel.1
  have htailOpen : IsOpen (radialTailInterval D side (morseChainSeam T side start)) := by
    cases side <;> exact isOpen_Ioo
  have htransport := negativeRadialComponent_travel_of_open_tail hR hH hcomponent
    (hcore l (hclosed (left_mem_Icc.mpr hcomponent.2.1.le))).1
    (hcore u (hclosed (right_mem_Icc.mpr hcomponent.2.1.le))).2
    hreal.geometry.2.2.1.1 hE.2.2.1.1
    (fun t ht => hclosed (Ioo_subset_Icc_self ht)) hprofile
  obtain ⟨m, hm, hrm⟩ := hmodel.2.2 r hrI
  refine ⟨R * l, R * u, max n floor, htransport.1,
    ⟨mul_lt_mul_of_pos_left hrI.1 hR, mul_lt_mul_of_pos_left hrI.2 hR⟩,
    ⟨m, by rw [hindex m, hm], hcells m r hr hrm⟩, fun t ht => ?_⟩
  let s : ℝ := t / R
  have hs : s ∈ Ioo l u := by
    constructor
    · exact (lt_div_iff₀ hR).mpr (by simpa only [mul_comm] using ht.1)
    · exact (div_lt_iff₀ hR).mpr (by simpa only [mul_comm] using ht.2)
  have hstail := hclosed (Ioo_subset_Icc_self hs)
  have htscale : R * s = t := by dsimp only [s]; field_simp [hR.ne']
  have hscore : s ∈ radialCore D :=
    ⟨hcomponent.1.trans hs.1, hs.2.trans hcomponent.2.2.1⟩
  have hspos : 0 < s := hreal.geometry.1.trans hscore.1
  have hwspos : 0 < D.w s := hreal.geometry.2.2.2.2.1 s hscore
  have hgerm : (fun y => E.w (R * y)) =ᶠ[𝓝 s] (fun y => (H * R) * D.w y) :=
    Filter.eventuallyEq_of_mem (htailOpen.mem_nhds hstail) hprofile
  have hscaled := n01c_opticalLower_dilation hR hH.ne' hspos.ne' hwspos.ne'
    (hE.2.2.1.1.differentiable (by simp) (R * s))
    (hreal.geometry.2.2.1.1.differentiable (by simp) s) hgerm
    (hoptical side n hn (hlarge.trans hn) s hs)
  rw [htscale] at hscaled
  have hweight : radialE (max n floor) ^ (-K) ≤ radialE n ^ (-K) :=
    rpow_le_rpow_of_nonpos (exp_pos _)
      (exp_le_exp.mpr (radialQ_monotone (Nat.le_max_left n floor)))
      (neg_nonpos.mpr hK.le)
  have hδ : 0 ≤ min (t - R * l) (R * u - t) :=
    le_min (sub_nonneg.mpr ht.1.le) (sub_nonneg.mpr ht.2.le)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hweight (by positivity : 0 ≤ K⁻¹ / R ^ 3)) hδ).trans hscaled

end ContinuousFlexibility.Radial
