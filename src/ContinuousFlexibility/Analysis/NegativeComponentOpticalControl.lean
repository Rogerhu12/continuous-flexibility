module

public import ContinuousFlexibility.Analysis.OpticalTravelVariation
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A normalized optical control on a negative component

The optical flux vanishes at the left turning point and is positive in the
interior. The mean value theorem yields a point where its reciprocal has
strictly negative derivative. This gives the interior collar for an actual
smooth normalized control, arbitrarily close to the turning point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

/-- Every left subinterval contains a closed collar of strict reciprocal-flux slope. -/
theorem exists_opticalInverseFlux_negative_collar {w : ℝ → ℝ} {l h c : ℝ}
    (hl : 0 < l) (hc : c ∈ Ioo l h) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Icc l h, 0 < w r) (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hroot : deriv w l = 0) :
    ∃ a b : ℝ, l < a ∧ a < b ∧ b < c ∧ ∀ r ∈ Icc a b, deriv (opticalInverseFlux w) r < 0 := by
  let Q (r : ℝ) := -deriv w r / (r * w r)
  let W (r : ℝ) := r * opticalSpeed w r
  have hQpos (r : ℝ) (hr : r ∈ Ioo l h) : 0 < Q r :=
    div_pos (neg_pos.mpr (hneg r hr)) (mul_pos (hl.trans hr.1) (hpos r (Ioo_subset_Icc_self hr)))
  have hWpos (r : ℝ) (hr : r ∈ Ioo l h) : 0 < W r :=
    mul_pos (hl.trans hr.1) (Real.sqrt_pos.mpr (hQpos r hr))
  have hd := (contDiff_infty_iff_deriv.mp hw).2
  have hQc : ContinuousOn Q (Icc l h) :=
    hd.continuous.neg.continuousOn.div (continuous_id.mul hw.continuous).continuousOn
      (fun r hr => (mul_pos (hl.trans_le hr.1) (hpos r hr)).ne')
  have hWc : ContinuousOn W (Icc l h) :=
    continuous_id.continuousOn.mul (Real.continuous_sqrt.comp_continuousOn hQc)
  have hQd : ContDiffOn ℝ ∞ Q (Ioo l h) :=
    hd.neg.contDiffOn.div (contDiff_id.mul hw).contDiffOn
      (fun r hr => (mul_pos (hl.trans hr.1) (hpos r (Ioo_subset_Icc_self hr))).ne')
  have hWd : ContDiffOn ℝ ∞ W (Ioo l h) :=
    contDiff_id.contDiffOn.mul (hQd.sqrt (fun r hr => (hQpos r hr).ne'))
  have hWzero : W l = 0 := by simp [W, opticalSpeed, hroot]
  have hsubClosed : Icc l c ⊆ Icc l h := fun _ hr => ⟨hr.1, hr.2.trans hc.2.le⟩
  have hsubOpen : Ioo l c ⊆ Ioo l h := fun _ hr => ⟨hr.1, hr.2.trans hc.2⟩
  obtain ⟨x, hx, hslope⟩ := exists_deriv_eq_slope W hc.1 (hWc.mono hsubClosed)
    ((hWd.differentiableOn (by simp)).mono hsubOpen)
  have hdx : 0 < deriv W x := by
    rw [hslope, hWzero, sub_zero]
    exact div_pos (hWpos c hc) (sub_pos.mpr hc.1)
  have hWx : DifferentiableAt ℝ W x :=
    (hWd.differentiableOn (by simp) x (hsubOpen hx)).differentiableAt
      (isOpen_Ioo.mem_nhds (hsubOpen hx))
  have hinv : HasDerivAt (opticalInverseFlux w) (-deriv W x / (W x) ^ 2) x :=
    hWx.hasDerivAt.inv (hWpos x (hsubOpen hx)).ne'
  have hnegAt : deriv (opticalInverseFlux w) x < 0 := by
    rw [hinv.deriv]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hdx) (pow_pos (hWpos x (hsubOpen hx)) 2)
  have hU := contDiffOn_opticalInverseFlux hl hw (fun r hr => hpos r (Ioo_subset_Icc_self hr)) hneg
  have hUc : ContinuousAt (deriv (opticalInverseFlux w)) x :=
    (hU.deriv_of_isOpen isOpen_Ioo (by simp : (0 : ℕ∞ω) + 1 ≤ ∞)).continuousOn.continuousAt
      (isOpen_Ioo.mem_nhds (hsubOpen hx))
  have he : ∀ᶠ r in 𝓝 x, r ∈ Ioo l c ∧ deriv (opticalInverseFlux w) r < 0 :=
    (show ∀ᶠ r in 𝓝 x, r ∈ Ioo l c from Ioo_mem_nhds hx.1 hx.2).and
      (hUc.eventually_lt continuousAt_const hnegAt)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp he
  let a := x - ε / 2
  let b := x + ε / 2
  have hab : a < b := by dsimp only [a, b]; linarith only [hε]
  have hclose (r : ℝ) (hr : r ∈ Icc a b) : r ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hdist : |r - x| ≤ ε / 2 := by
      apply abs_le.mpr
      have ha : a ≤ r := hr.1
      have hb : r ≤ b := hr.2
      dsimp only [a, b] at ha hb
      constructor <;> linarith only [ha, hb]
    exact hdist.trans_lt (half_lt_self hε)
  have ha := hball (hclose a ⟨le_rfl, hab.le⟩)
  have hb := hball (hclose b ⟨hab.le, le_rfl⟩)
  exact ⟨a, b, ha.1.1, hab, hb.1.2, fun r hr => (hball (hclose r hr)).2⟩

/-- An actual negative component has a compactly supported smooth control
with unit derivative of the exact travel angle. The support can be chosen in
any prescribed left subinterval of the component. -/
theorem exists_normalized_opticalControl_of_negativeRadialComponent
    {D : ReferenceData} {l h c : ℝ} (hD : RadialProfileGeometry D)
    (hcomponent : NegativeRadialComponent D l h) (hc : c ∈ Ioo l h) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ioo l c ∧
      HasDerivAt (fun t : ℝ => ∫ r in l..h,
        Real.sqrt (-deriv (fun s => D.w s * Real.exp (t * χ s)) r /
          (r * (D.w r * Real.exp (t * χ r))))) 1 0 := by
  obtain ⟨hal, _, hhb, hroot, _, hneg⟩ := hcomponent
  obtain ⟨ha, _, hw, _, hwpos, _⟩ := hD
  have hl := ha.trans hal
  have hpos (r : ℝ) (hr : r ∈ Icc l h) : 0 < D.w r :=
    hwpos r ⟨hal.trans_le hr.1, hr.2.trans_lt hhb⟩
  obtain ⟨a, b, hla, hab, hbc, hsign⟩ :=
    exists_opticalInverseFlux_negative_collar hl hc hw.1 hpos hneg hroot
  obtain ⟨χ, hχ, hcompact, hsupp, hderiv⟩ := exists_normalized_opticalControl
    hl hla hab (hbc.trans hc.2) hw.1 hpos hneg (Or.inr hsign)
  exact ⟨χ, hχ, hcompact, hsupp.trans (fun _ hr => ⟨hla.trans hr.1, hr.2.trans hbc⟩), hderiv⟩

end ContinuousFlexibility.Statements
