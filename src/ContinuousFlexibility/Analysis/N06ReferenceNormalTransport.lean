import ContinuousFlexibility.Analysis.N06ReferenceNormalTransportTests
import ContinuousFlexibility.Analysis.N06HalfPhysicalPairing
import ContinuousFlexibility.Analysis.N06WeakAngularCalculus
import ContinuousFlexibility.Analysis.N06ReferenceRemainderFields
import ContinuousFlexibility.Analysis.IntervalWeakPotential
import ContinuousFlexibility.Radial.R11bWeakNormalTensor

/-!
# The first weak radial derivative in actual reference coordinates

The physical unknown and its normal derivative are only L2 functions.
The proof tests their original weak equation with phi(chart)/height,
extended by zero on the actual piece. Genuine change of variables then
gives the derivative of the canonical height. Both chart orientations
are covered, and the derivative of the left cutoff remains explicit.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

/-- The actual candidate normal derivative, using the given physical weak
derivative and the first jets of the genuine reference radial coordinates. -/
def n06ReferenceNormalField (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (Y h : ℝ → ℝ)
    (w dw : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  let x := K.inverseChart z m p
  dw x / (h x.1 * deriv Y x.1) -
    deriv h x.1 / (h x.1 * deriv Y x.1) * canonicalHeight S K z m w p

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {base m : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {Y h : ℝ → ℝ}

/-- A true physical weak derivative becomes the actual canonical weak
derivative. The L2 premises concern the two displayed fields, not their
derivative identity; no pointwise derivative of the physical unknown is used. -/
theorem n06_reference_normal_transport
    (hK : N04PartA D S C K base ε) (hab : D.a ≤ D.b)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hY : ContDiffOn ℝ ∞ Y (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hh : ContDiffOn ℝ ∞ h (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hchart : ∀ p ∈ physicalPieceOpen S K m, K.chart z m p = (Y p.1, p.2))
    (hheight : ∀ p ∈ physicalPieceOpen S K m, K.height z m p = h p.1)
    {w dw : PolarPoint → ℝ} (hweak : WeakNormalDerivative D w dw)
    (hw : MemLp w 2 (radialPhysicalMeasure D))
    (hdw : MemLp dw 2 (radialPhysicalMeasure D))
    (hwp : Function.Periodic w (0, Real.pi))
    (hdwp : Function.Periodic dw (0, Real.pi))
    (hW : MemLp (canonicalHeight S K z m w) 2 (canonicalMeasure S K m))
    (hG : MemLp (n06ReferenceNormalField S K z m Y h w dw) 2
      (canonicalMeasure S K m)) :
    ∀ φ, CanonicalTest S K m φ →
      (∫ p, n06ReferenceNormalField S K z m Y h w dw p * φ p
        ∂canonicalMeasure S K m) =
      -(∫ p, canonicalHeight S K z m w p * mixedDerivative 1 0 φ p
        ∂canonicalMeasure S K m) := by
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hs m
  have hh0 (r : ℝ) (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) : h r ≠ 0 := by
    have he := (hcharts.2.2.2.2.2.2.2 (r, 0) ⟨hr, mem_univ _⟩).1.ne'
    rwa [hheight (r, 0) ⟨hr, mem_univ _⟩] at he
  have ha : ContDiffOn ℝ ∞ (fun r => (h r)⁻¹)
      (Ioo (K.physicalLeft m) (K.physicalRight m)) := hh.inv hh0
  obtain ⟨σ, hσ, horient⟩ := n06_reference_radial_orientation hK hz hs hY hchart
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  intro φ hφ
  have hmix : mixedDerivative 1 0 φ = radialPartial φ := by
    simpa only [spaces_mixedDerivative_zero, Nat.zero_add] using
      (radialPartial_mixedDerivative hφ.1 0 0).symm
  rw [hmix]
  let Φ : PolarPoint → ℝ := n06ReferenceWeightedTest S K z m (fun r => (h r)⁻¹) φ
  have hΦ : RadialTest D Φ := n06ReferenceWeightedTest_radialTest hK hz hs ha hφ
  have hΦp : Function.Periodic Φ (0, Real.pi) :=
    n06ReferenceWeightedTest_periodic hK hz hs hφ
  have hΦrp : Function.Periodic (radialPartial Φ) (0, Real.pi) :=
    r11b_periodic_directionalPartial hΦ.1 hΦp (1, 0)
  have hΦL : MemLp Φ 2 (radialPhysicalMeasure D) := r11b_continuous_memLp hΦ.1.continuous
  have hΦrL : MemLp (radialPartial Φ) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (r11b_radialTest_radialPartial hΦ).1.continuous
  have hiL : Integrable (fun p => w p * radialPartial Φ p) (radialPhysicalMeasure D) :=
    hw.integrable_mul hΦrL
  have hiR : Integrable (fun p => dw p * Φ p) (radialPhysicalMeasure D) :=
    hdw.integrable_mul hΦL
  let q : PolarPoint → ℝ := fun p => w p * radialPartial Φ p + dw p * Φ p
  have hiq : Integrable q (radialPhysicalMeasure D) := hiL.add hiR
  have hmeanZero : (∫ r in D.a..D.b, radialAngularMean (fun θ => q (r, θ))) = 0 := by
    have hwtest := hweak Φ hΦ
    rw [r11b_integral_angularMean_eq hab hiL, r11b_integral_angularMean_eq hab hiR] at hwtest
    rw [r11b_integral_angularMean_eq hab hiq]
    have he : (∫ p, q p ∂radialPhysicalMeasure D) =
        (∫ p, w p * radialPartial Φ p ∂radialPhysicalMeasure D) +
          ∫ p, dw p * Φ p ∂radialPhysicalMeasure D := by
      exact integral_add hiL hiR
    rw [he, mul_add]
    linarith only [hwtest]
  have hqp : Function.Periodic q (0, Real.pi) := by
    intro p
    change w (p + (0, Real.pi)) * radialPartial Φ (p + (0, Real.pi)) +
      dw (p + (0, Real.pi)) * Φ (p + (0, Real.pi)) = _
    rw [hwp p, hdwp p, hΦp p, hΦrp p]
  have hiqHalf : IntegrableOn q (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) volume := by
    have hiqFull : IntegrableOn q
        (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume := hiq
    exact hiqFull.mono_set (fun p hp =>
      ⟨hp.1, hp.2.1, hp.2.2.trans (by linarith [Real.pi_pos])⟩)
  have hqzero (p : PolarPoint) (hp : p ∉ physicalPieceOpen S K m) : q p = 0 := by
    have h0 : Φ p = 0 := n06ReferenceWeightedTest_of_not_mem hp
    have h1 : radialPartial Φ p = 0 := n06ReferenceWeightedTest_radialPartial_zero hK hz hs hφ hp
    simp only [q, h0, h1, mul_zero, add_zero]
  have hconvert := n06_physicalMean_pairing_eq_canonical hK hab hz hs m (fun _ => 1) q
    (by simpa only [one_mul] using hqp)
    (by simpa only [one_mul] using hiqHalf)
    (fun p hp => by rw [hqzero p hp, mul_zero])
  simp only [one_mul] at hconvert
  have hcanZero : (∫ p, canonicalHeight S K z m (fun _ => 1) p *
      canonicalSource S K z m q p ∂canonicalMeasure S K m) = 0 := by
    have he := hconvert.symm.trans hmeanZero
    exact (mul_eq_zero.mp he).resolve_left (inv_ne_zero Real.pi_ne_zero)
  have hpoint : (fun p => canonicalHeight S K z m (fun _ => 1) p *
      canonicalSource S K z m q p) =ᵐ[canonicalMeasure S K m]
      (fun p => σ * (canonicalHeight S K z m w p * radialPartial φ p +
        n06ReferenceNormalField S K z m Y h w dw p * φ p)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    have hpc : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    let x : PolarPoint := K.inverseChart z m p
    have hx : x ∈ physicalPieceOpen S K m := hcharts.2.1 hpc
    have hFx : K.chart z m x = p := hcharts.2.2.2.1 p hpc
    have hJ : planeJacobian (K.chart z m) x = deriv Y x.1 :=
      n06_reference_radial_jacobian hY hchart hx
    have hdY : deriv Y x.1 ≠ 0 := by
      rw [← hJ]
      exact (hcharts.2.2.2.2.2.2.2 x hx).2.1
    have hhx : h x.1 ≠ 0 := hh0 x.1 hx.1
    have hdhi : deriv (fun r => (h r)⁻¹) x.1 = -deriv h x.1 / h x.1 ^ 2 :=
      deriv_fun_inv'' ((hh.contDiffAt (isOpen_Ioo.mem_nhds hx.1)).differentiableAt (by simp)) hhx
    have hΦx : Φ x = (h x.1)⁻¹ * φ p := by
      dsimp only [Φ]
      rw [n06ReferenceWeightedTest_of_mem hx, hFx]
    have hΦrx : radialPartial Φ x =
        (-deriv h x.1 / h x.1 ^ 2) * φ p +
          (h x.1)⁻¹ * (deriv Y x.1 * radialPartial φ p) := by
      rw [n06ReferenceWeightedTest_radialPartial hK hz hs ha hY hchart hφ hx, hdhi, hFx]
    change (1 / K.height z m x) *
      (K.height z m x * (w x * radialPartial Φ x + dw x * Φ x) /
        |planeJacobian (K.chart z m) x|) =
      σ * ((w x / K.height z m x) * radialPartial φ p +
        (dw x / (h x.1 * deriv Y x.1) -
          deriv h x.1 / (h x.1 * deriv Y x.1) * (w x / K.height z m x)) * φ p)
    rw [hheight x hx, hJ, hΦx, hΦrx, horient x.1 hx.1]
    rcases hσ with rfl | rfl <;> simp only [one_mul, neg_one_mul] <;>
      field_simp [hhx, hdY] <;> ring
  have hiW : Integrable (fun p => canonicalHeight S K z m w p * radialPartial φ p)
      (canonicalMeasure S K m) := hW.integrable_mul
    (n06_memLp_canonical_of_continuous m (r11b_contDiff_directionalPartial hφ.1 (1, 0)).continuous)
  have hiG : Integrable (fun p => n06ReferenceNormalField S K z m Y h w dw p * φ p)
      (canonicalMeasure S K m) := hG.integrable_mul hφ.n06_memLp
  have hsum : (∫ p, canonicalHeight S K z m w p * radialPartial φ p +
      n06ReferenceNormalField S K z m Y h w dw p * φ p ∂canonicalMeasure S K m) =
      (∫ p, canonicalHeight S K z m w p * radialPartial φ p ∂canonicalMeasure S K m) +
      ∫ p, n06ReferenceNormalField S K z m Y h w dw p * φ p ∂canonicalMeasure S K m := by
    exact integral_add hiW hiG
  have he := (integral_congr_ae hpoint).symm.trans hcanZero
  rw [integral_const_mul, hsum] at he
  have he0 := (mul_eq_zero.mp he).resolve_left hσ0
  linarith only [he0]

/-- Linearity of the original physical weak derivative, justified in its
original full-period measure by the four actual L2 hypotheses. -/
theorem n06_weakNormalDerivative_sub_smul
    (hab : D.a ≤ D.b) {f df g dg : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D))
    (hdf : MemLp df 2 (radialPhysicalMeasure D))
    (hg : MemLp g 2 (radialPhysicalMeasure D))
    (hdg : MemLp dg 2 (radialPhysicalMeasure D))
    (hfd : WeakNormalDerivative D f df) (hgd : WeakNormalDerivative D g dg) (c : ℝ) :
    WeakNormalDerivative D (fun p => f p - c * g p) (fun p => df p - c * dg p) := by
  intro φ hφ
  have hφL : MemLp φ 2 (radialPhysicalMeasure D) := r11b_continuous_memLp hφ.1.continuous
  have hφrL : MemLp (radialPartial φ) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (r11b_radialTest_radialPartial hφ).1.continuous
  have hfr : MemLp (fun p => f p - c * g p) 2 (radialPhysicalMeasure D) :=
    hf.sub (hg.const_mul c)
  have hdr : MemLp (fun p => df p - c * dg p) 2 (radialPhysicalMeasure D) :=
    hdf.sub (hdg.const_mul c)
  have hF := hfd φ hφ
  have hG := hgd φ hφ
  rw [r11b_integral_angularMean_mul_eq hab hf hφrL,
    r11b_integral_angularMean_mul_eq hab hdf hφL] at hF
  rw [r11b_integral_angularMean_mul_eq hab hg hφrL,
    r11b_integral_angularMean_mul_eq hab hdg hφL] at hG
  have hleft : (∫ p, (f p - c * g p) * radialPartial φ p ∂radialPhysicalMeasure D) =
      (∫ p, f p * radialPartial φ p ∂radialPhysicalMeasure D) -
        c * ∫ p, g p * radialPartial φ p ∂radialPhysicalMeasure D := by
    calc
      _ = ∫ p, f p * radialPartial φ p - c * (g p * radialPartial φ p)
          ∂radialPhysicalMeasure D := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = _ := by
        have hi₁ : Integrable (fun p => f p * radialPartial φ p) (radialPhysicalMeasure D) :=
          hf.integrable_mul hφrL
        have hi₂ : Integrable (fun p => c * (g p * radialPartial φ p))
            (radialPhysicalMeasure D) := (hg.integrable_mul hφrL).const_mul c
        simpa only [Pi.sub_apply, integral_const_mul] using integral_sub hi₁ hi₂
  have hright : (∫ p, (df p - c * dg p) * φ p ∂radialPhysicalMeasure D) =
      (∫ p, df p * φ p ∂radialPhysicalMeasure D) -
        c * ∫ p, dg p * φ p ∂radialPhysicalMeasure D := by
    calc
      _ = ∫ p, df p * φ p - c * (dg p * φ p) ∂radialPhysicalMeasure D := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = _ := by
        have hi₁ : Integrable (fun p => df p * φ p) (radialPhysicalMeasure D) :=
          hdf.integrable_mul hφL
        have hi₂ : Integrable (fun p => c * (dg p * φ p))
            (radialPhysicalMeasure D) := (hdg.integrable_mul hφL).const_mul c
        simpa only [Pi.sub_apply, integral_const_mul] using integral_sub hi₁ hi₂
  rw [r11b_integral_angularMean_mul_eq hab hfr hφrL,
    r11b_integral_angularMean_mul_eq hab hdr hφL, hleft, hright]
  linear_combination hF - c * hG

/-- A smooth radial cutoff has its actual physical weak derivative.
This statement needs no compact support of the cutoff itself. -/
theorem n06_weakNormalDerivative_radial_cutoff
    (hab : D.a < D.b) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    WeakNormalDerivative D (fun p => χ p.1) (fun p => deriv χ p.1) := by
  have hdχ : Continuous (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2.continuous
  have hχL : MemLp χ 2 (volume.restrict (radialCore D)) :=
    interval_memLp_of_continuous hχ.continuous
  have hdχL : MemLp (deriv χ) 2 (volume.restrict (radialCore D)) :=
    interval_memLp_of_continuous hdχ
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := memLp_const 1
  simpa only [mul_one] using r11b_weakNormalDerivative_tensor hab hχL hdχL h1
    (fun r _ => (hχ.differentiable (by simp) r).hasDerivAt) hdχ.continuousOn

/-- The left constant is subtracted with the specified physical-space
cutoff. The formula retains its actual derivative and never identifies
this cutoff with the different cutoff in the radial inverse norm. -/
theorem n06_reference_remainder_normal_transport
    (hK : N04PartA D S C K base ε) (hab : D.a < D.b)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hY : ContDiffOn ℝ ∞ Y (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hh : ContDiffOn ℝ ∞ h (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hchart : ∀ p ∈ physicalPieceOpen S K m, K.chart z m p = (Y p.1, p.2))
    (hheight : ∀ p ∈ physicalPieceOpen S K m, K.height z m p = h p.1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {η ur : PolarPoint → ℝ} (aL : ℝ)
    (hweak : WeakNormalDerivative D η ur)
    (hη : MemLp η 2 (radialPhysicalMeasure D))
    (hur : MemLp ur 2 (radialPhysicalMeasure D))
    (hηp : Function.Periodic η (0, Real.pi))
    (hurp : Function.Periodic ur (0, Real.pi))
    (hW : MemLp (canonicalHeight S K z m (n06ReferenceRemainder χ η aL)) 2
      (canonicalMeasure S K m))
    (hG : MemLp (n06ReferenceNormalField S K z m Y h (n06ReferenceRemainder χ η aL)
      (fun p => ur p - aL * deriv χ p.1)) 2 (canonicalMeasure S K m)) :
    ∀ φ, CanonicalTest S K m φ →
      (∫ p, n06ReferenceNormalField S K z m Y h (n06ReferenceRemainder χ η aL)
          (fun q => ur q - aL * deriv χ q.1) p * φ p ∂canonicalMeasure S K m) =
      -(∫ p, canonicalHeight S K z m (n06ReferenceRemainder χ η aL) p *
        mixedDerivative 1 0 φ p ∂canonicalMeasure S K m) := by
  have hχL : MemLp (fun p : PolarPoint => χ p.1) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (hχ.continuous.comp continuous_fst)
  have hdχL : MemLp (fun p : PolarPoint => deriv χ p.1) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp
      ((contDiff_infty_iff_deriv.mp hχ).2.continuous.comp continuous_fst)
  have hrem : WeakNormalDerivative D (n06ReferenceRemainder χ η aL)
      (fun p => ur p - aL * deriv χ p.1) :=
    n06_weakNormalDerivative_sub_smul hab.le hη hur hχL hdχL hweak
      (n06_weakNormalDerivative_radial_cutoff hab hχ) aL
  have hremL : MemLp (n06ReferenceRemainder χ η aL) 2 (radialPhysicalMeasure D) :=
    hη.sub (hχL.const_mul aL)
  have hremrL : MemLp (fun p => ur p - aL * deriv χ p.1) 2 (radialPhysicalMeasure D) :=
    hur.sub (hdχL.const_mul aL)
  have hremp : Function.Periodic (n06ReferenceRemainder χ η aL) (0, Real.pi) := by
    intro p
    simp only [n06ReferenceRemainder, n06ReferenceLeftField, hηp p, Prod.fst_add, add_zero]
  have hremrp : Function.Periodic (fun p => ur p - aL * deriv χ p.1) (0, Real.pi) := by
    intro p
    simp only [hurp p, Prod.fst_add, add_zero]
  exact n06_reference_normal_transport hK hab.le hz hs hY hh hchart hheight
    hrem hremL hremrL hremp hremrp hW hG

end ContinuousFlexibility.Analysis
