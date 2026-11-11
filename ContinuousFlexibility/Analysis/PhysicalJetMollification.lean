import ContinuousFlexibility.Analysis.CylinderTestPeriodization
import ContinuousFlexibility.Analysis.PhysicalJetBonding
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Compact-kernel convolution of actual physical jets

Convolution of the periodic planar representative with a compact smooth
kernel is smooth and angularly periodic. The planar weak-test identity
transfers each mixed derivative of the kernel to the corresponding actual
unweighted derivative class of the physical jet graph.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Convolution

theorem locallyIntegrable_cylinderPeriodicExtension (u : CylinderL2) :
    LocallyIntegrable (cylinderPeriodicExtension u) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  let : IsFiniteMeasure ((volume : Measure PolarPoint).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact (memLp_cylinderPeriodicExtension_restrict_compact u hK).integrable (by norm_num)

/-- The actual planar convolution with respect to the product Lebesgue measure. -/
def planarConvolution (f κ : PolarPoint → ℝ) : PolarPoint → ℝ :=
  f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ

theorem planarConvolution_apply (f κ : PolarPoint → ℝ) (p : PolarPoint) :
    planarConvolution f κ p = ∫ q, f q * κ (p - q) := by
  simp only [planarConvolution, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

theorem integrable_planarConvolution_integrand {f κ : PolarPoint → ℝ}
    (hf : LocallyIntegrable f volume) (hκ : Continuous κ) (hc : HasCompactSupport κ)
    (p : PolarPoint) : Integrable (fun q => f q * κ (p - q)) volume := by
  simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    hc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hκ p

theorem contDiff_planarConvolution {f κ : PolarPoint → ℝ} (hf : LocallyIntegrable f volume)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) : ContDiff ℝ ∞ (planarConvolution f κ) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hκ

theorem planarConvolution_periodic_left {f κ : PolarPoint → ℝ} {v : PolarPoint}
    (hf : Function.Periodic f v) : Function.Periodic (planarConvolution f κ) v := by
  intro p
  simp only [planarConvolution_apply]
  calc
    (∫ q : PolarPoint, f q * κ (p + v - q)) =
        ∫ q : PolarPoint, f (q + v) * κ (p + v - (q + v)) :=
      (integral_add_right_eq_self (fun q : PolarPoint => f q * κ (p + v - q)) v).symm
    _ = ∫ q : PolarPoint, f q * κ (p - q) := by
      apply integral_congr_ae
      filter_upwards [] with q
      rw [hf q, add_sub_add_right_eq_sub]

/-- Evaluation of the actual Fréchet derivative commutes with compact-kernel convolution. -/
theorem fderiv_planarConvolution_apply {f κ : PolarPoint → ℝ} (hf : LocallyIntegrable f volume)
    (hκ : ContDiff ℝ 1 κ) (hc : HasCompactSupport κ) (p d : PolarPoint) :
    fderiv ℝ (planarConvolution f κ) p d = planarConvolution f (fun q => fderiv ℝ κ q d) p := by
  unfold planarConvolution
  rw [(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hκ p).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hf (hc.fderiv ℝ)
    (hκ.continuous_fderiv one_ne_zero) p d

theorem radialPartial_planarConvolution {f κ : PolarPoint → ℝ} (hf : LocallyIntegrable f volume)
    (hκ : ContDiff ℝ 1 κ) (hc : HasCompactSupport κ) :
    radialPartial (planarConvolution f κ) = planarConvolution f (radialPartial κ) :=
  funext fun p => fderiv_planarConvolution_apply hf hκ hc p (1, 0)

theorem angularPartial_planarConvolution {f κ : PolarPoint → ℝ} (hf : LocallyIntegrable f volume)
    (hκ : ContDiff ℝ 1 κ) (hc : HasCompactSupport κ) :
    angularPartial (planarConvolution f κ) = planarConvolution f (angularPartial κ) :=
  funext fun p => fderiv_planarConvolution_apply hf hκ hc p (0, 1)

theorem mixedDerivative_planarConvolution {f κ : PolarPoint → ℝ} (hf : LocallyIntegrable f volume)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (a b : ℕ) :
    mixedDerivative a b (planarConvolution f κ) = planarConvolution f (mixedDerivative a b κ) := by
  have hs := contDiff_planarConvolution hf hκ hc
  induction a with
  | zero =>
    induction b with
    | zero =>
      have he (g : PolarPoint → ℝ) : mixedDerivative 0 0 g = g := by
        funext p
        simp only [mixedDerivative, iteratedDeriv_zero]
      simp only [he]
    | succ b ih =>
      rw [← angularPartial_mixedDerivative hs 0 b, ih,
        angularPartial_planarConvolution hf ((contDiff_mixedDerivative hκ 0 b).of_le (by simp))
          (hasCompactSupport_mixedDerivative hκ hc 0 b), angularPartial_mixedDerivative hκ 0 b]
  | succ a ih =>
    rw [← radialPartial_mixedDerivative hs a b, ih,
      radialPartial_planarConvolution hf ((contDiff_mixedDerivative hκ a b).of_le (by simp))
        (hasCompactSupport_mixedDerivative hκ hc a b), radialPartial_mixedDerivative hκ a b]

private theorem mixedDerivative_comp_const_sub (κ : PolarPoint → ℝ) (a b : ℕ) (p q : PolarPoint) :
    mixedDerivative a b (fun y => κ (p - y)) q =
      (-1 : ℝ) ^ (a + b) * mixedDerivative a b κ (p - q) := by
  let G (r : ℝ) := iteratedDeriv b (fun θ : ℝ => κ (r, θ)) (p.2 - q.2)
  have hθ : (fun r : ℝ => iteratedDeriv b (fun θ : ℝ => κ (p.1 - r, p.2 - θ)) q.2) =
      (fun r : ℝ => (-1 : ℝ) ^ b * G (p.1 - r)) := by
    funext r
    have h := congrFun (iteratedDeriv_comp_const_sub b (fun θ : ℝ => κ (p.1 - r, θ)) p.2) q.2
    simpa only [G, Pi.smul_apply, smul_eq_mul] using h
  have hr : iteratedDeriv a (fun r : ℝ => G (p.1 - r)) q.1 =
      (-1 : ℝ) ^ a * iteratedDeriv a G (p.1 - q.1) := by
    have h := congrFun (iteratedDeriv_comp_const_sub a G p.1) q.1
    simpa only [Pi.smul_apply, smul_eq_mul] using h
  change iteratedDeriv a (fun r : ℝ => iteratedDeriv b (fun θ : ℝ => κ (p.1 - r, p.2 - θ)) q.2) q.1 =
    (-1 : ℝ) ^ (a + b) * iteratedDeriv a G (p.1 - q.1)
  rw [hθ, iteratedDeriv_const_mul_field ((-1 : ℝ) ^ b) (fun r : ℝ => G (p.1 - r)), hr, pow_add]
  ring

/-- Testing against the reflected and translated kernel transfers the derivative
to the actual weak derivative of the periodic planar representative. -/
theorem HasWeakMixedDerivative.periodicConvolution {f g : CylinderL2} {a b : ℕ}
    (h : HasWeakMixedDerivative f g a b) {κ : PolarPoint → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) :
    mixedDerivative a b (planarConvolution (cylinderPeriodicExtension f) κ) =
      planarConvolution (cylinderPeriodicExtension g) κ := by
  rw [mixedDerivative_planarConvolution (locallyIntegrable_cylinderPeriodicExtension f) hκ hc]
  funext p
  rw [planarConvolution_apply, planarConvolution_apply]
  let ψ (q : PolarPoint) := κ (p - q)
  have hψ : ContDiff ℝ ∞ ψ := hκ.comp (contDiff_const.sub contDiff_id)
  have hcψ : HasCompactSupport ψ := by
    simpa only [ψ, Function.comp_def, Homeomorph.trans_apply, Homeomorph.coe_neg,
      Homeomorph.coe_addLeft, sub_eq_add_neg] using
      hc.comp_homeomorph ((Homeomorph.neg PolarPoint).trans (Homeomorph.addLeft p))
  have hw := HasWeakMixedDerivative.periodicExtension_test h hψ hcψ
  have htest : (∫ q, cylinderPeriodicExtension f q * mixedDerivative a b ψ q) =
      (-1 : ℝ) ^ (a + b) *
        ∫ q, cylinderPeriodicExtension f q * mixedDerivative a b κ (p - q) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with q
    change cylinderPeriodicExtension f q * mixedDerivative a b (fun y => κ (p - y)) q = _
    rw [mixedDerivative_comp_const_sub κ a b p q]
    ring
  have hsign : (-1 : ℝ) ^ (a + b) * (-1 : ℝ) ^ (a + b) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [htest, ← mul_assoc, hsign, one_mul] at hw
  exact hw.symm

/-- Mollify the common zero coordinate of the actual projective limit. -/
def physicalJetMollification {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (u : PhysicalJetProjectiveLimit hT) (κ : PolarPoint → ℝ) : PolarPoint → ℝ :=
  planarConvolution (cylinderPeriodicExtension (physicalJetProjectiveZero hT u)) κ

theorem contDiff_physicalJetMollification {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (u : PhysicalJetProjectiveLimit hT) {κ : PolarPoint → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) :
    ContDiff ℝ ∞ (physicalJetMollification hT u κ) :=
  contDiff_planarConvolution (locallyIntegrable_cylinderPeriodicExtension (physicalJetProjectiveZero hT u)) hκ hc

theorem physicalJetMollification_periodic {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (u : PhysicalJetProjectiveLimit hT) (κ : PolarPoint → ℝ) :
    Function.Periodic (physicalJetMollification hT u κ) (0, Real.pi) :=
  planarConvolution_periodic_left (κ := κ) (cylinderPeriodicExtension_periodic (physicalJetProjectiveZero hT u))

theorem mixedDerivative_physicalJetMollification {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (u : PhysicalJetProjectiveLimit hT) {κ : PolarPoint → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) {s : ℕ} (j : JetIndex s) :
    mixedDerivative (j.val 0).val (j.val 1).val (physicalJetMollification hT u κ) =
      planarConvolution (cylinderPeriodicExtension (physicalJetNormalizedDerivative hT j (u.val s).val)) κ := by
  have hu : (u.val s).val ∈ physicalJetGraph T s := by
    rw [← physicalJetClosedSubmodule_carrier hT s]
    exact (u.val s).property
  have hw := ((mem_physicalJetGraph_iff_normalized hT (u.val s).val).mp hu).2 j
  rw [physicalJetMollification, physicalJetProjectiveZero_apply hT u s]
  exact HasWeakMixedDerivative.periodicConvolution hw hκ hc

end ContinuousFlexibility.Statements
