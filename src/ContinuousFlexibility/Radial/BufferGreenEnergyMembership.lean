module

public import ContinuousFlexibility.Radial.PositiveBufferEnergyMass
public import ContinuousFlexibility.Radial.PositiveBufferComparisonGreenRegularity
public import ContinuousFlexibility.Radial.BufferAffineCutGlue

/-!
# Actual derivative and weighted membership of the cutoff Green column
The exterior derivative and weight come from genuine positive energy. Measurable
gluing and affine transfer give the global derivative and weight in the energy graph.
-/

@[expose] public section
noncomputable section
namespace ContinuousFlexibility.Radial
open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem buffer_memLp_Ioi_of_zero_after {f : ℝ → ℝ} (hf : Continuous f) (L : ℝ)
    (hzero : ∀ x, L ≤ x → f x = 0) : MemLp f 2 (volume.restrict (Ioi 0)) := by
  have hc : MemLp f 2 (volume.restrict (Icc 0 L)) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
      (hf.pow 2).integrableOn_Icc
  have hi : MemLp ((Icc 0 L).indicator f) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).mpr hc
  refine MemLp.ae_eq ?_ (hi.restrict (Ioi 0))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  by_cases hxL : x ≤ L
  · exact indicator_of_mem (show x ∈ Icc 0 L from ⟨hx.le, hxL⟩) f
  · rw [indicator_of_notMem (show x ∉ Icc 0 L from fun h => hxL h.2),
      hzero x (le_of_not_ge hxL)]

def positiveBufferGreenProfileDerivative (σ : ℝ) (pin pout : ℝ → ℝ) : ℝ → ℝ :=
  bufferCutGlue 0 (deriv (fun t => pout (-t)))
    (deriv (fun t => positiveBufferCutoff σ t * pin t))

def positiveBufferGreenKernelDerivative (B : BufferData) (i : Fin 2) (A : ℝ)
    (pin pout : ℝ → ℝ) (x : ℝ) : ℝ :=
  A⁻¹ * (-bufferSign i * B.mass i) *
    positiveBufferGreenProfileDerivative (B.action i) pin pout (positiveBufferCoordinate B i x)

theorem positiveBufferGreenProfileDerivative_memLp {σ : ℝ} {pin pout : ℝ → ℝ}
    (hpin : ContDiff ℝ ∞ pin) (hpout : ContDiff ℝ ∞ pout)
    (hdout : MemLp (deriv pout) 2 (volume.restrict (Ici 0))) :
    MemLp (positiveBufferGreenProfileDerivative σ pin pout) 2 volume := by
  have hcomp := positiveBuffer_affine_memLp_two_restrict measurableSet_Ici hdout
    (0 : ℝ) (by norm_num : (-1 : ℝ) ≠ 0)
  have hpre : (fun x : ℝ => 0 + -1 * x) ⁻¹' Ici 0 = Iic 0 := by ext x; simp
  rw [hpre] at hcomp
  have hreflect : MemLp (fun x => deriv pout (-x)) 2 (volume.restrict (Iic 0)) := by
    simpa only [zero_add, neg_one_mul] using hcomp
  have hleft : MemLp (deriv (fun t => pout (-t))) 2 (volume.restrict (Iic 0)) := by
    have hd : deriv (fun t => pout (-t)) = fun t => -deriv pout (-t) := by
      funext t
      exact positiveBuffer_reflection_deriv (hpout.differentiable (by simp) (-t))
    rw [hd]
    refine MemLp.ae_eq ?_ hreflect.neg
    filter_upwards [] with t
    change -(deriv pout (-t)) = -(deriv pout (-t))
    rfl
  have hsm : ContDiff ℝ ∞ (fun t => positiveBufferCutoff σ t * pin t) :=
    (positiveBufferCutoff_contDiff σ).mul hpin
  have hright : MemLp (deriv (fun t => positiveBufferCutoff σ t * pin t)) 2
      (volume.restrict (Ioi 0)) := by
    apply buffer_memLp_Ioi_of_zero_after (contDiff_infty_iff_deriv.mp hsm).2.continuous (σ + 5)
    intro t ht
    have hχ := positiveBufferCutoff_zero (by linarith : σ + 4 ≤ t)
    have hχ' := (positiveBufferCutoff_derivatives_zero
      (show t ∉ Icc (σ + 2) (σ + 4) by intro h; linarith [h.2])).1
    rw [deriv_fun_mul ((positiveBufferCutoff_contDiff σ).differentiable (by simp) t)
      (hpin.differentiable (by simp) t), hχ, hχ']
    ring
  exact positiveBuffer_cutGlue_memLp 0 hleft hright

theorem positiveBufferGreenKernelDerivative_memLp {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) (A : ℝ) {pin pout : ℝ → ℝ}
    (hpin : ContDiff ℝ ∞ pin) (hpout : ContDiff ℝ ∞ pout)
    (hdout : MemLp (deriv pout) 2 (volume.restrict (Ici 0))) :
    MemLp (positiveBufferGreenKernelDerivative B i A pin pout) 2 volume := by
  have hraw := positiveBufferGreenProfileDerivative_memLp (σ := B.action i) hpin hpout hdout
  have hraw' : MemLp (positiveBufferGreenProfileDerivative (B.action i) pin pout) 2
      (volume.restrict univ) := by simpa only [Measure.restrict_univ] using hraw
  have h := positiveBuffer_affine_memLp_two_restrict MeasurableSet.univ hraw'
    (bufferSign i * B.mass i * bufferCut B i)
    (positiveBufferCoordinate_slope_ne_zero hB i)
  change MemLp (fun x => A⁻¹ * (-bufferSign i * B.mass i) *
    positiveBufferGreenProfileDerivative (B.action i) pin pout (positiveBufferCoordinate B i x))
      2 volume
  simpa only [preimage_univ, Measure.restrict_univ,
    ← positiveBufferCoordinate_affine] using h.const_mul (A⁻¹ * (-bufferSign i * B.mass i))

theorem positiveBufferGreenProfileWeight_memLp {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {pin pout : ℝ → ℝ}
    (hpin : Continuous pin)
    (hwout : MemLp (fun t => sqrt (1 + |B.potential (positiveBufferPoint B i (-t))|) * pout t)
      2 (volume.restrict (Ici 0))) :
    MemLp (fun t => sqrt (1 + |B.potential (positiveBufferPoint B i t)|) *
      positiveBufferGreenProfile (B.action i) pin pout t) 2 volume := by
  have hV := hB.2.2.2.2.1.continuous
  let w (t : ℝ) := sqrt (1 + |B.potential (positiveBufferPoint B i t)|)
  have hw : Continuous w :=
    (continuous_const.add (hV.comp (positiveBufferPoint_contDiff B i).continuous).abs).sqrt
  have hcomp := positiveBuffer_affine_memLp_two_restrict measurableSet_Ici hwout
    (0 : ℝ) (by norm_num : (-1 : ℝ) ≠ 0)
  have hpre : (fun x : ℝ => 0 + -1 * x) ⁻¹' Ici 0 = Iic 0 := by ext x; simp
  rw [hpre] at hcomp
  have hleft : MemLp (fun t => w t * pout (-t)) 2 (volume.restrict (Iic 0)) := by
    simpa only [w, zero_add, neg_one_mul, neg_neg] using hcomp
  have hright : MemLp (fun t => w t * (positiveBufferCutoff (B.action i) t * pin t))
      2 (volume.restrict (Ioi 0)) := by
    apply buffer_memLp_Ioi_of_zero_after
      (hw.mul ((positiveBufferCutoff_contDiff (B.action i)).continuous.mul hpin)) (B.action i + 4)
    intro t ht
    change w t * (positiveBufferCutoff (B.action i) t * pin t) = 0
    rw [positiveBufferCutoff_zero ht, zero_mul, mul_zero]
  refine MemLp.ae_eq ?_ (positiveBuffer_cutGlue_memLp 0 hleft hright)
  filter_upwards [] with t
  by_cases ht : t ≤ 0 <;> simp [positiveBufferGreenProfile, bufferCutGlue, ht, w]

theorem positiveBufferGreenKernel_weight_memLp {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) (A : ℝ) {pin pout : ℝ → ℝ}
    (hpin : Continuous pin)
    (hwout : MemLp (fun t => sqrt (1 + |B.potential (positiveBufferPoint B i (-t))|) * pout t)
      2 (volume.restrict (Ici 0))) :
    MemLp (fun x => sqrt (1 + |B.potential x|) * positiveBufferGreenKernel B i A pin pout x)
      2 volume := by
  let W (t : ℝ) := sqrt (1 + |B.potential (positiveBufferPoint B i t)|) *
    positiveBufferGreenProfile (B.action i) pin pout t
  have hraw : MemLp W 2 (volume.restrict univ) := by
    simpa only [Measure.restrict_univ] using positiveBufferGreenProfileWeight_memLp hB i hpin hwout
  have h := positiveBuffer_affine_memLp_two_restrict MeasurableSet.univ hraw
    (bufferSign i * B.mass i * bufferCut B i) (positiveBufferCoordinate_slope_ne_zero hB i)
  have hphysical : MemLp (fun x => A⁻¹ * W (positiveBufferCoordinate B i x)) 2 volume := by
    simpa only [preimage_univ, Measure.restrict_univ, ← positiveBufferCoordinate_affine] using
      h.const_mul A⁻¹
  refine MemLp.ae_eq ?_ hphysical
  filter_upwards [] with x
  dsimp [W, positiveBufferGreenKernel]
  rw [positiveBufferPoint_coordinate hB i x]
  ring

/-- Actual physical exterior energy supplies all normalized exterior L² data
needed by the Green-column construction. -/
theorem positiveBuffer_outward_profile_memLp {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {p : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p)
    (hpLp : MemLp p 2 (volume.restrict (bufferExterior B i)))
    (hE : IntegrableOn (fun x => deriv p x ^ 2 + B.potential x * p x ^ 2)
      (bufferExterior B i) volume) :
    MemLp (fun t => p (positiveBufferPoint B i (-t))) 2 (volume.restrict (Ici 0)) ∧
      MemLp (deriv (fun t => p (positiveBufferPoint B i (-t)))) 2
        (volume.restrict (Ici 0)) ∧
      MemLp (fun t => sqrt (1 + |B.potential (positiveBufferPoint B i (-t))|) *
        p (positiveBufferPoint B i (-t))) 2 (volume.restrict (Ici 0)) := by
  have hV := hB.2.2.2.2.1.continuous
  have hs : MeasurableSet (bufferExterior B i) := by
    unfold bufferExterior
    split_ifs
    · exact measurableSet_Iio
    · exact measurableSet_Ioi
  have hpos : ∀ x ∈ bufferExterior B i, 0 ≤ B.potential x :=
    fun x hx => (sq_nonneg (B.mass i)).trans
      (positiveBuffer_potential_lower_exterior hB i (subset_closure hx))
  have hdw := positiveBuffer_energy_memLp hV hp.continuous
    (contDiff_infty_iff_deriv.mp hp).2.continuous (bufferExterior B i) hs hpos hpLp hE
  have hb : bufferSign i / B.mass i ≠ 0 := by
    intro hz
    apply positiveBufferPoint_slope_ne_zero hB i
    rw [neg_div, hz, neg_zero]
  have haff (t : ℝ) : positiveBufferPoint B i (-t) =
      bufferCut B i + (bufferSign i / B.mass i) * t := by
    rw [positiveBufferPoint_affine]
    ring
  have hpre : (fun t : ℝ => bufferCut B i + (bufferSign i / B.mass i) * t) ⁻¹'
      bufferExterior B i = Ioi 0 := by
    have hfun : (fun t : ℝ => bufferCut B i + (bufferSign i / B.mass i) * t) =
        fun t => positiveBufferPoint B i (-t) := funext (fun t => (haff t).symm)
    rw [hfun, positiveBufferPoint_outward_preimage_exterior hB i]
  have htransfer (g : ℝ → ℝ) (hg : MemLp g 2 (volume.restrict (bufferExterior B i))) :
      MemLp (fun t => g (positiveBufferPoint B i (-t))) 2 (volume.restrict (Ici 0)) := by
    have h := positiveBuffer_affine_memLp_two_restrict hs hg (bufferCut B i) hb
    rw [hpre] at h
    have h' : MemLp (fun t => g (positiveBufferPoint B i (-t))) 2
        (volume.restrict (Ioi 0)) := by
      simpa only [← haff] using h
    rwa [restrict_Ioi_eq_restrict_Ici] at h'
  have hderiv : deriv (fun t => p (positiveBufferPoint B i (-t))) =
      fun t => (bufferSign i / B.mass i) * deriv p (positiveBufferPoint B i (-t)) := by
    funext t
    have hd := positiveBuffer_affine_hasDerivAt
      (a := bufferCut B i) (b := bufferSign i / B.mass i) (x := t)
      (by simpa only [haff] using
        (hp.differentiable (by simp) (positiveBufferPoint B i (-t))).hasDerivAt)
    simpa only [← haff] using hd.deriv
  refine ⟨htransfer p hpLp, ?_, htransfer _ hdw.2⟩
  rw [hderiv]
  exact (htransfer (deriv p) hdw.1).const_mul (bufferSign i / B.mass i)

end ContinuousFlexibility.Radial
