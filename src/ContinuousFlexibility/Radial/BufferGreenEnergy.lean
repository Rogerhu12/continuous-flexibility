import ContinuousFlexibility.Radial.BufferGreenEnergyMembership

/-!
# The genuine normalized Green energy column
The cutoff profile has an actual weak derivative and actual potential weight in L².
The classical commutator supplies the ordinary source, and conormal normalization
makes the derivative jump exactly one. The identity holds for every energy test.
-/
noncomputable section
namespace ContinuousFlexibility.Radial
open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem buffer_reflection_second_deriv {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p) (t : ℝ) :
    deriv (deriv (fun x => p (-x))) t = deriv (deriv p) (-t) := by
  have hfirst : deriv (fun x => p (-x)) = fun x => -deriv p (-x) := by
    funext x
    exact positiveBuffer_reflection_deriv (hp.differentiable (by simp) (-x))
  rw [hfirst]
  have hd := bufferAffineBranch_hasDerivAt (contDiff_infty_iff_deriv.mp hp).2
    0 (-1) (-1) t
  have hd' : HasDerivAt (fun x => -deriv p (-x)) (deriv (deriv p) (-t)) t := by
    simpa only [sub_zero, neg_one_mul, neg_neg, one_mul, neg_mul, mul_one] using hd
  exact hd'.deriv

theorem positiveBufferGreenProfile_curvature {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {pin pout : ℝ → ℝ}
    (hpin : ContDiff ℝ ∞ pin) (hpout : ContDiff ℝ ∞ pout)
    (hin : ∀ t ∈ Ioo 0 (B.action i + 6),
      -deriv (deriv pin) t + (B.potential (positiveBufferPoint B i t) / B.mass i ^ 2) * pin t = 0)
    (hout : ∀ t > 0,
      -deriv (deriv pout) t + (B.potential (positiveBufferPoint B i (-t)) / B.mass i ^ 2) * pout t = 0)
    {t : ℝ} (ht : t ≠ 0) :
    bufferCutGlue 0 (deriv (deriv (fun x => pout (-x))))
      (deriv (deriv (fun x => positiveBufferCutoff (B.action i) x * pin x))) t =
        (B.potential (positiveBufferPoint B i t) / B.mass i ^ 2) *
          positiveBufferGreenProfile (B.action i) pin pout t -
            positiveBufferCutoffError (B.action i) pin (deriv pin) t := by
  have hσ := buffer_action_pos hB i
  by_cases htneg : t < 0
  · rw [bufferCutGlue_of_le _ _ _ htneg.le, positiveBufferGreenProfile,
      bufferCutGlue_of_le _ _ _ htneg.le, buffer_reflection_second_deriv hpout]
    have he : positiveBufferCutoffError (B.action i) pin (deriv pin) t = 0 := by
      apply Function.notMem_support.mp
      intro hm
      have hx := positiveBufferCutoffError_support (B.action i) pin (deriv pin) hm
      linarith [hx.1]
    rw [he, sub_zero]
    have ho := hout (-t) (by linarith)
    rw [neg_neg] at ho
    linarith
  · have htpos : 0 < t := lt_of_le_of_ne (le_of_not_gt htneg) (Ne.symm ht)
    rw [bufferCutGlue_of_lt _ _ _ htpos, positiveBufferGreenProfile,
      bufferCutGlue_of_lt _ _ _ htpos]
    by_cases htw : t < B.action i + 6
    · have hu : ∀ x ∈ Ioo 0 (B.action i + 6), HasDerivAt pin (deriv pin x) x :=
        fun x _ => (hpin.differentiable (by simp) x).hasDerivAt
      have hdu : ∀ x ∈ Ioo 0 (B.action i + 6), HasDerivAt (deriv pin)
          ((B.potential (positiveBufferPoint B i x) / B.mass i ^ 2) * pin x) x := by
        intro x hx
        convert ((contDiff_infty_iff_deriv.mp hpin).2.differentiable (by simp) x).hasDerivAt using 1
        linarith [hin x hx]
      have hc := positiveBufferCutoff_commutator isOpen_Ioo hu hdu (B.action i) ⟨htpos, htw⟩
      linarith
    · have htcut : B.action i + 4 < t := by linarith [le_of_not_gt htw]
      have hlocal : (fun x => positiveBufferCutoff (B.action i) x * pin x) =ᶠ[𝓝 t]
          (fun _ => 0) := by
        filter_upwards [eventually_gt_nhds htcut] with x hx
        rw [positiveBufferCutoff_zero hx.le, zero_mul]
      have hsecond : deriv (deriv (fun x => positiveBufferCutoff (B.action i) x * pin x)) t = 0 := by
        simpa only [deriv_const] using hlocal.deriv.deriv_eq
      have he : positiveBufferCutoffError (B.action i) pin (deriv pin) t = 0 := by
        apply Function.notMem_support.mp
        intro hm
        exact htcut.not_ge (positiveBufferCutoffError_support (B.action i) pin (deriv pin) hm).2
      rw [hsecond, positiveBufferCutoff_zero htcut.le, zero_mul, mul_zero, he, sub_zero]

theorem positiveBufferGreenProfile_jump {σ : ℝ} (hσ : 0 < σ) {pin pout : ℝ → ℝ}
    (hpin : ContDiff ℝ ∞ pin) (hpout : ContDiff ℝ ∞ pout) :
    deriv (fun x => pout (-x)) 0 -
      deriv (fun x => positiveBufferCutoff σ x * pin x) 0 =
        -deriv pout 0 - deriv pin 0 := by
  have hχ0 := positiveBufferCutoff_one (σ := σ) (x := 0) (by linarith)
  have hχ'0 := (positiveBufferCutoff_derivatives_zero
    (show (0 : ℝ) ∉ Icc (σ + 2) (σ + 4) by intro h; linarith [h.1])).1
  have href0 := positiveBuffer_reflection_deriv (u := pout) (x := 0)
    (by simpa only [neg_zero] using hpout.differentiable (by simp) 0)
  rw [href0, neg_zero,
    deriv_mul ((positiveBufferCutoff_contDiff σ).differentiable (by simp) 0)
      (hpin.differentiable (by simp) 0), hχ0, hχ'0, zero_mul, one_mul, zero_add]

theorem positiveBufferGreenKernel_exists_energy {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {A : ℝ} (hA : 0 < A) {pin pout : ℝ → ℝ}
    (hpin : ContDiff ℝ ∞ pin) (hpout : ContDiff ℝ ∞ pout)
    (hpin0 : pin 0 = 1) (hpout0 : pout 0 = 1)
    (hpoutLp : MemLp pout 2 (volume.restrict (Ici 0)))
    (hdoutLp : MemLp (deriv pout) 2 (volume.restrict (Ici 0)))
    (hwoutLp : MemLp
      (fun t => sqrt (1 + |B.potential (positiveBufferPoint B i (-t))|) * pout t)
      2 (volume.restrict (Ici 0)))
    (hin : ∀ t ∈ Ioo 0 (B.action i + 6),
      -deriv (deriv pin) t + (B.potential (positiveBufferPoint B i t) / B.mass i ^ 2) * pin t = 0)
    (hout : ∀ t > 0,
      -deriv (deriv pout) t + (B.potential (positiveBufferPoint B i (-t)) / B.mass i ^ 2) * pout t = 0)
    (hAnorm : A = B.mass i * (-deriv pout 0 - deriv pin 0))
    (f : RadialL2) (hf : (f : ℝ → ℝ) =ᵐ[volume]
      positiveBufferGreenError B i A pin (deriv pin)) :
    ∃ e : PositiveBufferEnergy B.potential,
      (positiveBufferEnergyCoordinate B.potential 0 e : ℝ → ℝ) =ᵐ[volume]
        positiveBufferGreenKernel B i A pin pout ∧
      ∀ v : PositiveBufferEnergy B.potential,
        positiveBufferEnergyForm B.potential hB.2.2.2.2.1.continuous e v =
          inner (𝕜 := ℝ) f (positiveBufferEnergyCoordinate B.potential 0 v) +
            positiveBufferTraceAt B.potential (bufferCut B i) v := by
  have hm := buffer_mass_pos hB i
  have hV := hB.2.2.2.2.1.continuous
  have hreal := hB.2.2.2.2.2.1
  let hK := positiveBufferGreenKernel_memLp hB i A hpin.continuous hpout.continuous
    hpin0 hpout0 hpoutLp.integrable_sq
  let hD := positiveBufferGreenKernelDerivative_memLp hB i A hpin hpout hdoutLp
  let hW := positiveBufferGreenKernel_weight_memLp hB i A hpin.continuous hwoutLp
  let u : RadialL2 := hK.toLp (positiveBufferGreenKernel B i A pin pout)
  let d : RadialL2 := hD.toLp (positiveBufferGreenKernelDerivative B i A pin pout)
  let q : RadialL2 := hW.toLp
    (fun x => sqrt (1 + |B.potential x|) * positiveBufferGreenKernel B i A pin pout x)
  have hu : (u : ℝ → ℝ) =ᵐ[volume] positiveBufferGreenKernel B i A pin pout := MemLp.coeFn_toLp hK
  have hd : (d : ℝ → ℝ) =ᵐ[volume] positiveBufferGreenKernelDerivative B i A pin pout := MemLp.coeFn_toLp hD
  let pL (t : ℝ) := pout (-t)
  let pR (t : ℝ) := positiveBufferCutoff (B.action i) t * pin t
  have hpL : ContDiff ℝ ∞ pL := positiveBuffer_reflection_contDiff hpout
  have hpR : ContDiff ℝ ∞ pR := (positiveBufferCutoff_contDiff (B.action i)).mul hpin
  have hmatch : pL 0 = pR 0 := by
    dsimp [pL, pR]
    rw [neg_zero, hpout0, positiveBufferCutoff_one (by linarith [buffer_action_pos hB i]), hpin0, mul_one]
  have hu' : (u : ℝ → ℝ) =ᵐ[volume]
      (fun x => A⁻¹ * bufferCutGlue 0 pL pR ((-bufferSign i * B.mass i) * (x - bufferCut B i))) := by
    simpa only [pL, pR, positiveBufferGreenKernel, positiveBufferGreenProfile,
      positiveBufferCoordinate] using hu
  have hd' : (d : ℝ → ℝ) =ᵐ[volume]
      (fun x => A⁻¹ * (-bufferSign i * B.mass i) *
        bufferCutGlue 0 (deriv pL) (deriv pR) ((-bufferSign i * B.mass i) * (x - bufferCut B i))) := by
    simpa only [pL, pR, positiveBufferGreenKernelDerivative, positiveBufferGreenProfileDerivative,
      positiveBufferCoordinate] using hd
  have hr : (fun x => A⁻¹ * (-bufferSign i * B.mass i) ^ 2 *
      bufferCutGlue 0 (deriv (deriv pL)) (deriv (deriv pR))
        ((-bufferSign i * B.mass i) * (x - bufferCut B i))) =ᵐ[volume]
          (fun x => B.potential x * u x - f x) := by
    filter_upwards [hu, hf, volume.ae_ne (bufferCut B i)] with x hux hfx hxc
    have ht : positiveBufferCoordinate B i x ≠ 0 := by
      intro hz
      have h := positiveBufferPoint_coordinate hB i x
      rw [hz, positiveBufferPoint_zero] at h
      exact hxc h.symm
    have hcurv := positiveBufferGreenProfile_curvature hB i hpin hpout hin hout ht
    change A⁻¹ * (-bufferSign i * B.mass i) ^ 2 *
      bufferCutGlue 0 (deriv (deriv pL)) (deriv (deriv pR)) (positiveBufferCoordinate B i x) = _
    rw [hux, hfx]
    dsimp only [pL, pR]
    rw [hcurv, mul_pow, neg_sq, bufferSign_sq, one_mul,
      positiveBufferPoint_coordinate hB i x]
    unfold positiveBufferGreenKernel positiveBufferGreenError
    field_simp [hm.ne', hA.ne']
    <;> ring
  obtain ⟨hweak, hidentity⟩ := bufferCutGlue_affine_energy_identity hV hpL hpR
    (bufferCut B i) A⁻¹ (positiveBufferCoordinate_slope_ne_zero hB i) hmatch hu' hd' hr
  have hweight : (q : ℝ → ℝ) =ᵐ[volume] fun x => sqrt (1 + |B.potential x|) * u x := by
    filter_upwards [MemLp.coeFn_toLp hW, hu] with x hqx hux
    change q x = sqrt (1 + |B.potential x|) * u x
    rw [hqx, hux]
  let e : PositiveBufferEnergy B.potential :=
    ⟨WithLp.toLp 2 ![u, d, q], hweak, hweight⟩
  have hjump : A⁻¹ * |-bufferSign i * B.mass i| * (deriv pL 0 - deriv pR 0) = 1 := by
    change A⁻¹ * |-bufferSign i * B.mass i| *
      (deriv (fun t => pout (-t)) 0 -
        deriv (fun t => positiveBufferCutoff (B.action i) t * pin t) 0) = 1
    rw [positiveBufferCoordinate_abs_slope hB i,
      positiveBufferGreenProfile_jump (buffer_action_pos hB i) hpin hpout,
      mul_assoc, ← hAnorm, inv_mul_cancel₀ hA.ne']
  refine ⟨e, hu, ?_⟩
  intro v
  have h := positiveBuffer_delta_energy_of_integral_compact hreal hV e f (bufferCut B i) 1
    (fun φ hφ hcφ => by
      have h := hidentity φ hφ hcφ
      rw [hjump, one_mul] at h
      exact h) v
  simpa only [one_mul] using h
end ContinuousFlexibility.Radial
