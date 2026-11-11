import ContinuousFlexibility.Scalar.S05StateDerivative
import ContinuousFlexibility.Scalar.RectangleParameterIntegral

/-!
# Completion of the scalar type-correction calculus

This proves the frozen S05 statement in manuscript order.  The error is
an actual angular divergence in independent residual and increment variables;
its Green pairing uses the ordinary physical rectangle measure.  Height
compatibility and the corrected determinant identify the characteristic roots.
Finally the integral form of smooth division resolves a simple radial zero,
producing one positive smooth square-root factor on either signed side.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem smooth_angularPartial {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (angularPartial f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- Multiplication by a constant commutes with the actual angular derivative. -/
theorem angularPartial_const_mul_of_smooth {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (x : PolarPoint) :
    angularPartial (fun y => c * f y) x = c * angularPartial f x := by
  rw [angularPartial_mul (differentiableAt_const c) (hf.differentiable (by simp) x)]
  simp only [angularPartial_const, zero_mul, zero_add]

/-- Bilinearity of the concrete correction error, with its coefficient fixed. -/
theorem scalarCorrectionError_bilinear
    (B R S η ξ : PolarPoint → ℝ)
    (hB : ContDiff ℝ ∞ B) (hR : ContDiff ℝ ∞ R) (hS : ContDiff ℝ ∞ S)
    (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (c : ℝ) (x : PolarPoint) :
    scalarCorrectionError B (fun y => R y + S y) η x =
        scalarCorrectionError B R η x + scalarCorrectionError B S η x ∧
      scalarCorrectionError B R (fun y => η y + ξ y) x =
        scalarCorrectionError B R η x + scalarCorrectionError B R ξ x ∧
      scalarCorrectionError B (fun y => c * R y) η x = c * scalarCorrectionError B R η x ∧
      scalarCorrectionError B R (fun y => c * η y) x = c * scalarCorrectionError B R η x := by
  have hηt := smooth_angularPartial hη
  have hξt := smooth_angularPartial hξ
  have hRη := (hB.mul hR).mul hηt
  have hSη := (hB.mul hS).mul hηt
  have hRξ := (hB.mul hR).mul hξt
  refine ⟨?_, ?_, ?_, ?_⟩
  · have heq : (fun y => B y * (R y + S y) * angularPartial η y) =
        (fun y => B y * R y * angularPartial η y + B y * S y * angularPartial η y) := by
      funext y
      ring
    unfold scalarCorrectionError
    rw [heq, angularPartial_add (hRη.differentiable (by simp) x)
      (hSη.differentiable (by simp) x)]
  · have heq : (fun y => B y * R y * angularPartial (fun y => η y + ξ y) y) =
        (fun y => B y * R y * angularPartial η y + B y * R y * angularPartial ξ y) := by
      funext y
      rw [angularPartial_add (hη.differentiable (by simp) y) (hξ.differentiable (by simp) y)]
      ring
    unfold scalarCorrectionError
    rw [heq, angularPartial_add (hRη.differentiable (by simp) x)
      (hRξ.differentiable (by simp) x)]
  · have heq : (fun y => B y * (c * R y) * angularPartial η y) =
        (fun y => c * (B y * R y * angularPartial η y)) := by
      funext y
      ring
    unfold scalarCorrectionError
    rw [heq, angularPartial_const_mul_of_smooth hRη]
  · have heq : (fun y => B y * R y * angularPartial (fun y => c * η y) y) =
        (fun y => c * (B y * R y * angularPartial η y)) := by
      funext y
      rw [angularPartial_const_mul_of_smooth hη]
      ring
    unfold scalarCorrectionError
    rw [heq, angularPartial_const_mul_of_smooth hRη]

/-- A smooth periodic angular divergence has zero integral on one period. -/
theorem integral_scalarCorrectionError_eq_zero
    (B R η : PolarPoint → ℝ)
    (hB : ContDiff ℝ ∞ B) (hR : ContDiff ℝ ∞ R) (hη : ContDiff ℝ ∞ η)
    {T : ℝ} (hBp : Function.Periodic B (0, T))
    (hRp : Function.Periodic R (0, T)) (hηp : Function.Periodic η (0, T)) (r : ℝ) :
    (∫ θ in (0 : ℝ)..T, scalarCorrectionError B R η (r, θ)) = 0 := by
  let flux : PolarPoint → ℝ := fun y => B y * R y * angularPartial η y
  have hflux : ContDiff ℝ ∞ flux := (hB.mul hR).mul (smooth_angularPartial hη)
  have hfluxθ : ContDiff ℝ ∞ (angularPartial flux) := smooth_angularPartial hflux
  have hperiod : flux (r, T) = flux (r, 0) := by
    have hp : Function.Periodic flux (0, T) := by
      intro y
      simp only [flux, hBp y, hRp y, periodic_angularPartial hηp y]
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using hp (r, 0)
  have hslice : Continuous (fun θ : ℝ => angularPartial flux (r, θ)) := by
    simpa only [Function.comp_def, id_eq] using
      hfluxθ.continuous.comp ((continuous_const : Continuous (fun _ : ℝ => r)).prodMk
        continuous_id)
  change (∫ θ in (0 : ℝ)..T, angularPartial flux (r, θ)) = 0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hasDerivAt_angular_slice (hflux.differentiable (by simp) (r, θ)))
    (hslice.intervalIntegrable 0 T),
    hperiod, sub_self]

/-- The independent correction error preserves zero total source. -/
theorem integral_mean_scalarCorrectionError_eq_zero
    (B R η : PolarPoint → ℝ)
    (hB : ContDiff ℝ ∞ B) (hR : ContDiff ℝ ∞ R) (hη : ContDiff ℝ ∞ η)
    (hBp : Function.Periodic B (0, 2 * Real.pi))
    (hRp : Function.Periodic R (0, 2 * Real.pi))
    (hηp : Function.Periodic η (0, 2 * Real.pi)) (a b : ℝ) :
    (∫ r in a..b, (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      scalarCorrectionError B R η (r, θ)) = 0 := by
  simp only [integral_scalarCorrectionError_eq_zero B R η hB hR hη hBp hRp hηp,
    mul_zero, intervalIntegral.integral_zero]

/-- The admissible finite-rectangle Green identity in the frozen statement's convention. -/
theorem scalar_corrected_green_pairing
    (w : ℝ → ℝ) (z φ ψ : PolarPoint → ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a < b)
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z)
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hzp : Function.Periodic z (0, 2 * Real.pi))
    (hφp : Function.Periodic φ (0, 2 * Real.pi))
    (hψp : Function.Periodic ψ (0, 2 * Real.pi))
    (hadm : ∀ x ∈ Icc a b ×ˢ Icc (0 : ℝ) (2 * Real.pi),
      0 < polarDiscriminant w z x ∧
      heightQ (profileEnergy w x) (heightRadial z x) (angularPartial (heightAngular z) x) ≠ 0)
    (hboundary : ∀ θ,
      greenNormalFlux (polarLinearA w z) (polarLinearB w z) φ ψ (a, θ) = 0 ∧
      greenNormalFlux (polarLinearA w z) (polarLinearB w z) φ ψ (b, θ) = 0) :
    (∫ r in a..b, ∫ θ in (0 : ℝ)..(2 * Real.pi),
      φ (r, θ) * heightCorrectedDivergence w z ψ (r, θ) -
        ψ (r, θ) * heightCorrectedDivergence w z φ (r, θ)) = 0 := by
  have hrect : uIcc a b ×ˢ uIcc (0 : ℝ) (2 * Real.pi) =
      Icc a b ×ˢ Icc (0 : ℝ) (2 * Real.pi) := by
    rw [uIcc_of_le hab.le, uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  apply integral_heightCorrected_green_eq_zero_of_admissible
    (fun _ _ => hw.contDiffAt) (fun _ _ => hz.contDiffAt)
    (fun _ _ => hφ.contDiffAt) (fun _ _ => hψ.contDiffAt)
    (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) hzp hφp hψp
    (fun θ _ => (hboundary θ).1) (fun θ _ => (hboundary θ).2)
  · rw [hrect] at hx
    exact (ha.trans_le hx.1.1).ne'
  · rw [hrect] at hx
    exact (hadm x hx).1
  · rw [hrect] at hx
    exact (hadm x hx).2

private theorem quadratic_roots_of_drift_speed
    {a b c d v : ℝ} (ha : a ≠ 0) (hd : a * d = b)
    (hv : a ^ 2 * v ^ 2 = b ^ 2 - a * c) (s : ℝ) :
    a * s ^ 2 - 2 * b * s + c = 0 ↔ s = d - v ∨ s = d + v := by
  have hc : c = a * (d ^ 2 - v ^ 2) := by
    apply (mul_left_cancel₀ ha)
    calc
      a * c = b ^ 2 - a ^ 2 * v ^ 2 := by linarith only [hv]
      _ = a * (a * (d ^ 2 - v ^ 2)) := by rw [← hd]; ring
  have heq : a * s ^ 2 - 2 * b * s + c =
      a * ((s - (d - v)) * (s - (d + v))) := by
    rw [hc, ← hd]
    ring
  rw [heq]
  simp only [mul_eq_zero, ha, false_or, sub_eq_zero]

/-- Actual height compatibility identifies the characteristic drift. -/
theorem polarLinearA_mul_characteristicDrift
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiffAt ℝ 2 z x) (hr : x.1 ≠ 0)
    (hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) ≠ 0) :
    polarLinearA w z x * characteristicDrift w z x = polarLinearB w z x := by
  have hcompat := height_compatibility hz hr
  have hdiff : heightAngular z x - angularPartial (heightRadial z) x =
      -(x.1 * radialPartial (heightAngular z) x) := by linarith only [hcompat]
  unfold polarLinearA polarLinearB linearRadial linearMixed characteristicDrift
  rw [hdiff]
  field_simp [hr, hQ]

/-- The speed is exactly the square root of minus the corrected determinant, divided by `a`. -/
theorem polarLinearA_sq_mul_characteristicSpeed_sq
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hr : 0 < x.1) (hwp : 0 < w x.1)
    (hwn : deriv w x.1 < 0) (hD : 0 < polarDiscriminant w z x)
    (hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) ≠ 0) :
    polarLinearA w z x ^ 2 * characteristicSpeed w z x ^ 2 =
      polarLinearB w z x ^ 2 - polarLinearA w z x * polarCorrectedC w z x := by
  have hrad : 0 ≤ -w x.1 * deriv w x.1 / x.1 :=
    (div_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos hwp) hwn) hr).le
  have hdet := polar_corrected_determinant z hw hr.ne' hD hQ
  calc
    _ = -(w x.1 * deriv w x.1 / x.1) / polarDiscriminant w z x ^ 2 := by
      unfold polarLinearA linearRadial polarScale characteristicSpeed
      rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hrad, Real.sq_sqrt hD.le,
        inverseDThreeHalves_sq _ hD]
      field_simp [hQ, hD.ne', hr.ne']
      <;> ring
    _ = _ := by
      rw [neg_div, ← hdet]
      ring

/-- Both characteristic directions, with the drift and speed of the manuscript. -/
theorem correctedCharacteristicEquation_iff
    {w : ℝ → ℝ} {z : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z)
    {x : PolarPoint} (hr : 0 < x.1) (hwp : 0 < w x.1) (hwn : deriv w x.1 < 0)
    (hD : 0 < polarDiscriminant w z x)
    (hQ : 0 < heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x)) (s : ℝ) :
    correctedCharacteristicEquation w z x s ↔
      s = characteristicDrift w z x - characteristicSpeed w z x ∨
      s = characteristicDrift w z x + characteristicSpeed w z x := by
  have ha : 0 < polarLinearA w z x :=
    mul_pos hQ (inverseDThreeHalves_pos _ hD)
  exact quadratic_roots_of_drift_speed ha.ne'
    (polarLinearA_mul_characteristicDrift (hz.contDiffAt.of_le (by simp)) hr.ne' hQ.ne')
    (polarLinearA_sq_mul_characteristicSpeed_sq (hw.differentiable (by simp) x.1)
      hr hwp hwn hD hQ.ne') s

/-- Once the simple radial zero has been smoothly divided, the speed has
the required positive smooth square-root factor in a uniform rectangle. -/
theorem characteristicSpeed_sqrt_of_smooth_factor
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {g : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z)
    {r θ σ : ℝ} (hr : 0 < r) (hwp : 0 < w r)
    (hg : ContDiffAt ℝ ∞ g 0) (hgpos : 0 < g 0)
    (hdivide : ∀ t : ℝ, -deriv w (r + σ * t) = t * g t)
    (hD : 0 < polarDiscriminant w z (r, θ))
    (hQ : 0 < heightQ (profileEnergy w (r, θ)) (heightRadial z (r, θ))
      (angularPartial (heightAngular z) (r, θ))) :
    ∃ (δ : ℝ) (factor : PolarPoint → ℝ), 0 < δ ∧
      ContDiffAt ℝ ∞ factor (0, θ) ∧
      (∀ t ∈ Icc (0 : ℝ) δ, ∀ φ ∈ Ioo (θ - δ) (θ + δ), 0 < factor (t, φ)) ∧
      ∀ t ∈ Ioo (0 : ℝ) δ, ∀ φ ∈ Ioo (θ - δ) (θ + δ),
        characteristicSpeed w z (r + σ * t, φ) = Real.sqrt t * factor (t, φ) := by
  let shift : PolarPoint → PolarPoint := fun y => (r + σ * y.1, y.2)
  let A : PolarPoint → ℝ := fun y => w (r + σ * y.1) * g y.1 / (r + σ * y.1)
  let Q : PolarPoint → ℝ := fun y =>
    heightQ (profileEnergy w y) (heightRadial z y) (angularPartial (heightAngular z) y)
  let factor : PolarPoint → ℝ := fun y =>
    Real.sqrt (A y) * Real.sqrt (polarDiscriminant w z (shift y)) / Q (shift y)
  have hshift : ContDiff ℝ ∞ shift :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hshift0 : shift (0, θ) = (r, θ) := by simp only [shift, mul_zero, add_zero]
  have hrad : ContDiff ℝ ∞ (fun y : PolarPoint => r + σ * y.1) :=
    contDiff_const.add (contDiff_const.mul contDiff_fst)
  have hA : ContDiffAt ℝ ∞ A (0, θ) :=
    ((hw.comp hrad).contDiffAt.mul (hg.comp (0, θ) contDiffAt_fst)).div
      hrad.contDiffAt (by simpa only [mul_zero, add_zero] using hr.ne')
  have hApos : 0 < A (0, θ) := by
    simpa only [A, mul_zero, add_zero] using div_pos (mul_pos hwp hgpos) hr
  have hE : ContDiffAt ℝ ∞ (profileEnergy w) (r, θ) :=
    contDiffAt_const.add ((hw.contDiffAt.comp (r, θ) contDiffAt_fst).pow 2)
  have hk := contDiffAt_heightRadial (x := (r, θ)) hz.contDiffAt (m := ∞) (by simp)
  have hp := contDiffAt_heightAngular (x := (r, θ)) hz.contDiffAt (m := ∞) (by simp) hr.ne'
  have hpt := contDiffAt_angularPartial hp (m := ∞) (by simp)
  have hdisc : ContDiffAt ℝ ∞ (polarDiscriminant w z) (r, θ) :=
    (hE.mul (contDiffAt_const.sub (hp.pow 2))).sub (hk.pow 2)
  have hq : ContDiffAt ℝ ∞ Q (r, θ) := hk.add (hE.mul hpt)
  have hDshift : ContDiffAt ℝ ∞ (fun y => polarDiscriminant w z (shift y)) (0, θ) := by
    have houter : ContDiffAt ℝ ∞ (polarDiscriminant w z) (shift (0, θ)) := by
      simpa only [hshift0] using hdisc
    simpa only [Function.comp_def] using houter.comp (0, θ) hshift.contDiffAt
  have hQshift : ContDiffAt ℝ ∞ (fun y => Q (shift y)) (0, θ) := by
    have houter : ContDiffAt ℝ ∞ Q (shift (0, θ)) := by
      simpa only [hshift0] using hq
    simpa only [Function.comp_def] using houter.comp (0, θ) hshift.contDiffAt
  have hfactor : ContDiffAt ℝ ∞ factor (0, θ) :=
    ((hA.sqrt hApos.ne').mul (hDshift.sqrt (by simpa only [hshift0] using hD.ne'))).div
      hQshift (by simpa only [hshift0, Q] using hQ.ne')
  have hfactorpos : 0 < factor (0, θ) := by
    have hDs : 0 < polarDiscriminant w z (shift (0, θ)) := by
      simpa only [hshift0] using hD
    have hQs : 0 < Q (shift (0, θ)) := by
      simpa only [hshift0, Q] using hQ
    exact div_pos (mul_pos (Real.sqrt_pos.mpr hApos) (Real.sqrt_pos.mpr hDs)) hQs
  have hposnhds : {y | 0 < factor y} ∈ 𝓝 (0, θ) :=
    hfactor.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hfactorpos)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hposnhds
  refine ⟨ε / 2, factor, by positivity, hfactor, ?_, ?_⟩
  · intro t ht φ hφ
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero,
      abs_of_nonneg ht.1, max_lt_iff]
    constructor
    · linarith [ht.2]
    · rw [abs_lt]
      constructor <;> linarith [hφ.1, hφ.2]
  · intro t ht φ _
    have hradicand : -w (r + σ * t) * deriv w (r + σ * t) / (r + σ * t) =
        t * A (t, φ) := by
      calc
        _ = w (r + σ * t) * (-deriv w (r + σ * t)) / (r + σ * t) := by ring
        _ = _ := by rw [hdivide]; dsimp only [A]; ring
    simp only [characteristicSpeed, hradicand, Real.sqrt_mul ht.1.le,
      factor, shift, Q]
    ring

/-- One-dimensional smooth division, with the value at the origin identified. -/
theorem exists_smooth_division_at_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hfzero : f 0 = 0) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ g 0 = deriv f 0 ∧
      ∀ t : ℝ, f t = t * g t := by
  let G : ℝ × ℝ → ℝ := fun p => deriv f (p.2 * p.1)
  let g : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, G (t, s)
  have hdf : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hG : ContDiff ℝ ∞ G := hdf.comp (contDiff_snd.mul contDiff_fst)
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact contDiffAt_intervalIntegral_parameter (f := G) (O := univ)
      isOpen_univ (by norm_num : (0 : ℝ) ≤ 1)
      (fun _ _ _ _ => hG.contDiffAt) (mem_univ t)
  refine ⟨g, hg, ?_, ?_⟩
  · simp only [g, G, mul_zero, intervalIntegral.integral_const, sub_zero,
      one_smul]
  · intro t
    have hpath (s : ℝ) :
        HasDerivAt (fun u => f (u * t)) (deriv f (s * t) * t) s := by
      simpa only [Function.comp_def, id_eq, one_mul] using
        (hf.differentiable (by simp) (s * t)).hasDerivAt.comp s
          ((hasDerivAt_id s).mul_const t)
    have hslice : Continuous (fun s : ℝ => deriv f (s * t) * t) := by
      simpa only [Function.comp_def, id_eq] using
        (hdf.continuous.comp (continuous_id.mul_const t)).mul_const t
    have hint : IntervalIntegrable (fun s => deriv f (s * t) * t) volume 0 1 :=
      hslice.intervalIntegrable 0 1
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hpath s) hint
    rw [intervalIntegral.integral_mul_const] at hftc
    simp only [one_mul, zero_mul, hfzero, sub_zero] at hftc
    change f t = t * ∫ s in (0 : ℝ)..1, deriv f (s * t)
    linarith only [hftc]

/-- The simple-turning-point clause, with one signed coordinate for both sides. -/
theorem characteristicSpeed_simple_turning_germ
    {w : ℝ → ℝ} {z : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z)
    (r θ σ : ℝ) (hr : 0 < r) (hwp : 0 < w r) (hwzero : deriv w r = 0)
    (_hσ : σ ^ 2 = 1) (hsign : σ * deriv (deriv w) r < 0)
    (hD : 0 < polarDiscriminant w z (r, θ))
    (hQ : 0 < heightQ (profileEnergy w (r, θ)) (heightRadial z (r, θ))
      (angularPartial (heightAngular z) (r, θ))) :
    ∃ (δ : ℝ) (factor : PolarPoint → ℝ), 0 < δ ∧
      ContDiffAt ℝ ∞ factor (0, θ) ∧
      (∀ t ∈ Icc (0 : ℝ) δ, ∀ φ ∈ Ioo (θ - δ) (θ + δ), 0 < factor (t, φ)) ∧
      ∀ t ∈ Ioo (0 : ℝ) δ, ∀ φ ∈ Ioo (θ - δ) (θ + δ),
        characteristicSpeed w z (r + σ * t, φ) = Real.sqrt t * factor (t, φ) := by
  let f : ℝ → ℝ := fun t => -deriv w (r + σ * t)
  have hwd : ContDiff ℝ ∞ (deriv w) := (contDiff_infty_iff_deriv.mp hw).2
  have hf : ContDiff ℝ ∞ f :=
    (hwd.comp (contDiff_const.add (contDiff_const.mul contDiff_id))).neg
  have hfzero : f 0 = 0 := by simp only [f, mul_zero, add_zero, hwzero, neg_zero]
  obtain ⟨g, hg, hgzero, hdivide⟩ := exists_smooth_division_at_zero hf hfzero
  have hfderiv : HasDerivAt f (-(deriv (deriv w) r * σ)) 0 := by
    have houter : HasDerivAt (deriv w) (deriv (deriv w) r) (r + σ * 0) := by
      simpa only [mul_zero, add_zero] using (hwd.differentiable (by simp) r).hasDerivAt
    have hd := (houter.comp 0
      (((hasDerivAt_id 0).const_mul σ).const_add r)).neg
    simpa only [Function.comp_def, id_eq, Pi.neg_apply, f, mul_zero, add_zero, mul_one] using hd
  have hgpos : 0 < g 0 := by
    rw [hgzero, hfderiv.deriv]
    nlinarith only [hsign]
  exact characteristicSpeed_sqrt_of_smooth_factor hw hz hr hwp hg.contDiffAt hgpos
    hdivide hD hQ

theorem s05CalculusStatement : S05CalculusStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w h u η hw hh hu hη hhw q x hr hwp
    dsimp only
    intro hD hQ
    have hDpos : 0 < polarDiscriminant w
        (heightFamily (Radial.radialHeightField h) u q) x := by linarith only [hD]
    have hQpos : 0 < heightQ (profileEnergy w x)
        (heightRadial (heightFamily (Radial.radialHeightField h) u q) x)
        (angularPartial (heightAngular (heightFamily (Radial.radialHeightField h) u q)) x) :=
      (mul_pos (by norm_num : (0 : ℝ) < 7 / 8) hwp).trans_le hQ
    exact ⟨hasDerivAt_normalizedResidual_corrected hw hh hu hη hhw q hr.ne' hDpos hQpos.ne',
      polar_corrected_determinant _ (hw.differentiable (by simp) x.1)
        hr.ne' hDpos hQpos.ne'⟩
  · intro w z η
    rfl
  · exact heightCorrectedDivergence_const
  · exact scalarCorrectionError_bilinear
  · exact integral_mean_scalarCorrectionError_eq_zero
  · exact scalar_corrected_green_pairing
  · intro w z hw hz x hr hwp hwn hD hQ s
    exact correctedCharacteristicEquation_iff hw hz hr hwp hwn hD hQ s
  · intro w z hw hz r θ σ hr hwp hwzero hσ hsign hD hQ
    exact characteristicSpeed_simple_turning_germ hw hz r θ σ hr hwp hwzero hσ hsign hD hQ

end ContinuousFlexibility.Statements
