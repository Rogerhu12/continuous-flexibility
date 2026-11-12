import ContinuousFlexibility.Analysis.N04bSqrtAffine
import ContinuousFlexibility.Analysis.N01SingletonControl
import ContinuousFlexibility.Analysis.SmoothDirectionsScalarLine

/-!
# Strict optical type on singleton control lines

The first radial jet in the actual N01 flow tower is the negative
square root of the actual radial optical radicand. On a singleton
control line that radicand is affine. The scalar square-root obstruction
therefore excludes zeros throughout the allowed parameter interval.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

/-- Differentiability of the square root on an entire weighted parameter
interval forces a positive affine radicand to retain its sign there. -/
theorem n04b_affine_pos_of_sqrt_differentiableAt_weighted_ball
    {a b p ε t : ℝ} (ha : 0 < a) (hp : 0 ≤ p)
    (hdiff : ∀ s : ℝ, |s| * p < ε →
      DifferentiableAt ℝ (fun u : ℝ => Real.sqrt (a + b * u)) s)
    (ht : |t| * p < ε) : 0 < a + b * t := by
  by_contra hpos
  have hnonpos : a + b * t ≤ 0 := le_of_not_gt hpos
  have hb : b ≠ 0 := by
    intro hb
    rw [hb, zero_mul, add_zero] at hnonpos
    exact (not_le_of_gt ha) hnonpos
  have hbound : a ≤ |b| * |t| := by
    have hneg := neg_le_abs (b * t)
    rw [abs_mul] at hneg
    linarith only [hnonpos, hneg]
  have hrootbound : |-a / b| ≤ |t| := by
    rw [abs_div, abs_neg, abs_of_pos ha]
    exact (div_le_iff₀ (abs_pos.mpr hb)).mpr (by nlinarith only [hbound])
  have hrootmem : |-a / b| * p < ε :=
    (mul_le_mul_of_nonneg_right hrootbound hp).trans_lt ht
  have hzero : a + b * (-a / b) = 0 := by
    field_simp [hb]
    <;> ring
  exact n04b_sqrt_affine_not_differentiableAt_zero hzero hb
    (hdiff (-a / b) hrootmem)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

local instance n04bSingletonTypeStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n04bSingletonTypeRealNormedSpace : NormedSpace ℝ ℝ :=
  NormedField.toNormedSpace

theorem SmoothDirections.n04b_differentiableAt_line
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f : E → ℝ} (J : SmoothDirections U f)
    (x w : E) {t : ℝ} (ht : x + t • w ∈ U) :
    DifferentiableAt ℝ (fun s : ℝ => f (x + s • w)) t := by
  have hc : Continuous (fun s : ℝ => x + s • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : ∀ᶠ s in 𝓝 t, x + s • w ∈ U :=
    hc.continuousAt.eventually (J.open_domain.mem_nhds ht)
  have heq : (fun s : ℝ => f (x + s • w)) =ᶠ[𝓝 t]
      (fun s : ℝ => J.D 0 (x + s • w) Fin.elim0) := by
    filter_upwards [hmem] with s hs
    exact (J.zero (x + s • w) hs).symm
  exact ((J.hasDerivAt_line_jet x w 0 Fin.elim0 ht).congr_of_eventuallyEq
    heq).differentiableAt

/-- The affine identity uses the derivative of the actual exponential
profile, including at parameter values where its optical radicand is zero. -/
theorem n04b_opticalSpeed_logPerturbation_affine
    {w χ : ℝ → ℝ} {t r : ℝ}
    (hw : DifferentiableAt ℝ w r) (hχ : DifferentiableAt ℝ χ r)
    (hr : r ≠ 0) (hwr : w r ≠ 0) :
    opticalSpeed (opticalLogPerturbation w χ t) r =
      Real.sqrt (-deriv w r / (r * w r) + (-deriv χ r / r) * t) := by
  have hp := (hw.hasDerivAt.mul ((hχ.hasDerivAt.const_mul t).exp)).deriv
  change deriv (fun s => w s * Real.exp (t * χ s)) r = _ at hp
  unfold opticalSpeed
  change Real.sqrt (-deriv (fun s => w s * Real.exp (t * χ s)) r /
    (r * (w r * Real.exp (t * χ r)))) = _
  rw [hp]
  congr 1
  field_simp [hr, hwr, (Real.exp_pos (t * χ r)).ne']
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.n04b_minusFlow_zero_hasDerivAt
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (θ : ℝ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    HasDerivAt (fun s => C.minusFlow (x, 0) m s θ)
      (-opticalSpeed (stateProfile D S C x) r) r := by
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hrD : r ∈ Ioo D.a D.b :=
    ⟨(hcontrol.1 m).1.trans hr.1, hr.2.trans (hcontrol.1 m).2.2⟩
  have hr0 : r ≠ 0 := (hgeom.1.1.trans hrD.1).ne'
  have hp : 0 < stateProfile D S C x r :=
    mul_pos (hgeom.1.2.2.2.2.1 r hrD) (Real.exp_pos _)
  have hw := contDiff_stateProfile_of_n01 hS hT hN x
  obtain ⟨ha, hb, hc⟩ := originalCoefficients_radial_zero x hw
    (r, C.minusFlow (x, 0) m r θ)
  have hflow := (hN.2.2.2.2.2.2.1 (x, 0) hx m θ).2.2.1 r hr
  rw [minusCharacteristicSpeed_of_radial_coefficients ha hb hc hr0 hp] at hflow
  exact hflow

/-- This is an identity for the actual spatial derivative in N01,
obtained from its actual ODE before differentiating the state parameter. -/
theorem N01Properties.n04b_ordinaryFlowFamily_radial_zero
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (θ : ℝ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    ordinaryFlowFamily S C m 1 0 (r, θ) (x, 0) =
      opticalSpeed (stateProfile D S C C.referenceState) r -
        opticalSpeed (stateProfile D S C x) r := by
  have href : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
    constructor
    · have hz : stateGrading S base (C.referenceState - C.referenceState) = 0 :=
        (congrArg (fun u : AnnularState S => stateGrading S base u)
          (sub_self C.referenceState)).trans (stateGrading S base).map_zero'
      exact hz.trans_lt hN.2.1
    · simpa only [abs_zero] using hN.2.1
  have hxderiv := hN.n04b_minusFlow_zero_hasDerivAt hS hT hx m θ hr
  have hrefderiv := hN.n04b_minusFlow_zero_hasDerivAt hS hT href m θ hr
  simp only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one]
  have hd := (hxderiv.sub hrefderiv).deriv
  change deriv (fun s => C.minusFlow (x, 0) m s θ -
    C.minusFlow (C.referenceState, 0) m s θ) r = _ at hd
  rw [hd]
  ring

private theorem n04b_affine_zero_parameter {E : Type*}
    [AddCommGroup E] [Module ℝ E] (x v : E) :
    x + (0 : ℝ) • v = x := by
  rw [zero_smul, add_zero]

private theorem n04b_singleton_reference_profile
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (m : ℕ) : stateProfile D S C C.referenceState = D.w := by
  have hprofile := singletonKappaLine_profile (hS.2.1 (3 / 4 : ℝ)) href m 0
  have hzero := n04b_affine_zero_parameter C.referenceState
    (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m)
  have hperturbation : opticalLogPerturbation D.w (C.control m) 0 = D.w := by
    funext r
    simp only [opticalLogPerturbation, zero_mul, Real.exp_zero, mul_one]
  exact (congrArg (stateProfile D S C) hzero).symm.trans
    (hprofile.trans hperturbation)

private theorem n04b_control_opticalSpeed_affine
    (hN : N01Properties D T S C base loss ε) (m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) (t : ℝ) :
    opticalSpeed (opticalLogPerturbation D.w (C.control m) t) r =
      Real.sqrt (-deriv D.w r / (r * D.w r) + (-deriv (C.control m) r / r) * t) := by
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hrD : r ∈ Ioo D.a D.b :=
    ⟨(hcontrol.1 m).1.trans hr.1, hr.2.trans (hcontrol.1 m).2.2⟩
  exact n04b_opticalSpeed_logPerturbation_affine
    (hgeom.1.2.2.1.1.differentiable (by simp) r)
    ((hcontrol.2.2.2.2.2.1 m).1.differentiable (by simp) r)
    (hgeom.1.1.trans hrD.1).ne' (hgeom.1.2.2.2.2.1 r hrD).ne'

theorem N01Properties.n04b_ordinaryFlowFamily_singletonKappa_radial
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (θ : ℝ) {r t : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m))
    (ht : (C.referenceState +
      t • singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0) ∈
        stateNeighborhood S C base ε) :
    ordinaryFlowFamily S C m 1 0 (r, θ)
      (C.referenceState + t • singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0) =
      opticalSpeed D.w r -
        Real.sqrt (-deriv D.w r / (r * D.w r) + (-deriv (C.control m) r / r) * t) := by
  have href := n04b_singleton_reference_profile hS hN.2.2.1 m
  have hprofile := singletonKappaLine_profile
    (hS.2.1 (3 / 4 : ℝ)) hN.2.2.1 m t
  exact (hN.n04b_ordinaryFlowFamily_radial_zero hS hT ht m θ hr).trans
    (congrArg₂ (fun a b : ℝ => a - b)
      (congrArg (fun w : ℝ → ℝ => opticalSpeed w r) href)
      ((congrArg (fun w : ℝ → ℝ => opticalSpeed w r) hprofile).trans
        (n04b_control_opticalSpeed_affine hN m hr t)))

private theorem n04b_singleton_joint_line
    (hS : IsPhysicalSpaces D T S) (m : ℕ) (t : ℝ) :
    (C.referenceState, (0 : ℝ)) +
        t • (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, (0 : ℝ)) =
      (C.referenceState + t • singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0) := by
  change (C.referenceState + t • singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m,
    (0 : ℝ) + t • (0 : ℝ)) = _
  simp only [smul_zero, add_zero]

/-- The stored N01 tower forces differentiability in the control parameter
of the square root appearing in the actual radial speed. -/
theorem N01Properties.n04b_sqrt_singletonKappa_differentiableAt
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) {r t : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m))
    (ht : |t| * stateGrading S base
      (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m) < ε) :
    DifferentiableAt ℝ
      (fun s : ℝ => Real.sqrt
        (-deriv D.w r / (r * D.w r) + (-deriv (C.control m) r / r) * s)) t := by
  -- `obtain` on the parameter-loss existential is very slow; select the witnesses.
  let orderData := hN.2.2.2.2.2.2.2.2.2.2.2.2 0
  let htower := (orderData.choose_spec 1).choose_spec.2 m 1 0 (r, 0) (by norm_num) hr
  let J := htower.choose
  let v : AnnularState S × ℝ :=
    (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0)
  have hmem : (C.referenceState, (0 : ℝ)) + t • v ∈
      stateNeighborhood S C base ε := by
    dsimp only [v]
    rw [n04b_singleton_joint_line hS]
    exact singletonKappaLine_mem (hS.2.1 (3 / 4 : ℝ)) m base hN.2.1 ht
  have hdiff := J.n04b_differentiableAt_line (C.referenceState, 0) v hmem
  have hnear : ∀ᶠ s in 𝓝 t, |s| * stateGrading S base
      (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m) < ε :=
    (isOpen_lt (continuous_abs.mul continuous_const) continuous_const).mem_nhds ht
  have heq : (fun s : ℝ => Real.sqrt
      (-deriv D.w r / (r * D.w r) + (-deriv (C.control m) r / r) * s))
      =ᶠ[𝓝 t] (fun s : ℝ => opticalSpeed D.w r -
        ordinaryFlowFamily S C m 1 0 (r, 0) ((C.referenceState, 0) + s • v)) := by
    filter_upwards [hnear] with s hs
    dsimp only [v]
    rw [n04b_singleton_joint_line hS,
      hN.n04b_ordinaryFlowFamily_singletonKappa_radial hS hT m 0 hr
        (singletonKappaLine_mem (hS.2.1 (3 / 4 : ℝ)) m base hN.2.1 hs)]
    ring
  exact ((hdiff.hasDerivAt.const_sub (opticalSpeed D.w r)).congr_of_eventuallyEq
    heq).differentiableAt

theorem N01Properties.n04b_singletonKappa_radicand_ne_zero
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) {r t : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m))
    (ht : |t| * stateGrading S base
      (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m) < ε) :
    -deriv D.w r / (r * D.w r) + (-deriv (C.control m) r / r) * t ≠ 0 := by
  intro hzero
  have hb := Analysis.n04b_sqrt_affine_slope_eq_zero_of_differentiableAt hzero
    (hN.n04b_sqrt_singletonKappa_differentiableAt hS hT m hr ht)
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hrD : r ∈ Ioo D.a D.b :=
    ⟨(hcontrol.1 m).1.trans hr.1, hr.2.trans (hcontrol.1 m).2.2⟩
  have hbase : 0 < -deriv D.w r / (r * D.w r) :=
    div_pos (neg_pos.mpr (hcontrol.2.2.2.1 m r hr))
      (mul_pos (hgeom.1.1.trans hrD.1) (hgeom.1.2.2.2.2.1 r hrD))
  rw [hb, zero_mul, add_zero] at hzero
  exact hbase.ne' hzero


theorem N01Properties.n04b_singletonKappa_radicand_pos
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) {r t : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m))
    (ht : |t| * stateGrading S base
      (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m) < ε) :
    0 < -deriv D.w r / (r * D.w r) + (-deriv (C.control m) r / r) * t := by
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hrD : r ∈ Ioo D.a D.b :=
    ⟨(hcontrol.1 m).1.trans hr.1, hr.2.trans (hcontrol.1 m).2.2⟩
  have hbase : 0 < -deriv D.w r / (r * D.w r) :=
    div_pos (neg_pos.mpr (hcontrol.2.2.2.1 m r hr))
      (mul_pos (hgeom.1.1.trans hrD.1) (hgeom.1.2.2.2.2.1 r hrD))
  exact Analysis.n04b_affine_pos_of_sqrt_differentiableAt_weighted_ball
    hbase (apply_nonneg (stateGrading S base) _)
    (fun s hs => hN.n04b_sqrt_singletonKappa_differentiableAt hS hT m hr hs) ht

end ContinuousFlexibility.Statements
