module

public import ContinuousFlexibility.Statements.Analysis

/-!
# The scalar material coordinate and weights on a physical interval

An affine change of radius transports the actual unit-interval model.
The density scale changes with the interval length; the three weights
and the material coordinate are pulled back without rescaling.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The actual affine normalization of the physical interval. -/
def affineMaterialUnitCoordinate (D : ReferenceData) (r : ℝ) : ℝ :=
  (r - D.a) / (D.b - D.a)

/-- Material data obtained from the actual unit-interval construction.
The sample function is supplied independently of the scalar construction. -/
def affineMaterialData (D : ReferenceData) (sample : ℕ → ℝ) : MaterialData where
  ell := fun r => (D.b - D.a) * materialIntervalEll (affineMaterialUnitCoordinate D r)
  H := materialIntervalH ∘ affineMaterialUnitCoordinate D
  E0 := materialIntervalE0 ∘ affineMaterialUnitCoordinate D
  M := materialIntervalM ∘ affineMaterialUnitCoordinate D
  rho := materialIntervalRho ∘ affineMaterialUnitCoordinate D
  radius := fun x => D.a + (D.b - D.a) * materialIntervalInverse x
  sample := sample

variable {D : ReferenceData} {sample : ℕ → ℝ}

theorem affineMaterialUnitCoordinate_mem (hab : D.a < D.b) {r : ℝ}
    (hr : r ∈ Ioo D.a D.b) :
    affineMaterialUnitCoordinate D r ∈ Ioo (0 : ℝ) 1 :=
  ⟨div_pos (sub_pos.mpr hr.1) (sub_pos.mpr hab),
    (div_lt_one (sub_pos.mpr hab)).mpr (sub_lt_sub_right hr.2 D.a)⟩

private theorem contDiff_affineMaterialUnitCoordinate :
    ContDiff ℝ ∞ (affineMaterialUnitCoordinate D) :=
  (contDiff_id.sub contDiff_const).div_const _

private theorem affineMaterialUnitCoordinate_strictMono (hab : D.a < D.b) :
    StrictMono (affineMaterialUnitCoordinate D) :=
  fun _ _ h => div_lt_div_of_pos_right (sub_lt_sub_right h D.a) (sub_pos.mpr hab)

private theorem affineMaterialUnitCoordinate_leftDistance (hab : D.a < D.b) (r : ℝ) :
    (D.b - D.a) * affineMaterialUnitCoordinate D r = r - D.a := by
  rw [affineMaterialUnitCoordinate, mul_div_assoc', mul_div_cancel_left₀ _ (sub_pos.mpr hab).ne']

private theorem affineMaterialUnitCoordinate_rightDistance (hab : D.a < D.b) (r : ℝ) :
    (D.b - D.a) * (1 - affineMaterialUnitCoordinate D r) = D.b - r := by
  rw [mul_sub, mul_one, affineMaterialUnitCoordinate_leftDistance hab]
  ring

private theorem affineMaterialUnitCoordinate_reflected (hab : D.a < D.b) (r : ℝ) :
    1 - affineMaterialUnitCoordinate D r = (D.b - r) / (D.b - D.a) := by
  apply (eq_div_iff (sub_pos.mpr hab).ne').mpr
  rw [mul_comm, affineMaterialUnitCoordinate_rightDistance hab]

private theorem tendsto_affineMaterialUnitCoordinate_left (hab : D.a < D.b) :
    Tendsto (affineMaterialUnitCoordinate D) (𝓝[>] D.a) (𝓝[>] (0 : ℝ)) := by
  have hmap : MapsTo (affineMaterialUnitCoordinate D) (Ioi D.a) (Ioi 0) :=
    fun _ hr => div_pos (sub_pos.mpr hr) (sub_pos.mpr hab)
  have hcont : ContinuousWithinAt (affineMaterialUnitCoordinate D) (Ioi D.a) D.a :=
    contDiff_affineMaterialUnitCoordinate.continuous.continuousWithinAt
  have h0 : affineMaterialUnitCoordinate D D.a = 0 := by simp [affineMaterialUnitCoordinate]
  simpa only [h0] using hcont.tendsto_nhdsWithin hmap

private theorem tendsto_affineMaterialUnitCoordinate_right (hab : D.a < D.b) :
    Tendsto (affineMaterialUnitCoordinate D) (𝓝[<] D.b) (𝓝[<] (1 : ℝ)) := by
  have hmap : MapsTo (affineMaterialUnitCoordinate D) (Iio D.b) (Iio 1) :=
    fun _ hr => (div_lt_one (sub_pos.mpr hab)).mpr (sub_lt_sub_right hr D.a)
  have hcont : ContinuousWithinAt (affineMaterialUnitCoordinate D) (Iio D.b) D.b :=
    contDiff_affineMaterialUnitCoordinate.continuous.continuousWithinAt
  have h1 : affineMaterialUnitCoordinate D D.b = 1 :=
    div_self (sub_pos.mpr hab).ne'
  simpa only [h1] using hcont.tendsto_nhdsWithin hmap

theorem affineMaterialData_smooth_scalar (hab : D.a < D.b) :
    ∀ f ∈ ({(affineMaterialData D sample).ell, (affineMaterialData D sample).H,
      (affineMaterialData D sample).E0, (affineMaterialData D sample).M,
      (affineMaterialData D sample).rho} : Set (ℝ → ℝ)),
      ContDiffOn ℝ ∞ f (Ioo D.a D.b) := by
  have hs : ContDiffOn ℝ ∞ (affineMaterialUnitCoordinate D) (Ioo D.a D.b) :=
    contDiff_affineMaterialUnitCoordinate.contDiffOn
  have hm : MapsTo (affineMaterialUnitCoordinate D) (Ioo D.a D.b) (Ioo (0 : ℝ) 1) :=
    fun _ hr => affineMaterialUnitCoordinate_mem hab hr
  intro f hf
  simp only [mem_insert_iff, mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact contDiffOn_const.mul (contDiffOn_materialIntervalEll.comp hs hm)
  · exact contDiffOn_materialIntervalH.comp hs hm
  · exact contDiffOn_materialIntervalE0.comp hs hm
  · exact contDiffOn_materialIntervalM.comp hs hm
  · exact contDiffOn_materialIntervalRho.comp hs hm

private theorem one_le_materialIntervalM (t : ℝ) : 1 ≤ materialIntervalM t := by
  have hlog (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Real.log (materialM x) := by
    rw [materialM, Real.log_exp, materialMExponent]
    exact add_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg hx _) (sq_nonneg _))
  change 1 ≤ Real.exp (materialIntervalLogM t)
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr (materialIntervalTransition_le_one t))
      (hlog (materialIntervalXL t) (Real.sqrt_nonneg _)))
    (mul_nonneg (materialIntervalTransition_nonneg t)
      (hlog (materialIntervalXR t) (Real.sqrt_nonneg _)))

theorem affineMaterialData_positive (hab : D.a < D.b) {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    0 < (affineMaterialData D sample).ell r ∧ 0 < (affineMaterialData D sample).H r ∧
      0 < (affineMaterialData D sample).E0 r ∧ 1 ≤ (affineMaterialData D sample).M r :=
  ⟨mul_pos (sub_pos.mpr hab) (materialIntervalEll_pos (affineMaterialUnitCoordinate_mem hab hr)),
    materialIntervalH_pos _, materialIntervalE0_pos _, one_le_materialIntervalM _⟩

theorem hasDerivAt_affineMaterialData_rho (hab : D.a < D.b) {r : ℝ}
    (hr : r ∈ Ioo D.a D.b) :
    HasDerivAt (affineMaterialData D sample).rho (1 / (affineMaterialData D sample).ell r) r := by
  have hunit : HasDerivAt (affineMaterialUnitCoordinate D) (1 / (D.b - D.a)) r :=
    ((hasDerivAt_id' r).sub_const D.a).div_const _
  have h := (hasDerivAt_materialIntervalRho (affineMaterialUnitCoordinate_mem hab hr)).comp r hunit
  simpa only [affineMaterialData, one_div_mul_one_div_rev] using h

theorem strictMonoOn_affineMaterialData_rho (hab : D.a < D.b) :
    StrictMonoOn (affineMaterialData D sample).rho (Ioo D.a D.b) :=
  fun _ hr _ hs h => strictMonoOn_materialIntervalRho (affineMaterialUnitCoordinate_mem hab hr)
    (affineMaterialUnitCoordinate_mem hab hs) (affineMaterialUnitCoordinate_strictMono hab h)

theorem tendsto_affineMaterialData_rho_left (hab : D.a < D.b) :
    Tendsto (affineMaterialData D sample).rho (𝓝[>] D.a) atBot :=
  tendsto_materialIntervalRho_left.comp (tendsto_affineMaterialUnitCoordinate_left hab)

theorem tendsto_affineMaterialData_rho_right (hab : D.a < D.b) :
    Tendsto (affineMaterialData D sample).rho (𝓝[<] D.b) atTop :=
  tendsto_materialIntervalRho_right.comp (tendsto_affineMaterialUnitCoordinate_right hab)

theorem contDiff_affineMaterialData_radius :
    ContDiff ℝ ∞ (affineMaterialData D sample).radius :=
  contDiff_const.add (contDiff_const.mul contDiff_materialIntervalInverse)

theorem affineMaterialUnitCoordinate_radius (hab : D.a < D.b) (x : ℝ) :
    affineMaterialUnitCoordinate D ((affineMaterialData D sample).radius x) =
      materialIntervalInverse x := by
  change (D.a + (D.b - D.a) * materialIntervalInverse x - D.a) / (D.b - D.a) = _
  rw [add_sub_cancel_left, mul_div_cancel_left₀ _ (sub_pos.mpr hab).ne']

theorem affineMaterialData_radius_mem_rho (hab : D.a < D.b) (x : ℝ) :
    (affineMaterialData D sample).radius x ∈ Ioo D.a D.b ∧
      (affineMaterialData D sample).rho ((affineMaterialData D sample).radius x) = x := by
  have hi := materialIntervalInverse_mem x
  have hw := sub_pos.mpr hab
  constructor
  · change D.a < D.a + (D.b - D.a) * materialIntervalInverse x ∧
      D.a + (D.b - D.a) * materialIntervalInverse x < D.b
    exact ⟨by linarith only [mul_pos hw hi.1],
      by linarith only [mul_lt_mul_of_pos_left hi.2 hw]⟩
  · change materialIntervalRho
      (affineMaterialUnitCoordinate D ((affineMaterialData D sample).radius x)) = x
    rw [affineMaterialUnitCoordinate_radius hab, materialIntervalRho_inverse]

theorem affineMaterialData_radius_rho (hab : D.a < D.b) {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    (affineMaterialData D sample).radius ((affineMaterialData D sample).rho r) = r := by
  change D.a + (D.b - D.a) * materialIntervalInverse
    (materialIntervalRho (affineMaterialUnitCoordinate D r)) = r
  rw [materialIntervalInverse_rho (affineMaterialUnitCoordinate_mem hab hr),
    affineMaterialUnitCoordinate_leftDistance hab]
  ring

theorem hasDerivAt_affineMaterialData_radius (hab : D.a < D.b) (x : ℝ) :
    HasDerivAt (affineMaterialData D sample).radius
      ((affineMaterialData D sample).ell ((affineMaterialData D sample).radius x)) x := by
  change HasDerivAt (affineMaterialData D sample).radius ((D.b - D.a) * materialIntervalEll
    (affineMaterialUnitCoordinate D ((affineMaterialData D sample).radius x))) x
  rw [affineMaterialUnitCoordinate_radius hab]
  exact ((hasDerivAt_materialIntervalInverse x).const_mul (D.b - D.a)).const_add D.a

/-- The endpoint formulas hold with reference distance b - a and
collar size (b - a) / 4. -/
theorem affineMaterialData_endpoint_formulas (hab : D.a < D.b) :
    ∃ d0 δ : ℝ, 0 < d0 ∧ 0 < δ ∧ δ < min d0 ((D.b - D.a) / 2) ∧
      (∀ r ∈ Ioo D.a (D.a + δ),
        let x := endpointX d0 (r - D.a)
        (affineMaterialData D sample).ell r = (r - D.a) / (1 + x) ∧
        (affineMaterialData D sample).H r = materialH x ∧
        (affineMaterialData D sample).E0 r = materialE0 x ∧
        (affineMaterialData D sample).M r = materialM x) ∧
      (∀ r ∈ Ioo (D.b - δ) D.b,
        let x := endpointX d0 (D.b - r)
        (affineMaterialData D sample).ell r = (D.b - r) / (1 + x) ∧
        (affineMaterialData D sample).H r = materialH x ∧
        (affineMaterialData D sample).E0 r = materialE0 x ∧
        (affineMaterialData D sample).M r = materialM x) := by
  have hw := sub_pos.mpr hab
  refine ⟨D.b - D.a, (D.b - D.a) / 4, hw, by positivity,
    lt_min (by linarith) (by linarith), ?_, ?_⟩
  · intro r hr
    have ht : affineMaterialUnitCoordinate D r ≤ 1 / 3 := by
      apply le_of_lt
      change (r - D.a) / (D.b - D.a) < 1 / 3
      exact (div_lt_iff₀ hw).mpr (by linarith [hr.2])
    have hX : materialIntervalXL (affineMaterialUnitCoordinate D r) =
        endpointX (D.b - D.a) (r - D.a) := by
      change Real.sqrt (Real.log (1 / ((r - D.a) / (D.b - D.a)))) =
        Real.sqrt (Real.log ((D.b - D.a) / (r - D.a)))
      rw [one_div_div]
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (D.b - D.a) * materialIntervalEll (affineMaterialUnitCoordinate D r) =
        (r - D.a) / (1 + endpointX (D.b - D.a) (r - D.a))
      rw [materialIntervalEll_eq_left ht, endpointEll, mul_div_assoc',
        affineMaterialUnitCoordinate_leftDistance hab]
      exact congrArg (fun x : ℝ => (r - D.a) / (1 + x)) hX
    · change materialIntervalH (affineMaterialUnitCoordinate D r) = _
      rw [materialIntervalH_eq_left ht, hX]
    · change materialIntervalE0 (affineMaterialUnitCoordinate D r) = _
      rw [materialIntervalE0_eq_left ht, hX]
    · change materialIntervalM (affineMaterialUnitCoordinate D r) = _
      rw [materialIntervalM_eq_left ht, hX]
  · intro r hr
    have ht : 2 / 3 ≤ affineMaterialUnitCoordinate D r := by
      apply le_of_lt
      change 2 / 3 < (r - D.a) / (D.b - D.a)
      exact (lt_div_iff₀ hw).mpr (by linarith [hr.1])
    have hX : materialIntervalXR (affineMaterialUnitCoordinate D r) =
        endpointX (D.b - D.a) (D.b - r) := by
      change Real.sqrt (Real.log (1 / (1 - affineMaterialUnitCoordinate D r))) =
        Real.sqrt (Real.log ((D.b - D.a) / (D.b - r)))
      rw [affineMaterialUnitCoordinate_reflected hab, one_div_div]
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (D.b - D.a) * materialIntervalEll (affineMaterialUnitCoordinate D r) =
        (D.b - r) / (1 + endpointX (D.b - D.a) (D.b - r))
      rw [materialIntervalEll_eq_right ht, endpointEll, mul_div_assoc',
        affineMaterialUnitCoordinate_rightDistance hab]
      exact congrArg (fun x : ℝ => (D.b - r) / (1 + x)) hX
    · change materialIntervalH (affineMaterialUnitCoordinate D r) = _
      rw [materialIntervalH_eq_right ht, hX]
    · change materialIntervalE0 (affineMaterialUnitCoordinate D r) = _
      rw [materialIntervalE0_eq_right ht, hX]
    · change materialIntervalM (affineMaterialUnitCoordinate D r) = _
      rw [materialIntervalM_eq_right ht, hX]

theorem affineMaterialData_E0_rpow_le_M (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Ioo D.a D.b,
      (affineMaterialData D sample).E0 r ^ A ≤ C * (affineMaterialData D sample).M r := by
  obtain ⟨C, hC, hb⟩ := materialIntervalE0_rpow_le_M A
  exact ⟨C, hC, fun r _ => hb (affineMaterialUnitCoordinate D r)⟩

theorem affineMaterialData_H_rpow_mul_M_rpow (hab : D.a < D.b) (A ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      (∀ r ∈ Ioo D.a D.b,
        (affineMaterialData D sample).H r ^ ε * (affineMaterialData D sample).M r ^ A ≤ C) ∧
      Tendsto (fun r => (affineMaterialData D sample).H r ^ ε *
        (affineMaterialData D sample).M r ^ A) (𝓝[>] D.a) (𝓝 0) ∧
      Tendsto (fun r => (affineMaterialData D sample).H r ^ ε *
        (affineMaterialData D sample).M r ^ A) (𝓝[<] D.b) (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := materialIntervalH_rpow_mul_M_rpow_le A hε
  exact ⟨C, hC, fun r _ => hb (affineMaterialUnitCoordinate D r),
    (tendsto_materialIntervalH_rpow_mul_M_left A hε).comp
      (tendsto_affineMaterialUnitCoordinate_left hab),
    (tendsto_materialIntervalH_rpow_mul_M_right A hε).comp
      (tendsto_affineMaterialUnitCoordinate_right hab)⟩

end ContinuousFlexibility.Statements
