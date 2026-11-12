import ContinuousFlexibility.Radial.TerminalPhysicalCutoff
import ContinuousFlexibility.Radial.TerminalCapLayerL2
import ContinuousFlexibility.Radial.TerminalCapEnergyError

/-!
# Actual source estimates on a retained first cone

The physical transition occupies [a,2a]. Its logarithmic width is fixed,
so the weighted layer mass is bounded independently of how far inward
the layer is placed. The profile height and frequency cancel against the
same boundary normalization used by the actual cutoff lift.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory Filter
open scoped Topology ContDiff ENNReal

theorem terminalCone_source_formula {scale lam r ν : ℝ} {w χ u : ℝ → ℝ}
    (hs : scale ≠ 0) (hlam : 0 < lam) (hr : r ≠ 0)
    (hw : w r = scale * r) (hwd : deriv w r = scale)
    (hud : deriv u r = ν / r * u r) :
    terminalCapHilbertSource lam w χ u r =
      -(r ^ 2 * deriv (deriv χ) r + (1 + 2 * ν) * (r * deriv χ r)) * u r /
        (12 * sqrt lam) := by
  dsimp only [terminalCapHilbertSource, terminalCapResidual]
  rw [hw, hwd, hud]
  field_simp [hs, hr, (sqrt_pos.mpr hlam).ne']
  <;> ring

/-- A fixed ratio of physical radii bounds the dimensionless cutoff jets. -/
theorem terminalCone_cutoff_jets (right : Bool) {a r : ℝ} (ha : 0 < a)
    (hr : r ∈ Icc a (2 * a)) :
    |r * deriv (terminalPhysicalCutoff right a (2 * a)) r| ≤
        2 * terminalPhysicalCutoffJetConstant 1 ∧
      |r ^ 2 * deriv (deriv (terminalPhysicalCutoff right a (2 * a))) r| ≤
        4 * terminalPhysicalCutoffJetConstant 2 := by
  have hab : a < 2 * a := by linarith
  have hrpos : 0 < r := ha.trans_le hr.1
  have hwidth : 2 * a - a = a := by ring
  have h₁ := terminalPhysicalCutoff_deriv_bound right hab r
  have h₂ := terminalPhysicalCutoff_second_bound right hab r
  rw [hwidth] at h₁ h₂
  constructor
  · rw [abs_mul, abs_of_pos hrpos]
    calc
      _ ≤ (2 * a) * (terminalPhysicalCutoffJetConstant 1 / a) :=
        mul_le_mul hr.2 h₁ (abs_nonneg _) (by positivity)
      _ = _ := by field_simp [ha.ne'] <;> ring
  · rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
    calc
      _ ≤ (2 * a) ^ 2 * (terminalPhysicalCutoffJetConstant 2 / a ^ 2) :=
        mul_le_mul ((sq_le_sq₀ hrpos.le (by positivity)).mpr hr.2) h₂
          (abs_nonneg _) (sq_nonneg _)
      _ = _ := by field_simp [ha.ne'] <;> ring

theorem terminalCone_source_bound (right : Bool) {a r scale lam j ν σ : ℝ}
    {w u : ℝ → ℝ} (ha : 0 < a) (hs : 0 < scale) (hlam : 0 < lam)
    (hr : r ∈ Icc a (2 * a)) (hν : |ν| ≤ j)
    (hw : w r = scale * r) (hwd : deriv w r = scale)
    (hud : deriv u r = ν / r * u r) (hu : |u r| ≤ exp (-σ)) :
    |terminalCapHilbertSource lam w (terminalPhysicalCutoff right a (2 * a)) u r| ≤
      ((4 * terminalPhysicalCutoffJetConstant 2 +
        2 * (1 + 2 * j) * terminalPhysicalCutoffJetConstant 1) / (12 * sqrt lam)) *
        exp (-σ) := by
  let χ := terminalPhysicalCutoff right a (2 * a)
  have hrpos : 0 < r := ha.trans_le hr.1
  have hK₁ := terminalPhysicalCutoffJetConstant_nonneg 1
  have hK₂ := terminalPhysicalCutoffJetConstant_nonneg 2
  have hj : 0 ≤ j := (abs_nonneg ν).trans hν
  obtain ⟨h₁, h₂⟩ := terminalCone_cutoff_jets right ha hr
  have hν' : |1 + 2 * ν| ≤ 1 + 2 * j := by
    calc
      _ ≤ |(1 : ℝ)| + |2 * ν| := abs_add_le _ _
      _ = 1 + 2 * |ν| := by norm_num [abs_mul]
      _ ≤ _ := by linarith only [hν]
  have hb : |r ^ 2 * deriv (deriv χ) r + (1 + 2 * ν) * (r * deriv χ r)| ≤
      4 * terminalPhysicalCutoffJetConstant 2 +
        2 * (1 + 2 * j) * terminalPhysicalCutoffJetConstant 1 := by
    calc
      _ ≤ |r ^ 2 * deriv (deriv χ) r| + |(1 + 2 * ν) * (r * deriv χ r)| :=
        abs_add_le _ _
      _ ≤ 4 * terminalPhysicalCutoffJetConstant 2 +
          (1 + 2 * j) * (2 * terminalPhysicalCutoffJetConstant 1) := by
        apply add_le_add h₂
        rw [abs_mul]
        exact mul_le_mul hν' h₁ (abs_nonneg _) (by positivity)
      _ = _ := by ring
  rw [terminalCone_source_formula hs.ne' hlam hrpos.ne' hw hwd hud,
    abs_div, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 12 * sqrt lam)]
  calc
    _ ≤ ((4 * terminalPhysicalCutoffJetConstant 2 +
          2 * (1 + 2 * j) * terminalPhysicalCutoffJetConstant 1) * exp (-σ)) /
          (12 * sqrt lam) :=
      div_le_div_of_nonneg_right (mul_le_mul hb hu (abs_nonneg _) (by positivity))
        (by positivity)
    _ = _ := by ring

def terminalConeSourceConstant : ℝ :=
  4 * terminalPhysicalCutoffJetConstant 2 + 6 * terminalPhysicalCutoffJetConstant 1

theorem terminalConeSourceConstant_nonneg : 0 ≤ terminalConeSourceConstant := by
  have h₁ := terminalPhysicalCutoffJetConstant_nonneg 1
  have h₂ := terminalPhysicalCutoffJetConstant_nonneg 2
  unfold terminalConeSourceConstant
  positivity

/-- The actual normalization cancels both the cone height and the frequency. -/
theorem terminalCone_source_normalization {scale j : ℝ}
    (hs : 0 < scale) (hj : 1 ≤ j) :
    ((4 * terminalPhysicalCutoffJetConstant 2 +
        2 * (1 + 2 * j) * terminalPhysicalCutoffJetConstant 1) /
      (12 * sqrt (j ^ 2 * scale))) * sqrt (12 * scale) ≤ terminalConeSourceConstant := by
  have hjpos : 0 < j := lt_of_lt_of_le (by norm_num) hj
  have h₁ := terminalPhysicalCutoffJetConstant_nonneg 1
  have h₂ := terminalPhysicalCutoffJetConstant_nonneg 2
  have hnum : 4 * terminalPhysicalCutoffJetConstant 2 +
      2 * (1 + 2 * j) * terminalPhysicalCutoffJetConstant 1 ≤
        terminalConeSourceConstant * j := by
    dsimp only [terminalConeSourceConstant]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hj) h₁,
      mul_nonneg (sub_nonneg.mpr hj) h₂]
  have hroot : sqrt (12 * scale) ≤ 12 * sqrt scale := by
    rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
    apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
    nlinarith only [sq_sqrt (by norm_num : (0 : ℝ) ≤ 12), sqrt_nonneg (12 : ℝ)]
  rw [sqrt_mul (sq_nonneg j), sqrt_sq hjpos.le]
  calc
    _ ≤ ((terminalConeSourceConstant * j) / (12 * (j * sqrt scale))) *
        (12 * sqrt scale) := by
      exact mul_le_mul (div_le_div_of_nonneg_right hnum (by positivity)) hroot
        (sqrt_nonneg _) (by have := terminalConeSourceConstant_nonneg; positivity)
    _ = _ := by field_simp [hjpos.ne', (sqrt_pos.mpr hs).ne'] <;> ring

/-- Membership and norm bound use the original weighted radial measure. -/
theorem terminalCone_source_L2 (D : Statements.ReferenceData) (right : Bool)
    {a scale j ν σ : ℝ} {u : ℝ → ℝ}
    (ha : 0 < a) (hs : 0 < scale) (hj : 1 ≤ j) (hν : |ν| ≤ j)
    (hw : ContDiff ℝ ∞ D.w) (hu : ContDiff ℝ ∞ u)
    (hcone : ∀ r ∈ Icc a (2 * a), D.w =ᶠ[𝓝 r] (fun t => scale * t))
    (hud : ∀ r ∈ Icc a (2 * a), deriv u r = ν / r * u r)
    (huval : ∀ r ∈ Icc a (2 * a), |u r| ≤ exp (-σ)) :
    let f := terminalCapHilbertSource (j ^ 2 * scale) D.w
      (terminalPhysicalCutoff right a (2 * a)) u
    MemLp f 2 (Statements.radialHilbertMeasure D) ∧
      eLpNorm f 2 (Statements.radialHilbertMeasure D) ≤
        ENNReal.ofReal (terminalConeSourceConstant * exp (-σ)) := by
  let lam := j ^ 2 * scale
  let χ := terminalPhysicalCutoff right a (2 * a)
  let f := terminalCapHilbertSource lam D.w χ u
  let M := ((4 * terminalPhysicalCutoffJetConstant 2 +
    2 * (1 + 2 * j) * terminalPhysicalCutoffJetConstant 1) / (12 * sqrt lam)) * exp (-σ)
  have hjpos : 0 < j := lt_of_lt_of_le (by norm_num) hj
  have hlam : 0 < lam := mul_pos (sq_pos_of_pos hjpos) hs
  have hab : a < 2 * a := by linarith
  have hK₁ := terminalPhysicalCutoffJetConstant_nonneg 1
  have hK₂ := terminalPhysicalCutoffJetConstant_nonneg 2
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hwpos (r : ℝ) (hr : r ∈ Icc a (2 * a)) : 0 < D.w r := by
    rw [(hcone r hr).eq_of_nhds]
    exact mul_pos hs (ha.trans_le hr.1)
  have hρ (r : ℝ) (hr : r ∈ Icc a (2 * a)) :
      12 * D.w r / r ^ 2 ≤ 12 * scale / a := by
    have hrpos : 0 < r := ha.trans_le hr.1
    rw [(hcone r hr).eq_of_nhds]
    calc
      _ = 12 * scale / r := by field_simp [hrpos.ne'] <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) ha hr.1
  have hbound (r : ℝ) (hr : r ∈ Icc a (2 * a)) : |f r| ≤ M := by
    apply terminalCone_source_bound right ha hs hlam hr hν (hcone r hr).eq_of_nhds _
      (hud r hr) (huval r hr)
    rw [(hcone r hr).deriv_eq]
    simpa only [mul_one, id_eq] using ((hasDerivAt_id r).const_mul scale).deriv
  obtain ⟨hmem, hnorm⟩ := terminalCapLayer_memLp_eLpNorm D hab.le (by positivity) hM f
    (terminalCapHilbertSource_continuousOn lam hw (terminalPhysicalCutoff_smooth right a (2 * a))
      hu (fun r hr => (hwpos r hr).ne'))
    ((terminalCapHilbertSource_support lam D.w χ u).trans
      (terminalPhysicalCutoff_tsupport_deriv right hab)) hρ hbound
  refine ⟨hmem, hnorm.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hmass : (12 * scale / a) * (2 * a - a) = 12 * scale := by
    field_simp [ha.ne'] <;> ring
  rw [hmass]
  change M * sqrt (12 * scale) ≤ terminalConeSourceConstant * exp (-σ)
  dsimp only [M, lam]
  calc
    _ = (((4 * terminalPhysicalCutoffJetConstant 2 +
        2 * (1 + 2 * j) * terminalPhysicalCutoffJetConstant 1) /
        (12 * sqrt (j ^ 2 * scale))) * sqrt (12 * scale)) * exp (-σ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (terminalCone_source_normalization hs hj)
      (exp_pos _).le

end ContinuousFlexibility.Radial
