import ContinuousFlexibility.Analysis.CylinderTestPeriodization
import ContinuousFlexibility.Statements.Nonlinear

/-!
# Compact half-period tests in the full-period radial test class

A planar test compactly supported in the open half-period strip can be
extended to a smooth function of angular period 2π. On the entire physical
integration period (0, 2π], the extension equals the original planar test.
The construction reuses the existing cylinder test periodization after an
explicit change of angular scale.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

/-- The change of angular scale relating periods π and 2π. -/
def n07bDoubleAngle : PolarPoint ≃ₜ PolarPoint where
  toFun p := (p.1, 2 * p.2)
  invFun p := (p.1, p.2 / 2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · change (2 * p.2) / 2 = p.2
      ring
  right_inv p := by
    apply Prod.ext
    · rfl
    · change 2 * (p.2 / 2) = p.2
      ring
  continuous_toFun := continuous_fst.prodMk (continuous_const.mul continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.div_const 2)

theorem n07bDoubleAngle_apply (p : PolarPoint) :
    n07bDoubleAngle p = (p.1, 2 * p.2) := rfl

theorem n07bDoubleAngle_symm_apply (p : PolarPoint) :
    n07bDoubleAngle.symm p = (p.1, p.2 / 2) := rfl

/-- Actual periodization, with the full period used by RadialTest. -/
def n07bFullPeriodTest (φ : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  cylinderTestPeriodization (fun q => φ (n07bDoubleAngle q)) (n07bDoubleAngle.symm p)

theorem n07bFullPeriodTest_periodic (φ : PolarPoint → ℝ) :
    Function.Periodic (n07bFullPeriodTest φ) (0, 2 * Real.pi) := by
  intro p
  have he : n07bDoubleAngle.symm (p + (0, 2 * Real.pi)) =
      n07bDoubleAngle.symm p + (0, Real.pi) := by
    apply Prod.ext
    · change p.1 + 0 = p.1 + 0
      rfl
    · change (p.2 + 2 * Real.pi) / 2 = p.2 / 2 + Real.pi
      ring
  change cylinderTestPeriodization _ (n07bDoubleAngle.symm (p + (0, 2 * Real.pi))) = _
  rw [he, cylinderTestPeriodization_periodic]

theorem n07bFullPeriodTest_contDiff {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ContDiff ℝ ∞ (n07bFullPeriodTest φ) := by
  have he : ContDiff ℝ ∞ (n07bDoubleAngle : PolarPoint → PolarPoint) :=
    contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)
  have hei : ContDiff ℝ ∞ (n07bDoubleAngle.symm : PolarPoint → PolarPoint) :=
    contDiff_fst.prodMk (contDiff_snd.div_const 2)
  have hcompact : HasCompactSupport (fun q => φ (n07bDoubleAngle q)) := by
    simpa only [Function.comp_def] using hc.comp_homeomorph n07bDoubleAngle
  exact (isCylinderTest_cylinderTestPeriodization (hφ.comp he) hcompact).1.comp hei

/-- No translated copy meets the base period when the original test is
supported inside its first half. -/
theorem n07bFullPeriodTest_eqOn {φ : PolarPoint → ℝ}
    (hs : tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) Real.pi) :
    EqOn (n07bFullPeriodTest φ) φ
      ((univ : Set ℝ) ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) := by
  intro p hp
  have hzero (k : ℤ) (hk : k ≠ 0) :
      φ (n07bDoubleAngle (cylinderAngularShift k (n07bDoubleAngle.symm p))) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hkSupport
    have hangle := (hs hkSupport).2
    change 0 < 2 * (p.2 / 2 + k • Real.pi) ∧
      2 * (p.2 / 2 + k • Real.pi) < Real.pi at hangle
    simp only [zsmul_eq_mul] at hangle
    have hkCases : k ≤ -1 ∨ 1 ≤ k := by omega
    rcases hkCases with hkneg | hkpos
    · have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast hkneg
      have hbound := mul_le_mul_of_nonneg_right hkr Real.pi_pos.le
      linarith [hp.2.2, hangle.1]
    · have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
      have hbound := mul_le_mul_of_nonneg_right hkr Real.pi_pos.le
      linarith [hp.2.1, hangle.2, Real.pi_pos]
  change (∑' k : ℤ,
    φ (n07bDoubleAngle (cylinderAngularShift k (n07bDoubleAngle.symm p)))) = φ p
  rw [tsum_eq_single (0 : ℤ) hzero]
  have hshift : cylinderAngularShift (0 : ℤ) (n07bDoubleAngle.symm p) =
      n07bDoubleAngle.symm p := by
    change (p.1, p.2 / 2 + (0 : ℤ) • Real.pi) = (p.1, p.2 / 2)
    simp only [zero_smul, add_zero]
  rw [hshift, Homeomorph.apply_symm_apply]

/-- A compact planar test inside the physical half-period is an actual
full-period radial test after periodization. -/
theorem n07bFullPeriodTest_radialTest {D : ReferenceData} {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ radialCore D ×ˢ Ioo (0 : ℝ) Real.pi) :
    RadialTest D (n07bFullPeriodTest φ) := by
  refine ⟨n07bFullPeriodTest_contDiff hφ hc, n07bFullPeriodTest_periodic φ,
    Prod.fst '' tsupport φ, hc.image continuous_fst, ?_, ?_⟩
  · rintro r ⟨p, hp, rfl⟩
    exact (hs hp).1
  · intro r hr θ
    unfold n07bFullPeriodTest cylinderTestPeriodization
    apply tsum_eq_zero
    intro k
    apply image_eq_zero_of_notMem_tsupport
    intro hp
    apply hr
    exact ⟨n07bDoubleAngle
      (cylinderAngularShift k (n07bDoubleAngle.symm (r, θ))), hp, rfl⟩

end ContinuousFlexibility.Analysis
