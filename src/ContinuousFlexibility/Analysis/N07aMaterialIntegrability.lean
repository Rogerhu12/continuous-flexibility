import ContinuousFlexibility.Scalar.WeightedMaterialScale
import ContinuousFlexibility.Scalar.WeightedWeightShiftJets
import ContinuousFlexibility.Analysis.CylinderTestPairing
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Integrable positive powers of the actual material height weight

Changing variables by the given material coordinate reduces the integral
on the entire material axis to a bounded function on the finite physical
interval. The reciprocal scale has the existing `E0` bound, and every
positive height power absorbs that bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff ENNReal
open ContinuousFlexibility.Statements

/-- A positive height power absorbs the actual coordinate Jacobian. -/
theorem n07a_materialH_rpow_div_scale_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, r ∈ Ioo D.a D.b →
      (T.ell r)⁻¹ * T.H r ^ γ ≤ K := by
  obtain ⟨C, A, hC, _, hCb⟩ := materialEll_inv_le_E0 hT
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hE, hH, _⟩ := hdata
  obtain ⟨B, hB, hBb⟩ := hE A
  obtain ⟨K, hK, hKb, _⟩ := hH 1 γ hγ
  refine ⟨C * B * K, mul_nonneg (mul_nonneg hC hB.le) hK.le, fun r hr => ?_⟩
  have hHpos : 0 < T.H r := (hT.2.1 r hr).2.1
  calc
    (T.ell r)⁻¹ * T.H r ^ γ ≤ (C * T.E0 r ^ A) * T.H r ^ γ :=
      mul_le_mul_of_nonneg_right (hCb r hr) (Real.rpow_nonneg hHpos.le _)
    _ ≤ (C * (B * T.M r)) * T.H r ^ γ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hBb r hr) hC)
        (Real.rpow_nonneg hHpos.le _)
    _ = C * B * (T.H r ^ γ * T.M r) := by ring
    _ ≤ C * B * K := mul_le_mul_of_nonneg_left
      (by simpa only [Real.rpow_one] using hKb r hr) (mul_nonneg hC hB.le)

/-- Every positive height power is integrable on the entire actual
material axis. The argument uses the supplied inverse coordinate. -/
theorem n07a_materialH_rpow_integrable
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {γ : ℝ} (hγ : 0 < γ) :
    Integrable (fun x : ℝ => T.H (T.radius x) ^ γ) := by
  obtain ⟨K, _, hKb⟩ := n07a_materialH_rpow_div_scale_bound hT hγ
  have hdata := hT
  obtain ⟨hsmooth, hpos, hρ, hmono, _, _, _, hinside, hinv, _⟩ := hdata
  have hcont : ContinuousOn (fun r : ℝ => (T.ell r)⁻¹ * T.H r ^ γ)
      (Ioo D.a D.b) :=
    (((hsmooth T.ell (by simp)).continuousOn.inv₀ (fun r hr => (hpos r hr).1.ne')).mul
      ((hsmooth T.H (by simp)).rpow_const_of_ne
        (fun r hr => (hpos r hr).2.1.ne')).continuousOn)
  have hbase : IntegrableOn (fun r : ℝ => (T.ell r)⁻¹ * T.H r ^ γ)
      (Ioo D.a D.b) := by
    apply (integrableOn_const (C := K) (μ := volume)
      (s := Ioo D.a D.b) measure_Ioo_lt_top.ne).mono'
      (hcont.aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (inv_nonneg.mpr (hpos r hr).1.le)
        (Real.rpow_nonneg (hpos r hr).2.1.le γ))] using hKb r hr
  have himage : T.rho '' Ioo D.a D.b = univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact ⟨T.radius x, (hinside x).1, (hinside x).2⟩
  have hjac := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo (fun r hr => (hρ r hr).hasDerivWithinAt)
    hmono.injOn (fun x : ℝ => T.H (T.radius x) ^ γ)
  have hchange : IntegrableOn
      (fun r : ℝ => |1 / T.ell r| • (T.H (T.radius (T.rho r)) ^ γ))
      (Ioo D.a D.b) := by
    apply hbase.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    simp only [hinv r hr, smul_eq_mul, one_div,
      abs_of_pos (inv_pos.mpr (hpos r hr).1)]
  have h := hjac.mpr hchange
  simpa only [himage, IntegrableOn, Measure.restrict_univ] using h

/-- The positive material height weight is an actual `L²` majorant. -/
theorem n07a_materialH_rpow_memLp
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {γ : ℝ} (hγ : 0 < γ) :
    MemLp (fun x : ℝ => T.H (T.radius x) ^ γ) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    (contDiff_materialH_rpow hT γ).continuous.aestronglyMeasurable).mpr
  have hi := n07a_materialH_rpow_integrable hT (mul_pos hγ (by norm_num : (0 : ℝ) < 2))
  convert hi using 1
  funext x
  rw [Real.rpow_mul ((hT.2.1 _ (hT.2.2.2.2.2.2.2.1 x).1).2.1.le), Real.rpow_two]

/-- The same majorant belongs to the actual finite-period material cylinder. -/
theorem n07a_materialH_rpow_cylinder_memLp
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {γ : ℝ} (hγ : 0 < γ) :
    MemLp (fun p : PolarPoint => T.H (T.radius p.1) ^ γ) 2 materialCylinderMeasure := by
  letI : IsFiniteMeasure angleMeasure :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) Real.pi)))
  rw [materialCylinderMeasure_eq_prod]
  exact (n07a_materialH_rpow_memLp hT hγ).comp_fst angleMeasure

/-- Any fixed material-envelope power can be included in the same
square-integrable majorant by spending half of the positive height power. -/
theorem n07a_materialM_rpow_mul_H_rpow_cylinder_memLp
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (A : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    MemLp (fun p : PolarPoint =>
      T.M (T.radius p.1) ^ A * T.H (T.radius p.1) ^ γ) 2 materialCylinderMeasure := by
  have hdata := hT
  obtain ⟨hsmooth, hpos, _, _, _, _, hradius, hinside, _, _, _, _, hweight, _⟩ := hdata
  obtain ⟨K, _, hKb, _⟩ := hweight A (γ / 2) (half_pos hγ)
  have hM : ContDiff ℝ ∞ (fun x : ℝ => T.M (T.radius x) ^ A) :=
    ((hsmooth T.M (by simp)).rpow_const_of_ne
      (fun r hr => (zero_lt_one.trans_le (hpos r hr).2.2.2).ne')).comp_contDiff
        hradius (fun x => (hinside x).1)
  have hcont : Continuous (fun p : PolarPoint =>
      T.M (T.radius p.1) ^ A * T.H (T.radius p.1) ^ γ) :=
    (hM.comp contDiff_fst).continuous.mul
      ((contDiff_materialH_rpow hT γ).comp contDiff_fst).continuous
  apply ((n07a_materialH_rpow_cylinder_memLp hT (half_pos hγ)).const_mul K).mono'
    hcont.aestronglyMeasurable
  filter_upwards [] with p
  have hHpos := (hpos _ (hinside p.1).1).2.1
  have hMpos := zero_lt_one.trans_le (hpos _ (hinside p.1).1).2.2.2
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg hMpos.le _) (Real.rpow_nonneg hHpos.le _))]
  calc
    T.M (T.radius p.1) ^ A * T.H (T.radius p.1) ^ γ =
        (T.H (T.radius p.1) ^ (γ / 2) * T.M (T.radius p.1) ^ A) *
          T.H (T.radius p.1) ^ (γ / 2) := by
      rw [mul_comm (T.H _ ^ (γ / 2)) (T.M _ ^ A), mul_assoc,
        ← Real.rpow_add hHpos, add_halves]
    _ ≤ K * T.H (T.radius p.1) ^ (γ / 2) :=
      mul_le_mul_of_nonneg_right (hKb _ (hinside p.1).1)
        (Real.rpow_nonneg hHpos.le _)

end ContinuousFlexibility.Analysis
