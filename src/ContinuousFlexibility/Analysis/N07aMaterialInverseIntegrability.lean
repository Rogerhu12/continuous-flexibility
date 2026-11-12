import ContinuousFlexibility.Analysis.N07aMaterialIntegrability

/-!
# A square-integrable majorant without spending height weight

The actual inverse material scale is bounded by one power of M. After
changing variables by the supplied material coordinate, M⁻² therefore
has a bounded density on the finite physical interval. This is the
majorant used when the input and output have the same height exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff ENNReal

variable {D : ReferenceData} {T : MaterialData}

theorem n07a_materialM_inv_square_integrable (hT : IsMaterialData D T) :
    Integrable (fun x : ℝ => (T.M (T.radius x))⁻¹ ^ 2) := by
  obtain ⟨C, A, hC, _, hCb⟩ := materialEll_inv_le_E0 hT
  obtain ⟨B, hB, hBb⟩ := hT.2.2.2.2.2.2.2.2.2.2.2.1 A
  have hdata := hT
  obtain ⟨hsmooth, hpos, hρ, hmono, _, _, _, hinside, hinv, _⟩ := hdata
  have hb (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
      (T.ell r)⁻¹ * ((T.M r)⁻¹ ^ 2) ≤ C * B := by
    have hm : 0 < T.M r := zero_lt_one.trans_le (hpos r hr).2.2.2
    have hi : (T.M r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hpos r hr).2.2.2
    calc
      _ ≤ (C * (B * T.M r)) * ((T.M r)⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_right
          ((hCb r hr).trans (mul_le_mul_of_nonneg_left (hBb r hr) hC)) (sq_nonneg _)
      _ = (C * B) * (T.M r)⁻¹ := by field_simp [hm.ne'] <;> ring
      _ ≤ C * B := (mul_le_mul_of_nonneg_left hi (mul_nonneg hC hB.le)).trans_eq
        (mul_one _)
  have hcont : ContinuousOn
      (fun r : ℝ => (T.ell r)⁻¹ * ((T.M r)⁻¹ ^ 2)) (Ioo D.a D.b) :=
    ((hsmooth T.ell (by simp)).continuousOn.inv₀
      (fun r hr => (hpos r hr).1.ne')).mul
        (((hsmooth T.M (by simp)).continuousOn.inv₀
          (fun r hr => (zero_lt_one.trans_le (hpos r hr).2.2.2).ne')).pow 2)
  have hbase : IntegrableOn
      (fun r : ℝ => (T.ell r)⁻¹ * ((T.M r)⁻¹ ^ 2)) (Ioo D.a D.b) := by
    apply (integrableOn_const (C := C * B) (μ := volume)
      (s := Ioo D.a D.b) measure_Ioo_lt_top.ne).mono'
        (hcont.aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (inv_nonneg.mpr (hpos r hr).1.le) (sq_nonneg _))] using hb r hr
  have himage : T.rho '' Ioo D.a D.b = univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact ⟨T.radius x, (hinside x).1, (hinside x).2⟩
  have hjac := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo (fun r hr => (hρ r hr).hasDerivWithinAt)
    hmono.injOn (fun x : ℝ => (T.M (T.radius x))⁻¹ ^ 2)
  have hchange : IntegrableOn
      (fun r : ℝ => |1 / T.ell r| • ((T.M (T.radius (T.rho r)))⁻¹ ^ 2))
      (Ioo D.a D.b) := by
    apply hbase.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    simp only [hinv r hr, smul_eq_mul, one_div,
      abs_of_pos (inv_pos.mpr (hpos r hr).1)]
  simpa only [himage, IntegrableOn, Measure.restrict_univ] using hjac.mpr hchange

theorem n07a_materialM_inv_cylinder_memLp (hT : IsMaterialData D T) :
    MemLp (fun p : PolarPoint => (T.M (T.radius p.1))⁻¹) 2 materialCylinderMeasure := by
  have hM : Continuous (fun x : ℝ => (T.M (T.radius x))⁻¹) :=
    (((hT.1 T.M (by simp)).comp_contDiff hT.2.2.2.2.2.2.1
      (fun x => (hT.2.2.2.2.2.2.2.1 x).1)).inv
        (fun x => (zero_lt_one.trans_le
          (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 x).1).2.2.2).ne')).continuous
  have hm : MemLp (fun x : ℝ => (T.M (T.radius x))⁻¹) 2 volume :=
    (memLp_two_iff_integrable_sq hM.aestronglyMeasurable).mpr
      (n07a_materialM_inv_square_integrable hT)
  letI : IsFiniteMeasure angleMeasure :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) Real.pi)))
  rw [materialCylinderMeasure_eq_prod]
  exact hm.comp_fst angleMeasure

end ContinuousFlexibility.Analysis
