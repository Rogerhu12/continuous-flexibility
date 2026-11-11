import ContinuousFlexibility.Analysis.N07bHeightRadialMembers

/-!
# Natural radial classes from actual continuous fields and material decay

Only continuity inside the open annulus is required.  Values at the natural
endpoints and outside the annulus are not used for measurability or L2
membership.  The source compatibility condition remains the actual physical
integral, and the output uses the prescribed left constant.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial
open scoped BigOperators ENNReal

/-- A bounded field continuous only on the open annulus is genuinely L2 for
the restricted physical measure. No endpoint extension is assumed. -/
theorem n07b_memLp_of_continuousOn_annulus_bound {D : ReferenceData}
    {f : PolarPoint → ℝ} (hf : ContinuousOn f (annularOpen D)) {B : ℝ}
    (hbound : ∀ p ∈ annularOpen D, |f p| ≤ B) :
    MemLp f 2 (radialPhysicalMeasure D) := by
  letI : IsFiniteMeasure (radialPhysicalMeasure D) :=
    ⟨r11b_radialPhysicalMeasure_finite D⟩
  have hmeas : AEStronglyMeasurable f (radialPhysicalMeasure D) := by
    apply (hf.mono
      (fun p (hp : p ∈ radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) =>
        show p ∈ annularOpen D from ⟨hp.1, mem_univ _⟩)).aestronglyMeasurable
    exact measurableSet_Ioo.prod measurableSet_Ioc
  apply MemLp.of_bound hmeas B
  have hstrip : ∀ᵐ p ∂radialPhysicalMeasure D,
      p ∈ radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [hstrip] with p hp
  simpa only [Real.norm_eq_abs] using hbound p ⟨hp.1, mem_univ _⟩

/-- Positive material decay supplies the uniform bound needed above. -/
theorem n07b_memLp_of_material_decay {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    {f : PolarPoint → ℝ} (hf : ContinuousOn f (annularOpen D))
    (hbound : ∀ p ∈ annularOpen D, |f p| ≤ K * T.H p.1 ^ δ) :
    MemLp f 2 (radialPhysicalMeasure D) := by
  have hPower := hT.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨B, _, hB, _⟩ := hPower 0 δ hδ
  apply n07b_memLp_of_continuousOn_annulus_bound hf (B := K * B)
  intro p hp
  have hheight : T.H p.1 ^ δ ≤ B := by
    simpa only [Real.rpow_zero, mul_one] using hB p.1 hp.1
  exact (hbound p hp).trans (mul_le_mul_of_nonneg_left hheight hK)

/-- The actual localizers are contractions on physical L2. -/
theorem n07b_radialCellIntegrable_of_memLp {D : ReferenceData}
    (hpart : RadialPartition D) {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D)) : RadialCellIntegrable D f := by
  intro m
  have hmeas : AEStronglyMeasurable
      (fun p : PolarPoint => D.localizer m p.1 * f p) (radialPhysicalMeasure D) :=
    ((hpart.1 m).continuous.comp continuous_fst).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  apply hf.mono hmeas
  apply Eventually.of_forall
  intro p
  change ‖D.localizer m p.1 * f p‖ ≤ ‖f p‖
  rw [norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right
    (profile_localizer_abs_le_one hpart m p.1) (norm_nonneg (f p))).trans_eq
      (one_mul _)

/-- Fubini gives the integrability of the full angular mean. The radial
interval integral ignores the endpoints by `Ioo_ae_eq_Ioc`. -/
theorem n07b_intervalIntegrable_radialAngularMean_of_memLp {D : ReferenceData}
    (hab : D.a ≤ D.b) {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D)) :
    IntervalIntegrable (fun r => radialAngularMean (fun θ => f (r, θ)))
      volume D.a D.b := by
  letI : IsFiniteMeasure (radialPhysicalMeasure D) :=
    ⟨r11b_radialPhysicalMeasure_finite D⟩
  have hi : Integrable f (radialPhysicalMeasure D) :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf
  rw [r11b_radialPhysicalMeasure_eq_prod] at hi
  have hmean : Integrable (fun r => radialAngularMean (fun θ => f (r, θ)))
      (volume.restrict (radialCore D)) := by
    have hscaled := hi.integral_prod_left.const_mul ((2 * Real.pi)⁻¹)
    simpa only [radialAngularMean, intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ 2 * Real.pi by positivity)] using hscaled
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr hmean

/-- The two actual source integrals agree from continuity inside the
annulus and the global half-period symmetry. -/
theorem n07b_radialAngularMean_integral_eq_physicalSourceIntegral
    {D : ReferenceData} (hab : D.a ≤ D.b) {f : PolarPoint → ℝ}
    (hf : ContinuousOn f (annularOpen D))
    (hperiod : Function.Periodic f (0, Real.pi)) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) =
      physicalSourceIntegral D f := by
  have hmean :
      (fun r => radialAngularMean (fun θ => f (r, θ))) =ᵐ[volume.restrict (radialCore D)]
        (fun r => angularMean (fun θ => f (r, θ))) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo]
      with r hr
    apply n06_radialAngularMean_eq_angularMean_of_continuous
    · intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hperiod (r, θ)
    · exact hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun θ => ⟨hr, mem_univ θ⟩)
  have hrad : (volume : Measure ℝ).restrict (radialCore D) =
      volume.restrict (Ioc D.a D.b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  change (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) =
    ∫ r in D.a..D.b, angularMean (fun θ => f (r, θ))
  simp only [intervalIntegral.integral_of_le hab, ← hrad]
  exact integral_congr_ae hmean

/-- Pointwise material decay and interior continuity imply every strictly
weaker natural weighted cell sum, without a cell-count assumption. -/
theorem n07b_weighted_referenceCellSquare_summable_of_material_decay
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {δ γ K : ℝ} (hδ : 0 < δ) (hγδ : γ < δ) (hK : 0 ≤ K)
    {f : PolarPoint → ℝ} (hf : ContinuousOn f (annularOpen D))
    (hbound : ∀ p ∈ annularOpen D, |f p| ≤ K * T.H p.1 ^ δ) (A : ℝ) :
    Summable (fun m =>
      Real.exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        referenceCellSquare D m f) := by
  have hdata := hD
  obtain ⟨C0, hgeom, hpart, _⟩ := hdata
  obtain ⟨C, hC, hweight⟩ := n07b_material_cell_weight_bound hD hT hδ hγδ A
  have hLp := n07b_memLp_of_material_decay hT hδ hK hf hbound
  apply n07b_weighted_referenceCellSquare_summable hpart hgeom.2.1.le
    (n07b_radialCellIntegrable_of_memLp hpart hLp)
    (fun m => Real.exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)))
    (fun m => (Real.exp_pos _).le) (B := C * K ^ 2) (mul_nonneg hC.le (sq_nonneg K))
  intro m p hp
  have hpCore : p.1 ∈ Ioo D.a D.b := hpart.2.2.2.1 m hp
  have hH : 0 < T.H p.1 := (hT.2.1 p.1 hpCore).2.1
  have hpow : (T.H p.1 ^ δ) ^ (2 : ℕ) = T.H p.1 ^ (2 * δ) := by
    simpa only [Nat.cast_ofNat, mul_comm] using
      (Real.rpow_mul_natCast hH.le δ 2).symm
  have hsq : f p ^ 2 ≤ K ^ 2 * T.H p.1 ^ (2 * δ) := by
    calc
      f p ^ 2 = |f p| ^ 2 := (sq_abs _).symm
      _ ≤ (K * T.H p.1 ^ δ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hbound p ⟨hpCore, mem_univ _⟩) 2
      _ = _ := by rw [mul_pow, hpow]
  calc
    _ ≤ Real.exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        (K ^ 2 * T.H p.1 ^ (2 * δ)) :=
      mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = K ^ 2 * (Real.exp
        (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        T.H p.1 ^ (2 * δ)) := by ring
    _ ≤ K ^ 2 * C := mul_le_mul_of_nonneg_left (hweight m p.1 hp) (sq_nonneg K)
    _ = C * K ^ 2 := mul_comm _ _

/-- Primitive continuity, decay, actual symmetry and compatibility suffice
for the natural source class. No local L2 or height-space membership is input. -/
theorem n07b_sourceMember_of_material_decay {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {δ γ K : ℝ} (hδ : 0 < δ) (hγδ : γ < δ) (hK : 0 ≤ K)
    {f : PolarPoint → ℝ} (hf : ContinuousOn f (annularOpen D))
    (hbound : ∀ p ∈ annularOpen D, |f p| ≤ K * T.H p.1 ^ δ)
    (hperiod : Function.Periodic f (0, Real.pi))
    (heven : ∀ r θ, f (r, -θ) = f (r, θ))
    (M c : ℝ) (hQ : physicalSourceIntegral D f = 0) :
    SourceMember D γ M (f, c) := by
  have hdata := hD
  obtain ⟨C0, hgeom, hpart, _⟩ := hdata
  have hLp := n07b_memLp_of_material_decay hT hδ hK hf hbound
  refine ⟨n07b_radialCellIntegrable_of_memLp hpart hLp, ?_, hperiod, heven,
    n07b_intervalIntegrable_radialAngularMean_of_memLp hgeom.2.1.le hLp, ?_⟩
  · exact n07b_weighted_referenceCellSquare_summable_of_material_decay
      hD hT hδ hγδ hK hf hbound (2 * M)
  · rw [n07b_radialAngularMean_integral_eq_physicalSourceIntegral hgeom.2.1.le hf hperiod]
    exact hQ

/-- A continuous decaying remainder gives the natural output realization
with the specified scalar left constant. -/
theorem n07b_outputRealization_of_remainder_decay
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {δ γ K a : ℝ} (hδ : 0 < δ) (hγδ : γ < δ) (hK : 0 ≤ K)
    {U : RadialUnknown} (hrem : ContinuousOn (outputRemainder D a U) (annularOpen D))
    (hbound : ∀ p ∈ annularOpen D,
      |outputRemainder D a U p| ≤ K * T.H p.1 ^ δ)
    (hperiod : Function.Periodic U.1 (0, Real.pi))
    (heven : ∀ r θ, U.1 (r, -θ) = U.1 (r, θ)) (M : ℝ) :
    OutputRealization D γ M a U := by
  have hdata := hD
  obtain ⟨C0, _, hpart, _⟩ := hdata
  refine ⟨n07b_radialCellIntegrable_of_memLp hpart
    (n07b_memLp_of_material_decay hT hδ hK hrem hbound), ?_, hperiod, heven⟩
  exact n07b_weighted_referenceCellSquare_summable_of_material_decay
    hD hT hδ hγδ hK hrem hbound (-2 * M)

/-- For the genuine smooth radial border, continuity of the physical field
itself supplies continuity of its prescribed remainder. -/
theorem n07b_outputRealization_of_material_decay
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hborder : RadialTrueBorder D)
    {δ γ K a : ℝ} (hδ : 0 < δ) (hγδ : γ < δ) (hK : 0 ≤ K)
    {U : RadialUnknown} (hU : ContinuousOn U.1 (annularOpen D))
    (hbound : ∀ p ∈ annularOpen D,
      |U.1 p - a * D.chiLeft p.1| ≤ K * T.H p.1 ^ δ)
    (hperiod : Function.Periodic U.1 (0, Real.pi))
    (heven : ∀ r θ, U.1 (r, -θ) = U.1 (r, θ)) (M : ℝ) :
    OutputRealization D γ M a U := by
  have hleft : Continuous (fun p : PolarPoint => a * D.chiLeft p.1) :=
    continuous_const.mul (hborder.2.2.2.2.1.continuous.comp continuous_fst)
  have hrem : ContinuousOn (outputRemainder D a U) (annularOpen D) := by
    change ContinuousOn (fun p : PolarPoint => U.1 p - a * D.chiLeft p.1) (annularOpen D)
    exact hU.sub hleft.continuousOn
  exact n07b_outputRealization_of_remainder_decay hD hT hδ hγδ hK hrem hbound
    hperiod heven M

end ContinuousFlexibility.Statements
