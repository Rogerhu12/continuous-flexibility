import ContinuousFlexibility.Radial.R11bPhysicalPairing
import ContinuousFlexibility.Radial.R11bPartitionL2

/-!
# Physical L² bounds from positive radial attenuation

The strict positive attenuation dominates every fixed coefficient weight.
The overlap bound controls the physical square integral by the sum of the
localized square integrals. This argument uses no bound on the number of
cells having a given index.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open ContinuousFlexibility.Statements

/-- Uniform physical L² control for an arbitrary fixed coefficient exponent. -/
theorem r11b_cell_weighted_L2_bound {D : ReferenceData} (hpart : RadialPartition D)
    (hab : D.a ≤ D.b) (A γ : ℝ) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : PolarPoint → ℝ, RadialCellIntegrable D f →
      Summable (fun m => exp (A * radialQ (D.cellIndex m) +
        2 * γ * radialS (D.cellIndex m)) * referenceCellSquare D m f) →
      MemLp f 2 (radialPhysicalMeasure D) ∧
        (∫ x, f x ^ 2 ∂radialPhysicalMeasure D) ≤
          C * ∑' m, exp (A * radialQ (D.cellIndex m) +
            2 * γ * radialS (D.cellIndex m)) * referenceCellSquare D m f := by
  obtain ⟨B, hB⟩ := hpart.2.2.2.2.2
  obtain ⟨K, hK, hweight⟩ := r11b_exp_weight_le 0 A 0 γ hγ
  have hweight' : ∀ m, (1 : ℝ) ≤ K *
      exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) := by
    intro m
    simpa only [zero_mul, zero_add, exp_zero] using hweight (D.cellIndex m)
  let C₀ : ℝ := (B : ℝ) * (2 * Real.pi) * K
  have hC₀ : 0 ≤ C₀ := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg B) (by positivity)) (zero_le_one.trans hK)
  refine ⟨C₀ + 1, by linarith, fun f hf hs => ?_⟩
  obtain ⟨hs0, hnorm⟩ := r11b_weighted_tsum_le
    (fun _ => 1)
    (fun m => exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)))
    (fun m => referenceCellSquare D m f)
    (fun _ => zero_le_one) (fun m => r11b_referenceCellSquare_nonneg hab m f) hweight' hs
  simp only [one_mul] at hs0 hnorm
  have hint (m : ℕ) :
      (∫ x, (D.localizer m x.1 * f x) ^ 2 ∂radialPhysicalMeasure D) =
        (2 * Real.pi) * referenceCellSquare D m f := by
    rw [r11b_referenceCellSquare_eq_integral hab hf m]
    have hπ : 2 * Real.pi ≠ 0 := by positivity
    field_simp
  have hsI : Summable (fun m => ∫ x,
      (D.localizer m x.1 * f x) ^ 2 ∂radialPhysicalMeasure D) :=
    (hs0.mul_left (2 * Real.pi)).congr (fun m => (hint m).symm)
  have hsum : ∀ᵐ x ∂radialPhysicalMeasure D,
      (∑' m, D.localizer m x.1) = 1 := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with x hx
    exact (hpart.2.2.2.2.1 x.1 hx.1).2
  obtain ⟨hfLp, hI⟩ := r11b_memLp_of_localized_square_summable
    (fun (m : ℕ) (x : PolarPoint) => D.localizer m x.1) f hf
    (Filter.Eventually.of_forall fun x => (hB x.1).1)
    (Filter.Eventually.of_forall fun x => (hB x.1).2) hsum hsI
  refine ⟨hfLp, ?_⟩
  have hsum0 : 0 ≤ ∑' m, exp (A * radialQ (D.cellIndex m) +
      2 * γ * radialS (D.cellIndex m)) * referenceCellSquare D m f :=
    tsum_nonneg (fun m => mul_nonneg (exp_pos _).le
      (r11b_referenceCellSquare_nonneg hab m f))
  calc (∫ x, f x ^ 2 ∂radialPhysicalMeasure D)
      ≤ (B : ℝ) * ∑' m, ∫ x,
          (D.localizer m x.1 * f x) ^ 2 ∂radialPhysicalMeasure D := hI
    _ = (B : ℝ) * ((2 * Real.pi) * ∑' m, referenceCellSquare D m f) := by
      simp_rw [hint]
      rw [tsum_mul_left]
    _ ≤ (B : ℝ) * ((2 * Real.pi) * (K * ∑' m,
        exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          referenceCellSquare D m f)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hnorm (by positivity)) (Nat.cast_nonneg B)
    _ = C₀ * ∑' m, exp (A * radialQ (D.cellIndex m) +
        2 * γ * radialS (D.cellIndex m)) * referenceCellSquare D m f := by
      dsimp [C₀]
      ring
    _ ≤ (C₀ + 1) * ∑' m, exp (A * radialQ (D.cellIndex m) +
        2 * γ * radialS (D.cellIndex m)) * referenceCellSquare D m f :=
      mul_le_mul_of_nonneg_right (by linarith) hsum0

theorem r11b_source_memLp {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {γ M : ℝ} (hγ : 0 < γ) {F : RadialSource} (hF : SourceMember D γ M F) :
    MemLp F.1 2 (radialPhysicalMeasure D) := by
  obtain ⟨_, hgeom, hpart, _⟩ := hD
  obtain ⟨_, _, h⟩ := r11b_cell_weighted_L2_bound hpart hgeom.2.1.le (2 * M) γ hγ
  exact (h F.1 hF.1 hF.2.1).1

theorem r11b_sourceDerivative_memLp {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {γ M : ℝ} (hγ : 0 < γ) {fθ : PolarPoint → ℝ}
    (hfθ : SourceDerivativeMember D γ M fθ) :
    MemLp fθ 2 (radialPhysicalMeasure D) := by
  obtain ⟨_, hgeom, hpart, _⟩ := hD
  obtain ⟨_, _, h⟩ := r11b_cell_weighted_L2_bound hpart hgeom.2.1.le (2 * M) γ hγ
  exact (h fθ hfθ.1 hfθ.2).1

theorem r11b_outputRemainder_memLp {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {γ M aL : ℝ} (hγ : 0 < γ) {U : RadialUnknown}
    (hU : OutputRealization D γ M aL U) :
    MemLp (outputRemainder D aL U) 2 (radialPhysicalMeasure D) := by
  obtain ⟨_, hgeom, hpart, _⟩ := hD
  obtain ⟨_, _, h⟩ := r11b_cell_weighted_L2_bound hpart hgeom.2.1.le (-2 * M) γ hγ
  exact (h (outputRemainder D aL U) hU.1 hU.2.1).1

theorem r11b_output_memLp {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hborder : RadialTrueBorder D) {γ M : ℝ} (hγ : 0 < γ) {U : RadialUnknown}
    (hU : OutputMember D γ M U) : MemLp U.1 2 (radialPhysicalMeasure D) := by
  obtain ⟨aL, hU⟩ := hU
  have hrem := r11b_outputRemainder_memLp hD hγ hU
  have hleft : Continuous (fun x : PolarPoint => aL * D.chiLeft x.1) :=
    continuous_const.mul (hborder.2.2.2.2.1.continuous.comp continuous_fst)
  apply MemLp.ae_eq _ (hrem.add (r11b_continuous_memLp hleft))
  exact Filter.Eventually.of_forall fun x =>
    sub_add_cancel (U.1 x) (aL * D.chiLeft x.1)

end ContinuousFlexibility.Radial
