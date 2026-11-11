import ContinuousFlexibility.Analysis.SpacesTorusCellDerivatives

/-!
# Exact localized cell coefficients

The physical-cylinder integration-by-parts identities become coefficient
identities for the actual normalized torus chart. The radial support lies
strictly inside the cell, so all mixed derivatives have the required
vanishing boundary values.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology ComplexConjugate

set_option backward.isDefEq.respectTransparency false

local instance spacesTorusCellCoefficientsCircleMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

theorem spacesPhysicalFourierWave_quotient (n : ℤ) (j : SpacesTorusFrequency)
    (p : PolarPoint) :
    spacesPhysicalFourierWave n j p = UnitAddTorus.mFourier j (spacesPhysicalCellQuotient n p) := by
  simp only [spacesPhysicalFourierWave, spacesUnitFourierAffine, UnitAddTorus.mFourier,
    ContinuousMap.coe_mk, Fin.prod_univ_two, spacesPhysicalCellQuotient,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 2
  · congr 1
    ring
  · congr 1
    ring

theorem spacesPhysicalFourierWave_chart (n : ℤ) (j : SpacesTorusFrequency)
    (t : SpacesTorus) :
    spacesPhysicalFourierWave n j (spacesPhysicalCellChart n t) = UnitAddTorus.mFourier j t := by
  rw [spacesPhysicalFourierWave_quotient, spacesPhysicalCellQuotient_chart]

theorem spacesPhysicalCellMeasure_eq_smul_restrict (n : ℤ) :
    spacesPhysicalCellMeasure n = ENNReal.ofReal ((6 * Real.pi)⁻¹) •
      materialCylinderMeasure.restrict (Ioc ((n : ℝ) - 3) (n + 3) ×ˢ (univ : Set ℝ)) := by
  unfold spacesPhysicalCellMeasure materialCylinderMeasure
  rw [Measure.restrict_restrict (measurableSet_Ioc.prod MeasurableSet.univ)]
  congr 2
  ext p
  simp only [spacesPhysicalCell, mem_prod, mem_inter_iff, mem_univ, true_and, and_comm]

/-- The Fourier coefficient is exactly the normalized physical integral. -/
theorem spacesPhysicalCell_coefficient_integral (n : ℤ) (j : SpacesTorusFrequency)
    {v : PolarPoint → ℝ} (hv : IsCylinderTest v)
    (hz : ∀ p : PolarPoint, p.1 ∉ Ioc ((n : ℝ) - 3) (n + 3) → v p = 0) :
    UnitAddTorus.mFourierCoeff (fun t => (v (spacesPhysicalCellChart n t) : ℂ)) j =
      (((6 * Real.pi)⁻¹ : ℝ) : ℂ) *
        ∫ p, spacesPhysicalFourierWave n (-j) p * (v p : ℂ) ∂materialCylinderMeasure := by
  let f : PolarPoint → ℂ := fun p => spacesPhysicalFourierWave n (-j) p * (v p : ℂ)
  have hf := spacesPhysicalFourierWave_integrable_mul n (-j) hv
  have hfc : Integrable f (spacesPhysicalCellMeasure n) :=
    hf.mono_measure (spacesPhysicalCellMeasure_le_cylinder n)
  have hc : MeasurePreserving (spacesPhysicalCellChart n) (volume : Measure SpacesTorus)
      (spacesPhysicalCellMeasure n) := spacesPhysicalCellChart_preserving n
  have hm : AEStronglyMeasurable f (Measure.map (spacesPhysicalCellChart n)
      (volume : Measure SpacesTorus)) := by
    rw [hc.map_eq]
    exact hfc.aestronglyMeasurable
  have hmap := integral_map hc.measurable.aemeasurable hm
  rw [hc.map_eq] at hmap
  have he : (fun t : SpacesTorus => UnitAddTorus.mFourier (-j) t •
      (v (spacesPhysicalCellChart n t) : ℂ)) = fun t => f (spacesPhysicalCellChart n t) := by
    funext t
    dsimp only [f]
    rw [spacesPhysicalFourierWave_chart, smul_eq_mul]
  rw [UnitAddTorus.mFourierCoeff, he, ← hmap,
    spacesPhysicalCellMeasure_eq_smul_restrict, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (6 * Real.pi)⁻¹), Complex.real_smul]
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hpr : p.1 ∉ Ioc ((n : ℝ) - 3) (n + 3) := fun h => hp ⟨h, mem_univ _⟩
  simp only [f, hz p hpr, Complex.ofReal_zero, mul_zero]

theorem spaces_mixedDerivative_cell_support (n : ℤ) {v : PolarPoint → ℝ}
    (hz : ∀ p : PolarPoint, |p.1 - n| ≥ 1 → v p = 0) (a b : ℕ)
    (p : PolarPoint) (hp : p.1 ∉ Ioc ((n : ℝ) - 3) (n + 3)) :
    mixedDerivative a b v p = 0 := by
  have hstrict : 1 < |p.1 - n| := by
    by_contra h
    have hle := abs_le.mp (le_of_not_gt h)
    exact hp ⟨by linarith [hle.1], by linarith [hle.2]⟩
  have hnear : ∀ᶠ x : ℝ in 𝓝 p.1, 1 < |x - n| :=
    continuousAt_const.eventually_lt ((continuous_id.sub continuous_const).abs.continuousAt) hstrict
  have he : (fun x : ℝ => iteratedDeriv b (fun θ => v (x, θ)) p.2) =ᶠ[𝓝 p.1]
      (0 : ℝ → ℝ) := by
    filter_upwards [hnear] with x hx
    have hv : (fun θ : ℝ => v (x, θ)) = (0 : ℝ → ℝ) :=
      funext (fun θ => hz (x, θ) hx.le)
    simp only [hv, iteratedDeriv_const_zero, Pi.zero_apply]
  simpa only [mixedDerivative, iteratedDeriv_const_zero, Pi.zero_apply] using he.iteratedDeriv_eq a

/-- Localized mixed jets have the exact radial and angular Fourier symbols. -/
theorem spacesPhysicalCell_coefficient_mixedDerivative (n : ℤ) (j : SpacesTorusFrequency)
    {v : PolarPoint → ℝ} (hv : IsCylinderTest v)
    (hz : ∀ p : PolarPoint, |p.1 - n| ≥ 1 → v p = 0) (a b : ℕ) :
    UnitAddTorus.mFourierCoeff
      (fun t => (mixedDerivative a b v (spacesPhysicalCellChart n t) : ℂ)) j =
      spacesUnitFourierSymbol (j 0) (1 / 6) ^ a *
        spacesUnitFourierSymbol (j 1) (1 / Real.pi) ^ b *
        UnitAddTorus.mFourierCoeff (fun t => (v (spacesPhysicalCellChart n t) : ℂ)) j := by
  have hzv : ∀ p : PolarPoint, p.1 ∉ Ioc ((n : ℝ) - 3) (n + 3) → v p = 0 := by
    intro p hp
    simpa only [spaces_mixedDerivative_zero] using spaces_mixedDerivative_cell_support n hz 0 0 p hp
  rw [spacesPhysicalCell_coefficient_integral n j (hv.mixedDerivative a b)
      (spaces_mixedDerivative_cell_support n hz a b),
    spacesPhysicalCell_coefficient_integral n j hv hzv,
    spacesPhysicalFourierWave_integral_mixedDerivative n (-j) hv a b]
  have hs (i : Fin 2) (r : ℝ) : spacesUnitFourierSymbol ((-j) i) r =
      -spacesUnitFourierSymbol (j i) r := by
    simp only [spacesUnitFourierSymbol, Pi.neg_apply, Int.cast_neg, mul_neg]
  rw [hs 0, hs 1, neg_pow, neg_pow]
  have he : (-1 : ℂ) ^ (a + b) * ((-1 : ℂ) ^ a * (-1 : ℂ) ^ b) = 1 := by
    rw [← pow_add, ← pow_two, ← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  calc
    _ = ((-1 : ℂ) ^ (a + b) * ((-1 : ℂ) ^ a * (-1 : ℂ) ^ b)) *
        (spacesUnitFourierSymbol (j 0) (1 / 6) ^ a *
          spacesUnitFourierSymbol (j 1) (1 / Real.pi) ^ b *
          ((((6 * Real.pi)⁻¹ : ℝ) : ℂ) *
            ∫ p, spacesPhysicalFourierWave n (-j) p * (v p : ℂ) ∂materialCylinderMeasure)) := by ring
    _ = _ := by rw [he, one_mul]

end ContinuousFlexibility.Statements
