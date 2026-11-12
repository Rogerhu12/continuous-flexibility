import ContinuousFlexibility.Scalar.WeightedMaterialScale
import ContinuousFlexibility.Scalar.WeightedWeightShiftJets
import ContinuousFlexibility.Analysis.CylinderTestPairing
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Integrability of positive material weights

The derivative of the material radius is the positive scale `ell`, and
its image is the finite physical interval. Change of variables therefore
makes `ell ∘ radius` integrable on the entire material line. Any positive
power of `H` is bounded by a constant times this scale: the reciprocal
scale costs one envelope power, which the positive weight absorbs.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal

variable {D : ReferenceData} {T : MaterialData}

theorem n08_integrable_materialScale (hT : IsMaterialData D T) :
    Integrable (fun x : ℝ => T.ell (T.radius x)) := by
  obtain ⟨_, hpos, _, _, _, _, _, hinside, hinverse, hderiv, _⟩ := hT
  have hinj : Function.Injective T.radius :=
    (show Function.LeftInverse T.rho T.radius from fun x => (hinside x).2).injective
  have himage : T.radius '' (univ : Set ℝ) = Ioo D.a D.b := by
    ext r
    constructor
    · rintro ⟨x, _, rfl⟩
      exact (hinside x).1
    · intro hr
      exact ⟨T.rho r, mem_univ _, hinverse r hr⟩
  have hg : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (T.radius '' (univ : Set ℝ)) := by
    rw [himage]
    exact integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hc := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hderiv x).hasDerivWithinAt) hinj.injOn (fun _ : ℝ => (1 : ℝ))).mp hg
  have hc' : Integrable (fun x : ℝ => |T.ell (T.radius x)| • (1 : ℝ)) := by
    simpa only [integrableOn_univ] using hc
  apply hc'.congr
  exact Filter.Eventually.of_forall fun x => by
    simp only [smul_eq_mul, mul_one, abs_of_pos ((hpos _ (hinside x).1).1)]

/-- A fixed positive material weight has an integrable scale majorant. -/
theorem n08_materialH_rpow_le_scale (hT : IsMaterialData D T)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      T.H (T.radius x) ^ η ≤ C * T.ell (T.radius x) := by
  obtain ⟨C, hC, hCb⟩ := (materialEll_inv_subpower hT).le_materialM 0
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _, _, _, _, hdecay, _⟩ := hT
  obtain ⟨K, hK, hKb, _, _⟩ := hdecay 1 η hη
  refine ⟨C * K, mul_nonneg hC hK.le, fun x => ?_⟩
  have hell := (hpos _ (hinside x).1).1
  have hH := (hpos _ (hinside x).1).2.1
  have hi : (T.ell (T.radius x))⁻¹ ≤ C * T.M (T.radius x) := by
    simpa only [iteratedDeriv_zero, abs_of_pos (inv_pos.mpr hell)] using hCb x
  have hk : T.H (T.radius x) ^ η * T.M (T.radius x) ≤ K := by
    simpa only [Real.rpow_one] using hKb (T.radius x) (hinside x).1
  have hprod : T.H (T.radius x) ^ η * (T.ell (T.radius x))⁻¹ ≤ C * K := by
    calc
      _ ≤ T.H (T.radius x) ^ η * (C * T.M (T.radius x)) :=
        mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hH.le _)
      _ = C * (T.H (T.radius x) ^ η * T.M (T.radius x)) := by ring
      _ ≤ C * K := mul_le_mul_of_nonneg_left hk hC
  calc
    _ = (T.H (T.radius x) ^ η * (T.ell (T.radius x))⁻¹) * T.ell (T.radius x) := by
      rw [mul_assoc, inv_mul_cancel₀ hell.ne', mul_one]
    _ ≤ (C * K) * T.ell (T.radius x) := mul_le_mul_of_nonneg_right hprod hell.le

theorem n08_integrable_materialH_rpow (hT : IsMaterialData D T)
    {η : ℝ} (hη : 0 < η) :
    Integrable (fun x : ℝ => T.H (T.radius x) ^ η) := by
  obtain ⟨C, _, hCb⟩ := n08_materialH_rpow_le_scale hT hη
  apply ((n08_integrable_materialScale hT).const_mul C).mono'
    (contDiff_materialH_rpow hT η).continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg
      ((hT.2.1 _ (hT.2.2.2.2.2.2.2.1 x).1).2.1.le) _)]
    exact hCb x

theorem n08_memLp_materialH_rpow (hT : IsMaterialData D T)
    {η : ℝ} (hη : 0 < η) :
    MemLp (fun x : ℝ => T.H (T.radius x) ^ η) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    (contDiff_materialH_rpow hT η).continuous.aestronglyMeasurable).mpr
  have heq : (fun x : ℝ => (T.H (T.radius x) ^ η) ^ 2) =
      fun x => T.H (T.radius x) ^ (η * 2) := by
    funext x
    have hH := (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 x).1).2.1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hH.le]
    norm_num
  rw [heq]
  exact n08_integrable_materialH_rpow hT (mul_pos hη (by norm_num))

theorem n08_memLp_cylinder_materialH_rpow (hT : IsMaterialData D T)
    {η : ℝ} (hη : 0 < η) :
    MemLp (fun p : PolarPoint => T.H (T.radius p.1) ^ η) 2 materialCylinderMeasure := by
  letI : IsFiniteMeasure angleMeasure :=
    ⟨by rw [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top⟩
  rw [materialCylinderMeasure_eq_prod]
  exact (n08_memLp_materialH_rpow hT hη).comp_fst angleMeasure

end ContinuousFlexibility.Statements
