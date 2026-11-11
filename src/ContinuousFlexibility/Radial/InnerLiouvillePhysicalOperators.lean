import ContinuousFlexibility.Radial.InnerLiouvilleL2Transport
import ContinuousFlexibility.Radial.InnerWeightL2
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Actual physical operators from a retained model inverse

The field lift is the normalized Liouville map from the same Lebesgue
model space into the same radial measure. Its adjoint is the source
conversion. Keeping the scalar coordinate fixed gives the congruence
A G A* used by the central bordered inverse; noncentral zero scalars
remain zero. The field norm loses only the retained logarithmic
velocity, and the height scale cancels.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

/-- The actual logarithmic velocity, extended by zero off the model cell. -/
def innerLiouvilleModelVelocity (R : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  (Ioo a b).indicator (fun x => deriv R x / R x)

theorem innerLiouvilleModelVelocity_measurable {R : ℝ → ℝ}
    (hR : ContDiff ℝ ∞ R) (a b : ℝ) :
    Measurable (innerLiouvilleModelVelocity R a b) :=
  (((contDiff_infty_iff_deriv.mp hR).2.continuous.measurable).div
    hR.continuous.measurable).indicator measurableSet_Ioo

theorem innerLiouvilleModelVelocity_bound {R : ℝ → ℝ} {a b U : ℝ}
    (hU : 0 ≤ U) (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U) (x : ℝ) :
    |innerLiouvilleModelVelocity R a b x| ≤ U := by
  unfold innerLiouvilleModelVelocity
  by_cases hx : x ∈ Ioo a b
  · rw [indicator_of_mem hx]
    exact hv x (Ioo_subset_Icc_self hx)
  · rw [indicator_of_notMem hx, abs_zero]
    exact hU

def innerLiouvilleVelocityMultiplier (R : ℝ → ℝ) (a b : ℝ)
    (hR : ContDiff ℝ ∞ R) (U : ℝ) (hU : 0 ≤ U)
    (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U) :
    Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  innerWeightMultiplier volume (innerLiouvilleModelVelocity R a b)
    (innerLiouvilleModelVelocity_measurable hR a b) U
    (innerLiouvilleModelVelocity_bound hU hv)

theorem innerLiouvilleVelocityMultiplier_ae (R : ℝ → ℝ) (a b : ℝ)
    (hR : ContDiff ℝ ∞ R) (U : ℝ) (hU : 0 ≤ U)
    (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    (innerLiouvilleVelocityMultiplier R a b hR U hU hv f : ℝ → ℝ) =ᵐ[volume]
      (fun x => innerLiouvilleModelVelocity R a b x * f x) :=
  innerWeightMultiplier_ae volume _ _ U _ f

theorem innerLiouvilleVelocityMultiplier_norm_apply_le (R : ℝ → ℝ) (a b : ℝ)
    (hR : ContDiff ℝ ∞ R) (U : ℝ) (hU : 0 ≤ U)
    (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ‖innerLiouvilleVelocityMultiplier R a b hR U hU hv f‖ ≤ U * ‖f‖ :=
  innerWeightMultiplier_norm_apply_le volume _ _ U _ f

theorem innerLiouvilleVelocityMultiplier_adjoint (R : ℝ → ℝ) (a b : ℝ)
    (hR : ContDiff ℝ ∞ R) (U : ℝ) (hU : 0 ≤ U)
    (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U) :
    (innerLiouvilleVelocityMultiplier R a b hR U hU hv).adjoint =
      innerLiouvilleVelocityMultiplier R a b hR U hU hv :=
  innerWeightMultiplier_adjoint volume _ _ U _

section Physical

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)

/-- The model field is normalized by sqrt(lam); its physical lift is
f/(sqrt(lam)*s) on the actual retained radial cell and zero off it. -/
def innerLiouvilleFieldLift :
    Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (radialHilbertMeasure D) :=
  Real.sqrt 12 •
    (innerL2ZeroExtension (radialHilbertMeasure D) (Ioo (R a) (R b))).comp
      (((innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw).symm :
        Lp ℝ 2 (volume.restrict (Ioo a b)) →L[ℝ]
          Lp ℝ 2 ((radialHilbertMeasure D).restrict (Ioo (R a) (R b)))).comp
        ((LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ioo a b)).comp
          (innerLiouvilleVelocityMultiplier R a b hR U hU hv)))

theorem innerLiouvilleFieldLift_apply (f : Lp ℝ 2 (volume : Measure ℝ)) :
    innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f =
      Real.sqrt 12 • innerL2ZeroExtension (radialHilbertMeasure D) (Ioo (R a) (R b))
        ((innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw).symm
          (LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ioo a b)
            (innerLiouvilleVelocityMultiplier R a b hR U hU hv f))) := by
  unfold innerLiouvilleFieldLift
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_coe'']

theorem innerLiouvilleFieldLift_norm_apply_le (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ‖innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f‖ ≤
      (Real.sqrt 12 * U) * ‖f‖ := by
  rw [innerLiouvilleFieldLift_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 12), innerL2ZeroExtension_norm _ _ measurableSet_Ioo,
    LinearIsometryEquiv.norm_map]
  calc
    _ ≤ Real.sqrt 12 * ‖innerLiouvilleVelocityMultiplier R a b hR U hU hv f‖ :=
      mul_le_mul_of_nonneg_left
        (innerL2Restriction_norm_apply_le volume (Ioo a b) _)
        (Real.sqrt_nonneg 12)
    _ ≤ Real.sqrt 12 * (U * ‖f‖) :=
      mul_le_mul_of_nonneg_left
        (innerLiouvilleVelocityMultiplier_norm_apply_le R a b hR U hU hv f)
        (Real.sqrt_nonneg 12)
    _ = _ := (mul_assoc _ _ _).symm

theorem norm_innerLiouvilleFieldLift_le :
    ‖innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv‖ ≤ Real.sqrt 12 * U :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg 12) hU)
    (innerLiouvilleFieldLift_norm_apply_le D hab hlam hR hs hp hcore hw U hU hv)

/-- Source conversion is the adjoint of the actual normalized field lift. -/
def innerLiouvilleSource :
    Lp ℝ 2 (radialHilbertMeasure D) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv).adjoint

theorem norm_innerLiouvilleSource_le :
    ‖innerLiouvilleSource D hab hlam hR hs hp hcore hw U hU hv‖ ≤ Real.sqrt 12 * U := by
  unfold innerLiouvilleSource
  rw [LinearIsometryEquiv.norm_map]
  exact norm_innerLiouvilleFieldLift_le D hab hlam hR hs hp hcore hw U hU hv

theorem innerLiouvilleSource_inner
    (F : Lp ℝ 2 (radialHilbertMeasure D)) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ⟪innerLiouvilleSource D hab hlam hR hs hp hcore hw U hU hv F, f⟫_ℝ =
      ⟪F, innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

/-- The single central scalar is carried without rescaling. -/
def innerLiouvillePairLift :
    (Lp ℝ 2 (volume : Measure ℝ) × ℝ) →L[ℝ] (Lp ℝ 2 (radialHilbertMeasure D) × ℝ) :=
  (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv).prodMap
    (ContinuousLinearMap.id ℝ ℝ)

def innerLiouvillePairSource :
    (Lp ℝ 2 (radialHilbertMeasure D) × ℝ) →L[ℝ] (Lp ℝ 2 (volume : Measure ℝ) × ℝ) :=
  (innerLiouvilleSource D hab hlam hR hs hp hcore hw U hU hv).prodMap
    (ContinuousLinearMap.id ℝ ℝ)

theorem innerLiouvillePairLift_apply (f : Lp ℝ 2 (volume : Measure ℝ) × ℝ) :
    innerLiouvillePairLift D hab hlam hR hs hp hcore hw U hU hv f =
      (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f.1, f.2) := by
  unfold innerLiouvillePairLift
  simp only [ContinuousLinearMap.coe_prodMap', Prod.map_apply', ContinuousLinearMap.id_apply]

theorem innerLiouvillePairSource_apply (F : Lp ℝ 2 (radialHilbertMeasure D) × ℝ) :
    innerLiouvillePairSource D hab hlam hR hs hp hcore hw U hU hv F =
      (innerLiouvilleSource D hab hlam hR hs hp hcore hw U hU hv F.1, F.2) := by
  unfold innerLiouvillePairSource
  simp only [ContinuousLinearMap.coe_prodMap', Prod.map_apply', ContinuousLinearMap.id_apply]

private theorem norm_prodMap_id_le {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C) (hA : ‖A‖ ≤ C) :
    ‖A.prodMap (ContinuousLinearMap.id ℝ ℝ)‖ ≤ max C 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ ((by norm_num : (0 : ℝ) ≤ 1).trans
    (le_max_right C 1))
  rintro ⟨f, c⟩
  simp only [ContinuousLinearMap.coe_prodMap', Prod.map_apply', ContinuousLinearMap.id_apply,
    Prod.norm_def]
  apply max_le
  · calc
      ‖A f‖ ≤ C * ‖f‖ :=
        (A.le_opNorm f).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg f))
      _ ≤ max C 1 * max ‖f‖ ‖c‖ :=
        mul_le_mul (le_max_left C 1) (le_max_left ‖f‖ ‖c‖)
          (norm_nonneg f) (hC.trans (le_max_left C 1))
  · calc
      ‖c‖ = 1 * ‖c‖ := (one_mul _).symm
      _ ≤ max C 1 * max ‖f‖ ‖c‖ :=
        mul_le_mul (le_max_right C 1) (le_max_right ‖f‖ ‖c‖)
          (norm_nonneg c) (hC.trans (le_max_left C 1))

theorem norm_innerLiouvillePairLift_le :
    ‖innerLiouvillePairLift D hab hlam hR hs hp hcore hw U hU hv‖ ≤
      max (Real.sqrt 12 * U) 1 :=
  norm_prodMap_id_le _ (mul_nonneg (Real.sqrt_nonneg 12) hU)
    (norm_innerLiouvilleFieldLift_le D hab hlam hR hs hp hcore hw U hU hv)

theorem norm_innerLiouvillePairSource_le :
    ‖innerLiouvillePairSource D hab hlam hR hs hp hcore hw U hU hv‖ ≤
      max (Real.sqrt 12 * U) 1 :=
  norm_prodMap_id_le _ (mul_nonneg (Real.sqrt_nonneg 12) hU)
    (norm_innerLiouvilleSource_le D hab hlam hR hs hp hcore hw U hU hv)

/-- The same model inverse is transported on both sides; there is only
one scalar coordinate, including for the central bordered block. -/
def innerLiouvillePhysicalDirichlet
    (G : (Lp ℝ 2 (volume : Measure ℝ) × ℝ) →L[ℝ] (Lp ℝ 2 (volume : Measure ℝ) × ℝ)) :
    (Lp ℝ 2 (radialHilbertMeasure D) × ℝ) →L[ℝ]
      (Lp ℝ 2 (radialHilbertMeasure D) × ℝ) :=
  (innerLiouvillePairLift D hab hlam hR hs hp hcore hw U hU hv).comp
    (G.comp (innerLiouvillePairSource D hab hlam hR hs hp hcore hw U hU hv))

theorem innerLiouvillePhysicalDirichlet_apply
    (G : (Lp ℝ 2 (volume : Measure ℝ) × ℝ) →L[ℝ] (Lp ℝ 2 (volume : Measure ℝ) × ℝ))
    (F : Lp ℝ 2 (radialHilbertMeasure D) × ℝ) :
    innerLiouvillePhysicalDirichlet D hab hlam hR hs hp hcore hw U hU hv G F =
      (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv
          (G (innerLiouvilleSource D hab hlam hR hs hp hcore hw U hU hv F.1, F.2)).1,
        (G (innerLiouvilleSource D hab hlam hR hs hp hcore hw U hU hv F.1, F.2)).2) := by
  unfold innerLiouvillePhysicalDirichlet
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    innerLiouvillePairSource_apply, innerLiouvillePairLift_apply]

theorem norm_innerLiouvillePhysicalDirichlet_le
    (G : (Lp ℝ 2 (volume : Measure ℝ) × ℝ) →L[ℝ] (Lp ℝ 2 (volume : Measure ℝ) × ℝ)) :
    ‖innerLiouvillePhysicalDirichlet D hab hlam hR hs hp hcore hw U hU hv G‖ ≤
      (max (Real.sqrt 12 * U) 1) ^ 2 * ‖G‖ := by
  let C := max (Real.sqrt 12 * U) 1
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  unfold innerLiouvillePhysicalDirichlet
  calc
    _ ≤ ‖innerLiouvillePairLift D hab hlam hR hs hp hcore hw U hU hv‖ *
        ‖G.comp (innerLiouvillePairSource D hab hlam hR hs hp hcore hw U hU hv)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * (‖G‖ * ‖innerLiouvillePairSource D hab hlam hR hs hp hcore hw U hU hv‖) :=
      mul_le_mul (norm_innerLiouvillePairLift_le D hab hlam hR hs hp hcore hw U hU hv)
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) hC
    _ ≤ C * (‖G‖ * C) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (norm_innerLiouvillePairSource_le D hab hlam hR hs hp hcore hw U hU hv)
          (norm_nonneg G)) hC
    _ = _ := by dsimp only [C]; ring

end Physical

end ContinuousFlexibility.Radial
