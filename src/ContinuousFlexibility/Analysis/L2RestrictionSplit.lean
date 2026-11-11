import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The actual L² decomposition across a measurable interface

Restriction and extension by zero give a continuous linear equivalence
between one weighted L² space and the two spaces on a measurable partition.
The product carries its usual maximum norm, so restriction has norm at most
one and gluing has norm at most two.  These maps apply to the actual radial
measure and do not assume that it has finite total mass.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousLinearMap

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Restriction of an L² equivalence class to a measurable part of its measure. -/
def l2Restrict (s : Set X) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (μ.restrict s) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by norm_num)
    (by simpa only [one_smul] using (Measure.restrict_le_self : μ.restrict s ≤ μ))

theorem l2Restrict_coeFn (s : Set X) (f : Lp ℝ 2 μ) :
    (l2Restrict μ s f : X → ℝ) =ᵐ[μ.restrict s] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

theorem norm_l2Restrict_le (s : Set X) : ‖l2Restrict μ s‖ ≤ 1 := by
  simpa only [l2Restrict, ENNReal.toReal_one, Real.one_rpow] using
    (Lp.norm_LpToLpOfMeasureLeSMul_le
      (E := ℝ) (p := 2) (c := 1) (μ := μ.restrict s) (ν := μ)
      (by norm_num) (by simpa only [one_smul] using
        (Measure.restrict_le_self : μ.restrict s ≤ μ)))

private def l2ZeroExtendValue (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 (μ.restrict s)) : Lp ℝ 2 μ :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp
    (s.indicator (f : X → ℝ))

private theorem l2ZeroExtendValue_coeFn (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 (μ.restrict s)) :
    (l2ZeroExtendValue μ s hs f : X → ℝ) =ᵐ[μ] s.indicator (f : X → ℝ) :=
  MemLp.coeFn_toLp _

private theorem l2ZeroExtendValue_norm (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 (μ.restrict s)) : ‖l2ZeroExtendValue μ s hs f‖ = ‖f‖ := by
  rw [l2ZeroExtendValue, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs,
    Lp.norm_def]

private def l2ZeroExtendLinear (s : Set X) (hs : MeasurableSet s) :
    Lp ℝ 2 (μ.restrict s) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := l2ZeroExtendValue μ s hs
  map_add' f g := by
    apply Lp.ext
    filter_upwards [l2ZeroExtendValue_coeFn μ s hs (f + g),
      l2ZeroExtendValue_coeFn μ s hs f, l2ZeroExtendValue_coeFn μ s hs g,
      Lp.coeFn_add (l2ZeroExtendValue μ s hs f) (l2ZeroExtendValue μ s hs g),
      ae_imp_of_ae_restrict (Lp.coeFn_add f g)] with x hfg hf hg hsum hadd
    rw [hfg, hsum, Pi.add_apply, hf, hg]
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx, Pi.add_apply] using hadd hx
    · simp only [indicator_of_notMem hx, add_zero]
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [l2ZeroExtendValue_coeFn μ s hs (a • f),
      l2ZeroExtendValue_coeFn μ s hs f,
      Lp.coeFn_smul a (l2ZeroExtendValue μ s hs f),
      ae_imp_of_ae_restrict (Lp.coeFn_smul a f)] with x haf hf hsmul hscalar
    simp only [RingHom.id_apply]
    rw [haf, hsmul, Pi.smul_apply, hf]
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx, Pi.smul_apply] using hscalar hx
    · simp only [indicator_of_notMem hx, smul_zero]

private theorem l2ZeroExtendLinear_apply (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 (μ.restrict s)) :
    l2ZeroExtendLinear μ s hs f = l2ZeroExtendValue μ s hs f := rfl

/-- Extension by zero, on the actual measure, is an isometric linear map. -/
def l2ZeroExtend (s : Set X) (hs : MeasurableSet s) :
    Lp ℝ 2 (μ.restrict s) →L[ℝ] Lp ℝ 2 μ :=
  (l2ZeroExtendLinear μ s hs).mkContinuous 1 (fun f => by
    rw [l2ZeroExtendLinear_apply, l2ZeroExtendValue_norm, one_mul])

theorem l2ZeroExtend_coeFn (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 (μ.restrict s)) :
    (l2ZeroExtend μ s hs f : X → ℝ) =ᵐ[μ] s.indicator (f : X → ℝ) := by
  rw [l2ZeroExtend, LinearMap.mkContinuous_apply, l2ZeroExtendLinear_apply]
  exact l2ZeroExtendValue_coeFn μ s hs f

theorem norm_l2ZeroExtend_apply (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 (μ.restrict s)) : ‖l2ZeroExtend μ s hs f‖ = ‖f‖ := by
  rw [l2ZeroExtend, LinearMap.mkContinuous_apply, l2ZeroExtendLinear_apply,
    l2ZeroExtendValue_norm]

/-- The two actual restrictions on a measurable partition. -/
def l2Split (s : Set X) :
    Lp ℝ 2 μ →L[ℝ] (Lp ℝ 2 (μ.restrict s) × Lp ℝ 2 (μ.restrict sᶜ)) :=
  (l2Restrict μ s).prod (l2Restrict μ sᶜ)

theorem l2Split_apply (s : Set X) (f : Lp ℝ 2 μ) :
    l2Split μ s f = (l2Restrict μ s f, l2Restrict μ sᶜ f) :=
  prod_apply _ _ _

/-- The sum of the two zero extensions. -/
def l2Glue (s : Set X) (hs : MeasurableSet s) :
    (Lp ℝ 2 (μ.restrict s) × Lp ℝ 2 (μ.restrict sᶜ)) →L[ℝ] Lp ℝ 2 μ :=
  (l2ZeroExtend μ s hs).comp (fst ℝ _ _) +
    (l2ZeroExtend μ sᶜ hs.compl).comp (snd ℝ _ _)

theorem l2Glue_apply (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 (μ.restrict s) × Lp ℝ 2 (μ.restrict sᶜ)) :
    l2Glue μ s hs f = l2ZeroExtend μ s hs f.1 + l2ZeroExtend μ sᶜ hs.compl f.2 := by
  simp only [l2Glue, add_apply, comp_apply, coe_fst', coe_snd']

theorem l2Glue_coeFn (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 (μ.restrict s) × Lp ℝ 2 (μ.restrict sᶜ)) :
    (l2Glue μ s hs f : X → ℝ) =ᵐ[μ]
      fun x => s.indicator (f.1 : X → ℝ) x + sᶜ.indicator (f.2 : X → ℝ) x := by
  rw [l2Glue_apply]
  filter_upwards [Lp.coeFn_add (l2ZeroExtend μ s hs f.1)
      (l2ZeroExtend μ sᶜ hs.compl f.2),
    l2ZeroExtend_coeFn μ s hs f.1, l2ZeroExtend_coeFn μ sᶜ hs.compl f.2]
    with x hx hleft hright
  rw [hx, Pi.add_apply, hleft, hright]

theorem l2Glue_split (s : Set X) (hs : MeasurableSet s) (f : Lp ℝ 2 μ) :
    l2Glue μ s hs (l2Split μ s f) = f := by
  apply Lp.ext
  rw [l2Split_apply]
  filter_upwards [l2Glue_coeFn μ s hs (l2Restrict μ s f, l2Restrict μ sᶜ f),
    ae_imp_of_ae_restrict (l2Restrict_coeFn μ s f),
    ae_imp_of_ae_restrict (l2Restrict_coeFn μ sᶜ f)] with x hx hleft hright
  rw [hx]
  by_cases hxs : x ∈ s
  · simp only [indicator_of_mem hxs, indicator_of_notMem (notMem_compl_iff.mpr hxs),
      hleft hxs, add_zero]
  · have hsc : x ∈ sᶜ := hxs
    simp only [indicator_of_notMem hxs, indicator_of_mem hsc, hright hsc, zero_add]

theorem l2Split_glue (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 (μ.restrict s) × Lp ℝ 2 (μ.restrict sᶜ)) :
    l2Split μ s (l2Glue μ s hs f) = f := by
  rw [l2Split_apply]
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [l2Restrict_coeFn μ s (l2Glue μ s hs f),
      (l2Glue_coeFn μ s hs f).restrict, ae_restrict_mem hs] with x hx hglue hxs
    rw [hx, hglue, indicator_of_mem hxs,
      indicator_of_notMem (notMem_compl_iff.mpr hxs), add_zero]
  · apply Lp.ext
    filter_upwards [l2Restrict_coeFn μ sᶜ (l2Glue μ s hs f),
      (l2Glue_coeFn μ s hs f).restrict, ae_restrict_mem hs.compl] with x hx hglue hxs
    rw [hx, hglue, indicator_of_notMem hxs, indicator_of_mem hxs, zero_add]

/-- The exact decomposition of the ambient Hilbert space. -/
def l2RestrictionSplit (s : Set X) (hs : MeasurableSet s) :
    Lp ℝ 2 μ ≃L[ℝ] (Lp ℝ 2 (μ.restrict s) × Lp ℝ 2 (μ.restrict sᶜ)) where
  toFun := l2Split μ s
  invFun := l2Glue μ s hs
  left_inv := l2Glue_split μ s hs
  right_inv := l2Split_glue μ s hs
  map_add' := map_add (l2Split μ s)
  map_smul' := map_smul (l2Split μ s)
  continuous_toFun := (l2Split μ s).continuous
  continuous_invFun := (l2Glue μ s hs).continuous

theorem norm_l2Split_le (s : Set X) : ‖l2Split μ s‖ ≤ 1 := by
  rw [l2Split, opNorm_prod, Prod.norm_def]
  exact max_le (norm_l2Restrict_le μ s) (norm_l2Restrict_le μ sᶜ)

theorem norm_l2Glue_apply_le (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 (μ.restrict s) × Lp ℝ 2 (μ.restrict sᶜ)) :
    ‖l2Glue μ s hs f‖ ≤ 2 * ‖f‖ := by
  rw [l2Glue_apply]
  calc
    _ ≤ ‖l2ZeroExtend μ s hs f.1‖ + ‖l2ZeroExtend μ sᶜ hs.compl f.2‖ := norm_add_le _ _
    _ = ‖f.1‖ + ‖f.2‖ := by rw [norm_l2ZeroExtend_apply, norm_l2ZeroExtend_apply]
    _ ≤ ‖f‖ + ‖f‖ := add_le_add (le_max_left _ _) (le_max_right _ _)
    _ = 2 * ‖f‖ := by ring

theorem norm_l2Glue_le (s : Set X) (hs : MeasurableSet s) : ‖l2Glue μ s hs‖ ≤ 2 :=
  opNorm_le_bound _ (by norm_num) (norm_l2Glue_apply_le μ s hs)

/-- Transfer an actually constructed block operator to the ambient L² space. -/
def l2GluedOperator (s : Set X) (hs : MeasurableSet s)
    (A : (Lp ℝ 2 (μ.restrict s) × Lp ℝ 2 (μ.restrict sᶜ)) →L[ℝ]
      (Lp ℝ 2 (μ.restrict s) × Lp ℝ 2 (μ.restrict sᶜ))) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (l2Glue μ s hs).comp (A.comp (l2Split μ s))

theorem norm_l2GluedOperator_le (s : Set X) (hs : MeasurableSet s)
    (A : (Lp ℝ 2 (μ.restrict s) × Lp ℝ 2 (μ.restrict sᶜ)) →L[ℝ]
      (Lp ℝ 2 (μ.restrict s) × Lp ℝ 2 (μ.restrict sᶜ))) :
    ‖l2GluedOperator μ s hs A‖ ≤ 2 * ‖A‖ := by
  apply opNorm_le_bound _ (mul_nonneg (by norm_num) (norm_nonneg A))
  intro f
  rw [l2GluedOperator, comp_apply, comp_apply]
  have hsplit : ‖l2Split μ s f‖ ≤ ‖f‖ :=
    ((l2Split μ s).le_opNorm f).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (norm_l2Split_le μ s) (norm_nonneg f))
  calc
    _ ≤ 2 * ‖A (l2Split μ s f)‖ := norm_l2Glue_apply_le μ s hs _
    _ ≤ 2 * (‖A‖ * ‖l2Split μ s f‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) (by norm_num)
    _ ≤ 2 * (‖A‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsplit (norm_nonneg A)) (by norm_num)
    _ = (2 * ‖A‖) * ‖f‖ := (mul_assoc _ _ _).symm

end ContinuousFlexibility.Analysis
