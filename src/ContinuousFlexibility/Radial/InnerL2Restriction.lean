import ContinuousFlexibility.Radial.InnerRadialL2Mass
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Restriction and its actual zero extension in real L²

Restriction uses mathlib's existing continuous linear map. Its Hilbert
adjoint is proved to be extension by zero. These maps connect a retained
cell to the same ambient physical measure without changing that measure.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open MeasureTheory Set Filter
open scoped RealInnerProductSpace InnerProductSpace

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)

theorem innerL2Restriction_norm_apply_le (f : Lp ℝ 2 μ) :
    ‖LpToLpRestrictCLM α ℝ ℝ μ 2 s f‖ ≤ ‖f‖ := by
  have he : LpToLpRestrictCLM α ℝ ℝ μ 2 s f =
      ((Lp.memLp f).restrict s).toLp f := by
    apply Lp.ext
    exact (LpToLpRestrictCLM_coeFn ℝ s f).trans
      (MemLp.coeFn_toLp ((Lp.memLp f).restrict s)).symm
  rw [he]
  exact norm_Lp_toLp_restrict_le s f

theorem norm_innerL2Restriction_le_one :
    ‖LpToLpRestrictCLM α ℝ ℝ μ 2 s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simpa only [one_mul] using innerL2Restriction_norm_apply_le μ s f

/-- The zero extension is the adjoint of the existing restriction map. -/
def innerL2ZeroExtension : Lp ℝ 2 (μ.restrict s) →L[ℝ] Lp ℝ 2 μ :=
  (LpToLpRestrictCLM α ℝ ℝ μ 2 s).adjoint

theorem innerL2ZeroExtension_adjoint :
    (innerL2ZeroExtension μ s).adjoint = LpToLpRestrictCLM α ℝ ℝ μ 2 s := by
  unfold innerL2ZeroExtension
  exact ContinuousLinearMap.adjoint_adjoint _

theorem norm_innerL2ZeroExtension_le_one : ‖innerL2ZeroExtension μ s‖ ≤ 1 := by
  unfold innerL2ZeroExtension
  rw [LinearIsometryEquiv.norm_map]
  exact norm_innerL2Restriction_le_one μ s

/-- The adjoint has the genuine indicator representative, with no
choice of an off-set representative left in the result. -/
theorem innerL2ZeroExtension_ae (hs : MeasurableSet s) (f : Lp ℝ 2 (μ.restrict s)) :
    (innerL2ZeroExtension μ s f : α → ℝ) =ᵐ[μ] s.indicator f := by
  have hmem : MemLp (s.indicator f) 2 μ :=
    (memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)
  let z : Lp ℝ 2 μ := hmem.toLp (s.indicator f)
  have hz : (z : α → ℝ) =ᵐ[μ] s.indicator f := MemLp.coeFn_toLp hmem
  have he : innerL2ZeroExtension μ s f = z := by
    apply ext_inner_right ℝ
    intro g
    unfold innerL2ZeroExtension
    rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def, L2.inner_def]
    calc
      _ = ∫ x in s, ⟪f x, g x⟫_ℝ ∂μ := by
        apply integral_congr_ae
        filter_upwards [LpToLpRestrictCLM_coeFn ℝ s g] with x hx
        rw [hx]
      _ = ∫ x, s.indicator (fun y => ⟪f y, g y⟫_ℝ) x ∂μ :=
        (integral_indicator hs).symm
      _ = ∫ x, ⟪s.indicator f x, g x⟫_ℝ ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ s
        · rw [indicator_of_mem hx, indicator_of_mem hx]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, inner_zero_left]
      _ = ∫ x, ⟪z x, g x⟫_ℝ ∂μ := by
        apply integral_congr_ae
        filter_upwards [hz] with x hx
        rw [hx]
  rw [he]
  exact hz

theorem innerL2Restriction_zeroExtension (hs : MeasurableSet s)
    (f : Lp ℝ 2 (μ.restrict s)) :
    LpToLpRestrictCLM α ℝ ℝ μ 2 s (innerL2ZeroExtension μ s f) = f := by
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ s (innerL2ZeroExtension μ s f),
    ae_restrict_of_ae (innerL2ZeroExtension_ae μ s hs f),
    ae_restrict_mem hs] with x hrestrict hext hx
  rw [hrestrict, hext, indicator_of_mem hx]

theorem innerL2ZeroExtension_norm (hs : MeasurableSet s)
    (f : Lp ℝ 2 (μ.restrict s)) :
    ‖innerL2ZeroExtension μ s f‖ = ‖f‖ := by
  apply le_antisymm
  · calc
      _ ≤ ‖innerL2ZeroExtension μ s‖ * ‖f‖ :=
        (innerL2ZeroExtension μ s).le_opNorm f
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
        (norm_innerL2ZeroExtension_le_one μ s) (norm_nonneg f)
      _ = ‖f‖ := one_mul _
  · calc
      ‖f‖ = ‖LpToLpRestrictCLM α ℝ ℝ μ 2 s (innerL2ZeroExtension μ s f)‖ := by
        rw [innerL2Restriction_zeroExtension μ s hs f]
      _ ≤ ‖innerL2ZeroExtension μ s f‖ :=
        innerL2Restriction_norm_apply_le μ s _

theorem innerL2ZeroExtension_restriction_ae (hs : MeasurableSet s) (f : Lp ℝ 2 μ) :
    (innerL2ZeroExtension μ s (LpToLpRestrictCLM α ℝ ℝ μ 2 s f) : α → ℝ) =ᵐ[μ]
      s.indicator f := by
  filter_upwards [innerL2ZeroExtension_ae μ s hs (LpToLpRestrictCLM α ℝ ℝ μ 2 s f),
    ae_imp_of_ae_restrict (LpToLpRestrictCLM_coeFn ℝ s f)] with x hext hrestrict
  rw [hext]
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, indicator_of_mem hx, hrestrict hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]

end ContinuousFlexibility.Radial
