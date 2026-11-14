module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Restriction and zero extension in actual `L²` spaces

These operators retain the original measure normalization. Restriction is
contractive, zero extension from a restricted measure is isometric, and
their inverse identity is proved for the actual almost-everywhere classes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (s : Set α) (hs : MeasurableSet s)

private def spacesLpZeroExtensionFun (u : Lp E 2 (μ.restrict s)) : Lp E 2 μ :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp u)).toLp (s.indicator u)

omit [NormedSpace ℝ E] in
private theorem spacesLpZeroExtensionFun_ae (u : Lp E 2 (μ.restrict s)) :
    (spacesLpZeroExtensionFun μ s hs u : α → E) =ᵐ[μ] s.indicator u :=
  MemLp.coeFn_toLp _

omit [NormedSpace ℝ E] in
private theorem spacesLpZeroExtensionFun_norm (u : Lp E 2 (μ.restrict s)) :
    ‖spacesLpZeroExtensionFun μ s hs u‖ = ‖u‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (spacesLpZeroExtensionFun_ae μ s hs u),
    eLpNorm_indicator_eq_eLpNorm_restrict hs, Lp.norm_def]

/-- Extension by zero from a measurable subset preserves the actual `L²` norm. -/
def spacesLpZeroExtension : Lp E 2 (μ.restrict s) →ₗᵢ[ℝ] Lp E 2 μ where
  toFun := spacesLpZeroExtensionFun μ s hs
  map_add' := by
    intro u v
    apply Lp.ext
    have huv := (ae_restrict_iff' hs).mp (Lp.coeFn_add u v)
    filter_upwards [spacesLpZeroExtensionFun_ae μ s hs (u + v),
      spacesLpZeroExtensionFun_ae μ s hs u, spacesLpZeroExtensionFun_ae μ s hs v,
      Lp.coeFn_add (spacesLpZeroExtensionFun μ s hs u) (spacesLpZeroExtensionFun μ s hs v), huv]
      with x hout hu hv hadd hin
    rw [hout, hadd]
    simp only [Pi.add_apply]
    rw [hu, hv]
    by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx]
      exact hin hx
    · simp only [indicator_of_notMem hx, add_zero]
  map_smul' := by
    intro c u
    apply Lp.ext
    have hcu := (ae_restrict_iff' hs).mp (Lp.coeFn_smul c u)
    filter_upwards [spacesLpZeroExtensionFun_ae μ s hs (c • u),
      spacesLpZeroExtensionFun_ae μ s hs u,
      Lp.coeFn_smul c (spacesLpZeroExtensionFun μ s hs u), hcu] with x hout hu hsmul hin
    simp only [RingHom.id_apply]
    rw [hout, hsmul]
    simp only [Pi.smul_apply]
    rw [hu]
    by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx]
      exact hin hx
    · simp only [indicator_of_notMem hx, smul_zero]
  norm_map' := spacesLpZeroExtensionFun_norm μ s hs

theorem spacesLpZeroExtension_ae (u : Lp E 2 (μ.restrict s)) :
    (spacesLpZeroExtension μ s hs u : α → E) =ᵐ[μ] s.indicator u :=
  spacesLpZeroExtensionFun_ae μ s hs u

theorem spacesLpZeroExtension_norm (u : Lp E 2 (μ.restrict s)) :
    ‖spacesLpZeroExtension μ s hs u‖ = ‖u‖ :=
  (spacesLpZeroExtension μ s hs).norm_map u

omit hs in
/-- The actual restriction map between the `L²` spaces. -/
def spacesLpRestrict : Lp E 2 μ →L[ℝ] Lp E 2 (μ.restrict s) :=
  Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa only [one_smul] using (Measure.restrict_le_self : μ.restrict s ≤ μ))

omit hs in
theorem spacesLpRestrict_ae (u : Lp E 2 μ) :
    (spacesLpRestrict μ s u : α → E) =ᵐ[μ.restrict s] u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u

omit hs in
theorem spacesLpRestrict_norm_le (u : Lp E 2 μ) : ‖spacesLpRestrict μ s u‖ ≤ ‖u‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (spacesLpRestrict_ae μ s u), Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp u).eLpNorm_ne_top
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- Zero extension is a right inverse of restriction. -/
theorem spacesLpRestrict_zeroExtension (u : Lp E 2 (μ.restrict s)) :
    spacesLpRestrict μ s (spacesLpZeroExtension μ s hs u) = u := by
  apply Lp.ext
  have he := (spacesLpZeroExtension_ae μ s hs u).filter_mono
    (ae_mono (Measure.restrict_le_self : μ.restrict s ≤ μ))
  filter_upwards [spacesLpRestrict_ae μ s (spacesLpZeroExtension μ s hs u), he,
    ae_restrict_mem hs] with x hx he hsx
  exact hx.trans (he.trans (indicator_of_mem hsx u))

theorem spacesLpZeroExtension_restrict_ae (u : Lp E 2 μ) :
    (spacesLpZeroExtension μ s hs (spacesLpRestrict μ s u) : α → E) =ᵐ[μ] s.indicator u := by
  have hi := (ae_restrict_iff' hs).mp (spacesLpRestrict_ae μ s u)
  filter_upwards [spacesLpZeroExtension_ae μ s hs (spacesLpRestrict μ s u), hi] with x hx hi
  rw [hx]
  by_cases hsx : x ∈ s
  · simp only [indicator_of_mem hsx]
    exact hi hsx
  · simp only [indicator_of_notMem hsx]

end ContinuousFlexibility.Analysis
