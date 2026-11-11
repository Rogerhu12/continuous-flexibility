import ContinuousFlexibility.Radial.ModeRegionSources
import ContinuousFlexibility.Radial.ModeRegionalPairing

/-!
# Pairings for the constructed inner source restriction

These localization identities use the actual indicator projection,
without assuming the matching object whose existence is being proved.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace
open ContinuousFlexibility.Statements

theorem modeInnerSource_idempotent (D : ReferenceData) (l h : ℝ)
    (F : RadialModePair D) :
    modeInnerSource D l h (modeInnerSource D l h F) = modeInnerSource D l h F := by
  apply Prod.ext
  · exact modeRegionVector_idempotent D (Ioo l h) measurableSet_Ioo F.1
  · rfl

/-- An actual inner source localizes every product with its representative. -/
theorem modeInnerSource_integral_fixed {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {l h : ℝ} (hlh : l ≤ h)
    (hsub : Icc l h ⊆ radialCore D) (F : RadialModePair D)
    (hfix : modeInnerSource D l h F = F) (q : ℝ → ℝ) :
    (∫ r in D.a..D.b, q r * F.1 r) = ∫ r in l..h, q r * F.1 r := by
  classical
  let f : ℝ → ℝ := (Ioo l h).indicator (fun r => q r * F.1 r)
  have hs : (F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => if r ∈ Ioo l h then F.1 r else 0) := by
    simpa only [hfix] using (modeRegionSources_spec D l h F).2.2.1
  have he : (fun r => q r * F.1 r) =ᵐ[radialHilbertMeasure D] f := by
    filter_upwards [hs] with r hr
    by_cases hi : r ∈ Ioo l h
    · simp only [f, Set.indicator_of_mem hi]
    · rw [if_neg hi] at hr
      simp only [f, Set.indicator_of_notMem hi, hr, mul_zero]
  have hf : Function.support f ⊆ Ioo l h := by
    intro r hr
    by_contra hn
    exact hr (Set.indicator_of_notMem hn _)
  calc
    _ = ∫ r in D.a..D.b, f r := matchingInterval_congr_ae hD he
    _ = ∫ r in l..h, f r :=
      matchingInterval_eq_subinterval (Ioo_subset_Icc_self.trans hsub) hf
    _ = _ := by
      simp only [intervalIntegral.integral_of_le hlh, integral_Ioc_eq_integral_Ioo]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact Set.indicator_of_mem hr _

theorem modeInnerSource_pairing_eq_integral {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {l h : ℝ} (hlh : l ≤ h)
    (hsub : Icc l h ⊆ radialCore D) (U F : RadialModePair D)
    (hfix : modeInnerSource D l h F = F) (hscalar : F.2 = 0)
    {u : ℝ → ℝ} (hrep : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u) :
    modePairing D U F = ∫ r in l..h, matchingDensity D r * u r * F.1 r := by
  rw [modePairing, hscalar, mul_zero, add_zero, matchingMode_inner_eq_integral hD]
  rw [modeInnerSource_integral_fixed hD hlh hsub F hfix
    (fun r => matchingDensity D r * U.1 r)]
  apply matchingSubinterval_congr_ae hD hlh hsub
  filter_upwards [hrep] with r hr
  rw [hr]

/-- The pair product is bilinear in its actual L2 vector and scalar. -/
theorem modePairing_sub_left {D : ReferenceData} (U V F : RadialModePair D) :
    modePairing D (U - V) F = modePairing D U F - modePairing D V F := by
  simp only [modePairing, Prod.fst_sub, Prod.snd_sub, inner_sub_left]
  ring

end ContinuousFlexibility.Radial
