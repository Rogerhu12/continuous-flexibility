module

public import ContinuousFlexibility.Radial.MatchingCutoffTests
public import ContinuousFlexibility.Radial.ModeTestIntegrability
public import ContinuousFlexibility.Radial.ModeCompactLocal
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Gluing the frozen modal weak equation across interior cuts

The test residual is additive on smooth compactly supported tests.
Cutoff decomposition therefore reduces the global frozen weak equation
to the inner and outer equations and two equations in neighborhoods of
the matching cuts. Tests may approach the radial endpoints.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- Linearity in a smooth test, with the derivatives justified explicitly. -/
theorem matching_radialJacobi_add {w ψ φ : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hψ : ContDiff ℝ ∞ ψ)
    (hφ : ContDiff ℝ ∞ φ) (J r : ℝ) :
    radialJacobi J w (fun x => ψ x + φ x) r =
      radialJacobi J w ψ r + radialJacobi J w φ r := by
  have hdψ := (contDiff_infty_iff_deriv.mp hψ).1
  have hdφ := (contDiff_infty_iff_deriv.mp hφ).1
  have hdwψ := (contDiff_infty_iff_deriv.mp
    (hw.mul (contDiff_infty_iff_deriv.mp hψ).2)).1
  have hdwφ := (contDiff_infty_iff_deriv.mp
    (hw.mul (contDiff_infty_iff_deriv.mp hφ).2)).1
  have hd : deriv (fun x => ψ x + φ x) =
      fun x => deriv ψ x + deriv φ x := by
    funext x
    exact deriv_fun_add (hdψ x) (hdφ x)
  simp only [radialJacobi, hd, mul_add]
  rw [deriv_fun_add (hdwψ r) (hdwφ r)]
  ring

/-- The residual of exactly the equation frozen in `ModeLocalEquation`. -/
def matchingModeTestResidual (D : ReferenceData) (j : ℕ)
    (U F : RadialModePair D) (ψ : ℝ → ℝ) : ℝ :=
  (∫ r in D.a..D.b, U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) -
    U.2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r) +
    (∫ r in D.a..D.b, matchingDensity D r * F.1 r * ψ r)

theorem modeLocalEquation_iff_matchingModeTestResidual_zero
    {D : ReferenceData} {j : ℕ} {J : Set ℝ} {U F : RadialModePair D} :
    ModeLocalEquation D j J U F ↔
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        Function.support ψ ⊆ J → matchingModeTestResidual D j U F ψ = 0 := by
  constructor
  · intro h ψ hψ hψc hsupp
    have heq := h ψ hψ hψc hsupp
    unfold matchingModeTestResidual matchingDensity
    linarith only [heq]
  · intro h ψ hψ hψc hsupp
    have heq := h ψ hψ hψc hsupp
    unfold matchingModeTestResidual matchingDensity at heq
    linarith only [heq]

theorem matchingModeTestResidual_add {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {j : ℕ} {U F : RadialModePair D} {ψ φ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hφ : ContDiff ℝ ∞ φ)
    (hψc : HasCompactSupport ψ) (hφc : HasCompactSupport φ) :
    matchingModeTestResidual D j U F (fun x => ψ x + φ x) =
      matchingModeTestResidual D j U F ψ + matchingModeTestResidual D j U F φ := by
  have hw := (matchingProfileGeometry hD).2.2.1.1
  have hJ :
      (∫ r in D.a..D.b,
        U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w (fun x => ψ x + φ x) r) =
      (∫ r in D.a..D.b, U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) +
      (∫ r in D.a..D.b, U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w φ r) := by
    simp only [matching_radialJacobi_add hw hψ hφ, mul_add]
    exact intervalIntegral.integral_add
      (matchingJacobi_intervalIntegrable hD U.1 hψ j)
      (matchingJacobi_intervalIntegrable hD U.1 hφ j)
  have hC :
      (∫ r in D.a..D.b, referenceColumn D r * (ψ r + φ r)) =
      (∫ r in D.a..D.b, referenceColumn D r * ψ r) +
      (∫ r in D.a..D.b, referenceColumn D r * φ r) := by
    simp only [mul_add]
    exact intervalIntegral.integral_add
      (matchingColumn_intervalIntegrable hD hborder hψ.continuous)
      (matchingColumn_intervalIntegrable hD hborder hφ.continuous)
  have hS :
      (∫ r in D.a..D.b, matchingDensity D r * F.1 r * (ψ r + φ r)) =
      (∫ r in D.a..D.b, matchingDensity D r * F.1 r * ψ r) +
      (∫ r in D.a..D.b, matchingDensity D r * F.1 r * φ r) := by
    simp only [mul_add]
    exact intervalIntegral.integral_add
      (matchingSource_intervalIntegrable hD F.1 hψ.continuous hψc)
      (matchingSource_intervalIntegrable hD F.1 hφ.continuous hφc)
  unfold matchingModeTestResidual
  rw [hJ, hC, hS]
  ring

/-- A weak equation on the two sides and in a neighborhood of a cut
implies the frozen weak equation on the entire interval. -/
theorem modeLocalEquation_glue_at_cut {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {j : ℕ} {U F : RadialModePair D} {a u c v b : ℝ}
    (huc : u < c) (hcv : c < v)
    (hL : ModeLocalEquation D j (Ioo a c) U F)
    (hC : ModeLocalEquation D j (Ioo u v) U F)
    (hR : ModeLocalEquation D j (Ioo c b) U F) :
    ModeLocalEquation D j (Ioo a b) U F := by
  apply modeLocalEquation_iff_matchingModeTestResidual_zero.mpr
  intro ψ hψ hψc hψsupp
  obtain ⟨ψL, ψC, ψR, ⟨hLs, hLc, hLsupp⟩, ⟨hCs, hCc, hCsupp⟩,
    ⟨hRs, hRc, hRsupp⟩, heq⟩ :=
    exists_matching_cut_test_decomposition huc hcv hψ hψc hψsupp
  have hzL := modeLocalEquation_iff_matchingModeTestResidual_zero.mp hL
    ψL hLs hLc hLsupp
  have hzC := modeLocalEquation_iff_matchingModeTestResidual_zero.mp hC
    ψC hCs hCc (subset_tsupport ψC |>.trans hCsupp)
  have hzR := modeLocalEquation_iff_matchingModeTestResidual_zero.mp hR
    ψR hRs hRc hRsupp
  rw [heq, matchingModeTestResidual_add hD hborder (hLs.add hCs) hRs (hLc.add hCc) hRc,
    matchingModeTestResidual_add hD hborder hLs hCs hLc hCc, hzL, hzC, hzR]
  ring

/-- The exact global modal weak equation follows from the matching
regions and equations in neighborhoods of the two cuts. The same cut
lemma handles both sides. -/
theorem modeLocalEquation_glue_matchingRegions {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {M : RadialMatchingData D} {j : ℕ} {U F : RadialModePair D}
    {uL vL uR vR : ℝ}
    (huL : uL < M.innerLeft) (hvL : M.innerLeft < vL)
    (huR : uR < M.innerRight) (hvR : M.innerRight < vR)
    (hinner : ModeLocalEquation D j (Ioo M.innerLeft M.innerRight) U F)
    (houter : ModeLocalEquation D j (matchingOuterRegion D M) U F)
    (hleft : ModeLocalEquation D j (Ioo uL vL) U F)
    (hright : ModeLocalEquation D j (Ioo uR vR) U F) :
    ModeLocalEquation D j (radialCore D) U F := by
  have houterL : ModeLocalEquation D j (Ioo D.a M.innerLeft) U F := by
    intro ψ hψ hψc hsupp
    exact houter ψ hψ hψc (fun x hx => Or.inl (hsupp hx))
  have houterR : ModeLocalEquation D j (Ioo M.innerRight D.b) U F := by
    intro ψ hψ hψc hsupp
    exact houter ψ hψ hψc (fun x hx => Or.inr (hsupp hx))
  exact modeLocalEquation_glue_at_cut hD hborder huL hvL houterL hleft
    (modeLocalEquation_glue_at_cut hD hborder huR hvR hinner hright houterR)

end ContinuousFlexibility.Radial
