module

public import ContinuousFlexibility.Radial.ModeCompactLocal
public import ContinuousFlexibility.Radial.WeakGreenWithin

/-!
# Finite Green identities for actual modal weak solutions

These identities apply on any compact subinterval of the radial core,
including intervals whose endpoints are matching cuts. Representatives
only need C1 or C2 regularity within the displayed closed interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- A representative of a modal weak solution inherits the principal
distributional equation on each compact interior interval. -/
theorem modeLocalEquation_representative_principal_on_compact
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {j : ℕ} {J : Set ℝ} {U F : RadialModePair D}
    (hEq : ModeLocalEquation D j J U F)
    {u : ℝ → ℝ} (hrep : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    {l h : ℝ} (hlh : l ≤ h) (hsub : Icc l h ⊆ radialCore D)
    (hJ : Ioo l h ⊆ J) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo l h) :
    (∫ x in l..h, u x * deriv (fun y => D.w y * deriv ψ y) x) =
      ∫ x in l..h, matchingPrincipalSource D j U F x * ψ x := by
  have hrep' : (U.1 : ℝ → ℝ) =ᵐ[volume.restrict (Icc l h)] u :=
    ae_restrict_of_ae_restrict_of_subset hsub
      ((radialHilbertMeasure_ae_iff hD).mp hrep)
  have hrep'' := (ae_restrict_iff' measurableSet_Icc).mp hrep'
  calc
    _ = ∫ x in l..h, U.1 x * deriv (fun y => D.w y * deriv ψ y) x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hrep''] with x hx hxi
      have hxI : x ∈ Icc l h := by
        simpa only [uIcc_of_le hlh] using uIoc_subset_uIcc hxi
      rw [hx hxI]
    _ = _ := modeLocalEquation_principal_on_compact hD hB hEq hlh hsub hJ hψ hcψ hψs

/-- The actual modal equation paired with an arbitrary C2 test on a
compact interval. All boundary derivatives are one-sided within-derivatives. -/
theorem modeLocalEquation_green_on_compact
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {j : ℕ} {J : Set ℝ} {U F : RadialModePair D}
    (hEq : ModeLocalEquation D j J U F)
    {u φ : ℝ → ℝ} (hrep : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    {l h : ℝ} (hlh : l < h) (hsub : Icc l h ⊆ radialCore D)
    (hJ : Ioo l h ⊆ J)
    (hu : ContDiffOn ℝ 1 u (Icc l h))
    (hφ : ContDiffOn ℝ 2 φ (Icc l h)) :
    (∫ x in l..h, u x * radialJacobi ((j : ℝ) ^ 2) D.w φ x -
      (U.2 * referenceColumn D x - matchingDensity D x * F.1 x) * φ x) =
      (u h * (D.w h * derivWithin φ (Icc l h) h) -
        φ h * (D.w h * derivWithin u (Icc l h) h)) -
      (u l * (D.w l * derivWithin φ (Icc l h) l) -
        φ l * (D.w l * derivWithin u (Icc l h) l)) := by
  have hi := integral_radialJacobi_green_of_weak_principal (J := (j : ℝ) ^ 2) hlh hu hφ
    (matchingPrincipalSource_intervalIntegrable hD hB j U F hlh.le hsub)
    (matchingProfileGeometry hD).2.2.1.1
    (fun ψ hψ hcψ hψs =>
      modeLocalEquation_representative_principal_on_compact hD hB hEq hrep
        hlh.le hsub hJ hψ hcψ hψs)
  have hrep' : (U.1 : ℝ → ℝ) =ᵐ[volume.restrict (Icc l h)] u :=
    ae_restrict_of_ae_restrict_of_subset hsub
      ((radialHilbertMeasure_ae_iff hD).mp hrep)
  have hrep'' := (ae_restrict_iff' measurableSet_Icc).mp hrep'
  calc
    _ = ∫ x in l..h, u x * radialJacobi ((j : ℝ) ^ 2) D.w φ x -
        (matchingPrincipalSource D j U F x -
          (j : ℝ) ^ 2 * deriv D.w x / x * u x) * φ x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hrep''] with x hx hxi
      have hxI : x ∈ Icc l h := by
        simpa only [uIcc_of_le hlh.le] using uIoc_subset_uIcc hxi
      dsimp only [matchingPrincipalSource, matchingPotential]
      rw [hx hxI]
      ring
    _ = _ := hi

/-- Green's identity between two actual modal weak solutions. The
zeroth-order potential cancels without a pointwise Jacobi equation or
second classical derivatives of either representative. -/
theorem modeLocalEquation_green_pair_on_compact
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {j : ℕ} {J : Set ℝ} {U F V G : RadialModePair D}
    (hEqU : ModeLocalEquation D j J U F)
    (hEqV : ModeLocalEquation D j J V G)
    {u v : ℝ → ℝ}
    (hrepU : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    (hrepV : (V.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] v)
    {l h : ℝ} (hlh : l < h) (hsub : Icc l h ⊆ radialCore D)
    (hJ : Ioo l h ⊆ J)
    (hu : ContDiffOn ℝ 1 u (Icc l h))
    (hv : ContDiffOn ℝ 1 v (Icc l h)) :
    (∫ x in l..h,
      u x * (V.2 * referenceColumn D x - matchingDensity D x * G.1 x) -
        v x * (U.2 * referenceColumn D x - matchingDensity D x * F.1 x)) =
      (u h * (D.w h * derivWithin v (Icc l h) h) -
        v h * (D.w h * derivWithin u (Icc l h) h)) -
      (u l * (D.w l * derivWithin v (Icc l h) l) -
        v l * (D.w l * derivWithin u (Icc l h) l)) := by
  have hi := integral_green_of_weak_principal hlh hu hv
    (matchingPrincipalSource_intervalIntegrable hD hB j U F hlh.le hsub)
    (matchingPrincipalSource_intervalIntegrable hD hB j V G hlh.le hsub)
    (matchingProfileGeometry hD).2.2.1.1
    (fun ψ hψ hcψ hψs =>
      modeLocalEquation_representative_principal_on_compact hD hB hEqU hrepU
        hlh.le hsub hJ hψ hcψ hψs)
    (fun ψ hψ hcψ hψs =>
      modeLocalEquation_representative_principal_on_compact hD hB hEqV hrepV
        hlh.le hsub hJ hψ hcψ hψs)
  have hrepU' : (U.1 : ℝ → ℝ) =ᵐ[volume.restrict (Icc l h)] u :=
    ae_restrict_of_ae_restrict_of_subset hsub
      ((radialHilbertMeasure_ae_iff hD).mp hrepU)
  have hrepV' : (V.1 : ℝ → ℝ) =ᵐ[volume.restrict (Icc l h)] v :=
    ae_restrict_of_ae_restrict_of_subset hsub
      ((radialHilbertMeasure_ae_iff hD).mp hrepV)
  have hrepU'' := (ae_restrict_iff' measurableSet_Icc).mp hrepU'
  have hrepV'' := (ae_restrict_iff' measurableSet_Icc).mp hrepV'
  calc
    _ = ∫ x in l..h,
        u x * matchingPrincipalSource D j V G x -
          v x * matchingPrincipalSource D j U F x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hrepU'', hrepV''] with x hxU hxV hxi
      have hxI : x ∈ Icc l h := by
        simpa only [uIcc_of_le hlh.le] using uIoc_subset_uIcc hxi
      dsimp only [matchingPrincipalSource]
      rw [hxU hxI, hxV hxI]
      ring
    _ = _ := hi

end ContinuousFlexibility.Radial
