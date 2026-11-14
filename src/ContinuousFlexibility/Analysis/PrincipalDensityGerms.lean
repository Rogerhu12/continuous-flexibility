module

public import ContinuousFlexibility.Analysis.PrincipalDensityBoundaryJets
public import ContinuousFlexibility.Analysis.CanonicalFieldJetReduction
public import ContinuousFlexibility.Analysis.BoundaryJetClosure
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Principal-density germs and one-sided boundary equations

The density uses actual first derivatives of the coordinate map.
Equality of coordinate and height germs therefore gives equality of
density germs. An actual normal-form equation on only one open side
then determines the boundary jets of every field with those germs.
The equation is never asserted on the other side of the boundary.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- One selector gives actual smoothness for each principal component. -/
theorem contDiffAt_coordinatePrincipalDensity_component
    {A : SymmetricCoefficients} {F : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {p : PolarPoint}
    (hAa : ContDiffAt ℝ ∞ A.a p) (hAb : ContDiffAt ℝ ∞ A.b p)
    (hAc : ContDiffAt ℝ ∞ A.c p) (hF : ContDiffAt ℝ ∞ F p)
    (hh : ContDiffAt ℝ ∞ h p) (hJ : planeJacobian F p ≠ 0)
    (i : Fin 3) :
    ContDiffAt ℝ ∞
      (canonicalCoefficientComponent i (coordinatePrincipalDensity A F h)) p := by
  have hs := contDiffAt_coordinatePrincipalDensity hAa hAb hAc hF hh hJ
  unfold canonicalCoefficientComponent
  split_ifs
  · exact hs.1
  · exact hs.2.1
  · exact hs.2.2

/-- Locality of the actual Fréchet derivative gives density locality.
No smoothness outside the germ is required. -/
theorem coordinatePrincipalDensity_component_eventuallyEq
    {A : SymmetricCoefficients} {F G : PolarPoint → PolarPoint}
    {h g : PolarPoint → ℝ} {p : PolarPoint}
    (hF : F =ᶠ[𝓝 p] G) (hh : h =ᶠ[𝓝 p] g) (i : Fin 3) :
    canonicalCoefficientComponent i (coordinatePrincipalDensity A F h) =ᶠ[𝓝 p]
      canonicalCoefficientComponent i (coordinatePrincipalDensity A G g) := by
  have hD : fderiv ℝ F =ᶠ[𝓝 p] fderiv ℝ G := hF.fderiv (𝕜 := ℝ)
  filter_upwards [hD, hh] with q hq hheight
  unfold canonicalCoefficientComponent
  split_ifs <;>
    simp only [coordinatePrincipalDensity, planeJacobian, hq, hheight]

/-- The normal form is evaluated at the corresponding actual chart. -/
theorem coordinatePrincipalRemainder_eventuallyEq
    {A : SymmetricCoefficients} {F G : PolarPoint → PolarPoint}
    {h g : PolarPoint → ℝ} {p : PolarPoint}
    (hF : F =ᶠ[𝓝 p] G) (hh : h =ᶠ[𝓝 p] g)
    (N : ℝ → ℝ) (i : Fin 3) :
    (fun q => canonicalCoefficientComponent i (coordinatePrincipalDensity A F h) q -
      N ((F q).1)) =ᶠ[𝓝 p]
    (fun q => canonicalCoefficientComponent i (coordinatePrincipalDensity A G g) q -
      N ((G q).1)) := by
  filter_upwards [coordinatePrincipalDensity_component_eventuallyEq hF hh i, hF]
    with q hρ hchart
  rw [hρ, hchart]

/-- An actual one-sided normal form and genuine matching germs force
every finite radial boundary jet of the new remainder to vanish.
The new chart is not required to satisfy the equation on its side. -/
theorem radialBoundaryJet_principalRemainder_eq_zero_of_germs
    {A : SymmetricCoefficients} {F G : PolarPoint → PolarPoint}
    {h g : PolarPoint → ℝ} {c θ : ℝ} {V : Set PolarPoint}
    (hV : IsOpen V) (hclosure : (c, θ) ∈ closure V)
    (hAa : ContDiffAt ℝ ∞ A.a (c, θ))
    (hAb : ContDiffAt ℝ ∞ A.b (c, θ))
    (hAc : ContDiffAt ℝ ∞ A.c (c, θ))
    (hG : ContDiffAt ℝ ∞ G (c, θ))
    (hg : ContDiffAt ℝ ∞ g (c, θ))
    (hJ : planeJacobian G (c, θ) ≠ 0)
    (hFmatch : F =ᶠ[𝓝 (c, θ)] G) (hhmatch : h =ᶠ[𝓝 (c, θ)] g)
    {N : ℝ → ℝ} (hN : ContDiff ℝ ∞ N) (i : Fin 3)
    (hroot : EqOn (canonicalCoefficientComponent i (coordinatePrincipalDensity A G g))
      (fun q => N ((G q).1)) V) (k : ℕ) :
    radialBoundaryJet
      (fun q => canonicalCoefficientComponent i (coordinatePrincipalDensity A F h) q -
        N ((F q).1)) c k θ = 0 := by
  let ρ := canonicalCoefficientComponent i (coordinatePrincipalDensity A G g)
  have hρ : ContDiffAt ℝ ∞ ρ (c, θ) :=
    contDiffAt_coordinatePrincipalDensity_component hAa hAb hAc hG hg hJ i
  have hNG : ContDiffAt ℝ ∞ (fun q => N ((G q).1)) (c, θ) :=
    hN.contDiffAt.comp (c, θ) hG.fst
  have hnormal : radialBoundaryJet ρ c k θ =
      radialBoundaryJet (fun q => N ((G q).1)) c k θ := by
    simpa only [radialBoundaryJet, mixedDerivative, iteratedDeriv_zero] using
      mixedDerivative_eq_at_closure_of_contDiffAt hV hρ hNG hroot hclosure k 0
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) c :=
    contDiffAt_id.prodMk contDiffAt_const
  have hsρ : ContDiffAt ℝ ∞ (fun r => ρ (r, θ)) c := hρ.comp c hline
  have hsN : ContDiffAt ℝ ∞ (fun r => N ((G (r, θ)).1)) c :=
    ContDiffAt.comp (f := fun r : ℝ => (r, θ))
      (g := fun p : PolarPoint => N ((G p).1)) c hNG hline
  have hz : iteratedDeriv k (fun r => ρ (r, θ) - N ((G (r, θ)).1)) c = 0 := by
    rw [iteratedDeriv_fun_sub
      (hsρ.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
      (hsN.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))]
    change radialBoundaryJet ρ c k θ -
      radialBoundaryJet (fun q => N ((G q).1)) c k θ = 0
    rw [hnormal, sub_self]
  have hrem := coordinatePrincipalRemainder_eventuallyEq (A := A) hFmatch hhmatch N i
  have hs := hrem.comp_tendsto hline.continuousAt
  exact ((hs.iteratedDeriv k).eq_of_nhds).trans hz

end ContinuousFlexibility.Analysis

