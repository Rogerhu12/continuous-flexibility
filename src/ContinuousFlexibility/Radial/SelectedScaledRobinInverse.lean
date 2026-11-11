import ContinuousFlexibility.Radial.SelectedNaturalRobinInverse
import ContinuousFlexibility.Radial.SelectedTailRadiusWeakEquation
import ContinuousFlexibility.Radial.SelectedNaturalTailTransport

/-!
# The actual Robin inverse after the reference's retained-tail dilation

The prescribed target natural function is pulled back, not reselected.
The pullback has exactly the same full value/flux state when the physical
boundary scale is multiplied by the profile-height factor.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

namespace MorsePhysicalTailBasis

variable {M : MorseChainData} {D E : ReferenceData} {right : Bool} {j start : ℕ}
  {entrance η K cut lam κ β : ℝ}
  (F : MorsePhysicalTailBasis M D right j start entrance η K)

include F in
theorem exists_scaledNaturalInverse
    (hD : IsAccumulatingProfile D) (hE : IsAccumulatingProfile E)
    (hcut : cut ∈ radialCore D) (hentry : entrance ∈ radialCore D)
    (hac : outerTailSign right * cut < outerTailSign right * entrance) (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start entrance η K) right j start)
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K)
    (hκ : 0 < κ) (hβ : 0 < β) (hcutE : κ * cut ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right cut,
      E.w (κ * r) = (β * κ) * D.w r)
    (hprofileCut : E.w (κ * cut) = (β * κ) * D.w cut)
    {V : ℝ → ℝ} (hV : ContDiff ℝ ∞ V)
    (hN : RadialNaturalTail E right j (κ * cut) V)
    (hne : (V (κ * cut), outerTailSign right * E.w (κ * cut) * deriv V (κ * cut) /
      (β * lam)) ≠ 0) :
    let v := outerUnitState (V (κ * cut),
      outerTailSign right * E.w (κ * cut) * deriv V (κ * cut) / (β * lam))
    ∃ R : Lp ℝ 2 ((radialHilbertMeasure E).restrict (radialTailInterval E right (κ * cut))) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure E).restrict (radialTailInterval E right (κ * cut))),
      RadialTailWeakPairing E hE right (κ * cut) j R ∧
        RadialTailRegularResponse E right (κ * cut) (β * lam) v R ∧
        RadialTailCauchyUnique E right (κ * cut) ((j : ℝ) ^ 2) (β * lam) v := by
  let U : ℝ → ℝ := fun r => V (κ * r)
  have hU : ContDiff ℝ ∞ U := hV.comp (contDiff_const.mul contDiff_id)
  have hUscale : radialRadiusScale κ 1 U = V := by
    funext r
    have hcancel : κ * (r / κ) = r := by field_simp [hκ.ne'] <;> ring
    simp only [radialRadiusScale, U, hcancel, one_mul]
  have hUN : RadialNaturalTail D right j cut U := by
    apply (radialNaturalTail_reference_scaled_iff hκ hβ one_ne_zero right hcut hcutE
      hend hprofile).mp
    simpa only [hUscale] using hN
  have hstate : (U cut, outerTailSign right * D.w cut * deriv U cut / lam) =
      (V (κ * cut), outerTailSign right * E.w (κ * cut) * deriv V (κ * cut) / (β * lam)) := by
    have hderiv : deriv U cut = deriv V (κ * cut) * κ := by
      exact ((hV.differentiable (by simp) _).hasDerivAt.comp cut
        (by simpa only [mul_one] using (hasDerivAt_id cut).const_mul κ)).deriv
    apply Prod.ext
    · rfl
    · rw [hderiv, hprofileCut]
      field_simp [hβ.ne', hlam] <;> ring
  obtain ⟨R, hweak, hregular, hunique⟩ := F.exists_radialNaturalInverse hD hcut hentry hac
    hlam hT hphysical hη hK hKinv hU hUN (by rwa [hstate])
  let hm := radialHilbertMeasure_restrict_tail_radiusScale hκ hβ right hcut hcutE hend hprofile
  refine ⟨inverseRadiusOperator hκ.ne' hβ hm R,
    hweak.radiusScale hκ hβ hcut hcutE hend hprofile, ?_, ?_⟩
  · have h := hregular.radiusScale hκ hβ hcut hcutE hend hprofile hprofileCut
    simpa only [hstate] using h
  · have h := hunique.radiusScale hD hκ hβ hcut hcutE hend hprofile
    simpa only [hstate] using h

end MorsePhysicalTailBasis

end ContinuousFlexibility.Radial
