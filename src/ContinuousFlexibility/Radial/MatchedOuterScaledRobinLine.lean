module

public import ContinuousFlexibility.Radial.SelectedNaturalRobinInverse
public import ContinuousFlexibility.Radial.SelectedNaturalTailTransport

/-!
# The retained natural Robin line of the same quantified pair

The prescribed natural function on the final reference is pulled back by
the actual radius change. Its full normalized state agrees with that
pullback at the original cut. The original natural-line theorem therefore
identifies the Robin row of the supplied homogeneous pair without fixing
a sign for the normalized state.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem MorsePhysicalTailBasis.scaledNatural_robin_iff
    {M : MorseChainData} {D E : ReferenceData} {right : Bool} {j start : ℕ}
    {entrance η K cut lam κ β : ℝ}
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hD : IsAccumulatingProfile D) (hcut : cut ∈ radialCore D)
    (hentry : entrance ∈ radialCore D)
    (hac : outerTailSign right * cut < outerTailSign right * entrance) (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start entrance η K) right j start)
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      F.P (F.ZP lam) F.Q (F.ZQ lam)
      (outerTailSign right * cut) (outerTailSign right * entrance)
      (outerTailSign right * tailPhysicalEndpoint D right))
    (hκ : 0 < κ) (hβ : 0 < β) (hcutE : κ * cut ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right cut,
      E.w (κ * r) = (β * κ) * D.w r)
    (hprofileCut : E.w (κ * cut) = (β * κ) * D.w cut)
    {V : ℝ → ℝ} (hV : ContDiff ℝ ∞ V)
    (hN : RadialNaturalTail E right j (κ * cut) V)
    (hne : (V (κ * cut), outerTailSign right * E.w (κ * cut) *
      deriv V (κ * cut) / (β * lam)) ≠ 0) (q : ℝ × ℝ) :
    outerStatePair H.entrance q = 0 ↔
      outerStatePair (outerUnitState (V (κ * cut),
        outerTailSign right * E.w (κ * cut) * deriv V (κ * cut) / (β * lam))) q = 0 := by
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
      (V (κ * cut), outerTailSign right * E.w (κ * cut) * deriv V (κ * cut) /
        (β * lam)) := by
    have hderiv : deriv U cut = deriv V (κ * cut) * κ :=
      ((hV.differentiable (by simp) _).hasDerivAt.comp cut
        (hasDerivAt_const_mul κ)).deriv
    apply Prod.ext
    · rfl
    · rw [hderiv, hprofileCut]
      field_simp [hβ.ne', hlam] <;> ring
  have h := F.radialNatural_robin_iff hD hcut hentry hac hlam hT hphysical hη hK
    H hU hUN (by rwa [hstate]) q
  simpa only [hstate] using h.symm

end ContinuousFlexibility.Radial
