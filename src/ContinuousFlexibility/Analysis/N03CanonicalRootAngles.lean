import ContinuousFlexibility.Analysis.CanonicalCharacteristicEndpointTransport

/-!
# The two N03 trajectories have the canonical endpoint translations

The plus trajectory is the actual reflected minus trajectory, using the
stored N03 coefficient parities. Applying full-component transport gives
both boundary-angle translation identities on the existing construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem neg_minusCharacteristicSpeed_eq_plus_of_reflection
    {A : SymmetricCoefficients} {r θ : ℝ}
    (ha : A.a (r, -θ) = A.a (r, θ))
    (hb : A.b (r, -θ) = -A.b (r, θ))
    (hc : A.c (r, -θ) = A.c (r, θ)) :
    -minusCharacteristicSpeed A (r, θ) = plusCharacteristicSpeed A (r, -θ) := by
  simp only [minusCharacteristicSpeed, plusCharacteristicSpeed, ha, hb, hc, neg_sq, neg_div]
  ring

/-- The genuine canonical root-angle maps conjugate both actual N03
returns to translations by the same Airy width. -/
theorem canonicalRootAngles_of_n03Flows
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (θ : ℝ) :
    (K.chart z (K.cutPair m).2
        (C.right m, L.minusFlow z m (C.right m) θ)).2 =
      (K.chart z (K.cutPair m).1 (C.left m, θ)).2 -
        2 * airyTravelPrimitive (K.cutRadius m) ∧
    (K.chart z (K.cutPair m).2
        (C.right m, -L.minusFlow z m (C.right m) (-θ))).2 =
      (K.chart z (K.cutPair m).1 (C.left m, θ)).2 +
        2 * airyTravelPrimitive (K.cutRadius m) := by
  have hminus := hN03.2.2.2.2.1 z hz hs m θ
  have hreflected := hN03.2.2.2.2.1 z hz hs m (-θ)
  have hplusFlow (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) :
      HasDerivAt (fun t => -L.minusFlow z m t (-θ))
        ((L.coefficients z).b (r, -L.minusFlow z m r (-θ)) /
            (L.coefficients z).a (r, -L.minusFlow z m r (-θ)) -
          (-1 : ℝ) * Real.sqrt ((L.coefficients z).b (r, -L.minusFlow z m r (-θ)) ^ 2 -
            (L.coefficients z).a (r, -L.minusFlow z m r (-θ)) *
              (L.coefficients z).c (r, -L.minusFlow z m r (-θ))) /
            (L.coefficients z).a (r, -L.minusFlow z m r (-θ))) r := by
    obtain ⟨ha, hb, hc⟩ := hN03.2.2.2.1 z hz hs r (L.minusFlow z m r (-θ))
    have hd := (hreflected.2.2.1 r hr).neg
    rw [neg_minusCharacteristicSpeed_eq_plus_of_reflection ha hb hc] at hd
    simpa only [plusCharacteristicSpeed, neg_one_mul, neg_div, sub_neg_eq_add] using hd
  have hm := canonicalGluedAiryIntegral_endpoint_of_actual_ode
    hS hT hN01 hN03 hA hB hz hs m (σ := 1) (Or.inl rfl)
    hminus.2.1 (fun r hr => by
      simpa only [minusCharacteristicSpeed, one_mul] using hminus.2.2.1 r hr)
  have hp := canonicalGluedAiryIntegral_endpoint_of_actual_ode
    hS hT hN01 hN03 hA hB hz hs m (σ := -1) (Or.inr rfl)
    hreflected.2.1.neg hplusFlow
  rw [hminus.1] at hm
  rw [hreflected.1, neg_neg] at hp
  constructor
  · simpa only [mul_one] using (eq_sub_iff_add_eq.mpr hm)
  · have he : 2 * (-1 : ℝ) * airyTravelPrimitive (K.cutRadius m) =
        -(2 * airyTravelPrimitive (K.cutRadius m)) := by ring
    rw [he] at hp
    linarith only [hp]

end ContinuousFlexibility.Analysis
