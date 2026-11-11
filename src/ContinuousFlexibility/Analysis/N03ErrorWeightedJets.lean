import ContinuousFlexibility.Analysis.N03ErrorHomogeneousBounds
import ContinuousFlexibility.Scalar.WeightedOrdinaryPointwise

/-!
# Actual spatial jets of the N03 source error

The physical Sobolev decoding theorem costs exactly two grading orders
and one material-envelope factor. Combining it with the actual ordered
fiber estimate preserves the residual factor and a common loss at all
spatial orders. Constants are chosen before the state, residual, test
and evaluation point. No bound for an effective coefficient is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem weighted_error_scalar_bound {x C H M q B V : ℝ}
    (hweight : 0 ≤ C * H * M) (hx : x ≤ C * H * M * q) (hq : q ≤ B * V) :
    x ≤ (C * B) * H * M * V := by
  calc
    x ≤ C * H * M * (B * V) :=
      hx.trans (mul_le_mul_of_nonneg_left hq hweight)
    _ = (C * B) * H * M * V := by ring

/-- The decoded N03 error has genuine mixed spatial derivative bounds
with one common loss and one factor from each independent fiber. -/
theorem n03Error_mixedDerivative_weighted_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hε : 0 < ε) (hN03 : N03Properties D T S C R L base ε) :
    ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ a b : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ v ∈ sectorNeighborhood S base ε ε,
          pairGrading (sectorGrading S) realGrading low v < δ →
          ∀ r : CircleSpace S, ∀ η : HeightPair S, ∀ p ∈ annularOpen D,
            |mixedDerivative a b ((S.height (3 / 4 : ℝ)).decode
                ((L.error (liftSectorParameter S C v) r η).val)) p| ≤
              B * T.H p.1 ^ (3 / 4 : ℝ) * T.M p.1 *
                ((1 + pairGrading (sectorGrading S) realGrading (a + b + loss) v) *
                    ((S.circle (3 / 4 : ℝ)).grading low r * heightPairGrading S low η) +
                  ((S.circle (3 / 4 : ℝ)).grading (a + b + loss) r *
                      heightPairGrading S low η +
                    (S.circle (3 / 4 : ℝ)).grading low r *
                      heightPairGrading S (a + b + loss) η)) := by
  obtain ⟨loss, low, δ, hδ, herror⟩ := n03Error_homogeneous_tame_bound hε hN03
  refine ⟨2 + low + loss, low, δ, hδ, ?_⟩
  intro a b
  obtain ⟨C₀, hC₀, hpoint⟩ :=
    mixedDerivative_decode_le_weighted_grading hT (hS.1 (3 / 4 : ℝ)) a b
  obtain ⟨B₀, hB₀, herror⟩ := herror (a + b + 2 + low) (by omega)
  refine ⟨C₀ * B₀, mul_nonneg hC₀ hB₀, ?_⟩
  intro v hv hlow r η p hp
  let u : S.Source := L.error (liftSectorParameter S C v) r η
  have hgrade : (S.height (3 / 4 : ℝ)).grading (a + b + 2) u.val ≤
      S.sourceGrading (a + b + 2 + low) u :=
    gradedSeminorm_monotone _ _ (by omega) u.val
  have herr := herror v hv hlow r η
  have horder : a + b + 2 + low + loss = a + b + (2 + low + loss) := by omega
  rw [horder] at herr
  have hq := hgrade.trans herr
  have hH : 0 ≤ T.H p.1 ^ (3 / 4 : ℝ) :=
    (Real.rpow_pos_of_pos (hT.2.1 _ hp.1).2.1 _).le
  have hM : 0 ≤ T.M p.1 := zero_le_one.trans (hT.2.1 _ hp.1).2.2.2
  exact weighted_error_scalar_bound (mul_nonneg (mul_nonneg hC₀ hH) hM)
    (hpoint u.val p hp) hq

end ContinuousFlexibility.Analysis
