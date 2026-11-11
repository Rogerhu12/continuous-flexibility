import ContinuousFlexibility.Analysis.HeterogeneousBilinearTameBounds
import ContinuousFlexibility.Statements.Nonlinear

/-!
# A residual-preserving bound for the actual N03 error

The source error is bilinear in a circle residual and a height test.
Its smooth tame clause therefore gives a homogeneous estimate in these
two different spaces. The neighborhood and loss below are chosen once,
before the output order, residual and test; no constant independent of
the residual is added.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The N03 smooth tame error has one common low neighborhood and loss,
with one high factor among the sector parameter, residual and test. -/
theorem n03Error_homogeneous_tame_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hN03 : N03Properties D T S C R L base ε) :
    ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℕ, low ≤ s → ∃ B : ℝ, 0 ≤ B ∧
        ∀ v ∈ sectorNeighborhood S base ε ε,
          pairGrading (sectorGrading S) realGrading low v < δ →
          ∀ r : CircleSpace S, ∀ η : HeightPair S,
            S.sourceGrading s (L.error (liftSectorParameter S C v) r η) ≤ B *
              ((1 + pairGrading (sectorGrading S) realGrading (s + loss) v) *
                  ((S.circle (3 / 4 : ℝ)).grading low r * heightPairGrading S low η) +
                ((S.circle (3 / 4 : ℝ)).grading (s + loss) r * heightPairGrading S low η +
                  (S.circle (3 / 4 : ℝ)).grading low r *
                    heightPairGrading S (s + loss) η)) := by
  have hSmooth : SmoothTameOn
      (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading) (heightPairGrading S))
      S.sourceGrading ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × HeightPair S =>
        L.error (liftSectorParameter S C z.1.1) z.1.2 z.2) := hN03.2.2.2.2.2.2.2
  have hz₀ : (0 : StateDirections S × ℝ) ∈ sectorNeighborhood S base ε ε := by
    change sectorGrading S base (0 : StateDirections S) < ε ∧ |(0 : ℝ)| < ε
    simpa only [map_zero, abs_zero] using And.intro hε hε
  obtain ⟨loss, low, δ, hδ, hb⟩ :=
    heterogeneousBilinear_tame_bounds_on_ball_of_smoothTame
      (A := fun v : StateDirections S × ℝ => L.error (liftSectorParameter S C v))
      hSmooth hz₀
  refine ⟨loss, low, δ, hδ, ?_⟩
  intro s hs
  obtain ⟨B, hB, hb⟩ := hb s hs
  refine ⟨B, hB, ?_⟩
  intro v hv hlow r η
  exact hb v hv (by simpa only [sub_zero] using hlow) r η

end ContinuousFlexibility.Analysis
