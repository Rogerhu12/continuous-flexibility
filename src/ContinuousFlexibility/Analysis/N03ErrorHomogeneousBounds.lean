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

/-- Remove the zero base point in abstract spaces, before instantiating
the concrete projective sector. All spaces and gradings are fixed
explicitly when applying the heterogeneous estimate. -/
private theorem heterogeneousBilinear_tame_bounds_at_zero
    {Z E F G : Type*}
    [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G] [T2Space G]
    {a : ℕ → Seminorm ℝ Z} {p : ℕ → Seminorm ℝ E}
    {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set Z} {A : Z → E →ₗ[ℝ] F →ₗ[ℝ] G}
    (hT : SmoothTameOn (pairGrading (pairGrading a p) q) r ((U ×ˢ univ) ×ˢ univ)
      (fun z : (Z × E) × F => A z.1.1 z.1.2 z.2))
    (hz : (0 : Z) ∈ U) :
    ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℕ, low ≤ s → ∃ B : ℝ, 0 ≤ B ∧
        ∀ z ∈ U, a low z < δ → ∀ e : E, ∀ f : F,
          r s (A z e f) ≤ B *
            ((1 + a (s + loss) z) * (p low e * q low f) +
              (p (s + loss) e * q low f + p low e * q (s + loss) f)) := by
  obtain ⟨loss, low, δ, hδ, hb⟩ :=
    heterogeneousBilinear_tame_bounds_on_ball_of_smoothTame
      (Z := Z) (E := E) (F := F) (G := G)
      (a := a) (p := p) (q := q) (r := r) (U := U) (A := A) (z₀ := 0) hT hz
  refine ⟨loss, low, δ, hδ, ?_⟩
  intro s hs
  obtain ⟨B, hB, hb⟩ := hb s hs
  refine ⟨B, hB, ?_⟩
  intro z hz hlow e f
  exact hb z hz (by simpa only [sub_zero] using hlow) e f

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
  exact heterogeneousBilinear_tame_bounds_at_zero
    (Z := StateDirections S × ℝ) (E := CircleSpace S) (F := HeightPair S) (G := S.Source)
    (a := pairGrading (sectorGrading S) realGrading)
    (p := (S.circle (3 / 4 : ℝ)).grading) (q := heightPairGrading S) (r := S.sourceGrading)
    (U := sectorNeighborhood S base ε ε)
    (A := fun v : StateDirections S × ℝ => L.error (liftSectorParameter S C v))
    hSmooth hz₀

end ContinuousFlexibility.Analysis
