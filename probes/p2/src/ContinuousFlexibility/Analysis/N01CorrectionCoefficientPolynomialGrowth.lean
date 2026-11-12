import ContinuousFlexibility.Analysis.N01CorrectionOriginalFactorGrowth
import ContinuousFlexibility.Analysis.N01CorrectionCoefficientTameTransfer
import ContinuousFlexibility.Analysis.FlatMixedPolynomialCoefficients

/-!
# Actual coefficient growth from the same-cutoff velocity estimates

The original coefficients and square-root factor have proved N01
growth. The two genuine velocity families provide the remaining input.
Reflection gives the actual drift and speed, the division-free identity
gives the original coefficient error, and uniqueness applies all bounds
to its previously selected joint towers.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01CorrectionCoefficientPolynomialGrowthStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)
  (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
  (hstripDisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m (p : PolarPoint),
    p.1 ∈ Ioo (l m) (h m) →
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p)
  {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
  (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (p : PolarPoint),
    p.1 ∈ Ioo (l m) (h m) →
    let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
    d ≤ (originalCoefficients D S C z).a p ∧
    d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

include hlam hP hpositive

set_option profiler true in
theorem N01Properties.returnCorrectionCoefficient_joint_growth_of_velocity
    (Jρ : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2))
    (Je : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
          (R.residual (liftSectorParameter S C x.1.1))))
    (hJρ : HasFlatMixedTameGrowth
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (fun m => radialE (D.cellIndex (j m)))
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)) Jρ)
    (hJe : HasFlatMixedTameGrowth
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (fun m => radialE (D.cellIndex (j m))) (fun _ => 1) Je) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading
    let W := fun m => radialE (D.cellIndex (j m))
    let F := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
    HasFlatMixedTameGrowth p W F
      (fun m => solveSmoothDirectionsPostcomp
        (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
          m (j m) (hcell m) (l m) (h m) (hl m) (hh m)
          (fun z hz q hq => hstripDisc z hz m q hq)) (ContinuousLinearMap.fst ℝ ℝ ℝ)) ∧
    HasFlatMixedTameGrowth p W F
      (fun m => solveSmoothDirectionsPostcomp
        (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
          m (j m) (hcell m) (l m) (h m) (hl m) (hh m)
          (fun z hz q hq => hstripDisc z hz m q hq)) (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  sorry

end ContinuousFlexibility.Statements
