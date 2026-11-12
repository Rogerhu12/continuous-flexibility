import Mathlib.Util.CountHeartbeats
import ContinuousFlexibility.Analysis.N01CorrectionCoefficientFlatBounds
import ContinuousFlexibility.Analysis.FlatMixedDiagonalRealization
import ContinuousFlexibility.Analysis.ActualRadialCellComparison

/-!
# Transferring actual joint coefficient estimates to the source family

The genuine joint towers on each buffered strip equal the parameter
jets selected for the original global coefficient field. Polarization,
the fixed finite maximum for the two components, and the flat strip
estimate therefore control the same smooth coefficient family used by
the source operator.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01CorrectionCoefficientTameTransferStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)
  (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
  (χ : ℕ → ℝ → ℝ)
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
    |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
  (hdisc : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ m p, p.1 ∈ Ioo (C.left m) (C.right m) → deriv (χ m) p.1 ≠ 0 →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
  (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
  (hstripDisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m (p : PolarPoint),
    p.1 ∈ Ioo (l m) (h m) →
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p)

count_heartbeats in
theorem N01Properties.returnCorrectionCoefficientScalarJets_flat_bound_of_joint_growth
    (p : ℕ → Seminorm ℝ ((StateDirections S × ℝ) × CircleSpace S)) (hp : Monotone p)
    (hfst : HasFlatMixedTameGrowth p (fun m => radialE (D.cellIndex (j m)))
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
      (fun m => solveSmoothDirectionsPostcomp
        (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
          m (j m) (hcell m) (l m) (h m) (hl m) (hh m)
          (fun z hz q hq => hstripDisc z hz m q hq)) (ContinuousLinearMap.fst ℝ ℝ ℝ)))
    (hsnd : HasFlatMixedTameGrowth p (fun m => radialE (D.cellIndex (j m)))
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
      (fun m => solveSmoothDirectionsPostcomp
        (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR χ hχ hχrange
          m (j m) (hcell m) (l m) (h m) (hl m) (hh m)
          (fun z hz q hq => hstripDisc z hz m q hq)) (ContinuousLinearMap.snd ℝ ℝ ℝ))) :
    ∀ n : ℕ, ∃ B L : ℕ, StripCoefficientFlatOneHighBound p
      (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc)
      (sectorNeighborhood S base ε ε ×ˢ univ) l h
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
      (fun m => radialE (D.cellIndex (j m))) n B L := by
  all_goals sorry

end ContinuousFlexibility.Statements
