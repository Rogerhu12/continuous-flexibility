module

public import ContinuousFlexibility.Analysis.N01CorrectionCoefficientSmoothJets
public import ContinuousFlexibility.Analysis.N03SourceFromCoefficientJets

/-!
# The N03 source from the actual buffered coefficient family

The constructed correction family supplies the smooth coefficient space,
its exact zeroth value, all reflection and periodicity identities, and
all real material-jet parameter derivatives. The remaining quantitative
input is the local fixed-loss bound for this specific actual family.
The resulting operator is the original independent-residual source in
the original physical topology.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n03SourceFromActualCoefficientJetsStateSMul (S : PhysicalSpacesData) :
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

variable
  (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
  (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
    χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
  (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
  (hstripSupport : ∀ m, tsupport (deriv (χ m)) ⊆ Ioo (l m) (h m))
  (hstripDisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m (p : PolarPoint),
    p.1 ∈ Ioo (l m) (h m) →
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p)

include hχ hsupp hend hl hh hstripSupport hstripDisc

theorem N01Properties.exists_returnCorrectionSource_of_actual_coefficient_bounds
    (hdiscFull : ∀ z ∈ stateNeighborhood S C base ε, ∀ m p,
      p.1 ∈ tsupport (deriv (χ m)) →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (hcoeff : LocalCoefficientMaterialTameBounds (T := T)
      (U := sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)))
      (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading)
      (hN.returnCorrectionSmoothCoefficientJets hS hT hR j hcell χ hχrange hcutoff hdisc
        hχ hsupp hend l h hl hh hstripSupport hstripDisc)) :
    ∃ E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source,
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ ρ η p,
        physicalSourceDecode S (E z ρ η) p = returnCorrectionResidualErrorField D S C R χ z ρ η p) ∧
      SmoothTameOn
        (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading)
          (S.circle (3 / 4 : ℝ)).grading) (heightPairGrading S))
        S.sourceGrading ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ univ)
        (fun z : ((StateDirections S × ℝ) × CircleSpace S) × HeightPair S =>
          E (liftSectorParameter S C z.1.1) z.1.2 z.2) :=
  hN.exists_returnCorrectionSource_of_coefficient_jets hS hT R χ hχ hχrange hsupp hend hdiscFull
    (hN.returnCorrectionSmoothCoefficientJets hS hT hR j hcell χ hχrange hcutoff hdisc
      hχ hsupp hend l h hl hh hstripSupport hstripDisc)
    (hN.returnCorrectionSmoothCoefficientJets_zero hS hT hR j hcell χ hχrange hcutoff hdisc
      hχ hsupp hend l h hl hh hstripSupport hstripDisc)
    hcoeff
    (hN.returnCorrectionSmoothCoefficientJets_symmetry hS hT hR j hcell χ hχrange hcutoff hdisc
      hχ hsupp hend l h hl hh hstripSupport hstripDisc)
    (hN.returnCorrectionSmoothCoefficientJets_mixedJetHasDerivAt hS hT hR j hcell χ hχrange
      hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc)

end ContinuousFlexibility.Statements
