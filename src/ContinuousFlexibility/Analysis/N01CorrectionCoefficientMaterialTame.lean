import ContinuousFlexibility.Analysis.N01CorrectionCoefficientPolynomialGrowth
import ContinuousFlexibility.Analysis.N01TransportVelocityMixedGrowth

/-!
# Actual material tame bounds for the same correction coefficient jets

Every estimate below is supplied by the N01 flow, its buffered positive
strips and the chosen cutoff.  The genuine velocity bounds retain one
positive sample-height factor.  Polynomial reconstruction, polarization,
the actual support identity and the material coordinate estimate transfer
that factor to the original smooth coefficient family.  Its flatness
absorbs the radial weight without an order-dependent material loss.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01CorrectionCoefficientMaterialTameStateSMul (S : PhysicalSpacesData) :
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

/-- The actual coefficient family satisfies the local material tame
interface.  The hypotheses are precisely the buffered N01 witnesses;
no coefficient or velocity tame estimate is assumed. -/
theorem N01Properties.returnCorrectionSmoothCoefficientJets_local_material_tame
    (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
        deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)
    {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (p : PolarPoint),
      p.1 ∈ Ioo (l m) (h m) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      d ≤ (originalCoefficients D S C z).a p ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    LocalCoefficientMaterialTameBounds (T := T)
      (U := sectorNeighborhood S base ε ε ×ˢ univ)
      (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading)
      (hN.returnCorrectionSmoothCoefficientJets hS hT hR j hcell χ hχrange hcutoff hdisc
        hχ hsupp hend l h hl hh hstripSupport hstripDisc) := by
  let p := pairGrading (pairGrading (sectorGrading S) realGrading)
    (S.circle (3 / 4 : ℝ)).grading
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  let F : ℕ → ℝ := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
  let JV : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2) :=
    fun m => hN.returnCorrectionVelocity_parameterSpatialTower hS hT χ hχrange hχ
      m (l m) (h m) (hl m) (hh m) (fun z hz q hq => hstripDisc z hz m q hq)
  let JE : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
          (R.residual (liftSectorParameter S C x.1.1))) :=
    fun m => (hN.returnCorrectionVelocity_actual_parameterSpatialTower hS hT χ hχrange hχ
      m (l m) (h m) (hl m) (hh m) (fun z hz q hq => hstripDisc z hz m q hq) hR).fstParameter
        (F := CircleSpace S) (sectorNeighborhood_isOpen S base ε ε)
        (isOpen_Ioo.prod isOpen_univ)
  have hvelocity (n : ℕ) : ∃ B : ℕ,
      FlatMixedDiagonalGrowth p W F JV n B (B + 1) ∧
      FlatMixedDiagonalGrowth p W (fun _ => 1) JE n B (B + 1) :=
    hN.returnCorrectionVelocity_flatMixedGrowth hS hT hR hflow j hcell l h hl hh
      hlam hP hpositive χ hχ hχrange hcutoff JV JE n
  have hJV : HasFlatMixedTameGrowth p W F JV := by
    intro n
    let data := hvelocity n
    exact ⟨data.choose, data.choose + 1, data.choose_spec.1⟩
  have hJE : HasFlatMixedTameGrowth p W (fun _ => 1) JE := by
    intro n
    let data := hvelocity n
    exact ⟨data.choose, data.choose + 1, data.choose_spec.2⟩
  have hgrowth := hN.returnCorrectionCoefficient_joint_growth_of_velocity hS hT hR
    j hcell χ hχ hχrange l h hl hh hstripDisc hlam hP hpositive JV JE hJV hJE
  have hstrip := hN.returnCorrectionCoefficientScalarJets_flat_bound_of_joint_growth
    hS hT hR j hcell χ hχrange hcutoff hdisc hχ l h hl hh hstripDisc p
    (correctionParameterGrading_monotone S) hgrowth.1 hgrowth.2
  exact hN.returnCorrectionSmoothCoefficientJets_local_bounds_of_flat_strips hS hT hR
    j hcell χ hχrange hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc p hstrip

end ContinuousFlexibility.Statements
