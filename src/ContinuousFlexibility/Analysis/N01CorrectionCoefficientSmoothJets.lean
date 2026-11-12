import ContinuousFlexibility.Analysis.N01CorrectionCoefficientSpatialJets
import ContinuousFlexibility.Analysis.N01CorrectionCoefficientSourceData
import ContinuousFlexibility.Analysis.ReturnCorrectionSourceJets

/-!
# The actual correction jets in the original smooth coefficient space

The codomain restriction uses the proved whole-annulus smoothness of the
same genuine parameter jets. Its value on the open state domain is the
raw field itself. Zeroth-order identification, source symmetry and all
material parameter derivatives therefore follow without additional
regularity or formal-jet hypotheses.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01CorrectionCoefficientSmoothJetsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

local instance n01CorrectionCoefficientSmoothJetsSectorSMul (S : PhysicalSpacesData) :
    SMul ℝ (StateDirections S × ℝ) := Prod.instSMul

local instance n01CorrectionCoefficientSmoothJetsParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ ((StateDirections S × ℝ) × CircleSpace S) := Prod.instSMul

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

def N01Properties.returnCorrectionSmoothCoefficientJets
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S) :
    MultilinearMap ℝ (fun _ : Fin n => (StateDirections S × ℝ) × CircleSpace S)
      (annularSmoothCoefficientSpace D) :=
  smoothCoefficientJetRestriction (sectorNeighborhood S base ε ε ×ˢ univ)
    (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc)
    (hN.returnCorrectionCoefficientScalarJets_contDiffOn hS hT hR j hcell χ hχrange
      hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc) n x

theorem N01Properties.returnCorrectionSmoothCoefficientJets_apply
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S) :
    (hN.returnCorrectionSmoothCoefficientJets hS hT hR j hcell χ hχrange hcutoff hdisc
      hχ hsupp hend l h hl hh hstripSupport hstripDisc n x v).val =
      hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc
        n x v :=
  smoothCoefficientJetRestriction_apply (sectorNeighborhood S base ε ε ×ˢ univ)
    (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc)
    (hN.returnCorrectionCoefficientScalarJets_contDiffOn hS hT hR j hcell χ hχrange
      hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc) n x hx v

theorem N01Properties.returnCorrectionSmoothCoefficientJets_zero
    (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ) :
    (hN.returnCorrectionSmoothCoefficientJets hS hT hR j hcell χ hχrange hcutoff hdisc
      hχ hsupp hend l h hl hh hstripSupport hstripDisc 0 x Fin.elim0).val =
      fun p => returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C x.1) p x.2 :=
  (hN.returnCorrectionSmoothCoefficientJets_apply hS hT hR j hcell χ hχrange hcutoff hdisc
    hχ hsupp hend l h hl hh hstripSupport hstripDisc 0 x hx Fin.elim0).trans
      (hN.returnCorrectionCoefficientScalarJets_zero hS hT hR j hcell χ hχrange hcutoff hdisc x hx)

theorem N01Properties.returnCorrectionSmoothCoefficientJets_symmetry
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S) :
    SymmetricErrorCoefficientSymmetry
      (hN.returnCorrectionSmoothCoefficientJets hS hT hR j hcell χ hχrange hcutoff hdisc
        hχ hsupp hend l h hl hh hstripSupport hstripDisc n x v).val := by
  have hvalue := hN.returnCorrectionSmoothCoefficientJets_apply hS hT hR j hcell
    χ hχrange hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc n x hx v
  exact (congrArg SymmetricErrorCoefficientSymmetry hvalue).mpr
    (hN.returnCorrectionCoefficientScalarJets_sourceSymmetry hS hT hR j hcell χ
      hχrange hcutoff hdisc n x hx v)

theorem N01Properties.returnCorrectionSmoothCoefficientJets_mixedJetHasDerivAt
    (n : ℕ) (x w : (StateDirections S × ℝ) × CircleSpace S)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S)
    (t : ℝ) (ht : x + t • w ∈ sectorNeighborhood S base ε ε ×ˢ univ) :
    MixedJetHasDerivAt
      (fun s r => ((hN.returnCorrectionSmoothCoefficientJets hS hT hR j hcell χ hχrange
        hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc
          n (x + s • w) v).val (T.radius r.1, r.2)).1)
      (fun r => ((hN.returnCorrectionSmoothCoefficientJets hS hT hR j hcell χ hχrange
        hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc
          (n + 1) (x + t • w) (Fin.cons w v)).val (T.radius r.1, r.2)).1) t ∧
    MixedJetHasDerivAt
      (fun s r => ((hN.returnCorrectionSmoothCoefficientJets hS hT hR j hcell χ hχrange
        hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc
          n (x + s • w) v).val (T.radius r.1, r.2)).2)
      (fun r => ((hN.returnCorrectionSmoothCoefficientJets hS hT hR j hcell χ hχrange
        hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc
          (n + 1) (x + t • w) (Fin.cons w v)).val (T.radius r.1, r.2)).2) t :=
  smoothCoefficientJetRestriction_hasDerivAt_line
    ((sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ)
    (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff hdisc)
    (hN.returnCorrectionCoefficientScalarJets_contDiffOn hS hT hR j hcell χ hχrange
      hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc)
    (hN.returnCorrectionCoefficientScalarJets_mixedJetHasDerivAt hS hT hR j hcell χ hχrange
      hcutoff hdisc hχ hsupp hend l h hl hh hstripSupport hstripDisc) n x w v t ht

end ContinuousFlexibility.Statements
