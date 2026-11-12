import ContinuousFlexibility.Analysis.N01CorrectionCoefficientJets
import ContinuousFlexibility.Analysis.ReturnDivergenceMembership

/-!
# Source symmetry of the actual correction coefficient jets

The coefficient fields are the derivatives of the same cutoff correction
used in the return construction. Their proved reflection and period
identities give precisely the symmetry required by the physical
divergence realization at every parameter order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01CorrectionCoefficientSourceDataStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis

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

theorem N01Properties.returnCorrectionCoefficientScalarJets_sourceSymmetry
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S) :
    SymmetricErrorCoefficientSymmetry
      (hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff
        hdisc n x v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r θ
    exact congrArg Prod.fst (hN.returnCorrectionCoefficientScalarJets_reflection
      hS hT hR j hcell χ hχrange hcutoff hdisc n x hx v r θ)
  · intro r θ
    have h := congrArg (fun q : ℝ × ℝ => q.2)
      (hN.returnCorrectionCoefficientScalarJets_reflection
        hS hT hR j hcell χ hχrange hcutoff hdisc n x hx v r θ)
    exact h
  · intro p
    have hp : p + (0, Real.pi) = (p.1, p.2 + Real.pi) :=
      Prod.ext (add_zero p.1) rfl
    exact (congrArg (fun q : PolarPoint =>
      hN.returnCorrectionCoefficientScalarJets hS hT hR j hcell χ hχrange hcutoff
        hdisc n x v q) hp).trans
      (hN.returnCorrectionCoefficientScalarJets_periodic hS hT hR j hcell χ hχrange
        hcutoff hdisc n x hx v p.1 p.2)

end ContinuousFlexibility.Statements
