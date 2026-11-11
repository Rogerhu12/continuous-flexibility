import ContinuousFlexibility.Analysis.N01CoefficientDiscriminantBounds
import ContinuousFlexibility.Analysis.RootCoefficientDivision
import ContinuousFlexibility.Analysis.RootShiftMixedJets

/-!
# Actual N01 fixed-loss jets for the smooth root determinant factor

The original coefficient input is used at every spatial order. A single
interpolation loss controls its quadratic determinant, and true radial
division adds exactly one. The common low order and loss precede the
root, orientation, collar, physical cell, and requested derivative order.
Only numerical constants may depend on those geometric choices.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n01_rootCoefficientRadialFactor_fixed_loss_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ low outLoss : ℕ, ∀ r σ : ℝ, ∀ g : ℝ → ℝ, ∀ R : ℝ,
      (σ = 1 ∨ σ = -1) → 0 < R → ContDiff ℝ ∞ g →
      Ioo ((r - R) - R) ((r + R) + R) ⊆ Ioo D.a D.b →
      ∀ m : ℕ, Ioo (r - R) (r + R) ⊆ D.cells m →
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ R) →
      ∀ a b : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ),
        |mixedDerivative a b
          (rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
            (stateHeight D S C z) r σ) q| ≤
          B * (1 + pairGrading (stateGrading S) realGrading (a + b + outLoss)
            (z - (C.referenceState, 0))) := by
  obtain ⟨low, outLoss, hdisc⟩ := n01_coefficientDiscriminant_fixed_loss_bound hS hT hN
  refine ⟨low, outLoss + 1, ?_⟩
  intro r σ g R hσ hR hg hphysical m hcell hstrip a b
  have hlu : r - R ≤ r + R := by linarith
  obtain ⟨B, hB, hbound⟩ :=
    hdisc (r - R) (r + R) R hlu hR hphysical m hcell (a + 1) b
  refine ⟨B, hB, ?_⟩
  intro z hz hsector hlow q hq
  obtain ⟨_, hD⟩ := hN.1.1
  have hwref : ContDiff ℝ ∞ D.w := hD.1.2.2.1.1
  have hw := contDiff_stateProfile_of_n01 hS hT hN z.1
  have hZ := contDiff_stateHeight_of_n01 hS hT hN z
  let M := B * (1 + pairGrading (stateGrading S) realGrading ((a + 1) + b + outLoss)
    (z - (C.referenceState, 0)))
  have hb : |mixedDerivative a b
      (rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ) q| ≤ M := by
    apply abs_mixedDerivative_rootCoefficientRadialFactor_le
      hwref hg hw hZ hR (hstrip z hz hsector) a b hq
    intro p hp
    have he :
        |mixedDerivative (a + 1) b
          (rootCoefficientDiscriminant (stateProfile D S C z.1)
            (stateHeight D S C z) r σ) p| =
        |mixedDerivative (a + 1) b
          (fun x => (originalCoefficients D S C z).b x ^ 2 -
            (originalCoefficients D S C z).a x * (originalCoefficients D S C z).c x)
          (rootProfileShift r σ p)| :=
      abs_mixedDerivative_rootProfileShift
        (fun x => (originalCoefficients D S C z).b x ^ 2 -
          (originalCoefficients D S C z).a x * (originalCoefficients D S C z).c x)
        hσ (a + 1) b p
    exact he.trans_le (hbound z hz hsector hlow (rootProfileShift r σ p)
      ⟨rootProfileShift_mem_symmetric_interval hσ hp.1, mem_univ _⟩)
  have hindex : (a + 1) + b + outLoss = a + b + (outLoss + 1) := by omega
  simpa only [M, hindex] using hb

end ContinuousFlexibility.Analysis
