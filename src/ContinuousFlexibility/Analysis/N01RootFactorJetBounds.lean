module

public import ContinuousFlexibility.Analysis.N01CoefficientDiscriminantBounds
public import ContinuousFlexibility.Analysis.RootCoefficientDivision
public import ContinuousFlexibility.Analysis.RootShiftMixedJets

/-!
# Actual N01 fixed-loss jets for the smooth root determinant factor

The original coefficient input is used at every spatial order. A single
interpolation loss controls its quadratic determinant, and true radial
division adds exactly one. The common low order and loss precede the
root, orientation, collar, physical cell, and requested derivative order.
Only numerical constants may depend on those geometric choices.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The geometric division and the single grade shift do not depend on
the representation of the state space. -/
private theorem rootCoefficientRadialFactor_bound_of_discriminant
    {E : Type*} (p : ℕ → E → ℝ) (v : E) (outLoss : ℕ)
    {wref g w : ℝ → ℝ} {Z : PolarPoint → ℝ}
    (hwref : ContDiff ℝ ∞ wref) (hg : ContDiff ℝ ∞ g)
    (hw : ContDiff ℝ ∞ w) (hZ : ContDiff ℝ ∞ Z)
    {r σ R : ℝ} (hσ : σ = 1 ∨ σ = -1) (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions wref g w Z r σ R)
    (a b : ℕ) {B : ℝ}
    (hbound : ∀ q ∈ Ioo (r - R) (r + R) ×ˢ (univ : Set ℝ),
      |mixedDerivative (a + 1) b
        (fun x => polarLinearB w Z x ^ 2 -
          polarLinearA w Z x * polarCorrectedC w Z x) q| ≤
        B * (1 + p ((a + 1) + b + outLoss) v))
    {q : PolarPoint} (hq : q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ)) :
    |mixedDerivative a b (rootCoefficientRadialFactor wref g w Z r σ) q| ≤
      B * (1 + p (a + b + (outLoss + 1)) v) := by
  have hb :
      |mixedDerivative a b (rootCoefficientRadialFactor wref g w Z r σ) q| ≤
        B * (1 + p ((a + 1) + b + outLoss) v) := by
    apply abs_mixedDerivative_rootCoefficientRadialFactor_le
      hwref hg hw hZ hR hstrip a b hq
    intro x hx
    have he :
        |mixedDerivative (a + 1) b (rootCoefficientDiscriminant w Z r σ) x| =
        |mixedDerivative (a + 1) b
          (fun y => polarLinearB w Z y ^ 2 -
            polarLinearA w Z y * polarCorrectedC w Z y)
          (rootProfileShift r σ x)| :=
      abs_mixedDerivative_rootProfileShift
        (fun y => polarLinearB w Z y ^ 2 -
          polarLinearA w Z y * polarCorrectedC w Z y) hσ (a + 1) b x
    exact he.trans_le (hbound (rootProfileShift r σ x)
      ⟨rootProfileShift_mem_symmetric_interval hσ hx.1, mem_univ _⟩)
  have hindex : (a + 1) + b + outLoss = a + b + (outLoss + 1) := by omega
  simpa only [hindex] using hb

/-- Exactly the expanded state- and point-wise conclusion at one order. -/
def N01RootCoefficientRadialFactorBoundAtOrder
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base low outLoss : ℕ) (ε r σ : ℝ) (g : ℝ → ℝ) (R : ℝ)
    (a b : ℕ) (B : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
    ∀ q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ),
      |mixedDerivative a b
        (rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ) q| ≤
        B * (1 + pairGrading (stateGrading S) realGrading (a + b + outLoss)
          (z - (C.referenceState, 0)))

private theorem n01_rootCoefficientRadialFactor_bound_of_discriminant
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss low outLoss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {r σ : ℝ} {g : ℝ → ℝ} {R : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hR : 0 < R) (hg : ContDiff ℝ ∞ g)
    (hstrip : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ R)
    (a b : ℕ) (B : ℝ)
    (hbound : N01CoefficientDiscriminantBoundAtOrder
      D S C base low outLoss ε (r - R) (r + R) (a + 1) b B) :
    N01RootCoefficientRadialFactorBoundAtOrder
      D S C base low (outLoss + 1) ε r σ g R a b B := by
  obtain ⟨_, hD⟩ := hN.1.1
  have hwref : ContDiff ℝ ∞ D.w := hD.1.2.2.1.1
  intro z hz hsector hlow q hq
  exact rootCoefficientRadialFactor_bound_of_discriminant
    (fun n x => pairGrading (stateGrading S) realGrading n x)
    (z - (C.referenceState, 0)) outLoss hwref hg
    (contDiff_stateProfile_of_n01 hS hT hN z.1)
    (contDiff_stateHeight_of_n01 hS hT hN z)
    hσ hR (hstrip z hz hsector) a b
    (hbound z hz hsector hlow) hq

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
        N01RootCoefficientRadialFactorBoundAtOrder
          D S C base low outLoss ε r σ g R a b B := by
  obtain ⟨low, outLoss, hdisc⟩ := n01_coefficientDiscriminant_fixed_loss_bound hS hT hN
  refine ⟨low, outLoss + 1, ?_⟩
  intro r σ g R hσ hR hg hphysical m hcell hstrip a b
  have hlu : r - R ≤ r + R := by linarith
  obtain ⟨B, hB, hbound⟩ :=
    hdisc (r - R) (r + R) R hlu hR hphysical m hcell (a + 1) b
  exact ⟨B, hB, n01_rootCoefficientRadialFactor_bound_of_discriminant
    hS hT hN hσ hR hg hstrip a b B hbound⟩

end ContinuousFlexibility.Analysis
