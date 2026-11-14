module

public import ContinuousFlexibility.Analysis.N08ProfilePointwise
public import ContinuousFlexibility.Analysis.N08ScalarFormula
public import ContinuousFlexibility.Analysis.N08ReferenceFlow
public import ContinuousFlexibility.Analysis.N08Neighborhoods
public import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation
public import ContinuousFlexibility.Analysis.N08RealJetBounds

/-!
# Extracting the actual logarithmic profile from the N01 coefficient tower

At zero external parameter the radial coefficient is precisely the physical
profile. Its genuine first state derivative is the profile times the linear
logarithmic perturbation. Consequently N01 controls that actual perturbation
at every reference cell, independently of where the control labels are placed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08_coefficientA_zeroParameter (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (p : PolarPoint) :
    (originalCoefficients D S C (x, 0)).a p = stateProfile D S C x p.1 := by
  change polarLinearA (stateProfile D S C x) (stateHeight D S C (x, 0)) p = _
  rw [n08_stateHeight_zero_parameter]
  exact (n08_radialHeight_coefficients (n08_stateRadialHeight_hasDerivAt hT hS hN x)
    ((contDiff_stateProfile_of_n01 hS hT hN x).differentiable (by simp) p.1)).1

theorem n08_coefficientFamily_zero_zeroParameter (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (p : PolarPoint) :
    coefficientFamily D S C 0 0 0 p (x, 0) = stateProfile D S C x p.1 - D.w p.1 := by
  simp only [coefficientFamily, ↓reduceIte, mixedDerivative, iteratedDeriv_zero]
  rw [n08_coefficientA_zeroParameter hT hS hN,
    n08_coefficientA_zeroParameter hT hS hN, n08_stateProfile_reference hN.2.2.1]

theorem n08_coefficientA_state_hasDerivAt (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (x v : AnnularState S) (p : PolarPoint) :
    HasDerivAt
      (fun t : ℝ => coefficientFamily D S C 0 0 0 p (x + n08StateSMul S t v, 0))
      (stateProfile D S C x p.1 * n08_stateLogProfile D S C v p.1) 0 := by
  simpa only [n08_coefficientFamily_zero_zeroParameter hT hS hN] using
    (n08_stateProfile_hasDerivAt hS hN.2.2.2.1 x v p.1).sub_const (D.w p.1)

theorem n08_reference_mem_stateNeighborhood (hε : 0 < ε) :
    (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
  ⟨n08_seminorm_center_lt (stateGrading S base) C.referenceState hε,
    (abs_zero : |(0 : ℝ)| = 0).trans_lt hε⟩

theorem n08_n01_coefficientTowers (hN : N01Properties D T S C base loss ε) :
    N08RealCoefficientTowers (stateGrading S) (stateNeighborhood S C base ε)
      (coefficientFamily D S C) (fun m y => y.1 ∈ D.cells m)
      (fun B m => B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B)
      base loss C.referenceState :=
  hN.2.2.2.2.2.2.2.2.2.2.2.1

theorem n08_coefficientA_reference_hasDerivAt (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (v : AnnularState S) (p : PolarPoint) :
    HasDerivAt
      (fun t : ℝ => coefficientFamily D S C 0 0 0 p
        (C.referenceState + n08StateSMul S t v, 0))
      (D.w p.1 * n08_stateLogProfile D S C v p.1) 0 := by
  simpa only [n08_stateProfile_reference hN.2.2.1] using
    n08_coefficientA_state_hasDerivAt hT hS hN C.referenceState v p

/-- An actual position-dependent bound for every logarithmic state direction.
The only cell appearing on the right is the cell containing the evaluation
point. No control interval-to-cell identification is used. -/
theorem n08_logProfile_reference_coefficient_bound (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ D.cells m → ∀ v : AnnularState S,
      |D.w r * n08_stateLogProfile D S C v r| ≤
        B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
          (stateGrading S base v + stateGrading S loss v) :=
  n08_realFirstJet_zero_tower_reference_bound (stateGrading S) (stateNeighborhood S C base ε)
    (coefficientFamily D S C) (fun m y => y.1 ∈ D.cells m)
    (fun B m => B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B)
    base loss C.referenceState 0 (fun r : ℝ => (r, 0))
    (fun r v => D.w r * n08_stateLogProfile D S C v r)
    (n08_reference_mem_stateNeighborhood hN.2.1)
    (fun r v => n08_coefficientA_reference_hasDerivAt hT hS hN v (r, 0))
    (n08_n01_coefficientTowers hN)

end ContinuousFlexibility.Statements
