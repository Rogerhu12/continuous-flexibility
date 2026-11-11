import ContinuousFlexibility.Analysis.N08ProfilePointwise
import ContinuousFlexibility.Analysis.N08ScalarFormula
import ContinuousFlexibility.Analysis.N08ReferenceFlow
import ContinuousFlexibility.Analysis.N08Neighborhoods
import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation

/-!
# Extracting the actual logarithmic profile from the N01 coefficient tower

At zero external parameter the radial coefficient is precisely the physical
profile. Its genuine first state derivative is the profile times the linear
logarithmic perturbation. Consequently N01 controls that actual perturbation
at every reference cell, independently of where the control labels are placed.
-/

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
      (fun t : ℝ => coefficientFamily D S C 0 0 0 p (x + t • v, 0))
      (stateProfile D S C x p.1 * n08_stateLogProfile D S C v p.1) 0 := by
  simpa only [n08_coefficientFamily_zero_zeroParameter hT hS hN] using
    (n08_stateProfile_hasDerivAt hS hN.2.2.2.1 x v p.1).sub_const (D.w p.1)

private theorem n08_reference_mem (hε : 0 < ε) :
    (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
  constructor
  · simpa only [sub_self, map_zero] using hε
  · simpa only [abs_zero] using hε

private theorem n08_oneHigh_first_at_zero (v : AnnularState S) :
    oneHighVariationWeight (pairGrading (stateGrading S) realGrading) base loss
      (0 : AnnularState S × ℝ) (Fin.cons (v, 0) Fin.elim0) =
      stateGrading S base v + stateGrading S loss v := by
  simp [oneHighVariationWeight, pairGrading, realGrading]

/-- An actual position-dependent bound for every logarithmic state direction.
The only cell appearing on the right is the cell containing the evaluation
point. No control interval-to-cell identification is used. -/
theorem n08_logProfile_reference_coefficient_bound (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ D.cells m → ∀ v : AnnularState S,
      |D.w r * n08_stateLogProfile D S C v r| ≤
        B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
          (stateGrading S base v + stateGrading S loss v) := by
  have hε : 0 < ε := hN.2.1
  have hcoeff := hN.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨B, hB, hBj⟩ := hcoeff 1 0
  refine ⟨B, hB, ?_⟩
  intro m r hr v
  obtain ⟨J, hJ⟩ := hBj m 0 0 0 (r, 0) (by omega) hr
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε := n08_reference_mem hε
  have hline := J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain hz (v, 0)
  have hd : HasDerivAt
      (fun t : ℝ => coefficientFamily D S C 0 0 0 (r, 0)
        ((C.referenceState, 0) + t • (v, 0)))
      (J.D 1 (C.referenceState, 0) (Fin.cons (v, 0) Fin.elim0)) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr hline
  have ha := n08_coefficientA_state_hasDerivAt hT hS hN C.referenceState v (r, 0)
  have hd' : HasDerivAt
      (fun t : ℝ => coefficientFamily D S C 0 0 0 (r, 0) (C.referenceState + t • v, 0))
      (J.D 1 (C.referenceState, 0) (Fin.cons (v, 0) Fin.elim0)) 0 := by
    simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero] using hd
  have hvalue : J.D 1 (C.referenceState, 0) (Fin.cons (v, 0) Fin.elim0) =
      D.w r * n08_stateLogProfile D S C v r := by
    simpa only [n08_stateProfile_reference hN.2.2.1] using hd'.unique ha
  have hbound := hJ (C.referenceState, 0) hz (Fin.cons (v, 0) Fin.elim0)
  simpa only [hvalue, sub_self, Nat.zero_add, n08_oneHigh_first_at_zero] using hbound

end ContinuousFlexibility.Statements
