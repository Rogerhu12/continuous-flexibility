import ContinuousFlexibility.Analysis.N07aGeometryOpenCoefficients
import ContinuousFlexibility.Analysis.N07aNeighborhood

/-!
# Positivity of the actual current canonical leading coefficient

The reference inverse-coefficient bound and the genuine H^(3/4) difference
gain give one neighborhood for every piece. No lower bound E0 ≥ 1 and no
positivity certificate for a new coefficient are used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

set_option backward.isDefEq.respectTransparency true
open ContinuousFlexibility.Statements

attribute [local instance]
  n07aNonlinearAnnularGroup
  n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup
  n07aNonlinearAnnularSMul
  n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup
  n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup
  n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup
  n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup
  n07aNonlinearDirectionsSMul
  n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup
  n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup
  n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

theorem n07aCanonicalUnitPoint_maps (m : ℕ) (hm : K.left m < K.right m) :
    MapsTo (CanonicalGeometry.canonicalUnitPoint K m) CanonicalGeometry.unitStrip
      (canonicalOpen S K m) := by
  intro p hp
  have hL : 0 < K.right m - K.left m := sub_pos.mpr hm
  refine ⟨⟨?_, ?_⟩, mem_univ _⟩
  · change K.left m < K.left m + (K.right m - K.left m) * p.1
    nlinarith [mul_pos hL hp.1.1]
  · change K.left m + (K.right m - K.left m) * p.1 < K.right m
    nlinarith [mul_pos hL (sub_pos.mpr hp.1.2)]

theorem n07a_referencePrincipal_inverse_bound
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hprincipal : CanonicalGeometry.ReferencePrincipal T S C K)
    (hinterval : ∀ m, K.left m < K.right m) :
    ∃ B : ℝ, 0 < B ∧ ∀ m y, y ∈ canonicalOpen S K m →
      ((K.coefficients (C.referenceState, 0) m).a y)⁻¹ ≤
        B * T.E0 (T.sample (K.cell m)) ^ B := by
  let B : ℝ := (href.2 0).choose
  have hB : 0 < B := (href.2 0).choose_spec.1
  have hBb := (href.2 0).choose_spec.2
  refine ⟨B, hB, fun m y hy => ?_⟩
  let p := n07aCanonicalUnitInversePoint K m y
  have hp : p ∈ CanonicalGeometry.unitStrip :=
    n07aCanonicalUnitInversePoint_maps (hinterval m) hy
  have hpy : CanonicalGeometry.canonicalUnitPoint K m p = y :=
    n07aCanonicalUnitPoint_inverse (hinterval m) y
  have ha₀ : 0 < (K.coefficients (C.referenceState, 0) m).a y :=
    (hprincipal.1 m y hy).1
  have hi := hBb m .principalAInverse p hp 0 0 (by omega)
  rw [spaces_mixedDerivative_zero] at hi
  change |((K.coefficients (C.referenceState, 0) m).a
    (CanonicalGeometry.canonicalUnitPoint K m p))⁻¹| ≤ _ at hi
  rw [hpy, abs_of_pos (inv_pos.mpr ha₀)] at hi
  exact hi

theorem n07a_principalDifference_zero
    (z : CanonicalGeometry.Parameter S) (m : ℕ)
    (hm : K.left m < K.right m) (y : PolarPoint) (hy : y ∈ canonicalOpen S K m) :
    CanonicalGeometry.differenceJets D T S C L K z .principalA m 0 0
      ⟨n07aCanonicalUnitInversePoint K m y, n07aCanonicalUnitInversePoint_maps hm hy⟩ =
      (K.coefficients (liftSectorParameter S C z) m).a y -
        (K.coefficients (C.referenceState, 0) m).a y := by
  change mixedDerivative 0 0
    (fun q => CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m
      .principalA q - CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m
      .principalA q) (n07aCanonicalUnitInversePoint K m y) = _
  rw [spaces_mixedDerivative_zero]
  change (K.coefficients (liftSectorParameter S C z) m).a
    (CanonicalGeometry.canonicalUnitPoint K m (n07aCanonicalUnitInversePoint K m y)) -
    (K.coefficients (C.referenceState, 0) m).a
    (CanonicalGeometry.canonicalUnitPoint K m (n07aCanonicalUnitInversePoint K m y)) = _
  rw [n07aCanonicalUnitPoint_inverse hm y]

private theorem n07a_principal_abs_bound_transport {x y R Q : ℝ}
    (he : x = y) (hR : R = Q) (h : |x| ≤ R) : |y| ≤ Q := he ▸ hR ▸ h

theorem n07a_currentPrincipal_difference_bound
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hinterval : ∀ m, K.left m < K.right m) :
    ∃ loss : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m y,
        y ∈ canonicalOpen S K m →
          |(K.coefficients (liftSectorParameter S C z) m).a y -
            (K.coefficients (C.referenceState, 0) m).a y| ≤
            B * T.E0 (T.sample (K.cell m)) ^ B *
              T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
                CanonicalGeometry.parameterGrading S loss z := by
  let loss : ℕ := hcur.2.1.choose
  have hdiff := hcur.2.1.choose_spec
  let B : ℝ := (hdiff 0).choose
  have hB : 0 < B := (hdiff 0).choose_spec.1
  have hBb := (hdiff 0).choose_spec.2
  refine ⟨loss, B, hB, fun z hz m y hy => ?_⟩
  have hd := hBb z hz m .principalA
    ⟨n07aCanonicalUnitInversePoint K m y,
      n07aCanonicalUnitInversePoint_maps (hinterval m) hy⟩ 0 0 (by omega)
  exact n07a_principal_abs_bound_transport
    (n07a_principalDifference_zero (D := D) (T := T) (L := L) z m (hinterval m) y hy)
    (congrArg (fun v : ℝ => B * T.E0 (T.sample (K.cell m)) ^ B *
      T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * v)
      (congrArg (fun n => CanonicalGeometry.parameterGrading S n z) (Nat.zero_add loss))) hd

end ContinuousFlexibility.Analysis
