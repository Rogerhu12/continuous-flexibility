import ContinuousFlexibility.Analysis.CircleStripAngularInterpolation
import ContinuousFlexibility.Analysis.N01ResidualUniformBounds
import ContinuousFlexibility.Analysis.N01ReturnTransportSpatialTowers
import ContinuousFlexibility.Analysis.MaterialSampleDiscreteEnvelope

/-!
# The actual angular boundary estimates for the transport system

All closed-radius selectors are estimated before a radius is chosen.
The actual spatial towers are then identified with the same circle
families. The independent displacement retains its positive sample
height; the bounded height factors of the other two fields are absorbed
only into numerical constants.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

local instance n01TransportAngularInterpolationStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem correctionParameterGrading_monotone (S : PhysicalSpacesData) :
    Monotone (pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading) :=
  tamePairGrading_monotone (sectorPairGrading_monotone S)
    (gradedSeminorm_monotone (fun n => (S.circle (3 / 4 : ℝ)).level n)
      (S.circle (3 / 4 : ℝ)).bond)

theorem correctionParameterGrading_hasInterpolation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) :
    HasInterpolation (pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading) :=
  hasInterpolation_of_hasSmoothing (correctionParameterGrading_monotone S)
    (hasSmoothing_pairGrading
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
      (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.1)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)

/-- A point of a negative component extends to an actual closed-radius
selector. The extension leaves all other components at their left end. -/
include hN in
theorem N01Properties.closedRadiusSelector_cover
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) :
    ∃ s : {s : ℕ → ℝ // ∀ i, s i ∈ Icc (C.left i) (C.right i)}, s.val m = r := by
  classical
  let s : ℕ → ℝ := Function.update C.left m r
  have hs (i : ℕ) : s i ∈ Icc (C.left i) (C.right i) := by
    by_cases hi : i = m
    · subst i
      simpa only [s, Function.update_self] using hr
    · have hleft : C.left i ∈ Icc (C.left i) (C.right i) :=
        ⟨le_rfl, (hN.2.2.2.1.1 i).2.1.le⟩
      simpa only [s, Function.update_noteq hi] using hleft
  exact ⟨⟨s, hs⟩, Function.update_self _ _ _⟩

variable
  (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
    r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
      deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)
  (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
  (χ : ℕ → ℝ → ℝ)
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)

include hN hS hT hflow hl hh hχrange in
theorem N01Properties.returnCorrectionPulledDisplacement_angular_diagonal_interpolation
    (J : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1.1)
          m x.2 x.1.2))
    (nmax : ℕ) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading
    ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ m x, x ∈ sectorNeighborhood S base ε ε ×ˢ univ →
        ∀ w, p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
        |jointMixedDiagonal (J m) n 0 b x w y| ≤
          K * T.H (T.sample m) ^ (3 / 4 : ℝ) *
            (1 + p (N + B + 1) x + p (N + B + 1) w) ^
              ((b : ℝ) / ((N : ℝ) + 1)) := by
  let I := {s : ℕ → ℝ // ∀ m, s m ∈ Icc (C.left m) (C.right m)}
  let rsel : I → ℕ → ℝ := Subtype.val
  have hrsel (i : I) (m : ℕ) := i.property m
  have hcover (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (l m) (h m)) : ∃ i : I, rsel i m = r :=
    hN.closedRadiusSelector_cover m r ⟨((hl m).trans hr.1).le, (hr.2.trans (hh m)).le⟩
  have hg := hN.uniformSmoothFamilyOn_returnCorrectionPulledDisplacementCircleLinear
    hS hT hflow χ hχrange rsel hrsel
  apply hg.realized_strip_angular_interpolation (correctionParameterGrading_monotone S)
    (correctionParameterGrading_hasInterpolation hS) (hS.2.1 (3 / 4 : ℝ))
    ((material_circle_sample_weights_pos hT hN.1.1).2) l h rsel hcover J _ nmax
  intro i m hr x hx θ
  exact (hN.returnCorrectionPulledDisplacementCircleLinear_decode hS hT χ hχrange
    (rsel i) (hrsel i) x.1 hx.1 x.2 m θ).symm

include hN hS hT hflow hl hh in
theorem N01Properties.returnFlowInverseSlope_angular_diagonal_interpolation
    (J : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnFlowInverseSlope S C (liftSectorParameter S C x.1.1) m x.2))
    (nmax : ℕ) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading
    ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ m x, x ∈ sectorNeighborhood S base ε ε ×ˢ univ →
        ∀ w, p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
        |jointMixedDiagonal (J m) n 0 b x w y| ≤
          K * (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            ((b : ℝ) / ((N : ℝ) + 1)) := by
  let I := {s : ℕ → ℝ // ∀ m, s m ∈ Icc (C.left m) (C.right m)}
  let rsel : I → ℕ → ℝ := Subtype.val
  have hrsel (i : I) (m : ℕ) := i.property m
  have hcover (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (l m) (h m)) : ∃ i : I, rsel i m = r :=
    hN.closedRadiusSelector_cover m r ⟨((hl m).trans hr.1).le, (hr.2.trans (hh m)).le⟩
  have hg := (hN.uniformSmoothFamilyOn_selectorInverseSlopeCircle hS hT hflow rsel hrsel).fst
    (sectorPairGrading_monotone S)
    (gradedSeminorm_monotone (fun n => (S.circle (3 / 4 : ℝ)).level n)
      (S.circle (3 / 4 : ℝ)).bond)
    (sectorNeighborhood_isOpen S base ε ε)
  obtain ⟨KH, hKH, hheight⟩ := materialSample_H_M_envelope hT hN.1.1
    (γ := (3 / 4 : ℝ)) (by norm_num) 0
  have hhgt (m : ℕ) : T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ KH := by
    simpa only [Real.rpow_zero, mul_one] using hheight m
  apply hg.realized_strip_angular_interpolation_add_const (correctionParameterGrading_monotone S)
    (correctionParameterGrading_hasInterpolation hS) (hS.2.1 (3 / 4 : ℝ))
    ((material_circle_sample_weights_pos hT hN.1.1).2) KH hKH.le hhgt l h rsel hcover J 1 _ nmax
  intro i m hr x hx θ
  rw [hN.selectorInverseSlopeCircle_decode hS hT (rsel i) (hrsel i) x.1 hx.1 m θ]
  change _ = 1 + (returnFlowInverseSlope S C (liftSectorParameter S C x.1) m
    (rsel i m, θ) - 1)
  ring

include hN hS hT hflow hl hh hχrange in
theorem N01Properties.returnCorrectionPulledResidual_angular_diagonal_interpolation
    (hR : N02Properties D T S C R base ε)
    (J : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1.1)
          m x.2 (R.residual (liftSectorParameter S C x.1.1))))
    (nmax : ℕ) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading
    ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ m x, x ∈ sectorNeighborhood S base ε ε ×ˢ univ →
        ∀ w, p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
        |jointMixedDiagonal (J m) n 0 b x w y| ≤
          K * (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            ((b : ℝ) / ((N : ℝ) + 1)) := by
  let I := {s : ℕ → ℝ // ∀ m, s m ∈ Icc (C.left m) (C.right m)}
  let rsel : I → ℕ → ℝ := Subtype.val
  have hrsel (i : I) (m : ℕ) := i.property m
  have hcover (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (l m) (h m)) : ∃ i : I, rsel i m = r :=
    hN.closedRadiusSelector_cover m r ⟨((hl m).trans hr.1).le, (hr.2.trans (hh m)).le⟩
  have hg := (hN.uniformSmoothFamilyOn_returnCorrectionPulledResidual_of_N02
    hS hT hR hflow χ hχrange rsel hrsel).fst
    (sectorPairGrading_monotone S)
    (gradedSeminorm_monotone (fun n => (S.circle (3 / 4 : ℝ)).level n)
      (S.circle (3 / 4 : ℝ)).bond)
    (sectorNeighborhood_isOpen S base ε ε)
  obtain ⟨KH, hKH, hheight⟩ := materialSample_H_M_envelope hT hN.1.1
    (γ := (3 / 4 : ℝ)) (by norm_num) 0
  have hhgt (m : ℕ) : T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ KH := by
    simpa only [Real.rpow_zero, mul_one] using hheight m
  apply hg.realized_strip_angular_interpolation_add_const (correctionParameterGrading_monotone S)
    (correctionParameterGrading_hasInterpolation hS) (hS.2.1 (3 / 4 : ℝ))
    ((material_circle_sample_weights_pos hT hN.1.1).2) KH hKH.le hhgt l h rsel hcover J 0 _ nmax
  intro i m hr x hx θ
  simpa only [zero_add] using
    (hN.returnCorrectionPulledDisplacementCircleLinear_decode hS hT χ hχrange
      (rsel i) (hrsel i) x.1 hx.1 (R.residual (liftSectorParameter S C x.1)) m θ).symm

end ContinuousFlexibility.Statements
