module

public import ContinuousFlexibility.Analysis.N05CanonicalSourceSingle
public import ContinuousFlexibility.Analysis.N05CanonicalInverseDefinition
public import ContinuousFlexibility.Analysis.N05CanonicalOutputBlock

/-!
# Actual raw endpoint blocks of the fixed canonical inverse

Each block is literally a coordinate of the one global inverse applied to
a single canonical L² input. Its source uses the same actual auxiliary
integral and normalizer at every endpoint. The physical inverse and selected
left constant then give a uniform endpoint square bound on that very block.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open ContinuousFlexibility.Radial

/-- The raw block has no endpoint or material exponent in its definition. -/
def n05CanonicalInverseBlock (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (G : RadialSource → RadialUnknown) (k m : ℕ)
    (u : CanonicalL2 S K m) : CanonicalL2 S K k :=
  (n05CanonicalGlobalInverse D S C K G (Pi.single m u)).1 k

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The literal corrected single-coordinate source is compatible at the
same positive endpoint. Its actual auxiliary scalar is included in the
bound, without any angular constancy assumption on the normalizer. -/
theorem n05_canonicalNormalizedSource_single_reference_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {σ : ℝ} (hσ : 0 < σ) (M : ℝ) :
    ∃ C0 A : ℝ, 0 < C0 ∧ 0 < A ∧ ∀ m (u : CanonicalL2 S K m),
      SourceMember D σ M (n05CanonicalNormalizedSource D S C K (Pi.single m u)) ∧
      n05CanonicalAuxiliaryScalar D S C K (Pi.single m u) ^ 2 +
        sourceNormSquare D σ M (n05CanonicalNormalizedSource D S C K (Pi.single m u)) ≤
          C0 * radialE (D.cellIndex (K.cell m)) ^ A *
            Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖u‖ ^ 2 := by
  obtain ⟨Cs, A, hCs, hA, hsource⟩ :=
    n05_canonicalSourceLift_single_reference_bound hD hT h hcoordinates hσ.le M
  obtain ⟨Cn, hCn, hnormalize⟩ := n05_referenceSource_normalized_square_bound hD hS hσ M
  refine ⟨Cn * Cs, A, mul_pos hCn hCs, hA, fun m u => ?_⟩
  have hf := (hsource m u).1
  have hmember : SourceMember D σ M
      (n05CanonicalNormalizedSource D S C K (Pi.single m u)) :=
    n05_referenceSource_normalized_member hD hS hσ hf
      (n05CanonicalSourceLift_periodic S C K (Pi.single m u))
      (fun r θ => n05CanonicalSourceLift_even S C K (Pi.single m u) r θ)
  refine ⟨hmember, ?_⟩
  have hn := hnormalize (n05CanonicalSourceLift S C K (Pi.single m u)) hf
  change n05CanonicalAuxiliaryScalar D S C K (Pi.single m u) ^ 2 +
      sourceNormSquare D σ M (n05CanonicalNormalizedSource D S C K (Pi.single m u)) ≤
    Cn * sourceNormSquare D σ M (n05CanonicalSourceLift S C K (Pi.single m u), 0) at hn
  calc
    _ ≤ Cn * sourceNormSquare D σ M
        (n05CanonicalSourceLift S C K (Pi.single m u), 0) := hn
    _ ≤ Cn * (Cs * radialE (D.cellIndex (K.cell m)) ^ A *
        Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hsource m u).2 hCn.le
    _ = _ := by ring

/-- A uniform bound for the actual raw inverse block at a fixed endpoint.
The source and output material exponents are exactly those of the given
physical inverse. Only the coefficient power grows under coordinate change. -/
theorem n05_canonicalInverseBlock_endpoint_square_bound
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {σ M0 M1 : ℝ} (hσ : 0 < σ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D σ M0 M1 G) :
    ∃ C0 A : ℝ, 0 < C0 ∧ 0 < A ∧ ∀ k m (u : CanonicalL2 S K m),
      Real.exp (2 * σ * radialS (D.cellIndex (K.cell k))) *
          ‖n05CanonicalInverseBlock D S C K G k m u‖ ^ 2 ≤
        C0 * radialE (D.cellIndex (K.cell k)) ^ A *
          radialE (D.cellIndex (K.cell m)) ^ A *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖u‖ ^ 2 := by
  obtain ⟨Cs, As, hCs, hAs, hsource⟩ :=
    n05_canonicalNormalizedSource_single_reference_bound hD.1 hT hS h hcoordinates hσ M0
  obtain ⟨Ci, hCi, hinverse⟩ :=
    n05_referenceInverse_selectedLeftConstant hD.1 hD.2.2.2.1 hσ hG
  obtain ⟨_, _, houtput⟩ :=
    n05_outputRealization_canonicalHeight_choice_bound hD hT hS h hcoordinates hσ M1
  obtain ⟨Co, Ao, hCo, hAo, hpiece⟩ :=
    n05_outputRealization_canonical_piece_bound hD hT hS h hcoordinates hσ.le M1
  let B : ℝ := Co * Ci ^ 2 * Cs
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, As + Ao, hB, add_pos hAs hAo, fun k m u => ?_⟩
  let F : CanonicalSequence S K := Pi.single m u
  let H : RadialSource := n05CanonicalNormalizedSource D S C K F
  let U : RadialUnknown := G H
  let a : ℝ := n05_referenceLeftConstant D U
  let w : CanonicalL2Sequence S K :=
    n05CanonicalHeightL2Sequence S C K (fun p => U.1 p - a * S.chiLeft p.1)
  have hH : SourceMember D σ M0 H := (hsource m u).1
  have hHnorm : sourceNormSquare D σ M0 H ≤
      Cs * radialE (D.cellIndex (K.cell m)) ^ As *
        Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖u‖ ^ 2 := by
    have hn : n05CanonicalAuxiliaryScalar D S C K F ^ 2 +
        sourceNormSquare D σ M0 H ≤
      Cs * radialE (D.cellIndex (K.cell m)) ^ As *
        Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖u‖ ^ 2 :=
      (hsource m u).2
    linarith only [hn, sq_nonneg (n05CanonicalAuxiliaryScalar D S C K F)]
  obtain ⟨hU, hUnorm⟩ := hinverse H hH
  have hrep (j : ℕ) : (w j : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K j]
      canonicalHeight S K (C.referenceState, 0) j
        (fun p => U.1 p - a * S.chiLeft p.1) :=
    (houtput a U hU).1 j
  have hEkpos : 0 < radialE (D.cellIndex (K.cell k)) := Real.exp_pos _
  have hEmpos : 0 < radialE (D.cellIndex (K.cell m)) := Real.exp_pos _
  have hraw : Real.exp (2 * σ * radialS (D.cellIndex (K.cell k))) * ‖w k‖ ^ 2 ≤
      B * radialE (D.cellIndex (K.cell k)) ^ Ao *
        radialE (D.cellIndex (K.cell m)) ^ As *
        Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖u‖ ^ 2 := by
    calc
      _ ≤ Co * radialE (D.cellIndex (K.cell k)) ^ Ao * outputNormSquare D σ M1 a U :=
        hpiece k a U (w k) hU (hrep k)
      _ ≤ Co * radialE (D.cellIndex (K.cell k)) ^ Ao *
          (Ci ^ 2 * sourceNormSquare D σ M0 H) :=
        mul_le_mul_of_nonneg_left hUnorm (by positivity)
      _ ≤ Co * radialE (D.cellIndex (K.cell k)) ^ Ao *
          (Ci ^ 2 * (Cs * radialE (D.cellIndex (K.cell m)) ^ As *
            Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖u‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hHnorm (sq_nonneg Ci)) (by positivity)
      _ = _ := by dsimp only [B]; ring
  have hEk : 1 ≤ radialE (D.cellIndex (K.cell k)) :=
    Real.one_le_exp (radialQ_nonneg _)
  have hEm : 1 ≤ radialE (D.cellIndex (K.cell m)) :=
    Real.one_le_exp (radialQ_nonneg _)
  have hk : radialE (D.cellIndex (K.cell k)) ^ Ao ≤
      radialE (D.cellIndex (K.cell k)) ^ (As + Ao) :=
    Real.rpow_le_rpow_of_exponent_le hEk (by linarith only [hAs])
  have hm : radialE (D.cellIndex (K.cell m)) ^ As ≤
      radialE (D.cellIndex (K.cell m)) ^ (As + Ao) :=
    Real.rpow_le_rpow_of_exponent_le hEm (by linarith only [hAo])
  have hcoeff := mul_le_mul hk hm
    (Real.rpow_nonneg hEmpos.le As)
    (Real.rpow_nonneg hEkpos.le (As + Ao))
  change Real.exp (2 * σ * radialS (D.cellIndex (K.cell k))) * ‖w k‖ ^ 2 ≤ _
  calc
    _ ≤ B * radialE (D.cellIndex (K.cell k)) ^ Ao *
        radialE (D.cellIndex (K.cell m)) ^ As *
        Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖u‖ ^ 2 := hraw
    _ = B * (radialE (D.cellIndex (K.cell k)) ^ Ao *
        radialE (D.cellIndex (K.cell m)) ^ As) *
        (Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖u‖ ^ 2) := by ring
    _ ≤ B * (radialE (D.cellIndex (K.cell k)) ^ (As + Ao) *
        radialE (D.cellIndex (K.cell m)) ^ (As + Ao)) *
        (Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoeff hB.le)
        (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    _ = _ := by ring

end ContinuousFlexibility.Statements
