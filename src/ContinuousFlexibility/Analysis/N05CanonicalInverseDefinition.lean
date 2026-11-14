module

public import ContinuousFlexibility.Analysis.N05CanonicalSourceEmbedding
public import ContinuousFlexibility.Analysis.N05CanonicalOutputChoice
public import ContinuousFlexibility.Analysis.N05ReferenceSourceBounds
public import ContinuousFlexibility.Analysis.N05ReferenceLeftChoice

/-!
# One fixed canonical inverse from the actual physical reference inverse

The source lift, its actual compatibility integral, the physical inverse,
the selected left scalar, and the unique canonical height sequence are
chosen once. Their definitions have no endpoint or material weight parameter.
Every stronger canonical volume level gives their genuine physical graph
and canonical representative identities.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open ContinuousFlexibility.Radial

/-- The actual compatibility integral of the fixed physical source lift. -/
def n05CanonicalAuxiliaryScalar (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (F : CanonicalSequence S K) : ℝ :=
  ∫ r in D.a..D.b, radialAngularMean (fun θ => n05CanonicalSourceLift S C K F (r, θ))

/-- The source obtained by the actual normalized auxiliary correction. -/
def n05CanonicalNormalizedSource (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (F : CanonicalSequence S K) : RadialSource :=
  ((fun p => n05CanonicalSourceLift S C K F p -
    n05CanonicalAuxiliaryScalar D S C K F * (S.height (3 / 4 : ℝ)).decode S.psi p), 0)

/-- One map on all canonical sequences, obtained from the same physical
inverse and the same actual representative choices at every volume level. -/
def n05CanonicalGlobalInverse (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (G : RadialSource → RadialUnknown) : CanonicalSequence S K → CanonicalUnknown S K :=
  fun F =>
    let U := G (n05CanonicalNormalizedSource D S C K F)
    let a := n05_referenceLeftConstant D U
    (n05CanonicalHeightL2Sequence S C K (fun p => U.1 p - a * S.chiLeft p.1),
      (a, U.2, n05CanonicalAuxiliaryScalar D S C K F))

theorem n05CanonicalNormalizedSource_mem
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    {γw γ : ℝ} (hγw : 0 < γw) (hgap : γw < γ) (t M : ℝ) (s : ℕ)
    (v : V.level γ t s) :
    SourceMember D γw M
      (n05CanonicalNormalizedSource D S C K (V.forget γ t s v)) := by
  obtain ⟨_, _, hsource⟩ :=
    n05_canonicalSourceLift_reference_bound hD hT h hcoordinates hV hγw hgap t M s
  exact n05_referenceSource_normalized_member hD hS hγw (hsource v).1
    (n05CanonicalSourceLift_periodic S C K (V.forget γ t s v))
    (fun r θ => n05CanonicalSourceLift_even S C K (V.forget γ t s v) r θ)

/-- The fixed map has the actual canonical representatives and literal
physical reference graph on every stronger canonical volume level. -/
theorem n05CanonicalGlobalInverse_represents
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    {γw γ M0 M1 : ℝ} (hγw : 0 < γw) (hgap : γw < γ)
    {G : RadialSource → RadialUnknown} (hG : ReferenceInverseProperties D γw M0 M1 G)
    (t : ℝ) (s : ℕ) (v : V.level γ t s) :
    let F := V.forget γ t s v
    let U := G (n05CanonicalNormalizedSource D S C K F)
    HasCanonicalRepresentation D S C K (C.referenceState, 0)
      (n05CanonicalGlobalInverse D S C K G F) F U.1 (n05CanonicalSourceLift S C K F) ∧
    ReferenceGraph D γw M0 M1
      (U.1, (n05CanonicalGlobalInverse D S C K G F).2.2.1)
      ((fun p => n05CanonicalSourceLift S C K F p -
        (n05CanonicalGlobalInverse D S C K G F).2.2.2 *
          (S.height (3 / 4 : ℝ)).decode S.psi p), 0) := by
  dsimp only
  let F : CanonicalSequence S K := V.forget γ t s v
  let U : RadialUnknown := G (n05CanonicalNormalizedSource D S C K F)
  have hsource : SourceMember D γw M0 (n05CanonicalNormalizedSource D S C K F) :=
    n05CanonicalNormalizedSource_mem hD.1 hT hS h hcoordinates hV hγw hgap t M0 s v
  have hgraph : ReferenceGraph D γw M0 M1 U
      (n05CanonicalNormalizedSource D S C K F) :=
    hG.1 _ hsource
  obtain ⟨a, ha⟩ := hgraph.1
  have hselected : OutputRealization D γw M1 (n05_referenceLeftConstant D U) U := by
    rw [n05_referenceLeftConstant_eq hD.1 hD.2.2.2.1 hγw ha]
    exact ha
  obtain ⟨_, _, houtput⟩ :=
    n05_outputRealization_canonicalHeight_choice_bound hD hT hS h hcoordinates hγw M1
  have hrep := (houtput (n05_referenceLeftConstant D U) U hselected).1
  have hFrep := n05CanonicalSourceLift_source_ae h hcoordinates F
    (n05_volumeMember_reflection hV (show VolumeMember S K V γ t s F from ⟨v, rfl⟩))
  exact ⟨⟨hrep, hFrep⟩, hgraph⟩

/-- The unweighted canonical output and all three actual auxiliary scalars
satisfy one square bound on each stronger volume level. This estimate does
not assert membership in a final weighted canonical output graph. -/
theorem n05CanonicalGlobalInverse_square_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    {γw γ M0 M1 : ℝ} (hγw : 0 < γw) (hgap : γw < γ)
    {G : RadialSource → RadialUnknown} (hG : ReferenceInverseProperties D γw M0 M1 G)
    (t : ℝ) (s : ℕ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ v : V.level γ t s,
      let u := n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)
      ‖u.1‖ ^ 2 + u.2.1 ^ 2 + u.2.2.1 ^ 2 + u.2.2.2 ^ 2 ≤ C0 * ‖v‖ ^ 2 := by
  obtain ⟨Cs, hCs, hsource⟩ :=
    n05_canonicalSourceLift_reference_bound hD.1 hT h hcoordinates hV hγw hgap t M0 s
  obtain ⟨Cn, hCn, hnormalize⟩ := n05_referenceSource_normalized_square_bound hD.1 hS hγw M0
  obtain ⟨Ci, hCi, hinverse⟩ := n05_referenceInverse_selectedLeftConstant
    hD.1 hD.2.2.2.1 hγw hG
  obtain ⟨Co, hCo, houtput⟩ :=
    n05_outputRealization_canonicalHeight_choice_bound hD hT hS h hcoordinates hγw M1
  let A : ℝ := (Co + 1) * Ci ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨((A + 1) * Cn) * Cs, by positivity, fun v => ?_⟩
  dsimp only
  let F : CanonicalSequence S K := V.forget γ t s v
  let f : PolarPoint → ℝ := n05CanonicalSourceLift S C K F
  let lam : ℝ := n05CanonicalAuxiliaryScalar D S C K F
  let H : RadialSource := n05CanonicalNormalizedSource D S C K F
  let U : RadialUnknown := G H
  let a : ℝ := n05_referenceLeftConstant D U
  let w : CanonicalL2Sequence S K :=
    n05CanonicalHeightL2Sequence S C K (fun p => U.1 p - a * S.chiLeft p.1)
  have hf : SourceDerivativeMember D γw M0 f := (hsource v).1
  have hF : SourceMember D γw M0 H :=
    n05CanonicalNormalizedSource_mem hD.1 hT hS h hcoordinates hV hγw hgap t M0 s v
  have hnormN : lam ^ 2 + sourceNormSquare D γw M0 H ≤ Cn * sourceNormSquare D γw M0 (f, 0) :=
    hnormalize f hf
  obtain ⟨hU, hnormU⟩ := hinverse H hF
  have hnormW : ‖w‖ ^ 2 ≤ Co * outputNormSquare D γw M1 a U :=
    (houtput a U hU).2
  have hsourceNonneg : 0 ≤ sourceNormSquare D γw M0 H :=
    add_nonneg (sq_nonneg _) (tsum_nonneg
      (fun m => sourceCellSquare_nonneg hD.1.choose_spec.1.2.1.le γw M0 hF.1 m))
  have hremNonneg : 0 ≤ ∑' m, outputCellSquare D γw M1 (outputRemainder D a U) m :=
    tsum_nonneg (fun m => outputCellSquare_nonneg hD.1.choose_spec.1.2.1.le γw M1 hU.1 m)
  have hscalars : a ^ 2 + U.2 ^ 2 ≤ outputNormSquare D γw M1 a U := by
    change a ^ 2 + U.2 ^ 2 ≤ a ^ 2 + U.2 ^ 2 +
      ∑' m, outputCellSquare D γw M1 (outputRemainder D a U) m
    exact le_add_of_nonneg_right hremNonneg
  have hfirst : ‖w‖ ^ 2 + a ^ 2 + U.2 ^ 2 ≤
      A * sourceNormSquare D γw M0 H := by
    calc
      _ ≤ (Co + 1) * outputNormSquare D γw M1 a U := by
        nlinarith only [hnormW, hscalars]
      _ ≤ (Co + 1) * (Ci ^ 2 * sourceNormSquare D γw M0 H) :=
        mul_le_mul_of_nonneg_left hnormU (by positivity)
      _ = _ := (mul_assoc _ _ _).symm
  change ‖w‖ ^ 2 + a ^ 2 + U.2 ^ 2 + lam ^ 2 ≤ _
  calc
    _ ≤ (A + 1) * (lam ^ 2 + sourceNormSquare D γw M0 H) := by
      nlinarith only [hfirst, hsourceNonneg, mul_nonneg hA (sq_nonneg lam)]
    _ ≤ (A + 1) * (Cn * sourceNormSquare D γw M0 (f, 0)) :=
      mul_le_mul_of_nonneg_left hnormN (by positivity)
    _ ≤ (A + 1) * (Cn * (Cs * ‖v‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hsource v).2 hCn.le) (by positivity)
    _ = _ := by ring

end ContinuousFlexibility.Statements
