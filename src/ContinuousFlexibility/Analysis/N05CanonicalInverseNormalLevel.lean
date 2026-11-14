module

public import ContinuousFlexibility.Analysis.N05CanonicalInverseNormal
public import ContinuousFlexibility.Analysis.N05CanonicalNormalizedAngularJets

/-!
# Actual first normal derivatives on every stronger source level

The first angular jet is the genuine corrected source derivative. Thus the
physical first-normal estimate applies to the normalized source used by the
fixed global inverse. The material shift and piece coefficient power are
chosen before the source level and its finite angular order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory ContinuousFlexibility.Radial

theorem n05CanonicalGlobalInverse_normal_level_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss : ℕ} {ε γw γ M0 M1 MN : ℝ} {G : RadialSource → RadialUnknown}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hγw : 0 < γw) (hG : ReferenceInverseProperties D γw M0 M1 G)
    (hN : FirstNormalInverseEstimate D γw M0 MN G)
    (hV : IsVolumeModel T S K V) (hgap : γw < γ) :
    ∃ A P : ℝ, 0 < A ∧ 0 < P ∧ ∀ t : ℝ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ v : V.level γ t (s + 1),
      let F := V.forget γ t (s + 1) v
      let U := n05CanonicalGlobalInverse D S C K G F
      let W := n05CanonicalRadialJetSequence S K U.1
      ∃ ur : PolarPoint → ℝ,
        let g := n05CanonicalInverseNormalField D S C K G F ur
        WeakNormalDerivative D (G (n05CanonicalNormalizedSource D S C K F)).1 ur ∧
        OutputRealization D γw MN 0 (ur, 0) ∧
        MemLp g 2 (referenceWeightedMeasure D γw (-(max M1 MN + A))) ∧
        (∀ m, n05WeakCanonicalRadialDerivative S K m (U.1 m) (W m)) ∧
        (∀ m, (W m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          canonicalHeight S K (C.referenceState, 0) m g) ∧
        (∀ m, n05CanonicalReflection S K m (W m) = W m) ∧
        ‖W‖ ^ 2 + outputNormSquare D γw (max M1 MN + A) 0 (g, 0) ≤ B * ‖v‖ ^ 2 ∧
        ∀ k, Real.exp (2 * γw * radialS (D.cellIndex (K.cell k))) * ‖W k‖ ^ 2 ≤
          B * radialE (D.cellIndex (K.cell k)) ^ P * ‖v‖ ^ 2 := by
  obtain ⟨A, hA, hall⟩ := n05CanonicalGlobalInverse_normal_of_source hD hT hS h hcoordinates
  obtain ⟨B0, P, hB0, hP, hnormal⟩ := hall γw hγw M0 M1 MN G hG hN
  refine ⟨A, P, hA, hP, fun t s => ?_⟩
  obtain ⟨Cr, hCr, hraw⟩ :=
    n05_canonicalSourceLift_reference_bound hD.1 hT h hcoordinates hV hγw hgap t M0 (s + 1)
  obtain ⟨Cn, hCn, hnormalize⟩ := n05_referenceSource_normalized_square_bound hD.1 hS hγw M0
  obtain ⟨Cj, hCj, hjets⟩ := n05CanonicalNormalizedSource_allAngularJets
    h hcoordinates hD.1 hT hV hγw hgap t M0 hS (s + 1)
  let C0 : ℝ := Cn * Cr + Cj
  have hC0 : 0 < C0 := by dsimp only [C0]; positivity
  refine ⟨B0 * C0, mul_pos hB0 hC0, fun v => ?_⟩
  let j : Fin (s + 1 + 1) := ⟨1, by omega⟩
  let F := V.forget γ t (s + 1) v
  let X := n05CanonicalNormalizedSource D S C K F
  let fθ := n05CanonicalNormalizedJetSource D T S C K V γ t (s + 1) j v
  have hF : SourceMember D γw M0 X :=
    n05CanonicalNormalizedSource_mem hD.1 hT hS h hcoordinates hV hγw hgap t M0 (s + 1) v
  have hs := hjets v j
  have hθ : WeakAngularDerivative D X.1 fθ :=
    n05_weakAngularDerivative_of_weakReferenceJet hs.2.2
  obtain ⟨ur, hur, hUr, hg, hweak, hrep, hreflect, hbound, hpiece⟩ :=
    hnormal F fθ hF hs.1 hθ
  have hFnorm : sourceNormSquare D γw M0 X ≤ (Cn * Cr) * ‖v‖ ^ 2 := by
    have hn : n05CanonicalAuxiliaryScalar D S C K F ^ 2 + sourceNormSquare D γw M0 X ≤
        Cn * sourceNormSquare D γw M0 (n05CanonicalSourceLift S C K F, 0) :=
      hnormalize (n05CanonicalSourceLift S C K F) (hraw v).1
    have hb : sourceNormSquare D γw M0 X ≤
        Cn * sourceNormSquare D γw M0 (n05CanonicalSourceLift S C K F, 0) := by
      linarith only [hn, sq_nonneg (n05CanonicalAuxiliaryScalar D S C K F)]
    exact hb.trans ((mul_le_mul_of_nonneg_left (hraw v).2 hCn.le).trans_eq (by ring))
  have hQ : sourceNormSquare D γw M0 X + sourceNormSquare D γw M0 (fθ, 0) ≤
      C0 * ‖v‖ ^ 2 := by
    exact (add_le_add hFnorm hs.2.1).trans_eq (by dsimp only [C0]; ring)
  refine ⟨ur, hur, hUr, hg, hweak, hrep, hreflect, ?_, fun k => ?_⟩
  · exact hbound.trans ((mul_le_mul_of_nonneg_left hQ hB0.le).trans_eq (by ring))
  · have hEk : 0 < radialE (D.cellIndex (K.cell k)) := Real.exp_pos _
    exact (hpiece k).trans ((mul_le_mul_of_nonneg_left hQ
      (show 0 ≤ B0 * radialE (D.cellIndex (K.cell k)) ^ P by positivity)).trans_eq (by ring))

end ContinuousFlexibility.Statements
