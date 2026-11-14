module

public import ContinuousFlexibility.Analysis.N05CanonicalInverseAngularJets
public import ContinuousFlexibility.Analysis.N05CanonicalNormalizedAngularJets
public import ContinuousFlexibility.Analysis.N05CanonicalInverseLinearity
public import ContinuousFlexibility.Radial.R11bAngularFrequencySource

/-!
# Genuine bounded jets of the fixed inverse on each source level

Actual normalized source jets give actual weak derivatives of the one
global inverse. Their unweighted bounds hold uniformly over the retained
finite angular family. These identities keep the choice's default branch
out of the later linearity and finite-truncation arguments.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory ContinuousFlexibility.Radial
open scoped BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {base loss : ℕ} {ε γw γ M0 M1 : ℝ} {G : RadialSource → RadialUnknown}
  (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)
  (hγw : 0 < γw) (hG : ReferenceInverseProperties D γw M0 M1 G)
  (hV : IsVolumeModel T S K V) (hgap : γw < γ)

include hD hT hS h hcoordinates hγw hG hV hgap

theorem n05CanonicalGlobalInverse_angularJets_bound (t : ℝ) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (v : V.level γ t s) (j : Fin (s + 1)),
      (∀ m, WeakCanonicalAngularDerivative S K m
        ((n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)).1 m)
        (n05CanonicalAngularJetSequence S K
          (n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)).1 j.val m) j.val) ∧
      ‖n05CanonicalAngularJetSequence S K
        (n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)).1 j.val‖ ^ 2 ≤ B * ‖v‖ ^ 2 := by
  obtain ⟨Cb, hCb, hbase⟩ :=
    n05CanonicalGlobalInverse_square_bound hD hT hS h hcoordinates hV hγw hgap hG t s
  obtain ⟨Cr, hCr, hraw⟩ :=
    n05_canonicalSourceLift_reference_bound hD.1 hT h hcoordinates hV hγw hgap t M0 s
  obtain ⟨Cn, hCn, hnormalize⟩ := n05_referenceSource_normalized_square_bound hD.1 hS hγw M0
  obtain ⟨Cj, hCj, hjets⟩ :=
    n05CanonicalNormalizedSource_allAngularJets h hcoordinates hD.1 hT hV hγw hgap t M0 hS s
  obtain ⟨Cg, hCg, hinverse⟩ :=
    n05CanonicalGlobalInverse_positive_angularJet hD hT hS h hcoordinates hγw hG
  let Z : ℝ := ∑ j : Fin (s + 1), (2 : ℝ) ^ (2 * j.val)
  have hterm (j : Fin (s + 1)) : 0 ≤ (2 : ℝ) ^ (2 * j.val) := by positivity
  have hZ : 0 ≤ Z := Finset.sum_nonneg (fun j _ => hterm j)
  have hpow (j : Fin (s + 1)) : (2 : ℝ) ^ (2 * j.val) ≤ Z :=
    Finset.single_le_sum (fun k _ => hterm k) (Finset.mem_univ j)
  let E := Cn * Cr
  have hE : 0 < E := mul_pos hCn hCr
  let B := Cb + Cg * (Cj + Z * E)
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, fun v j => ?_⟩
  let F := n05CanonicalNormalizedSource D S C K (V.forget γ t s v)
  let U := n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)
  have hab : D.a ≤ D.b := hD.1.choose_spec.1.2.1.le
  have hF : SourceMember D γw M0 F :=
    n05CanonicalNormalizedSource_mem hD.1 hT hS h hcoordinates hV hγw hgap t M0 s v
  have hFnorm : sourceNormSquare D γw M0 F ≤ E * ‖v‖ ^ 2 := by
    have hn : n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s v) ^ 2 +
        sourceNormSquare D γw M0 F ≤ Cn * sourceNormSquare D γw M0
          (n05CanonicalSourceLift S C K (V.forget γ t s v), 0) :=
      hnormalize (n05CanonicalSourceLift S C K (V.forget γ t s v)) (hraw v).1
    have hl : sourceNormSquare D γw M0 F ≤ Cn * sourceNormSquare D γw M0
        (n05CanonicalSourceLift S C K (V.forget γ t s v), 0) := by
      linarith only [hn, sq_nonneg (n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s v))]
    exact hl.trans ((mul_le_mul_of_nonneg_left (hraw v).2 hCn.le).trans_eq (by dsimp only [E]; ring))
  by_cases hj : j.val = 0
  · simp only [hj, n05CanonicalAngularJetSequence_zero]
    refine ⟨?_, ?_⟩
    · intro m φ hφ
      simp only [pow_zero, one_mul, mixedDerivative, iteratedDeriv_zero, Prod.eta]
    · have hb : ‖U.1‖ ^ 2 + U.2.1 ^ 2 + U.2.2.1 ^ 2 + U.2.2.2 ^ 2 ≤ Cb * ‖v‖ ^ 2 :=
        hbase v
      have hu : ‖U.1‖ ^ 2 ≤ Cb * ‖v‖ ^ 2 := by
        linarith only [hb, sq_nonneg U.2.1, sq_nonneg U.2.2.1, sq_nonneg U.2.2.2]
      exact hu.trans (mul_le_mul_of_nonneg_right
        (show Cb ≤ B from le_add_of_nonneg_right (by positivity)) (sq_nonneg _))
  · have hs := hjets v j
    obtain ⟨d, _, _, hw, _, hb⟩ := hinverse (V.forget γ t s v) hF j.val
      (Nat.pos_of_ne_zero hj) (n05CanonicalNormalizedJetSource D T S C K V γ t s j v)
      hs.1 hs.2.2
    refine ⟨hw, ?_⟩
    have hout : 0 ≤ outputNormSquare D γw M1 0 (d, 0) := by
      rw [n05_zeroOutputNormSquare_eq_sourceNormSquare_neg]
      exact r11b_sourceNormSquare_nonneg hab γw (-M1) (d, 0)
    have hu : ‖n05CanonicalAngularJetSequence S K U.1 j.val‖ ^ 2 ≤ Cg *
        (sourceNormSquare D γw M0
          (n05CanonicalNormalizedJetSource D T S C K V γ t s j v, 0) +
            (2 : ℝ) ^ (2 * j.val) * sourceNormSquare D γw M0 F) := by
      linarith only [hb, hout]
    have hlow : (2 : ℝ) ^ (2 * j.val) * sourceNormSquare D γw M0 F ≤ Z * (E * ‖v‖ ^ 2) :=
      mul_le_mul (hpow j) hFnorm (sourceNormSquare_nonneg hab hF) hZ
    calc
      _ ≤ Cg * (sourceNormSquare D γw M0
          (n05CanonicalNormalizedJetSource D T S C K V γ t s j v, 0) +
            (2 : ℝ) ^ (2 * j.val) * sourceNormSquare D γw M0 F) := hu
      _ ≤ Cg * (Cj * ‖v‖ ^ 2 + Z * (E * ‖v‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hs.2.1 hlow) hCg.le
      _ = (Cg * (Cj + Z * E)) * ‖v‖ ^ 2 := by ring
      _ ≤ B * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right
        (show Cg * (Cj + Z * E) ≤ B from le_add_of_nonneg_left hCb.le) (sq_nonneg _)

theorem n05CanonicalGlobalInverse_angularJets_norm_bound (t : ℝ) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (v : V.level γ t s) (j : Fin (s + 1)),
      ‖n05CanonicalAngularJetSequence S K
        (n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)).1 j.val‖ ≤ B * ‖v‖ := by
  obtain ⟨B, hB, hb⟩ :=
    n05CanonicalGlobalInverse_angularJets_bound hD hT hS h hcoordinates hγw hG hV hgap t s
  refine ⟨Real.sqrt B, Real.sqrt_pos.mpr hB, fun v j => ?_⟩
  have he := abs_le_of_sq_le_sq
    (show ‖n05CanonicalAngularJetSequence S K
        (n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)).1 j.val‖ ^ 2 ≤
        (Real.sqrt B * ‖v‖) ^ 2 by
      simpa only [mul_pow, Real.sq_sqrt hB.le] using (hb v j).2)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  simpa only [abs_of_nonneg (norm_nonneg _)] using he

end ContinuousFlexibility.Statements
