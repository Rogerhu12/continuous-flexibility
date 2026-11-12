import ContinuousFlexibility.Analysis.N05CanonicalInverseNormalLevel
import ContinuousFlexibility.Analysis.N05CanonicalInverseNormalAngular
import ContinuousFlexibility.Analysis.N05CanonicalInverseLinearity

/-!
# Genuine bounded angular jets of the fixed first normal derivative

The actual corrected source and its consecutive angular jets control the
single canonical radial derivative. All choices below are identified by
their weak test identities before any linearity or continuity is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory ContinuousFlexibility.Radial
open scoped BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {base loss : ℕ} {ε γw γ M0 M1 MN : ℝ} {G : RadialSource → RadialUnknown}
  (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)
  (hγw : 0 < γw) (hG : ReferenceInverseProperties D γw M0 M1 G)
  (hN : FirstNormalInverseEstimate D γw M0 MN G)
  (hV : IsVolumeModel T S K V) (hgap : γw < γ)

include hD hT hS h hcoordinates hγw hG hN hV hgap

theorem n05CanonicalGlobalInverse_normalJets_bound (t : ℝ) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v : V.level γ t (s + 1),
      let U := (n05CanonicalGlobalInverse D S C K G (V.forget γ t (s + 1) v)).1
      let W := n05CanonicalRadialJetSequence S K U
      (∀ m, n05WeakCanonicalRadialDerivative S K m (U m) (W m)) ∧
      (∀ m, n05CanonicalReflection S K m (W m) = W m) ∧
      ∀ j : Fin (s + 1),
        (∀ m, WeakCanonicalAngularDerivative S K m (W m)
          (n05CanonicalAngularJetSequence S K W j.val m) j.val) ∧
        ‖n05CanonicalAngularJetSequence S K W j.val‖ ^ 2 ≤ B * ‖v‖ ^ 2 := by
  obtain ⟨A0, _, _, _, hlevels⟩ :=
    n05CanonicalGlobalInverse_normal_level_bound hD hT hS h hcoordinates hγw hG hN hV hgap
  obtain ⟨Cb, hCb, hbase⟩ := hlevels t s
  obtain ⟨Aj, _, hpositive⟩ :=
    n05CanonicalGlobalInverse_normalAngular_of_source hD hT hS h hcoordinates
  obtain ⟨Cg, _, hCg, _, hinverse⟩ := hpositive γw hγw M0 M1 MN G hG hN
  obtain ⟨Cr, hCr, hraw⟩ :=
    n05_canonicalSourceLift_reference_bound hD.1 hT h hcoordinates hV hγw hgap t M0 (s + 1)
  obtain ⟨Cn, hCn, hnormalize⟩ := n05_referenceSource_normalized_square_bound hD.1 hS hγw M0
  obtain ⟨Cj, hCj, hjets⟩ := n05CanonicalNormalizedSource_allAngularJets
    h hcoordinates hD.1 hT hV hγw hgap t M0 hS (s + 1)
  let E : ℝ := Cn * Cr
  have hE : 0 < E := mul_pos hCn hCr
  let Z : ℝ := ∑ j : Fin (s + 1), (2 : ℝ) ^ (2 * j.val)
  have hterm (j : Fin (s + 1)) : 0 ≤ (2 : ℝ) ^ (2 * j.val) := by positivity
  have hZ : 0 ≤ Z := Finset.sum_nonneg (fun j _ => hterm j)
  have hpow (j : Fin (s + 1)) : (2 : ℝ) ^ (2 * j.val) ≤ Z :=
    Finset.single_le_sum (fun k _ => hterm k) (Finset.mem_univ j)
  let B : ℝ := Cb + Cg * (2 * Cj + Z * (E + Cj))
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, fun v => ?_⟩
  let F := V.forget γ t (s + 1) v
  let X := n05CanonicalNormalizedSource D S C K F
  let U := (n05CanonicalGlobalInverse D S C K G F).1
  let W := n05CanonicalRadialJetSequence S K U
  let d := fun i : Fin (s + 1 + 1) =>
    n05CanonicalNormalizedJetSource D T S C K V γ t (s + 1) i v
  let first : Fin (s + 1 + 1) := ⟨1, by omega⟩
  have hab : D.a ≤ D.b := hD.1.choose_spec.1.2.1.le
  have hF : SourceMember D γw M0 X :=
    n05CanonicalNormalizedSource_mem hD.1 hT hS h hcoordinates hV hγw hgap t M0 (s + 1) v
  have hFnorm : sourceNormSquare D γw M0 X ≤ E * ‖v‖ ^ 2 := by
    have hn : n05CanonicalAuxiliaryScalar D S C K F ^ 2 + sourceNormSquare D γw M0 X ≤
        Cn * sourceNormSquare D γw M0 (n05CanonicalSourceLift S C K F, 0) :=
      hnormalize (n05CanonicalSourceLift S C K F) (hraw v).1
    have hb : sourceNormSquare D γw M0 X ≤
        Cn * sourceNormSquare D γw M0 (n05CanonicalSourceLift S C K F, 0) := by
      linarith only [hn, sq_nonneg (n05CanonicalAuxiliaryScalar D S C K F)]
    exact hb.trans ((mul_le_mul_of_nonneg_left (hraw v).2 hCn.le).trans_eq (by dsimp only [E]; ring))
  have hfirst := hjets v first
  have hθ : WeakAngularDerivative D X.1 (d first) :=
    n05_weakAngularDerivative_of_weakReferenceJet hfirst.2.2
  have hQbase : sourceNormSquare D γw M0 X + sourceNormSquare D γw M0 (d first, 0) ≤
      (E + Cj) * ‖v‖ ^ 2 := (add_le_add hFnorm hfirst.2.1).trans_eq (by ring)
  have hQnonneg : 0 ≤ sourceNormSquare D γw M0 X + sourceNormSquare D γw M0 (d first, 0) :=
    add_nonneg (sourceNormSquare_nonneg hab hF)
      (r11b_sourceNormSquare_nonneg hab γw M0 (d first, 0))
  obtain ⟨ur, _, _, _, hr, _, hreflect, hb, _⟩ := hbase v
  refine ⟨hr, hreflect, fun j => ?_⟩
  by_cases hj : j.val = 0
  · simp only [hj, n05CanonicalAngularJetSequence_zero]
    refine ⟨?_, ?_⟩
    · intro m φ hφ
      simp only [pow_zero, one_mul, mixedDerivative, iteratedDeriv_zero, Prod.eta]
    · have hout : 0 ≤ outputNormSquare D γw (max M1 MN + A0) 0
          (n05CanonicalInverseNormalField D S C K G F ur, 0) := by
        rw [n05_zeroOutputNormSquare_eq_sourceNormSquare_neg]
        exact r11b_sourceNormSquare_nonneg hab γw (-(max M1 MN + A0)) _
      have hw : ‖W‖ ^ 2 ≤ Cb * ‖v‖ ^ 2 := by linarith only [hb, hout]
      exact hw.trans (mul_le_mul_of_nonneg_right
        (show Cb ≤ B from le_add_of_nonneg_right (by positivity)) (sq_nonneg _))
  · obtain ⟨g, _, _, hweak, _, hbound, _⟩ :=
      hinverse F (d first) hF hfirst.1 hθ j.val (Nat.pos_of_ne_zero hj)
        (d j.castSucc) (d j.succ) (hjets v j.castSucc).1 (hjets v j.succ).1
          (hjets v j.castSucc).2.2 (hjets v j.succ).2.2
    have hout : 0 ≤ outputNormSquare D γw (max M1 MN + Aj) 0 (g, 0) := by
      rw [n05_zeroOutputNormSquare_eq_sourceNormSquare_neg]
      exact r11b_sourceNormSquare_nonneg hab γw (-(max M1 MN + Aj)) _
    have hjet : ‖n05CanonicalAngularJetSequence S K W j.val‖ ^ 2 ≤ Cg *
        (sourceNormSquare D γw M0 (d j.castSucc, 0) + sourceNormSquare D γw M0 (d j.succ, 0) +
          (2 : ℝ) ^ (2 * j.val) *
            (sourceNormSquare D γw M0 X + sourceNormSquare D γw M0 (d first, 0))) := by
      linarith only [hbound, hout]
    have hlow := mul_le_mul (hpow j) hQbase hQnonneg hZ
    refine ⟨hweak, ?_⟩
    calc
      _ ≤ Cg * (sourceNormSquare D γw M0 (d j.castSucc, 0) +
          sourceNormSquare D γw M0 (d j.succ, 0) + (2 : ℝ) ^ (2 * j.val) *
            (sourceNormSquare D γw M0 X + sourceNormSquare D γw M0 (d first, 0))) := hjet
      _ ≤ Cg * (Cj * ‖v‖ ^ 2 + Cj * ‖v‖ ^ 2 + Z * ((E + Cj) * ‖v‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add (hjets v j.castSucc).2.1 (hjets v j.succ).2.1) hlow) hCg.le
      _ = (Cg * (2 * Cj + Z * (E + Cj))) * ‖v‖ ^ 2 := by ring
      _ ≤ B * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right
        (show Cg * (2 * Cj + Z * (E + Cj)) ≤ B from le_add_of_nonneg_left hCb.le) (sq_nonneg _)

theorem n05CanonicalGlobalInverse_normalJets_norm_bound (t : ℝ) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (v : V.level γ t (s + 1)) (j : Fin (s + 1)),
      ‖n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
        (n05CanonicalGlobalInverse D S C K G (V.forget γ t (s + 1) v)).1) j.val‖ ≤ B * ‖v‖ := by
  obtain ⟨B, hB, hb⟩ :=
    n05CanonicalGlobalInverse_normalJets_bound hD hT hS h hcoordinates hγw hG hN hV hgap t s
  refine ⟨Real.sqrt B, Real.sqrt_pos.mpr hB, fun v j => ?_⟩
  have he := abs_le_of_sq_le_sq
    (show ‖n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
        (n05CanonicalGlobalInverse D S C K G (V.forget γ t (s + 1) v)).1) j.val‖ ^ 2 ≤
        (Real.sqrt B * ‖v‖) ^ 2 by
      simpa only [mul_pow, Real.sq_sqrt hB.le] using ((hb v).2.2 j).2)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  simpa only [abs_of_nonneg (norm_nonneg _)] using he

end ContinuousFlexibility.Statements
