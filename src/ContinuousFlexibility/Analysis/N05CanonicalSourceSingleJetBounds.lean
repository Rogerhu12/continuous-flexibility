import ContinuousFlexibility.Analysis.N05CanonicalSourceSingleJets
import ContinuousFlexibility.Analysis.N05CanonicalNormalizedAngularJets

/-!
# Same-endpoint bounds for the normalized single-row angular jets

The source and all its unsigned derivatives retain the original endpoint
exponential. The actual normalizer contributes only a finite-order constant.
The coefficient power is fixed before the angular order; the material
exponent is exactly the one prescribed for the physical inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory ContinuousFlexibility.Radial
open scoped BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)
  {σ : ℝ} (hσ : 0 < σ) (M : ℝ)

include hD hT hS h hcoordinates hσ

theorem n05_canonicalNormalizedSingleJet_reference_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m (v : n05CanonicalClosedSubmodule S K s) (j : Fin (s + 1)),
      SourceMember D σ M
        (n05CanonicalNormalizedSource D S C K (Pi.single m (v.val m 0))) ∧
      SourceDerivativeMember D σ M (n05CanonicalNormalizedSingleJetSource D S C K s m v j) ∧
      n05_weakReferenceAngularJet D
        (n05CanonicalNormalizedSource D S C K (Pi.single m (v.val m 0))).1
        (n05CanonicalNormalizedSingleJetSource D S C K s m v j) j.val ∧
      sourceNormSquare D σ M (n05CanonicalNormalizedSingleJetSource D S C K s m v j, 0) +
          (2 : ℝ) ^ (2 * j.val) * sourceNormSquare D σ M
            (n05CanonicalNormalizedSource D S C K (Pi.single m (v.val m 0))) ≤
        B * radialE (D.cellIndex (K.cell m)) ^ A *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2 := by
  obtain ⟨Cs, As, hCs, hAs, hsource⟩ :=
    n05_canonicalNormalizedSource_single_reference_bound hD hT hS h hcoordinates hσ M
  obtain ⟨Cd, Ad, hCd, hAd, hder⟩ :=
    n05_canonicalAngularLift_single_reference_bound hD hT h hcoordinates hσ.le M
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  let ψ : ℕ → PolarPoint → ℝ := fun j =>
    mixedDerivative 0 j ((S.height (3 / 4 : ℝ)).decode S.psi)
  have hψ (j : ℕ) : SourceDerivativeMember D σ M (ψ j) :=
    n05_physicalNormalizer_angular_sourceDerivativeMember hD hS σ M j
  let Q (j : ℕ) : ℝ := sourceNormSquare D σ M (ψ j, 0)
  have hQ (j : ℕ) : 0 ≤ Q j := by
    change 0 ≤ (0 : ℝ) ^ 2 + ∑' m, sourceCellSquare D σ M (ψ j) m
    exact add_nonneg (sq_nonneg _) (tsum_nonneg
      (fun m => sourceCellSquare_nonneg hab σ M (hψ j).1 m))
  refine ⟨As + Ad, add_pos hAs hAd, fun s => ?_⟩
  let Z : ℝ := ∑ j : Fin (s + 1), (Q j.val + (2 : ℝ) ^ (2 * j.val))
  have hterm (j : Fin (s + 1)) : 0 ≤ Q j.val + (2 : ℝ) ^ (2 * j.val) :=
    add_nonneg (hQ j.val) (by positivity)
  have hZ : 0 ≤ Z := Finset.sum_nonneg (fun j _ => hterm j)
  have hsingle (j : Fin (s + 1)) : Q j.val + (2 : ℝ) ^ (2 * j.val) ≤ Z :=
    Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ j)
  have hQZ (j : Fin (s + 1)) : Q j.val ≤ Z :=
    (le_add_of_nonneg_right (by positivity)).trans (hsingle j)
  have hpowZ (j : Fin (s + 1)) : (2 : ℝ) ^ (2 * j.val) ≤ Z :=
    (le_add_of_nonneg_left (hQ j.val)).trans (hsingle j)
  refine ⟨2 * (Cd + Cs * Z) + Z * Cs, by positivity, fun m v j => ?_⟩
  let F := n05CanonicalNormalizedSource D S C K (Pi.single m (v.val m 0))
  let lam := n05CanonicalAuxiliaryScalar D S C K (Pi.single m (v.val m 0))
  let W := radialE (D.cellIndex (K.cell m)) ^ (As + Ad) *
    Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hEpos : 0 < radialE (D.cellIndex (K.cell m)) := Real.exp_pos _
  have hE : 1 ≤ radialE (D.cellIndex (K.cell m)) :=
    Real.one_le_exp (radialQ_nonneg _)
  have hrow (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ As + Ad) (i : Fin (s + 1)) :
      a * radialE (D.cellIndex (K.cell m)) ^ b *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m i‖ ^ 2 ≤ a * W := by
    have he := Real.rpow_le_rpow_of_exponent_le hE hb
    have hn := pow_le_pow_left₀ (norm_nonneg (v.val m i))
      (PiLp.norm_apply_le (v.val m) i) 2
    calc
      _ ≤ a * radialE (D.cellIndex (K.cell m)) ^ (As + Ad) *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he ha) (Real.exp_pos _).le)
          hn (sq_nonneg _) (by positivity)
      _ = a * W := by dsimp only [W]; ring
  have hF : SourceMember D σ M F := (hsource m (v.val m 0)).1
  have hsum : lam ^ 2 + sourceNormSquare D σ M F ≤ Cs * W :=
    (hsource m (v.val m 0)).2.trans
      (hrow Cs As hCs.le (by linarith only [hAd]) 0)
  have hlam : lam ^ 2 ≤ Cs * W := by
    linarith only [hsum, sourceNormSquare_nonneg hab hF]
  have hFnorm : sourceNormSquare D σ M F ≤ Cs * W := by
    linarith only [hsum, sq_nonneg lam]
  have hd := hder m (v.val m j)
  have hdBound : sourceNormSquare D σ M
      (n05CanonicalAngularLift S C K (Pi.single m (v.val m j)), 0) ≤ Cd * W :=
    hd.2.trans (hrow Cd Ad hCd.le (by linarith only [hAs]) j)
  have hc := n05_sourceDerivativeMember_sub_const_mul_bound hab hd.1 (hψ j.val) lam
  refine ⟨hF, hc.1,
    n05CanonicalNormalizedSingleJetSource_weak hD hT h hcoordinates hS hσ M s m v j, ?_⟩
  have hlamQ : lam ^ 2 * Q j.val ≤ (Cs * W) * Z :=
    mul_le_mul hlam (hQZ j) (hQ j.val) (mul_nonneg hCs.le hW)
  have hlow : (2 : ℝ) ^ (2 * j.val) * sourceNormSquare D σ M F ≤ Z * (Cs * W) :=
    mul_le_mul (hpowZ j) hFnorm (sourceNormSquare_nonneg hab hF) hZ
  calc
    _ ≤ 2 * (sourceNormSquare D σ M
          (n05CanonicalAngularLift S C K (Pi.single m (v.val m j)), 0) + lam ^ 2 * Q j.val) +
        Z * (Cs * W) := add_le_add hc.2 hlow
    _ ≤ 2 * (Cd * W + (Cs * W) * Z) + Z * (Cs * W) :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add hdBound hlamQ) (by norm_num)) le_rfl
    _ = _ := by dsimp only [W]; ring

end ContinuousFlexibility.Statements
