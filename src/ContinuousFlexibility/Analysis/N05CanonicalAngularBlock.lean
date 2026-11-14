module

public import ContinuousFlexibility.Analysis.N05CanonicalInverseAngularJets
public import ContinuousFlexibility.Analysis.N05CanonicalSourceSingleJetBounds

/-!
# Actual endpoint blocks for every retained canonical angular jet

Every output is a fixed weak jet of the same literal global inverse of
the single zero column. The derivative sources can have either parity.
The endpoint exponent and the two physical material orders are unchanged.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory ContinuousFlexibility.Radial

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)
  {σ M0 M1 : ℝ} (hσ : 0 < σ) {G : RadialSource → RadialUnknown}
  (hG : ReferenceInverseProperties D σ M0 M1 G)

include hD hT hS h hcoordinates hσ hG

/-- One coefficient power works for every angular order. For each finite
order the constant precedes the two pieces, graph row, and jet coordinate. -/
theorem n05_canonicalAngularInverseBlock_endpoint_square_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ k m (v : n05CanonicalClosedSubmodule S K s) (j : Fin (s + 1)),
      Real.exp (2 * σ * radialS (D.cellIndex (K.cell k))) *
          ‖n05CanonicalAngularJetSequence S K
            (n05CanonicalGlobalInverse D S C K G (Pi.single m (v.val m 0))).1 j.val k‖ ^ 2 ≤
        B * radialE (D.cellIndex (K.cell k)) ^ A * radialE (D.cellIndex (K.cell m)) ^ A *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2 := by
  obtain ⟨C0, A0, hC0, hA0, hzero⟩ :=
    n05_canonicalInverseBlock_endpoint_square_bound hD hT hS h hcoordinates hσ hG
  obtain ⟨Cp, Ap, hCp, hAp, hpositive⟩ :=
    n05CanonicalGlobalInverse_angularJet_endpoint_piece_bound hD hT hS h hcoordinates hσ hG
  obtain ⟨As, hAs, hsource⟩ :=
    n05_canonicalNormalizedSingleJet_reference_bound hD.1 hT hS h hcoordinates hσ M0
  let A := A0 + Ap + As
  have hA : 0 < A := by dsimp only [A]; linarith only [hA0, hAp, hAs]
  refine ⟨A, hA, fun s => ?_⟩
  obtain ⟨Cs, hCs, hs⟩ := hsource s
  let B := C0 + Cp * Cs
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, fun k m v j => ?_⟩
  have hEkpos : 0 < radialE (D.cellIndex (K.cell k)) := Real.exp_pos _
  have hEmpos : 0 < radialE (D.cellIndex (K.cell m)) := Real.exp_pos _
  have hEk : 1 ≤ radialE (D.cellIndex (K.cell k)) := Real.one_le_exp (radialQ_nonneg _)
  have hEm : 1 ≤ radialE (D.cellIndex (K.cell m)) := Real.one_le_exp (radialQ_nonneg _)
  have hupgrade (c a b : ℝ) (hc : c ≤ B) (ha : a ≤ A) (hb : b ≤ A) :
      c * radialE (D.cellIndex (K.cell k)) ^ a * radialE (D.cellIndex (K.cell m)) ^ b *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2 ≤
        B * radialE (D.cellIndex (K.cell k)) ^ A * radialE (D.cellIndex (K.cell m)) ^ A *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2 := by
    have hk := Real.rpow_le_rpow_of_exponent_le hEk ha
    have hm := Real.rpow_le_rpow_of_exponent_le hEm hb
    have hck := mul_le_mul hc hk (Real.rpow_nonneg hEkpos.le a) hB.le
    have hprod := mul_le_mul hck hm (Real.rpow_nonneg hEmpos.le b)
      (mul_nonneg hB.le (Real.rpow_nonneg hEkpos.le A))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le) (sq_nonneg _)
  by_cases hj : j.val = 0
  · simp only [hj, n05CanonicalAngularJetSequence_zero]
    change Real.exp (2 * σ * radialS (D.cellIndex (K.cell k))) *
      ‖n05CanonicalInverseBlock D S C K G k m (v.val m 0)‖ ^ 2 ≤ _
    calc
      _ ≤ C0 * radialE (D.cellIndex (K.cell k)) ^ A0 *
          radialE (D.cellIndex (K.cell m)) ^ A0 *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m 0‖ ^ 2 :=
        hzero k m (v.val m 0)
      _ ≤ C0 * radialE (D.cellIndex (K.cell k)) ^ A0 *
          radialE (D.cellIndex (K.cell m)) ^ A0 *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (v.val m) 0) 2) (by positivity)
      _ ≤ _ := hupgrade C0 A0 A0
        (by dsimp only [B]; exact le_add_of_nonneg_right (mul_nonneg hCp.le hCs.le))
        (by dsimp only [A]; linarith only [hAp, hAs])
        (by dsimp only [A]; linarith only [hAp, hAs])
  · have hf := hs m v j
    have hp := hpositive (Pi.single m (v.val m 0)) hf.1 j.val (Nat.pos_of_ne_zero hj)
      (n05CanonicalNormalizedSingleJetSource D S C K s m v j) hf.2.1 hf.2.2.1 k
    calc
      _ ≤ Cp * radialE (D.cellIndex (K.cell k)) ^ Ap *
          (Cs * radialE (D.cellIndex (K.cell m)) ^ As *
            Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2) :=
        hp.trans (mul_le_mul_of_nonneg_left hf.2.2.2 (by positivity))
      _ = (Cp * Cs) * radialE (D.cellIndex (K.cell k)) ^ Ap *
          radialE (D.cellIndex (K.cell m)) ^ As *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2 := by ring
      _ ≤ _ := hupgrade (Cp * Cs) Ap As
        (by dsimp only [B]; linarith only [hC0])
        (by dsimp only [A]; linarith only [hA0, hAs])
        (by dsimp only [A]; linarith only [hA0, hAp])

end ContinuousFlexibility.Statements
