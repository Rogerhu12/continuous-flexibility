module

public import ContinuousFlexibility.Analysis.N05CanonicalNormalSingleEnergy
public import ContinuousFlexibility.Analysis.N05CanonicalInverseNormalAngular

/-!
# Actual endpoint blocks for the fixed first normal derivative

The output is the fixed angular jet of the fixed radial derivative of the
same global inverse. Consecutive corrected source jets provide the exact
first-normal energy at the original endpoint and material order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory ContinuousFlexibility.Radial

theorem n05_canonicalNormalInverseBlock_endpoint_square_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {σ M0 M1 MN : ℝ} (hσ : 0 < σ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D σ M0 M1 G)
    (hN : FirstNormalInverseEstimate D σ M0 MN G) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ k m (v : n05CanonicalClosedSubmodule S K (s + 1)) (j : Fin (s + 1)),
      Real.exp (2 * σ * radialS (D.cellIndex (K.cell k))) *
          ‖n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
            (n05CanonicalGlobalInverse D S C K G (Pi.single m (v.val m 0))).1) j.val k‖ ^ 2 ≤
        B * radialE (D.cellIndex (K.cell k)) ^ A * radialE (D.cellIndex (K.cell m)) ^ A *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2 := by
  obtain ⟨_, _, hzeroAll⟩ :=
    n05CanonicalGlobalInverse_normal_of_source hD hT hS h hcoordinates
  obtain ⟨C0, A0, hC0, hA0, hzero⟩ := hzeroAll σ hσ M0 M1 MN G hG hN
  obtain ⟨_, _, hpositiveAll⟩ :=
    n05CanonicalGlobalInverse_normalAngular_of_source hD hT hS h hcoordinates
  obtain ⟨Cp, Ap, hCp, hAp, hpositive⟩ := hpositiveAll σ hσ M0 M1 MN G hG hN
  obtain ⟨As, hAs, hsource⟩ :=
    n05_canonicalNormalSingle_source_energy_bound hD.1 hT hS h hcoordinates hσ M0
  let A := A0 + Ap + As
  have hA : 0 < A := by dsimp only [A]; linarith only [hA0, hAp, hAs]
  refine ⟨A, hA, fun s => ?_⟩
  obtain ⟨Cs, hCs, hs⟩ := hsource s
  let B := (C0 + Cp) * Cs
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, fun k m v j => ?_⟩
  let F : CanonicalSequence S K := Pi.single m (v.val m 0)
  let d := n05CanonicalNormalizedSingleJetSource D S C K (s + 1) m v
  let first : Fin (s + 1 + 1) := ⟨1, by omega⟩
  obtain ⟨hF, hjets, hbaseE, hpositiveE⟩ := hs m v
  have hθ : WeakAngularDerivative D (n05CanonicalNormalizedSource D S C K F).1 (d first) :=
    n05_weakAngularDerivative_of_weakReferenceJet (hjets first).2
  have hEkpos : 0 < radialE (D.cellIndex (K.cell k)) := Real.exp_pos _
  have hEmpos : 0 < radialE (D.cellIndex (K.cell m)) := Real.exp_pos _
  have hEk : 1 ≤ radialE (D.cellIndex (K.cell k)) := Real.one_le_exp (radialQ_nonneg _)
  have hEm : 1 ≤ radialE (D.cellIndex (K.cell m)) := Real.one_le_exp (radialQ_nonneg _)
  have hupgrade (c a : ℝ) (hc : c ≤ B) (ha : a ≤ A) :
      c * radialE (D.cellIndex (K.cell k)) ^ a * radialE (D.cellIndex (K.cell m)) ^ As *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2 ≤
        B * radialE (D.cellIndex (K.cell k)) ^ A * radialE (D.cellIndex (K.cell m)) ^ A *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2 := by
    have hk := Real.rpow_le_rpow_of_exponent_le hEk ha
    have hm := Real.rpow_le_rpow_of_exponent_le hEm
      (show As ≤ A by dsimp only [A]; linarith only [hA0, hAp])
    have hck := mul_le_mul hc hk (Real.rpow_nonneg hEkpos.le a) hB.le
    have hprod := mul_le_mul hck hm (Real.rpow_nonneg hEmpos.le As)
      (mul_nonneg hB.le (Real.rpow_nonneg hEkpos.le A))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le) (sq_nonneg _)
  by_cases hj : j.val = 0
  · simp only [hj, n05CanonicalAngularJetSequence_zero]
    obtain ⟨_, _, _, _, _, _, _, _, hpiece⟩ := hzero F (d first) hF (hjets first).1 hθ
    calc
      _ ≤ C0 * radialE (D.cellIndex (K.cell k)) ^ A0 *
          (Cs * (radialE (D.cellIndex (K.cell m)) ^ As *
            Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2)) :=
        (hpiece k).trans (mul_le_mul_of_nonneg_left hbaseE (by positivity))
      _ = (C0 * Cs) * radialE (D.cellIndex (K.cell k)) ^ A0 *
          radialE (D.cellIndex (K.cell m)) ^ As *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2 := by ring
      _ ≤ _ := hupgrade (C0 * Cs) A0
        (by dsimp only [B]; nlinarith only [mul_nonneg hCp.le hCs.le])
        (by dsimp only [A]; linarith only [hAp, hAs])
  · obtain ⟨_, _, _, _, _, _, hpiece⟩ :=
      hpositive F (d first) hF (hjets first).1 hθ j.val (Nat.pos_of_ne_zero hj)
        (d j.castSucc) (d j.succ) (hjets j.castSucc).1 (hjets j.succ).1
          (hjets j.castSucc).2 (hjets j.succ).2
    calc
      _ ≤ Cp * radialE (D.cellIndex (K.cell k)) ^ Ap *
          (Cs * (radialE (D.cellIndex (K.cell m)) ^ As *
            Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2)) :=
        (hpiece k).trans (mul_le_mul_of_nonneg_left (hpositiveE j) (by positivity))
      _ = (Cp * Cs) * radialE (D.cellIndex (K.cell k)) ^ Ap *
          radialE (D.cellIndex (K.cell m)) ^ As *
          Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2 := by ring
      _ ≤ _ := hupgrade (Cp * Cs) Ap
        (by dsimp only [B]; nlinarith only [mul_nonneg hC0.le hCs.le])
        (by dsimp only [A]; linarith only [hA0, hAs])

end ContinuousFlexibility.Statements
