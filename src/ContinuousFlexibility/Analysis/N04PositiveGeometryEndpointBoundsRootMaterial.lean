module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsRootHeight
public import ContinuousFlexibility.Analysis.N01cPhysicalHeightBounds

/-!
# Polynomial material costs for the actual normalized root inputs

The normalized radial operators already map into the original weighted
height space. Evaluating those maps with the physical `E0` estimate
retains `H^(3/4)` and a finite `E0` power, with fixed spatial loss seven.
This is stronger than the older estimate using the material envelope M.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04PositiveRootMaterialStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

private theorem rootMaterial_tame_evaluation
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (s : ℕ) {C A : ℝ} (hC : 0 ≤ C)
    (hpoint : ∀ u : ScalarHeightSpace S, ∀ a b : ℕ, a + b ≤ s + 1 →
      ∀ p ∈ annularOpen D,
        |mixedDerivative a b ((S.height scalarBeta).decode u) p| ≤
          C * T.E0 p.1 ^ A * T.H p.1 ^ scalarBeta *
            scalarHeightGrading S (s + 3) u)
    (L : ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S)
    (hL : IsTameLinear (scalarCommonHeightGrading S) (scalarHeightGrading S)
      L.toLinearMap 4 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a b : ℕ, a + b ≤ s + 1 →
      ∀ p (hp : p ∈ annularOpen D), ∀ u : ScalarCommonHeight S,
        |((heightPhysicalJetCLM hT (hS.1 scalarBeta) a b p hp).comp L) u| ≤
          B * T.E0 p.1 ^ A * T.H p.1 ^ scalarBeta *
            scalarCommonHeightGrading S (s + 7) u := by
  refine (hL (s + 3) (Nat.zero_le _)).elim ?_
  intro B hB
  refine ⟨C * B, mul_nonneg hC B.coe_nonneg, ?_⟩
  intro a b hab p hp u
  rw [ContinuousLinearMap.comp_apply, heightPhysicalJetCLM_apply]
  have hfactor : 0 ≤ C * T.E0 p.1 ^ A * T.H p.1 ^ scalarBeta :=
    mul_nonneg (mul_nonneg hC
      (Real.rpow_nonneg (hT.2.1 p.1 hp.1).2.2.1.le _))
      (Real.rpow_nonneg (hT.2.1 p.1 hp.1).2.1.le _)
  have hg : scalarHeightGrading S (s + 3) (L u) ≤
      (B : ℝ) * scalarCommonHeightGrading S (s + 7) u := hB u
  exact (hpoint (L u) a b hab p hp).trans
    ((mul_le_mul_of_nonneg_left hg hfactor).trans_eq (by ring))

/-- A uniform `E0` polynomial and the original material height bound
every physical mixed jet of all four normalized inputs. -/
theorem n04PositiveGeometry_rootHeightJetCLM_material_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (s : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ i : Fin 4,
      ∀ a b : ℕ, a + b ≤ s → ∀ p (hp : p ∈ annularOpen D),
      ∀ u : ScalarCommonHeight S,
        |n04PositiveGeometry_rootHeightJetCLM hD hT hS a b p hp i u| ≤
          C * T.E0 p.1 ^ A * T.H p.1 ^ scalarBeta *
            scalarCommonHeightGrading S (s + 7) u := by
  obtain ⟨C, A, hC, hA, hpoint⟩ :=
    sobolevModel_physicalMixedJets_le_E0_grading hT (hS.1 scalarBeta) (s + 1)
  have hpoint' : ∀ u : ScalarHeightSpace S, ∀ a b : ℕ, a + b ≤ s + 1 →
      ∀ p ∈ annularOpen D,
        |mixedDerivative a b ((S.height scalarBeta).decode u) p| ≤
          C * T.E0 p.1 ^ A * T.H p.1 ^ scalarBeta *
            scalarHeightGrading S (s + 3) u := by
    exact hpoint
  have hm := weighted_scalarCommonHeightGrading_monotone S
  obtain ⟨B0, hB0, hb0⟩ := rootMaterial_tame_evaluation hT hS s hC hpoint'
    (n06RootNormalizedRadialCLM hD hT hS)
    ((n06RootNormalizedRadialCLM_isTame hD hT hS).weaken hm (by norm_num) le_rfl)
  obtain ⟨B1, hB1, hb1⟩ := rootMaterial_tame_evaluation hT hS s hC hpoint'
    (n06RootAngularPrimitiveCLM hD hT hS)
    ((n06RootAngularPrimitiveCLM_isTame hD hT hS).weaken hm (by norm_num) le_rfl)
  obtain ⟨B2, hB2, hb2⟩ := rootMaterial_tame_evaluation hT hS s hC hpoint'
    (n06RootNormalizedMixedPrimitiveCLM hD hT hS)
    (n06RootNormalizedMixedPrimitiveCLM_isTame hD hT hS)
  obtain ⟨B3, hB3, hb3⟩ := rootMaterial_tame_evaluation hT hS s hC hpoint'
    (n06RootNormalizedAngularSecondCLM hD hT hS)
    (n06RootNormalizedAngularSecondCLM_isTame hD hT hS)
  refine ⟨B0 + B1 + B2 + B3, A, by positivity, hA, ?_⟩
  intro i a b hab p hp u
  have hmono {B : ℝ} (hB : B ≤ B0 + B1 + B2 + B3) :
      B * T.E0 p.1 ^ A * T.H p.1 ^ scalarBeta *
          scalarCommonHeightGrading S (s + 7) u ≤
        (B0 + B1 + B2 + B3) * T.E0 p.1 ^ A * T.H p.1 ^ scalarBeta *
          scalarCommonHeightGrading S (s + 7) u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hB
        (Real.rpow_nonneg (hT.2.1 p.1 hp.1).2.2.1.le _))
      (Real.rpow_nonneg (hT.2.1 p.1 hp.1).2.1.le _)) (apply_nonneg _ _)
  fin_cases i
  · exact (hb0 a b (by omega) p hp u).trans (hmono (by linarith))
  · exact (hb1 a (b + 1) (by omega) p hp u).trans (hmono (by linarith))
  · exact (hb2 a (b + 1) (by omega) p hp u).trans (hmono (by linarith))
  · exact (hb3 a b (by omega) p hp u).trans (hmono (by linarith))

/-- The original state projection preserves the same physical material
cost and the same fixed spatial loss. -/
theorem n04PositiveGeometry_rootHeightStateJetCLM_material_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (s : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ i : Fin 4,
      ∀ a b : ℕ, a + b ≤ s → ∀ p (hp : p ∈ annularOpen D),
      ∀ x : AnnularState S,
        |n04PositiveGeometry_rootHeightStateJetCLM hD hT hS a b p hp i x| ≤
          C * T.E0 p.1 ^ A * T.H p.1 ^ scalarBeta * stateGrading S (s + 7) x := by
  refine (n04PositiveGeometry_rootHeightJetCLM_material_bound hD hT hS s).elim ?_
  intro C hC
  refine hC.elim ?_
  intro A hA
  refine ⟨C, A, hA.1, hA.2.1, ?_⟩
  intro i a b hab p hp x
  have hW : 0 ≤ C * T.E0 p.1 ^ A * T.H p.1 ^ scalarBeta :=
    mul_nonneg (mul_nonneg hA.1
      (Real.rpow_nonneg (hT.2.1 p.1 hp.1).2.2.1.le _))
      (Real.rpow_nonneg (hT.2.1 p.1 hp.1).2.1.le _)
  have he : n04PositiveGeometry_rootHeightStateJetCLM hD hT hS a b p hp i x =
      n04PositiveGeometry_rootHeightJetCLM hD hT hS a b p hp i x.1 := rfl
  exact (congrArg abs he).trans_le ((hA.2.2 i a b hab p hp x.1).trans
    (mul_le_mul_of_nonneg_left (n06_root_commonHeightGrading_le_state S (s + 7) x) hW))

/-- The genuine quadratic parameter jets retain their polynomial cost
and full height gain at every parameter order, with one fixed loss. -/
theorem n04PositiveGeometry_rootHeightInputs_material_oneHigh
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (s : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ i : Fin 4, ∀ a b : ℕ, a + b ≤ s →
      ∀ p ∈ annularOpen D, ∀ U : Set (AnnularState S × ℝ),
      ∀ J : SmoothDirections U (fun z => z.2 *
        mixedDerivative a b (n06RootNormalizedHeightFields D S z.1.1 i) p),
      ∀ k B : ℕ, ∀ x0 : AnnularState S, ∀ z ∈ U, |z.2| ≤ 1 →
      ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ C * T.E0 p.1 ^ A * T.H p.1 ^ scalarBeta *
          (1 + stateGrading S (s + 7) x0) *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            B (s + 7) (z - (x0, 0)) v := by
  refine (n04PositiveGeometry_rootHeightStateJetCLM_material_bound hD hT hS s).elim ?_
  intro C hC
  refine hC.elim ?_
  intro A hA
  refine ⟨C, A, hA.1, hA.2.1, ?_⟩
  intro i a b hab p hp U J k B x0 z hz hzq v
  let L := n04PositiveGeometry_rootHeightStateJetCLM hD hT hS a b p hp i
  have hW : 0 ≤ C * T.E0 p.1 ^ A * T.H p.1 ^ scalarBeta :=
    mul_nonneg (mul_nonneg hA.1
      (Real.rpow_nonneg (hT.2.1 p.1 hp.1).2.2.1.le _))
      (Real.rpow_nonneg (hT.2.1 p.1 hp.1).2.1.le _)
  have hL (x : AnnularState S) : |L x| ≤
      (C * T.E0 p.1 ^ A * T.H p.1 ^ scalarBeta) * stateGrading S (s + 7) x :=
    hA.2.2 i a b hab p hp x
  exact qLinear_oneHigh_bound (stateGrading S) L B (s + 7) hW hL J
    (fun y _ => congrArg (fun t : ℝ => y.2 * t)
      (n04PositiveGeometry_rootHeightStateJetCLM_apply hD hT hS a b p hp i y.1).symm)
    k x0 z hz hzq v

end ContinuousFlexibility.Analysis
