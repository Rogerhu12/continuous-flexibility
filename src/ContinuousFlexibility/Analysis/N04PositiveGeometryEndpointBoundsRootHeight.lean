module

public import ContinuousFlexibility.Analysis.N06RootWeightedHeights
public import ContinuousFlexibility.Analysis.N01cPolarMixedParameterJets
public import ContinuousFlexibility.Analysis.CylinderMixedJetNorms

/-!
# Actual parameter jets of the four normalized root height inputs

Each root input is either the decoder of an existing tame linear height
map or one angular derivative of that decoder. Its physical mixed jet
is therefore a continuous linear functional of the original common
height. Multiplying by the original scalar parameter gives the genuine
quadratic tower and preserves the material height gain at every
parameter order. The four inputs share one fixed spatial loss seven.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04PositiveRootHeightStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- The exact mixed jet of one of the four normalized root height
fields, realized by the original continuous linear height maps. -/
def n04PositiveGeometry_rootHeightJetCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    Fin 4 → ScalarCommonHeight S →L[ℝ] ℝ :=
  Fin.cases
    ((heightPhysicalJetCLM hT (hS.1 scalarBeta) a b p hp).comp
      (n06RootNormalizedRadialCLM hD hT hS))
    (Fin.cases
      ((heightPhysicalJetCLM hT (hS.1 scalarBeta) a (b + 1) p hp).comp
        (n06RootAngularPrimitiveCLM hD hT hS))
      (Fin.cases
        ((heightPhysicalJetCLM hT (hS.1 scalarBeta) a (b + 1) p hp).comp
          (n06RootNormalizedMixedPrimitiveCLM hD hT hS))
        (Fin.cases
          ((heightPhysicalJetCLM hT (hS.1 scalarBeta) a b p hp).comp
            (n06RootNormalizedAngularSecondCLM hD hT hS))
          (fun i => i.elim0))))

theorem n04PositiveGeometry_rootHeightJetCLM_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D)
    (i : Fin 4) (u : ScalarCommonHeight S) :
    n04PositiveGeometry_rootHeightJetCLM hD hT hS a b p hp i u =
      mixedDerivative a b (n06RootNormalizedHeightFields D S u i) p := by
  have heval (L : ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S) (c : ℕ) :
      ((heightPhysicalJetCLM hT (hS.1 scalarBeta) a c p hp).comp L) u =
        mixedDerivative a c ((S.height scalarBeta).decode (L u)) p := by
    rw [ContinuousLinearMap.comp_apply, heightPhysicalJetCLM_apply]
  have hangle (L : ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S) :
      ((heightPhysicalJetCLM hT (hS.1 scalarBeta) a (b + 1) p hp).comp L) u =
        mixedDerivative a b (angularPartial ((S.height scalarBeta).decode (L u))) p :=
    (heval L (b + 1)).trans
      (mixedDerivative_angularPartial isOpen_univ
        (scalarHeight_decode_contDiff_and_flatJets hT hS (L u)).1.contDiffOn
        a b (mem_univ p)).symm
  fin_cases i
  · exact (heval (n06RootNormalizedRadialCLM hD hT hS) b).trans
      (congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f p)
        (funext (n06_decode_rootNormalizedRadial hD hT hS u)))
  · exact (hangle (n06RootAngularPrimitiveCLM hD hT hS)).trans
      (congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f p)
        (n06_angularPartial_decode_rootAngularPrimitive hD hT hS u))
  · exact (hangle (n06RootNormalizedMixedPrimitiveCLM hD hT hS)).trans
      (congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f p)
        (n06_angularPartial_decode_rootNormalizedMixedPrimitive hD hT hS u))
  · exact (heval (n06RootNormalizedAngularSecondCLM hD hT hS) b).trans
      (congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f p)
        (funext (n06_decode_rootNormalizedAngularSecond hD hT hS u)))

/-- The same functional on the original nonlinear state. -/
def n04PositiveGeometry_rootHeightStateJetCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) (i : Fin 4) :
    AnnularState S →L[ℝ] ℝ :=
  (n04PositiveGeometry_rootHeightJetCLM hD hT hS a b p hp i).comp
    (ContinuousLinearMap.fst ℝ (ScalarCommonHeight S)
      (ℝ × CircleSpace S × CircleSpace S))

theorem n04PositiveGeometry_rootHeightStateJetCLM_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D)
    (i : Fin 4) (x : AnnularState S) :
    n04PositiveGeometry_rootHeightStateJetCLM hD hT hS a b p hp i x =
      mixedDerivative a b (n06RootNormalizedHeightFields D S x.1 i) p := by
  exact n04PositiveGeometry_rootHeightJetCLM_apply hD hT hS a b p hp i x.1

/-- Uniform material decay and fixed spatial loss for the actual
q-weighted normalized inputs. Every genuine tower satisfies the same
estimate; no parameter jet is supplied as a quantitative assumption. -/
theorem n04PositiveGeometry_rootHeightInputs_oneHigh
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (s : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i : Fin 4, ∀ a b : ℕ, a + b ≤ s →
      ∀ p ∈ annularOpen D, ∀ U : Set (AnnularState S × ℝ),
      ∀ J : SmoothDirections U (fun z => z.2 *
        mixedDerivative a b (n06RootNormalizedHeightFields D S z.1.1 i) p),
      ∀ k B : ℕ, ∀ x0 : AnnularState S, ∀ z ∈ U, |z.2| ≤ 1 →
      ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ A * n06RootJetWeight T p * (1 + stateGrading S (s + 7) x0) *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            B (s + 7) (z - (x0, 0)) v := by
  refine (n06_rootNormalizedHeightFields_spatial_weighted_bound hD hT hS s).elim ?_
  intro A hA
  refine ⟨A, hA.1, ?_⟩
  intro i a b hab p hp U J k B x0 z hz hzq v
  let L := n04PositiveGeometry_rootHeightStateJetCLM hD hT hS a b p hp i
  have hW : 0 ≤ A * n06RootJetWeight T p :=
    mul_nonneg hA.1 (n06_rootJetWeight_nonneg hT hp)
  have hL (x : AnnularState S) : |L x| ≤
      (A * n06RootJetWeight T p) * stateGrading S (s + 7) x := by
    have hm := abs_mixedDerivative_le_norm_iteratedFDeriv isOpen_univ
      (n06_rootNormalizedHeightFields_contDiff hD hT hS x.1 i).contDiffOn
      a b (mem_univ p)
    have hb := hA.2 x.1 i (a + b) hab p hp
    exact (congrArg abs (n04PositiveGeometry_rootHeightStateJetCLM_apply
      hD hT hS a b p hp i x)).trans_le
      ((hm.trans hb).trans (mul_le_mul_of_nonneg_left
        (n06_root_commonHeightGrading_le_state S (s + 7) x) hW))
  exact qLinear_oneHigh_bound (stateGrading S) L B (s + 7) hW hL J
    (fun y _ => congrArg (fun t : ℝ => y.2 * t)
      (n04PositiveGeometry_rootHeightStateJetCLM_apply hD hT hS a b p hp i y.1).symm)
    k x0 z hz hzq v

end ContinuousFlexibility.Analysis
