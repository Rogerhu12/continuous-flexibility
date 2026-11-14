import ContinuousFlexibility.Analysis.N01RightChartJets
import ContinuousFlexibility.Analysis.NeighborhoodCircleCharts

/-!
# The two actual angular root labels

One Boolean selector uses the actual left lift or the actual right return
coordinate. Both labels have genuine smoothness, lift laws, positive
first derivatives, and displacement jets with one common low order and
fixed loss. The right endpoint uses the stored return inverse; no label
regularity or high-jet estimate is supplied as an extra hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def n01RootLabel (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (m : ℕ) (rightEnd : Bool) : ℝ → ℝ :=
  if rightEnd then rightChartCandidate S C z m else stateLeftChart S z.1 m

theorem n01RootLabel_contDiff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool) :
    ContDiff ℝ ∞ (n01RootLabel S C z m rightEnd) := by
  cases rightEnd with
  | false => exact contDiff_stateLeftChart hS z.1 m
  | true => exact n01_rightChartCandidate_contDiff hS hT hN hz hs m

theorem n01RootLabel_period_add
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool) (θ : ℝ) :
    n01RootLabel S C z m rightEnd (θ + Real.pi) =
      n01RootLabel S C z m rightEnd θ + Real.pi := by
  have hl (η : ℝ) := hN.2.2.2.2.2.2.2.1 z hz hs m η
  cases rightEnd with
  | false => exact (hl θ).2.2.1
  | true =>
      have hr : C.right m ∈ Icc (C.left m) (C.right m) :=
        ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩
      have hi (η : ℝ) := hN.2.2.2.2.2.2.2.2.1 z hz hs m η
      have hret (η : ℝ) :=
        ((hN.2.2.2.2.2.2.1 z hz m η).2.2.2 (C.right m) hr).2
      have hinv := circleInverse_lift (fun η => (hi η).1)
        (fun η => (hi η).2.1) hret
      have hcomp (η : ℝ) :
          stateLeftChart S z.1 m (C.minusReturnInverse z m (η + Real.pi)) =
            stateLeftChart S z.1 m (C.minusReturnInverse z m η) + Real.pi := by
        rw [hinv η]
        exact (hl (C.minusReturnInverse z m η)).2.2.1
      change circleOddPart
          (fun η => stateLeftChart S z.1 m (C.minusReturnInverse z m η))
          (C.travel m) (θ + Real.pi) =
        circleOddPart (fun η => stateLeftChart S z.1 m (C.minusReturnInverse z m η))
          (C.travel m) θ + Real.pi
      exact circleOddPart_lift hcomp (C.travel m) θ

theorem n01RootLabel_odd
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool) (θ : ℝ) :
    n01RootLabel S C z m rightEnd (-θ) = -n01RootLabel S C z m rightEnd θ := by
  cases rightEnd with
  | false => exact (hN.2.2.2.2.2.2.2.1 z hz hs m θ).2.2.2
  | true =>
      exact circleOddPart_odd
        (fun η => stateLeftChart S z.1 m (C.minusReturnInverse z m η)) (C.travel m) θ

/-- Retain the sharper left lower bound, so the existing left root
normalization is recovered without weakening its conclusion. -/
theorem n01RootLabel_deriv_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool) (θ : ℝ) :
    (if rightEnd then (1 / 4 : ℝ) else 1 / 2) ≤
        deriv (n01RootLabel S C z m rightEnd) θ ∧
      deriv (n01RootLabel S C z m rightEnd) θ ≤ 4 := by
  cases rightEnd with
  | false =>
      have hl := hN.2.2.2.2.2.2.2.1 z hz hs m θ
      exact ⟨hl.1, hl.2.1.trans (by norm_num : (2 : ℝ) ≤ 4)⟩
  | true => exact (canonicalReturnJacobianBounds_of_n01 hN hflow z hz hs m θ).2.1

theorem n01RootLabel_deriv_mem_quarter_four
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool) (θ : ℝ) :
    deriv (n01RootLabel S C z m rightEnd) θ ∈ Icc (1 / 4 : ℝ) 4 := by
  have h := n01RootLabel_deriv_bounds hN hflow hz hs m rightEnd θ
  have hl : (1 / 4 : ℝ) ≤ if rightEnd then (1 / 4 : ℝ) else 1 / 2 := by
    cases rightEnd <;> norm_num
  exact ⟨hl.trans h.1, h.2⟩

def RootLabelPointwiseJets {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (B : ℕ → ℝ) (z : E) (h : ℝ → ℝ) : Prop :=
  ∀ n θ, ‖iteratedFDeriv ℝ n (fun η => h η - η) θ‖ ≤
    B n * (1 + p (n + loss) z)

theorem RootLabelPointwiseJets.mono
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {loss loss' : ℕ} {A B : ℕ → ℝ} {z : E} {h : ℝ → ℝ}
    (hloss : loss ≤ loss') (hB : ∀ n, 0 ≤ B n) (hAB : ∀ n, A n ≤ B n)
    (hj : RootLabelPointwiseJets p loss A z h) :
    RootLabelPointwiseJets p loss' B z h := by
  intro n θ
  exact (hj n θ).trans (mul_le_mul (hAB n)
    (add_le_add (le_refl (1 : ℝ)) ((hp (Nat.add_le_add_left hloss n)) z))
    (add_nonneg zero_le_one (apply_nonneg _ _)) (hB n))

def N01RootLabelJetBound
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base low loss : ℕ) (ε : ℝ) (m : ℕ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
    ∀ rightEnd : Bool,
      RootLabelPointwiseJets (pairGrading (stateGrading S) realGrading) loss B
        (z - (C.referenceState, 0)) (n01RootLabel S C z m rightEnd)

private theorem n01RootLabelJetBound_of_left_right
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base low loss : ℕ} {ε L : ℝ} {m : ℕ} {A : ℕ → ℝ}
    (hL : 0 < L) (hA : ∀ n, 0 < A n)
    (hleft : N01LeftChartPairJetBound S C L)
    (hright : N01RightChartJetBound S C base low loss ε m A) :
    N01RootLabelJetBound S C base low (max 1 loss) ε m (fun n => L + A n) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  intro z hz hs hlow rightEnd
  cases rightEnd with
  | false =>
      exact RootLabelPointwiseJets.mono hp (le_max_left 1 loss)
        (fun n => (add_pos hL (hA n)).le)
        (fun n => le_add_of_nonneg_right (hA n).le) (fun n θ => hleft n m z θ)
  | true =>
      exact RootLabelPointwiseJets.mono hp (le_max_right 1 loss)
        (fun n => (add_pos hL (hA n)).le)
        (fun _ => le_add_of_nonneg_left hL.le) (hright z hz hs hlow)

/-- Both actual labels use one low order and one loss, chosen before
the component. Their numerical constants precede every state and angle. -/
theorem n01_rootLabels_displacement_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) :
    ∃ low outLoss : ℕ, ∀ m : ℕ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      N01RootLabelJetBound S C base low outLoss ε m B := by
  obtain ⟨L, hL, hleft⟩ := n01_stateLeftChart_pairJets hS hT hN
  obtain ⟨low, lossR, hright⟩ :=
    n01_rightChartCandidate_displacement_fixed_loss hS hT hN hflow
  refine ⟨low, max 1 lossR, ?_⟩
  intro m
  obtain ⟨A, hA, hbound⟩ := hright m
  exact ⟨fun n => L + A n, fun n => add_pos hL (hA n),
    n01RootLabelJetBound_of_left_right hL hA hleft hbound⟩

end ContinuousFlexibility.Analysis
