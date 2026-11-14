import ContinuousFlexibility.Analysis.N01ReturnInverseJets
import ContinuousFlexibility.Analysis.N01LeftChartJets
import ContinuousFlexibility.Analysis.CircleLiftCompositionJets

/-!
# Actual all-order jets of the right return coordinate

The actual right coordinate is the odd part of the left lift composed
with the stored return inverse. The travel constant cancels exactly.
Composition uses the existing one-high-factor estimate; odd projection
does not enlarge the uniform angular jet bound or the derivative loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Odd projection preserves a uniform angular displacement-jet bound.
The travel subtraction cancels at every order, including order zero. -/
theorem oddPart_lift_displacement_jet_le
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {n : ℕ} {M : ℝ}
    (hb : ∀ θ, ‖iteratedFDeriv ℝ n (fun η => f η - η) θ‖ ≤ M)
    (T θ : ℝ) :
    ‖iteratedFDeriv ℝ n
      (fun η => oddPart (fun ξ => f ξ - T) η - η) θ‖ ≤ M := by
  let u : ℝ → ℝ := fun η => f η - η
  have hu : ContDiff ℝ ∞ u := hf.sub contDiff_id
  have huNeg : ContDiff ℝ ∞ (fun η : ℝ => u (-η)) := hu.comp contDiff_neg
  have he : (fun η => oddPart (fun ξ => f ξ - T) η - η) =
      (fun η => (u η - u (-η)) / 2) := by
    funext η
    dsimp only [oddPart, u]
    ring
  have hpos : |iteratedDeriv n u θ| ≤ M := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hb θ
  have hneg : |iteratedDeriv n u (-θ)| ≤ M := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hb (-θ)
  have href : |iteratedDeriv n (fun η => u (-η)) θ| =
      |iteratedDeriv n u (-θ)| := by
    rw [iteratedDeriv_comp_neg]
    simp only [smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [he, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    iteratedDeriv_div_const,
    iteratedDeriv_fun_sub (n := n) (x := θ)
      (hu.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      (huNeg.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)), abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  have htriangle :
      |iteratedDeriv n u θ - iteratedDeriv n (fun η => u (-η)) θ| ≤
        |iteratedDeriv n u θ| + |iteratedDeriv n (fun η => u (-η)) θ| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      (abs_sub_le (iteratedDeriv n u θ) (0 : ℝ)
        (iteratedDeriv n (fun η => u (-η)) θ))
  exact htriangle.trans (by rw [href]; linarith)

private def CircleReturnDisplacementJetBound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (B : ℕ → ℝ)
    (z : E) (f : ℝ → ℝ) : Prop :=
  ∀ n θ, ‖iteratedFDeriv ℝ n (fun η => f η - η) θ‖ ≤
    B n * (1 + p (n + loss) z)

private theorem circleReturn_displacement_fixed_loss
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inverseLoss : ℕ) :
    ∃ low loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p low z ≤ 1 → ∀ l g : ℝ → ℝ,
      ContDiff ℝ ∞ l → ContDiff ℝ ∞ g →
      CircleReturnDisplacementJetBound p 1 A z l →
      CircleReturnDisplacementJetBound p inverseLoss A z g → ∀ T : ℝ,
      CircleReturnDisplacementJetBound p loss B z (oddPart (fun θ => l (g θ) - T)) := by
  obtain ⟨low, loss, htarget⟩ :=
    circleLiftComposition_displacement_fixed_loss (X := ℝ) hp hI (max 1 inverseLoss)
  refine ⟨low, loss, ?_⟩
  intro A hA
  obtain ⟨B, hB, hbound⟩ := htarget A hA
  refine ⟨B, hB, ?_⟩
  intro z hz l g hl hg hleft hinverse T n θ
  apply oddPart_lift_displacement_jet_le (hl.comp hg) (T := T)
  intro η
  apply hbound z hz l hl g hg (ContinuousLinearMap.id ℝ ℝ)
    (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ)) η
  · intro k
    exact (hleft k (g η)).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl (1 : ℝ))
        ((hp (Nat.add_le_add_left (le_max_left 1 inverseLoss) k)) z)) (hA k).le)
  · intro k
    exact (hinverse k η).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl (1 : ℝ))
        ((hp (Nat.add_le_add_left (le_max_right 1 inverseLoss) k)) z)) (hA k).le)

/-- Smoothness of the actual right chart follows from the stored return
identities and the actual angular regularity of the ordinary flow. -/
theorem n01_rightChartCandidate_contDiff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ContDiff ℝ ∞ (rightChartCandidate S C z m) := by
  have hg := n01_minusReturnInverse_contDiff hS hT hN hz hs m
  have hf : ContDiff ℝ ∞
      (fun θ => stateLeftChart S z.1 m (C.minusReturnInverse z m θ) - C.travel m) :=
    ((contDiff_stateLeftChart hS z.1 m).comp hg).sub contDiff_const
  exact (hf.sub (hf.comp contDiff_neg)).div_const 2

/-- All actual angular jets of the right displacement on one common
state neighborhood, with a common low order and a fixed derivative loss. -/
def N01RightChartJetBound
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base low outLoss : ℕ) (ε : ℝ) (m : ℕ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
    ∀ n θ, ‖iteratedFDeriv ℝ n (fun η => rightChartCandidate S C z m η - η) θ‖ ≤
      B n * (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
        (z - (C.referenceState, 0)))

private theorem displacementJetBound_enlarge_majorant
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {z : E} {f : ℝ → ℝ} {loss : ℕ}
    {A B : ℕ → ℝ} (hAB : ∀ n, A n ≤ B n)
    (hf : CircleReturnDisplacementJetBound p loss A z f) :
    CircleReturnDisplacementJetBound p loss B z f := by
  intro n θ
  exact (hf n θ).trans (mul_le_mul_of_nonneg_right (hAB n)
    (add_nonneg zero_le_one (apply_nonneg _ _)))

private theorem n01_rightChart_bound_of_circleReturn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss lowI lossI lowR lossR : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {L : ℝ} (hL : 0 < L) (hleft : N01LeftChartPairJetBound S C L)
    (m : ℕ) (A B : ℕ → ℝ) (hA : ∀ n, 0 < A n)
    (hinverse : N01ReturnInverseJetBound S C base lowI lossI ε m A)
    (hreturn : ∀ x : AnnularState S × ℝ,
      pairGrading (stateGrading S) realGrading lowR x ≤ 1 → ∀ l g : ℝ → ℝ,
      ContDiff ℝ ∞ l → ContDiff ℝ ∞ g →
      CircleReturnDisplacementJetBound (pairGrading (stateGrading S) realGrading)
        1 (fun n => L + A n) x l →
      CircleReturnDisplacementJetBound (pairGrading (stateGrading S) realGrading)
        lossI (fun n => L + A n) x g → ∀ t : ℝ,
      CircleReturnDisplacementJetBound (pairGrading (stateGrading S) realGrading)
        lossR B x (oddPart (fun θ => l (g θ) - t))) :
    N01RightChartJetBound S C base (max lowI lowR) lossR ε m B := by
  intro z hz hs hlow
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hlowI := (hp (le_max_left lowI lowR) (z - (C.referenceState, 0))).trans hlow
  have hlowR := (hp (le_max_right lowI lowR) (z - (C.referenceState, 0))).trans hlow
  exact hreturn (z - (C.referenceState, 0)) hlowR
    (stateLeftChart S z.1 m) (C.minusReturnInverse z m)
    (contDiff_stateLeftChart hS z.1 m)
    (n01_minusReturnInverse_contDiff hS hT hN hz hs m)
    (displacementJetBound_enlarge_majorant
      (fun n => le_add_of_nonneg_right (hA n).le) (fun n θ => hleft n m z θ))
    (displacementJetBound_enlarge_majorant
      (fun _ => le_add_of_nonneg_left hL.le) (hinverse z hz hs hlowI)) (C.travel m)

/-- The genuine right coordinate has fixed-loss angular jets. No
smoothness or high-jet estimate for that coordinate is supplied as input. -/
theorem n01_rightChartCandidate_displacement_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) :
    ∃ low outLoss : ℕ, ∀ m : ℕ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      N01RightChartJetBound S C base low outLoss ε m B := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
    coordinate_hasInterpolation_realGrading
  obtain ⟨lowI, lossI, hinverse⟩ := n01_minusReturnInverse_displacement_fixed_loss hS hT hN hflow
  obtain ⟨lowR, lossR, htarget⟩ := circleReturn_displacement_fixed_loss hp hI lossI
  obtain ⟨L, hL, hleft⟩ := n01_stateLeftChart_pairJets hS hT hN
  refine ⟨max lowI lowR, lossR, ?_⟩
  intro m
  obtain ⟨A, hA, hAjet⟩ := hinverse m
  obtain ⟨B, hB, hreturn⟩ := htarget (fun n => L + A n) (fun n => add_pos hL (hA n))
  exact ⟨B, hB, n01_rightChart_bound_of_circleReturn hS hT hN hL hleft m A B hA hAjet hreturn⟩

end ContinuousFlexibility.Analysis
