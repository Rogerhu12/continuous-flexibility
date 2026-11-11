import ContinuousFlexibility.Analysis.N01FlowInverseJetBounds
import ContinuousFlexibility.Analysis.ScalarJetFamilyBounds
import ContinuousFlexibility.Analysis.CircleCompositionModel
import ContinuousFlexibility.Analysis.ReturnCorrectionDisplacementRegularity

/-!
# Uniform angular bounds for the actual return charts

The first-derivative intervals are propagated through the specified
inverse maps, the odd right chart and the correction conjugation.
Positive-order jets are controlled by composition and the scalar inverse
estimate. One common N01 neighborhood supplies all lower bounds.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem returnChart_inverse_deriv_bounds
    (f g : ℝ → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hbound : ∀ x, a ≤ deriv f x ∧ deriv f x ≤ b)
    (hleft : ∀ x, g (f x) = x) (hright : ∀ x, f (g x) = x) (x : ℝ) :
    b⁻¹ ≤ deriv g x ∧ deriv g x ≤ a⁻¹ := by
  have hpos (t : ℝ) : 0 < deriv f t := ha.trans_le (hbound t).1
  rw [(returnChart_hasDerivAt_inverse f g hpos hleft hright x).deriv]
  exact ⟨(inv_le_inv₀ hb (hpos (g x))).mpr (hbound (g x)).2,
    (inv_le_inv₀ (hpos (g x)) ha).mpr (hbound (g x)).1⟩

section FirstDerivatives

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)
  (hflow : ∀ m θ, 1 / 2 ≤ deriv (C.minusFlow z m (C.right m)) θ ∧
    deriv (C.minusFlow z m (C.right m)) θ ≤ 3 / 2)

include hN hz hsector hflow

theorem N01Properties.minusReturnInverse_deriv_bounds (m : ℕ) (θ : ℝ) :
    2 / 3 ≤ deriv (C.minusReturnInverse z m) θ ∧
      deriv (C.minusReturnInverse z m) θ ≤ 2 := by
  have hI := N01Properties.return_inverse_and_positive S C z m hN hz hsector
  simpa only [inv_div, inv_one, one_mul, div_one] using
    returnChart_inverse_deriv_bounds (C.minusFlow z m (C.right m)) (C.minusReturnInverse z m)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 3 / 2)
      (hflow m) (fun t => (hI t).2.1) (fun t => (hI t).1) θ

theorem N01Properties.rightChartCandidate_deriv_bounds (m : ℕ) (θ : ℝ) :
    1 / 3 ≤ deriv (rightChartCandidate S C z m) θ ∧
      deriv (rightChartCandidate S C z m) θ ≤ 4 := by
  let F : ℝ → ℝ := fun t => stateLeftChart S z.1 m (C.minusReturnInverse z m t) - C.travel m
  have hL := hN.2.2.2.2.2.2.2.1 z hz hsector m
  have hI := N01Properties.return_inverse_and_positive S C z m hN hz hsector
  have hfpos (t : ℝ) : 0 < deriv (C.minusFlow z m (C.right m)) t :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le (hflow m t).1
  have hF (t : ℝ) : HasDerivAt F
      (deriv (stateLeftChart S z.1 m) (C.minusReturnInverse z m t) *
        deriv (C.minusReturnInverse z m) t) t := by
    have hi := returnChart_hasDerivAt_inverse (C.minusFlow z m (C.right m))
      (C.minusReturnInverse z m) hfpos (fun s => (hI s).2.1) (fun s => (hI s).1) t
    have hl := (differentiableAt_of_deriv_ne_zero
      (((by norm_num : (0 : ℝ) < 1 / 2).trans_le (hL (C.minusReturnInverse z m t)).1).ne')).hasDerivAt
    have h := (hl.comp t hi).sub_const (C.travel m)
    rw [← hi.deriv] at h
    exact h
  have hFb (t : ℝ) : 1 / 3 ≤ deriv F t ∧ deriv F t ≤ 4 := by
    rw [(hF t).deriv]
    have hi := hN.minusReturnInverse_deriv_bounds hz hsector hflow m t
    have hl := hL (C.minusReturnInverse z m t)
    constructor
    · have h := mul_le_mul hl.1 hi.1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
        ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans hl.1)
      norm_num at h
      exact h
    · have h := mul_le_mul hl.2.1 hi.2
        ((by norm_num : (0 : ℝ) ≤ 2 / 3).trans hi.1) (by norm_num : (0 : ℝ) ≤ 2)
      norm_num at h
      exact h
  have hd := oddPart_hasDerivAt ((hF θ).congr_deriv (hF θ).deriv.symm)
    ((hF (-θ)).congr_deriv (hF (-θ)).deriv.symm)
  change HasDerivAt (rightChartCandidate S C z m) ((deriv F θ + deriv F (-θ)) / 2) θ at hd
  rw [hd.deriv]
  constructor <;> linarith only [(hFb θ).1, (hFb θ).2, (hFb (-θ)).1, (hFb (-θ)).2]

theorem N01Properties.rightChartInverse_deriv_bounds (m : ℕ) (θ : ℝ) :
    1 / 4 ≤ deriv (C.rightChartInverse z m) θ ∧
      deriv (C.rightChartInverse z m) θ ≤ 3 := by
  have hI := N01Properties.return_inverse_and_positive S C z m hN hz hsector
  have h := returnChart_inverse_deriv_bounds (rightChartCandidate S C z m)
    (C.rightChartInverse z m)
    (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num : (0 : ℝ) < 4)
    (hN.rightChartCandidate_deriv_bounds hz hsector hflow m)
    (fun t => (hI t).2.2.2.1) (fun t => (hI t).2.2.1) θ
  norm_num at h ⊢
  exact h

theorem N01Properties.returnTransportInverse_deriv_bounds (m : ℕ) (θ : ℝ) :
    1 / 6 ≤ deriv (fun t => C.minusReturnInverse z m (C.rightChartInverse z m t)) θ ∧
      deriv (fun t => C.minusReturnInverse z m (C.rightChartInverse z m t)) θ ≤ 6 := by
  have hf := N01Properties.minusReturnInverse_differentiable S C z m hN hz hsector
  have hg := N01Properties.rightChartInverse_differentiable S C z m hN hz hsector
  have heq := deriv_comp θ (hf (C.rightChartInverse z m θ)) (hg θ)
  change deriv (fun t => C.minusReturnInverse z m (C.rightChartInverse z m t)) θ = _ at heq
  rw [heq]
  have hfirst := hN.minusReturnInverse_deriv_bounds hz hsector hflow m (C.rightChartInverse z m θ)
  have hsecond := hN.rightChartInverse_deriv_bounds hz hsector hflow m θ
  constructor
  · have h := mul_le_mul hfirst.1 hsecond.1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
      ((by norm_num : (0 : ℝ) ≤ 2 / 3).trans hfirst.1)
    norm_num at h
    exact h
  · have h := mul_le_mul hfirst.2 hsecond.2
      ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans hsecond.1) (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h
    exact h

theorem N01Properties.returnCorrectionInitialMap_deriv_bounds (m : ℕ) (θ : ℝ) :
    1 / 12 ≤ deriv (returnCorrectionInitialMap S C z m) θ ∧
      deriv (returnCorrectionInitialMap S C z m) θ ≤ 12 := by
  let G : ℝ → ℝ := fun t => C.minusReturnInverse z m (C.rightChartInverse z m t)
  have hL := hN.2.2.2.2.2.2.2.1 z hz hsector m
  have hG (t : ℝ) := hN.returnTransportInverse_deriv_bounds hz hsector hflow m t
  have hg : DifferentiableAt ℝ G (stateLeftChart S z.1 m θ - C.travel m) :=
    differentiableAt_of_deriv_ne_zero
      (((by norm_num : (0 : ℝ) < 1 / 6).trans_le (hG _).1).ne')
  have hl : DifferentiableAt ℝ (stateLeftChart S z.1 m) θ :=
    differentiableAt_of_deriv_ne_zero
      (((by norm_num : (0 : ℝ) < 1 / 2).trans_le (hL θ).1).ne')
  have hd := hg.hasDerivAt.comp θ (hl.hasDerivAt.sub_const (C.travel m))
  have heq : G ∘ (fun t => stateLeftChart S z.1 m t - C.travel m) =
      returnCorrectionInitialMap S C z m := by
    funext t
    simp only [G, Function.comp_def, returnCorrectionInitialMap_apply]
  rw [heq] at hd
  rw [hd.deriv]
  have hf := hG (stateLeftChart S z.1 m θ - C.travel m)
  constructor
  · have h := mul_le_mul hf.1 (hL θ).1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      ((by norm_num : (0 : ℝ) ≤ 1 / 6).trans hf.1)
    norm_num at h
    exact h
  · have h := mul_le_mul hf.2 (hL θ).2.1
      ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hL θ).1) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num at h
    exact h

end FirstDerivatives

theorem stateLeftChart_positive_jets_uniform
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (z : AnnularState S × ℝ)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ, |iteratedDeriv n (stateLeftChart S z.1 m) θ| ≤ A := by
  obtain ⟨A, hA, hbound⟩ := circleModelLift_uniform_jets_of_material
    (hS.2.1 (3 / 4 : ℝ)) hT hD (by norm_num : (0 : ℝ) < 3 / 4) z.1.2.2.2 n
  exact ⟨A ^ n, pow_nonneg hA _, fun m θ => hbound m n θ hn le_rfl⟩

section HigherDerivatives

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)
  (hflow : ∀ m θ, 1 / 2 ≤ deriv (C.minusFlow z m (C.right m)) θ ∧
    deriv (C.minusFlow z m (C.right m)) θ ≤ 3 / 2)
  (hinverse : ∀ n : ℕ, 1 ≤ n → ∃ A : ℝ, 0 ≤ A ∧
    ∀ m θ, |iteratedDeriv n (C.minusReturnInverse z m) θ| ≤ A)

include hN hS hT hz hsector hflow hinverse

theorem N01Properties.rightChartCandidate_positive_jets_uniform
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
      |iteratedDeriv n (rightChartCandidate S C z m) θ| ≤ A := by
  obtain ⟨A, hA, hbound⟩ := positive_iteratedDeriv_comp_uniform_bound
    (stateLeftChart S z.1) (C.minusReturnInverse z)
    (fun m => stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ)))
    (fun m => hN.minusReturnInverse_contDiff hS hT hz hsector m)
    (stateLeftChart_positive_jets_uniform hS hT hN.1.1 z) hinverse n hn
  refine ⟨A, hA, fun m θ => ?_⟩
  let F : ℝ → ℝ := fun t => stateLeftChart S z.1 m (C.minusReturnInverse z m t) - C.travel m
  have hF := hN.transportedLeftChart_contDiff hS hT hz hsector m
  apply iteratedDeriv_oddPart_abs_le hF n (fun t => ?_) θ
  rw [iteratedDeriv_sub_const_of_pos
    ((stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ))).comp
      (hN.minusReturnInverse_contDiff hS hT hz hsector m)) n hn]
  exact hbound m t

theorem N01Properties.rightChartInverse_positive_jets_uniform
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
      |iteratedDeriv n (C.rightChartInverse z m) θ| ≤ A := by
  apply inverse_iteratedDeriv_uniform_bound
    (rightChartCandidate S C z) (C.rightChartInverse z)
    (fun m => hN.rightChartCandidate_contDiff hS hT hz hsector m)
    (by norm_num : (0 : ℝ) < 1 / 3)
    (fun m θ => (hN.rightChartCandidate_deriv_bounds hz hsector hflow m θ).1)
    (fun m θ => (N01Properties.return_inverse_and_positive S C z m hN hz hsector θ).2.2.2.1)
    (fun m θ => (N01Properties.return_inverse_and_positive S C z m hN hz hsector θ).2.2.1)
    (hN.rightChartCandidate_positive_jets_uniform hS hT hz hsector hflow hinverse) n hn

theorem N01Properties.returnTransportInverse_positive_jets_uniform
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
      |iteratedDeriv n (fun t => C.minusReturnInverse z m (C.rightChartInverse z m t)) θ| ≤ A :=
  positive_iteratedDeriv_comp_uniform_bound
    (C.minusReturnInverse z) (C.rightChartInverse z)
    (fun m => hN.minusReturnInverse_contDiff hS hT hz hsector m)
    (fun m => hN.rightChartInverse_contDiff hS hT hz hsector m) hinverse
    (hN.rightChartInverse_positive_jets_uniform hS hT hz hsector hflow hinverse) n hn

theorem N01Properties.returnCorrectionInitialMap_positive_jets_uniform
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
      |iteratedDeriv n (returnCorrectionInitialMap S C z m) θ| ≤ A := by
  apply positive_iteratedDeriv_comp_uniform_bound
    (fun m t => C.minusReturnInverse z m (C.rightChartInverse z m t))
    (fun m t => stateLeftChart S z.1 m t - C.travel m)
    (fun m => hN.returnTransportInverse_contDiff hS hT hz hsector m)
    (fun m => (stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ))).sub contDiff_const)
    (hN.returnTransportInverse_positive_jets_uniform hS hT hz hsector hflow hinverse)
    (fun k hk => ?_) n hn
  obtain ⟨A, hA, hbound⟩ := stateLeftChart_positive_jets_uniform hS hT hN.1.1 z k hk
  refine ⟨A, hA, fun m θ => ?_⟩
  rw [iteratedDeriv_sub_const_of_pos (stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ))) k hk]
  exact hbound m θ

end HigherDerivatives

/-- All the return-chart bounds above hold on one neighborhood obtained
from the original N01 assumptions. -/
theorem N01Properties.exists_uniform_returnChart_angular_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ N01Properties D T S C base' loss ε' ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
      (∀ m θ, 1 / 12 ≤ deriv (returnCorrectionInitialMap S C z m) θ ∧
        deriv (returnCorrectionInitialMap S C z m) θ ≤ 12) ∧
      (∀ n : ℕ, 1 ≤ n → ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
        |iteratedDeriv n (C.rightChartInverse z m) θ| ≤ A ∧
        |iteratedDeriv n (fun t => C.minusReturnInverse z m (C.rightChartInverse z m t)) θ| ≤ A ∧
        |iteratedDeriv n (returnCorrectionInitialMap S C z m) θ| ≤ A) := by
  obtain ⟨base', ε', hb, hε', hεε, hnew, hbound⟩ :=
    hN.exists_uniform_inverse_angular_jets hS hT
  refine ⟨base', ε', hb, hε', hεε, hnew, fun z hz hsector => ?_⟩
  have hcontrol : controlGeometryConditions D S C := hnew.2.2.2.1
  have hflow (m : ℕ) (θ : ℝ) :
      1 / 2 ≤ deriv (C.minusFlow z m (C.right m)) θ ∧
        deriv (C.minusFlow z m (C.right m)) θ ≤ 3 / 2 :=
    (hbound z hz hsector).1 m (C.right m) ⟨(hcontrol.1 m).2.1.le, le_rfl⟩ θ
  have hinverse (n : ℕ) (hn : 1 ≤ n) :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ, |iteratedDeriv n (C.minusReturnInverse z m) θ| ≤ A := by
    obtain ⟨A, hA, _, hret⟩ := (hbound z hz hsector).2 n hn
    exact ⟨A, hA, hret⟩
  refine ⟨hnew.returnCorrectionInitialMap_deriv_bounds hz hsector hflow, fun n hn => ?_⟩
  obtain ⟨A, hA, hbA⟩ :=
    hnew.rightChartInverse_positive_jets_uniform hS hT hz hsector hflow hinverse n hn
  obtain ⟨B, hB, hbB⟩ :=
    hnew.returnTransportInverse_positive_jets_uniform hS hT hz hsector hflow hinverse n hn
  obtain ⟨E, hE, hbE⟩ :=
    hnew.returnCorrectionInitialMap_positive_jets_uniform hS hT hz hsector hflow hinverse n hn
  refine ⟨A + B + E, by positivity, fun m θ => ?_⟩
  exact ⟨(hbA m θ).trans (by linarith), (hbB m θ).trans (by linarith),
    (hbE m θ).trans (by linarith)⟩

end ContinuousFlexibility.Statements

