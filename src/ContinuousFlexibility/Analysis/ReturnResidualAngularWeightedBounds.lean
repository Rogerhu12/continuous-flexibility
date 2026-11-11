import ContinuousFlexibility.Analysis.ReturnResidualWeightedBounds
import ContinuousFlexibility.Analysis.ScalarParameterIntegralJets
import ContinuousFlexibility.Analysis.ScalarWeightedJetBounds

/-!
# All angular jets of the independent residual displacement

The actual residual, right chart and endpoint flow have uniformly bounded
positive-order jets. The exact integral formula for the removable divided
difference therefore has uniformly bounded jets of every order. Its
product with the independently decoded circle argument retains the
original component height weight, at every angular order.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

section ActualCharts

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

theorem N01Properties.returnResidualField_positive_jets_uniform
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
      |iteratedDeriv n (returnResidualField S C z m) θ| ≤ A := by
  let F (m : ℕ) : ℝ → ℝ := fun θ =>
    stateLeftChart S z.1 m (C.minusReturnInverse z m θ) - C.travel m
  have hF (m : ℕ) : ContDiff ℝ ∞ (F m) :=
    hN.transportedLeftChart_contDiff hS hT hz hsector m
  have hFb (k : ℕ) (hk : 1 ≤ k) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ m θ, |iteratedDeriv k (F m) θ| ≤ A := by
    obtain ⟨A, hA, hb⟩ := positive_iteratedDeriv_comp_uniform_bound
      (stateLeftChart S z.1) (C.minusReturnInverse z)
      (fun m => stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ)))
      (fun m => hN.minusReturnInverse_contDiff hS hT hz hsector m)
      (stateLeftChart_positive_jets_uniform hS hT hN.1.1 z) hinverse k hk
    refine ⟨A, hA, fun m θ => ?_⟩
    change |iteratedDeriv k (fun t =>
      stateLeftChart S z.1 m (C.minusReturnInverse z m t) - C.travel m) θ| ≤ A
    rw [iteratedDeriv_sub_const_of_pos
      ((stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ))).comp
        (hN.minusReturnInverse_contDiff hS hT hz hsector m)) k hk]
    exact hb m θ
  have heF (m : ℕ) : ContDiff ℝ ∞ (evenPart (F m)) :=
    ((hF m).add ((hF m).comp contDiff_neg)).div_const 2
  have heFb (k : ℕ) (hk : 1 ≤ k) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ m θ, |iteratedDeriv k (evenPart (F m)) θ| ≤ A := by
    obtain ⟨A, hA, hb⟩ := hFb k hk
    exact ⟨A, hA, fun m θ => iteratedDeriv_evenPart_abs_le (hF m) k (hb m) θ⟩
  exact positive_iteratedDeriv_comp_uniform_bound
    (fun m => evenPart (F m)) (C.rightChartInverse z) heF
    (fun m => hN.rightChartInverse_contDiff hS hT hz hsector m)
    heFb (hN.rightChartInverse_positive_jets_uniform hS hT hz hsector hflow hinverse) n hn

theorem N01Properties.returnCorrectionEndpointCoordinate_positive_jets_uniform
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
      |iteratedDeriv n (fun t =>
        rightChartCandidate S C z m (C.minusFlow z m (C.right m) t)) θ| ≤ A := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  apply positive_iteratedDeriv_comp_uniform_bound
    (rightChartCandidate S C z) (fun m => C.minusFlow z m (C.right m))
    (fun m => hN.rightChartCandidate_contDiff hS hT hz hsector m)
    (fun m => hN.minusFlow_angular_contDiff hS hT hz hsector m
      ⟨(hC.1 m).2.1.le, le_rfl⟩)
    (hN.rightChartCandidate_positive_jets_uniform hS hT hz hsector hflow hinverse)
    (fun k hk => ?_) n hn
  obtain ⟨A, hA, hb⟩ := hN.minusFlow_angular_iteratedDeriv_uniform_bound hS hT hz hsector k hk
  exact ⟨A, hA, fun m θ => hb m (C.right m) ⟨(hC.1 m).2.1.le, le_rfl⟩ θ⟩

theorem N01Properties.returnCorrectionDisplacementLinear_angular_weighted_bound
    (ρ : CircleSpace S) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
      |iteratedDeriv n (fun t => returnCorrectionDisplacementLinear S C z m t ρ) θ| ≤
        A * T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  let y (m : ℕ) : ℝ → ℝ := fun θ =>
    rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ)
  let G (m : ℕ) : ℝ → ℝ := fun t => C.minusReturnInverse z m (C.rightChartInverse z m t)
  let e (m : ℕ) : ℝ → ℝ := fun θ => returnResidualField S C z m (y m θ)
  let q (m : ℕ) : ℝ → ℝ := fun θ => dslope (G m) (y m θ) (y m θ + e m θ)
  let W (m : ℕ) : ℝ := T.H (T.sample m) ^ (3 / 4 : ℝ)
  have hH := (material_circle_sample_weights_pos hT hN.1.1).2
  have hW (m : ℕ) : 0 < W m := Real.rpow_pos_of_pos (hH m) _
  have hy (m : ℕ) : ContDiff ℝ ∞ (y m) :=
    (hN.rightChartCandidate_contDiff hS hT hz hsector m).comp
      (hN.minusFlow_angular_contDiff hS hT hz hsector m
        ⟨(hC.1 m).2.1.le, le_rfl⟩)
  have hG (m : ℕ) : ContDiff ℝ ∞ (G m) :=
    hN.returnTransportInverse_contDiff hS hT hz hsector m
  have he (m : ℕ) : ContDiff ℝ ∞ (e m) :=
    (hN.returnResidualField_contDiff hS hT hz hsector m).comp (hy m)
  have hyb (k : ℕ) (hk : 1 ≤ k) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ m θ, |iteratedDeriv k (y m) θ| ≤ A :=
    hN.returnCorrectionEndpointCoordinate_positive_jets_uniform
      hS hT hz hsector hflow hinverse k hk
  have hGb (k : ℕ) (hk : 1 ≤ k) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ m θ, |iteratedDeriv k (G m) θ| ≤ A :=
    hN.returnTransportInverse_positive_jets_uniform hS hT hz hsector hflow hinverse k hk
  have heb (k : ℕ) (hk : 1 ≤ k) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ m θ, |iteratedDeriv k (e m) θ| ≤ A :=
    positive_iteratedDeriv_comp_uniform_bound (returnResidualField S C z) y
      (fun m => hN.returnResidualField_contDiff hS hT hz hsector m) hy
      (hN.returnResidualField_positive_jets_uniform hS hT hz hsector hflow hinverse)
      hyb k hk
  have hq (m : ℕ) : ContDiff ℝ ∞ (q m) :=
    returnCorrection_dslope_comp_contDiff (hG m) (hy m) (he m)
  have hqb (k : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ m θ, |iteratedDeriv k (q m) θ| ≤ A :=
    dslope_comp_iteratedDeriv_uniform_bound G y e hG hy he hGb hyb heb k
  let u (m : ℕ) : ℝ → ℝ := (S.circle (3 / 4 : ℝ)).decode ρ m
  have hu (m : ℕ) : ContDiff ℝ ∞ (u m) :=
    (((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 ρ).1 m).1
  have hub (k : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ m θ, |iteratedDeriv k (u m) θ| ≤ A * W m := by
    refine ⟨2 * circleSobolevConstant * (S.circle (3 / 4 : ℝ)).grading (k + 1) ρ,
      mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg)
        (apply_nonneg _ _), ?_⟩
    exact fun m θ => circleModel_iteratedDeriv_abs_le (hS.2.1 (3 / 4 : ℝ)) hH ρ m k θ
  have hcompb (k : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ m θ, |iteratedDeriv k (fun t => u m (y m t)) θ| ≤ A * W m :=
    iteratedDeriv_comp_weighted_bound u y W hW hu hy k (fun j _ => hub j)
      (fun j hj _ => hyb j hj)
  obtain ⟨A, hA, hb⟩ := iteratedDeriv_mul_weighted_bound q
    (fun m t => u m (y m t)) W hW hq (fun m => (hu m).comp (hy m)) n
    (fun k _ => hqb k) (fun k _ => hcompb k)
  refine ⟨A, hA, fun m θ => ?_⟩
  have heq : (fun t => returnCorrectionDisplacementLinear S C z m t ρ) =
      fun t => q m t * u m (y m t) := by
    funext t
    exact returnCorrectionDisplacementLinear_apply S C z m t ρ
  rw [heq]
  exact hb m θ

end ActualCharts

/-- All angular orders of the independent displacement retain the exact
height exponent on one neighborhood derived from the original N01 data. -/
theorem N01Properties.exists_independent_displacement_angular_weighted_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ N01Properties D T S C base' loss ε' ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
      ∀ ρ : CircleSpace S, ∀ n : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
        |iteratedDeriv n (fun t => returnCorrectionDisplacementLinear S C z m t ρ) θ| ≤
          A * T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  obtain ⟨base', ε', hb, hε', hεε, hnew, hbound⟩ :=
    hN.exists_uniform_inverse_angular_jets hS hT
  refine ⟨base', ε', hb, hε', hεε, hnew, fun z hz hsector ρ n => ?_⟩
  have hC : controlGeometryConditions D S C := hnew.2.2.2.1
  have hflow (m : ℕ) (θ : ℝ) :
      1 / 2 ≤ deriv (C.minusFlow z m (C.right m)) θ ∧
        deriv (C.minusFlow z m (C.right m)) θ ≤ 3 / 2 :=
    (hbound z hz hsector).1 m (C.right m) ⟨(hC.1 m).2.1.le, le_rfl⟩ θ
  have hinverse (k : ℕ) (hk : 1 ≤ k) :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ, |iteratedDeriv k (C.minusReturnInverse z m) θ| ≤ A := by
    obtain ⟨A, hA, _, hret⟩ := (hbound z hz hsector).2 k hk
    exact ⟨A, hA, hret⟩
  exact hnew.returnCorrectionDisplacementLinear_angular_weighted_bound
    hS hT hz hsector hflow hinverse ρ n

end ContinuousFlexibility.Statements
