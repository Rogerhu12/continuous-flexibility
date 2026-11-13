import ContinuousFlexibility.Analysis.N04RealizationFixedSpatialProduct
import ContinuousFlexibility.Analysis.FlowJetLinearization
import ContinuousFlexibility.Analysis.CylinderMixedJetNorms

/-! Multiplication by the actual normalized radius keeps the full
positive-state bound and its original high seminorm. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04NegativeChart_radialProduct_parameterJet_bound
    {U : Set X} {Ω : Set PolarPoint} {f : X → PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (F : MixedJetRegularity U Ω f)
    (a b s k : ℕ) (hab : a + b ≤ s) {q : PolarPoint} (hq : q ∈ Ω)
    (hqone : |q.1| ≤ 1)
    (J : SmoothDirections U
      (fun x => mixedDerivative a b (fun p => p.1 * f x p) q))
    {x : X} (hx : x ∈ U) (v : Fin k → X) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u w : ℕ, u + w ≤ s →
      |(F.parameter u w q hq).D k x v| ≤ M) :
    |J.D k x v| ≤ (2 : ℝ) ^ s * M := by
  have hfixed (u w : ℕ) (_ : u + w ≤ s) :
      |mixedDerivative u w (fun p : PolarPoint => p.1) q| ≤ 1 := by
    apply (abs_mixedDerivative_le_norm_iteratedFDeriv hΩ contDiff_fst.contDiffOn
      u w hq).trans
    by_cases hn : u + w = 0
    · simpa only [hn, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hqone
    · exact (flowJet_norm_iteratedFDeriv_clm_le
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (Nat.pos_of_ne_zero hn) q).trans
        (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
  have hb := n04Realization_fixedSpatialProduct_parameterJet_bound
    hΩ contDiff_fst.contDiffOn F a b s k hab hq J hx v
    zero_le_one hM (le_rfl : (1 : ℝ) ≤ 1) hfixed
    (fun u w huw => by simpa only [Real.one_rpow, mul_one] using hbound u w huw)
  have hb' : |J.D k x v| ≤ (2 : ℝ) ^ (a + b) * M := by
    simpa only [one_mul, mul_one, Real.one_rpow] using hb
  exact hb'.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hab) hM)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_radialProduct_parameterJet_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_radialProduct_parameterJet_bound
