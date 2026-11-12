import ContinuousFlexibility.Analysis.N04RealizationMixedProductJets
import ContinuousFlexibility.Analysis.N04RealizationParameterRescale

/-!
# A spatial scale for the existing finite product estimate

This is a numerical specialization of the existing mixed product rule.
The positive spatial scale is retained to exactly the sum of the input
orders. The parameter directions are arbitrary members of the supplied
predicate, so a common direction rescaling remains admissible.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04Realization_finiteProduct_scale_bound (m k a b : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (U : Set X), IsOpen U →
      ∀ (Ω : Set PolarPoint), IsOpen Ω → ∀ f : Fin m → X → PolarPoint → ℝ,
      ∀ F : ∀ i, MixedJetRegularity U Ω (f i), ∀ q (hq : q ∈ Ω),
      ∀ J : SmoothDirections U (fun x => mixedDerivative a b (fun p => ∏ i, f i x p) q),
      ∀ x ∈ U, ∀ (P : X → Prop) (v : Fin k → X), (∀ i, P (v i)) →
      ∀ H M t : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ M → 1 ≤ t →
      (∀ i : Fin m, ∀ j : ℕ, j ≤ k → ∀ u w : ℕ, u + w ≤ a + b →
        ∀ z : Fin j → X, (∀ l, P (z l)) →
        ‖((F i).parameter u w q hq).D j x z‖ ≤
          M * parameterHeightWeight H j * t ^ (u + w)) →
      ‖J.D k x v‖ ≤ B * M ^ m * parameterHeightWeight H k * t ^ (a + b) := by
  obtain ⟨B, hB, hb⟩ := n04Realization_shiftedProduct_parameter_bound (X := X) m k a b RH
  refine ⟨B, hB, ?_⟩
  intro U hU Ω hΩ f F q hq J x hx P v hv H M t hH hHR hM ht hsource
  let r : ℝ := t ^ (((a + b : ℕ) : ℝ) + 1)
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hr : 1 ≤ r := Real.one_le_rpow ht (by positivity)
  have hrpow (d : ℕ) :
      r ^ ((d : ℝ) / (((a + b : ℕ) : ℝ) + 1)) = t ^ d := by
    have h := n04Realization_rpow_change_budget htpos.le
      (by positivity : (((a + b : ℕ) : ℝ) + 1) ≠ 0) 1 (d : ℝ)
    simpa only [r, div_one, Real.rpow_natCast] using h
  have hbase (i : Fin m) (u w : ℕ) (huw : u + w ≤ a + b) :
      ‖mixedDerivative u w (f i x) q‖ ≤
        M * (1 : ℝ) ^ (0 : ℝ) * r ^ (((u + w : ℕ) : ℝ) / (((a + b : ℕ) : ℝ) + 1)) := by
    have h := hsource i 0 (Nat.zero_le k) u w huw Fin.elim0 (fun l => l.elim0)
    simpa only [smoothDirections_D_zero_apply ((F i).parameter u w q hq) hx,
      parameterHeightWeight, ite_true, mul_one, Real.rpow_zero, hrpow] using h
  have hjet (i : Fin m) (u w : ℕ) (huw : u + w ≤ a + b)
      (d : OrderedFinpartition k) (j : Fin d.length) :
      ‖((F i).parameter u w q hq).D (d.partSize j) x (v ∘ d.emb j)‖ ≤
        H * (M * (1 : ℝ) ^ (0 : ℝ) *
          r ^ (((u + w : ℕ) : ℝ) / (((a + b : ℕ) : ℝ) + 1))) := by
    have h := hsource i (d.partSize j) (d.partSize_le j) u w huw
      (v ∘ d.emb j) (fun l => hv _)
    simpa only [parameterHeightWeight, if_neg (Nat.ne_of_gt (d.partSize_pos j)),
      Real.rpow_zero, mul_one, hrpow, mul_assoc, mul_comm, mul_left_comm] using h
  let Jprod : SmoothDirections U (fun y => mixedDerivative a b
      (fun p => ∏ i, mixedDerivative 0 0 (f i y) p) q) :=
    J.congr (fun _ _ => by simp only [mixedDerivative, iteratedDeriv_zero])
  have h := hb (fun _ => 0) (fun _ => 0) U hU Ω hΩ f F q hq Jprod x hx v
    (a + b) (by simp) H 1 M 0 r hH hHR le_rfl hM le_rfl hr hbase hjet
  simpa only [Jprod, SmoothDirections.congr, Nat.add_zero, Finset.sum_const_zero,
    zero_mul, Real.rpow_zero, mul_one, hrpow] using h

end ContinuousFlexibility.Analysis
