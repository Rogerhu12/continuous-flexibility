module

public import ContinuousFlexibility.Analysis.N01cMixedPowerComposition
public import ContinuousFlexibility.Analysis.N01cStateHeightJets

/-!
# Radial inputs for the coefficient algebra

An actual radial parameter tower with low-order bounds supplies the
distributed mixed-jet bound at any fixed interpolation base and loss.
The only angular jets are zero. The construction also adjoins a scalar
parameter through the genuine linear projection.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]

theorem radialLowJets_powerBounds
    (p : ℕ → Seminorm ℝ X) (center : X) (base loss : ℕ)
    {U : Set X} {I : Set ℝ} {H E : ℝ → ℝ}
    (hH : ∀ r ∈ I, 0 ≤ H r) (hE : ∀ r ∈ I, 1 ≤ E r)
    (f : X → ℝ → ℝ)
    (Jr : ∀ n r, r ∈ I → SmoothDirections univ (fun x => iteratedDeriv n (f x) r))
    (hraw : ∀ n k : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ r (hr : r ∈ I), ∀ x ∈ U, ∀ v : Fin k → X,
      (∀ i, p base (v i) ≤ 1) →
        ‖(Jr n r hr).D k x v‖ ≤ C * E r ^ A * parameterHeightWeight (H r) k) :
    MixedPowerBounds p center base loss U (I ×ˢ univ)
      (fun q => H q.1) (fun q => E q.1) (fun x q => f x q.1) := by
  classical
  intro K s
  choose c A hc hA hb using (fun i : Fin (s + 1) × Fin (K + 1) =>
    hraw i.1.val i.2.val)
  let C : ℝ := 1 + ∑ i : Fin (s + 1) × Fin (K + 1), c i
  let B : ℝ := ∑ i : Fin (s + 1) × Fin (K + 1), A i
  have hC : 1 ≤ C := by
    have hh : 0 ≤ ∑ i : Fin (s + 1) × Fin (K + 1), c i :=
      Finset.sum_nonneg (fun i _ => (hc i).le)
    dsimp only [C]
    linarith
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hA i)
  have hcC (i) : c i ≤ C :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hAB (i) : A i ≤ B :=
    Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
  refine ⟨C, B, hC, hB, ?_⟩
  intro k hk a b hab q hq J x hx hlow v hv R hR hhigh hvhigh
  have hW : 0 ≤ parameterHeightWeight (H q.1) k :=
    parameterHeightWeight_nonneg (hH q.1 hq.1) k
  have hRpow : 1 ≤ R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) :=
    Real.one_le_rpow hR (spatialOrder_fraction_nonneg (a + b) s)
  by_cases hb0 : b = 0
  · subst b
    let i : Fin (s + 1) × Fin (K + 1) :=
      (⟨a, by omega⟩, ⟨k, Nat.lt_succ_of_le hk⟩)
    let Jcan := (Jr a q.1 hq.1).restrict J.open_domain (subset_univ _)
    let Jrad : SmoothDirections U (fun y => iteratedDeriv a (f y) q.1) :=
      J.congr (fun y _ => by
        simp only [mixedDerivative_radialFunction, ite_true])
    have heq := HasProjectiveJetsOn.unique J.open_domain
      Jrad.hasProjectiveJetsOn Jcan.hasProjectiveJetsOn k x hx
    have hd : J.D k x v = (Jr a q.1 hq.1).D k x v :=
      congrArg (fun A : X [×k]→L[ℝ] ℝ => A v) heq
    rw [hd]
    have hbound := hb i q.1 hq.1 x hx v hv
    have henv : c i * E q.1 ^ A i ≤ C * E q.1 ^ B :=
      mul_le_mul (hcC i)
        (Real.rpow_le_rpow_of_exponent_le (hE q.1 hq.1) (hAB i))
        (Real.rpow_nonneg (zero_le_one.trans (hE q.1 hq.1)) _)
        (zero_le_one.trans hC)
    exact (hbound.trans (mul_le_mul_of_nonneg_right henv hW)).trans
      (le_mul_of_one_le_right
        (mul_nonneg (mul_nonneg (zero_le_one.trans hC)
          (Real.rpow_nonneg (zero_le_one.trans (hE q.1 hq.1)) _)) hW) hRpow)
  · let Jzero : SmoothDirections U (fun _ : X => (0 : ℝ)) :=
      J.congr (fun y _ => by
        simp only [mixedDerivative_radialFunction, if_neg hb0])
    have hz : J.D k x v = 0 := by
      by_cases hk0 : k = 0
      · subst k
        exact smoothDirections_D_zero_apply Jzero hx v
      · exact smoothDirections_D_constant Jzero (Nat.pos_of_ne_zero hk0) hx v
    rw [hz, norm_zero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (zero_le_one.trans hC)
        (Real.rpow_nonneg (zero_le_one.trans (hE q.1 hq.1)) _)) hW)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)

/-- The mixed towers of a radial field come from its genuine radial tower. -/
def radialMixedRegularity
    {U : Set X} {I : Set ℝ} (hU : IsOpen U)
    (f : X → ℝ → ℝ)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) I)
    (Jr : ∀ n r, r ∈ I → SmoothDirections univ (fun x => iteratedDeriv n (f x) r)) :
    MixedJetRegularity U (I ×ˢ univ) (fun x q => f x q.1) where
  spatial x hx := (hf x hx).comp contDiffOn_fst (fun _ hq => hq.1)
  parameter a b q hq := by
    by_cases hb : b = 0
    · subst b
      exact ((Jr a q.1 hq.1).restrict hU (subset_univ _)).congr (fun x _ => by
        simp only [mixedDerivative_radialFunction, ite_true])
    · exact (smoothDirections_constant hU (0 : ℝ)).congr (fun _ _ => by
        simp only [mixedDerivative_radialFunction, if_neg hb])

/-- The projected tower and its actual low-seminorm envelope. -/
theorem projectedRadialJets_powerBounds
    (p : ℕ → Seminorm ℝ X) (q : Seminorm ℝ Y)
    (center : X) (base loss : ℕ) {U : Set X} {I : Set ℝ} {H E : ℝ → ℝ}
    (hH : ∀ r ∈ I, 0 ≤ H r) (hE : ∀ r ∈ I, 1 ≤ E r)
    (L : X →L[ℝ] Y) (hL : ∀ v, q (L v) ≤ p base v)
    (f : Y → ℝ → ℝ)
    (Jr : ∀ n r, r ∈ I → SmoothDirections univ (fun y => iteratedDeriv n (f y) r))
    (hzero : ∀ n : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ r ∈ I, ∀ x ∈ U, ‖iteratedDeriv n (f (L x)) r‖ ≤ C * E r ^ A)
    (hpositive : ∀ n k : ℕ, 0 < k → ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ r (hr : r ∈ I), ∀ x ∈ U, ∀ v : Fin k → Y,
        ‖(Jr n r hr).D k (L x) v‖ ≤ C * E r ^ A * H r * ∏ i, q (v i)) :
    MixedPowerBounds p center base loss U (I ×ˢ univ)
      (fun t => H t.1) (fun t => E t.1) (fun x t => f (L x) t.1) := by
  let Jjoint n r hr := smoothDirections_precompCLM (Jr n r hr) L
  apply radialLowJets_powerBounds p center base loss hH hE (fun x => f (L x)) Jjoint
  intro n k
  by_cases hk : k = 0
  · subst k
    obtain ⟨C, A, hC, hA, hb⟩ := hzero n
    refine ⟨C, A, hC, hA, fun r hr x hx v hv => ?_⟩
    simpa only [smoothDirections_D_zero_apply (Jjoint n r hr) (mem_univ x),
      parameterHeightWeight, ite_true, mul_one, Function.comp_def] using hb r hr x hx
  · obtain ⟨C, A, hC, hA, hb⟩ := hpositive n k (Nat.pos_of_ne_zero hk)
    refine ⟨C, A, hC, hA, fun r hr x hx v hv => ?_⟩
    have hprod : (∏ i, q (L (v i))) ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => apply_nonneg _ _) (fun i _ => (hL _).trans (hv i))
    have hweight : 0 ≤ C * E r ^ A * H r :=
      mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans (hE r hr)) _))
        (hH r hr)
    have hh := (hb r hr x hx (fun i => L (v i))).trans
      (mul_le_mul_of_nonneg_left hprod hweight)
    simpa only [Jjoint, smoothDirections_precompCLM_D_apply,
      parameterHeightWeight, if_neg hk, mul_one] using hh

end ContinuousFlexibility.Analysis
