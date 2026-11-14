module

public import ContinuousFlexibility.Analysis.MaterialCoordinateParameterDerivatives
public import ContinuousFlexibility.Analysis.N01cMixedPowerBounds
public import ContinuousFlexibility.Analysis.N01cFiniteParameterProducts

/-!
# Genuine mixed towers under the fixed radial reference inverse

The existing radial chain coefficients work on an arbitrary open radial
domain. Their coefficients depend only on the fixed map, so the exact
spatial formula identifies every genuine parameter derivative by a
finite scalar linear combination on the original parameter set.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

/-- Localize the existing radial chain-coefficient formula to the true
open domain of a fixed radial map. No extension of the outer field is
evaluated away from that domain. -/
theorem n04Realization_mixedDerivative_comp_fixedRadial
    {I : Set ℝ} {Ω : Set PolarPoint} {χ : ℝ → ℝ} {f : PolarPoint → ℝ}
    (hI : IsOpen I) (hΩ : IsOpen Ω) (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiffOn ℝ ∞ f Ω)
    (hmap : ∀ r ∈ I, ∀ θ : ℝ, (χ r, θ) ∈ Ω)
    (a b : ℕ) {p : PolarPoint} (hp : p.1 ∈ I) :
    mixedDerivative a b (fun q => f (χ q.1, q.2)) p =
      ∑ i : Fin (a + 1), radialChainCoefficient χ a i p.1 *
        mixedDerivative i.val b f (χ p.1, p.2) := by
  induction a generalizing p with
  | zero =>
      change iteratedDeriv b (fun θ => f (χ p.1, θ)) p.2 =
        ∑ i : Fin 1, radialChainCoefficient χ 0 i p.1 *
          mixedDerivative i.val b f (χ p.1, p.2)
      rw [Fin.sum_univ_one]
      simp only [Fin.val_zero, radialChainCoefficient, one_mul,
        mixedDerivative, iteratedDeriv_zero]
  | succ a ih =>
      have heq : (fun r => mixedDerivative a b (fun q => f (χ q.1, q.2)) (r, p.2))
          =ᶠ[𝓝 p.1] (fun r => ∑ i : Fin (a + 1), radialChainCoefficient χ a i r *
            mixedDerivative i.val b f (χ r, p.2)) := by
        filter_upwards [hI.mem_nhds hp] with r hr
        exact ih (p := (r, p.2)) hr
      have hc (i : Fin (a + 1)) :
          HasDerivAt (radialChainCoefficient χ a i)
            (deriv (radialChainCoefficient χ a i) p.1) p.1 :=
        ((radialChainCoefficient_contDiff hχ a i).differentiable (by simp) p.1).hasDerivAt
      have hm (i : Fin (a + 1)) :
          HasDerivAt (fun r => mixedDerivative i.val b f (χ r, p.2))
            (mixedDerivative (i.val + 1) b f (χ p.1, p.2) * deriv χ p.1) p.1 := by
        exact (mixedDerivative_hasDerivAt_radial hΩ hf i.val b (hmap p.1 hp p.2)).comp p.1
          ((hχ.differentiable (by simp) p.1).hasDerivAt)
      have hd := HasDerivAt.fun_sum
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin (a + 1)))) => (hc i).mul (hm i))
      have hderiv : deriv
          (fun r => ∑ i : Fin (a + 1), radialChainCoefficient χ a i r *
            mixedDerivative i.val b f (χ r, p.2)) p.1 =
          ∑ i : Fin (a + 1),
            (deriv (radialChainCoefficient χ a i) p.1 * mixedDerivative i.val b f (χ p.1, p.2) +
              radialChainCoefficient χ a i p.1 *
                (mixedDerivative (i.val + 1) b f (χ p.1, p.2) * deriv χ p.1)) := hd.deriv
      have hsucc : mixedDerivative (a + 1) b (fun q => f (χ q.1, q.2)) p =
          deriv (fun r => mixedDerivative a b (fun q => f (χ q.1, q.2)) (r, p.2)) p.1 := by
        simp only [mixedDerivative, iteratedDeriv_succ]
      rw [hsucc, heq.deriv_eq, hderiv,
        radialChainCoefficient_sum_succ χ a p.1 (fun j => mixedDerivative j b f (χ p.1, p.2)),
        Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {U : Set X} {I : Set ℝ} {Ω : Set PolarPoint}
  {χ : ℝ → ℝ} {f : X → PolarPoint → ℝ}

/-- A fixed radial reference map acts on the actual mixed tower without
requiring joint spatial continuity of its higher parameter jets. -/
def n04Realization_mixedJetRegularity_fixedRadial
    (hU : IsOpen U) (hI : IsOpen I) (hΩ : IsOpen Ω) (hχ : ContDiff ℝ ∞ χ)
    (RF : MixedJetRegularity U Ω f)
    (hmap : ∀ r ∈ I, ∀ θ : ℝ, (χ r, θ) ∈ Ω) :
    MixedJetRegularity U (I ×ˢ (univ : Set ℝ)) (fun x q => f x (χ q.1, q.2)) where
  spatial x hx := (RF.spatial x hx).comp
    ((hχ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
    (fun q hq => hmap q.1 hq.1 q.2)
  parameter a b q hq := by
    let J : ∀ i : Fin (a + 1), SmoothDirections U (fun x =>
        radialChainCoefficient χ a i q.1 * mixedDerivative i.val b (f x) (χ q.1, q.2)) :=
      fun i => (smoothDirections_postcompCLM
        (RF.parameter i.val b (χ q.1, q.2) (hmap q.1 hq.1 q.2))
        (radialChainCoefficient χ a i q.1 • ContinuousLinearMap.id ℝ ℝ)).congr
          (fun _ _ => by
            simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul])
    exact (smoothDirections_finiteSum hU J).congr (fun x hx =>
      (n04Realization_mixedDerivative_comp_fixedRadial hI hΩ hχ
        (RF.spatial x hx) hmap a b hq.1).symm)

/-- Fixed-map chain coefficients commute with every genuine parameter
jet by uniqueness of the finite scalar linear-combination tower. -/
theorem n04Realization_fixedRadial_parameterJet_formula
    (hI : IsOpen I) (hΩ : IsOpen Ω) (hχ : ContDiff ℝ ∞ χ)
    (RF : MixedJetRegularity U Ω f)
    (hmap : ∀ r ∈ I, ∀ θ : ℝ, (χ r, θ) ∈ Ω)
    (a b : ℕ) {q : PolarPoint} (hq : q ∈ I ×ˢ (univ : Set ℝ))
    (J : SmoothDirections U (fun x => mixedDerivative a b (fun p => f x (χ p.1, p.2)) q))
    (k : ℕ) {x : X} (hx : x ∈ U) (v : Fin k → X) :
    J.D k x v = ∑ i : Fin (a + 1), radialChainCoefficient χ a i q.1 *
      ((RF.parameter i.val b (χ q.1, q.2) (hmap q.1 hq.1 q.2)).D k x v) :=
  smoothDirections_D_eq_linearCombination J
    (fun i => RF.parameter i.val b (χ q.1, q.2) (hmap q.1 hq.1 q.2))
    (fun i => radialChainCoefficient χ a i q.1)
    (fun y hy => n04Realization_mixedDerivative_comp_fixedRadial hI hΩ hχ
      (RF.spatial y hy) hmap a b hq.1) k hx v

/-- The fixed pullback retains the original spatial-power budget and
every external material/parameter weight in `M`. Only its explicit
fixed chain-coefficient mass is added. -/
theorem n04Realization_fixedRadial_parameterJet_bound
    (hI : IsOpen I) (hΩ : IsOpen Ω) (hχ : ContDiff ℝ ∞ χ)
    (RF : MixedJetRegularity U Ω f)
    (hmap : ∀ r ∈ I, ∀ θ : ℝ, (χ r, θ) ∈ Ω)
    (a b s k : ℕ) {q : PolarPoint} (hq : q ∈ I ×ˢ (univ : Set ℝ))
    (J : SmoothDirections U (fun x => mixedDerivative a b (fun p => f x (χ p.1, p.2)) q))
    {x : X} (hx : x ∈ U) (v : Fin k → X) {M R : ℝ} (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hbound : ∀ i : Fin (a + 1),
      |((RF.parameter i.val b (χ q.1, q.2) (hmap q.1 hq.1 q.2)).D k x v)| ≤
        M * R ^ (((i.val + b : ℕ) : ℝ) / ((s : ℝ) + 1))) :
    |J.D k x v| ≤ (∑ i : Fin (a + 1), |radialChainCoefficient χ a i q.1|) *
      M * R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  rw [n04Realization_fixedRadial_parameterJet_formula hI hΩ hχ RF hmap a b hq J k hx v]
  have hterm (i : Fin (a + 1)) :
      |((RF.parameter i.val b (χ q.1, q.2) (hmap q.1 hq.1 q.2)).D k x v)| ≤
        M * R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
    have horder : (((i.val + b : ℕ) : ℝ) / ((s : ℝ) + 1)) ≤
        (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt_succ i.isLt) b
    exact (hbound i).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR horder) hM)
  calc
    _ ≤ ∑ i : Fin (a + 1), |radialChainCoefficient χ a i q.1| *
        |((RF.parameter i.val b (χ q.1, q.2) (hmap q.1 hq.1 q.2)).D k x v)| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun i : Fin (a + 1) => radialChainCoefficient χ a i q.1 *
          ((RF.parameter i.val b (χ q.1, q.2) (hmap q.1 hq.1 q.2)).D k x v)) Finset.univ
    _ ≤ ∑ i : Fin (a + 1), |radialChainCoefficient χ a i q.1| *
        (M * R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hterm i) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

end ContinuousFlexibility.Analysis
