import ContinuousFlexibility.Analysis.N04RealizationCubicOneHighBounds
import ContinuousFlexibility.Statements.Nonlinear

/-!
# Value estimates for the actual cubic quotient

The open-strip numerator bound extends to the two endpoints through its
smooth representative. Two cubic factors cost six radial orders and do
not change the fixed external weight or the parameter seminorm.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

/-- An open-strip bound suffices: the smooth representative extends the
bound to the endpoints by continuity. -/
theorem n04PrincipalDivided_value_of_representative
    {N e : PolarPoint → ℝ}
    (hrep : ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧ EqOn F N unitStrip ∧
      ∀ c : Bool, ∀ θ i, i ≤ 2 →
        iteratedDeriv i (fun t : ℝ => F (t, θ)) (if c then 1 else 0) = 0)
    (hfactor : ∀ q ∈ unitStrip, N q = (q.1 * (1 - q.1)) ^ 3 * e q)
    (a b : ℕ) {M : ℝ}
    (hbound : ∀ q ∈ unitStrip, |mixedDerivative (a + 6) b N q| ≤ M)
    {q : PolarPoint} (hq : q ∈ unitStrip) :
    |mixedDerivative a b e q| ≤ M / 36 := by
  rcases hrep with ⟨F, hF, he, hz⟩
  have hc : Continuous (fun t : ℝ => |mixedDerivative (a + 6) b F (t, q.2)|) :=
    ((contDiff_mixedDerivative hF (a + 6) b).continuous.comp
      (continuous_id.prodMk continuous_const)).abs
  have hclosed : IsClosed {t : ℝ | |mixedDerivative (a + 6) b F (t, q.2)| ≤ M} :=
    isClosed_le hc continuous_const
  have hinner : Ioo (0 : ℝ) 1 ⊆
      {t : ℝ | |mixedDerivative (a + 6) b F (t, q.2)| ≤ M} := by
    intro t ht
    have heq := mixedDerivative_eq_of_eqOn_radialCylinder
      (fun r hr θ => @he (r, θ) ⟨hr, mem_univ _⟩) (a + 6) b (p := (t, q.2)) ht
    change |mixedDerivative (a + 6) b F (t, q.2)| ≤ M
    rw [heq]
    exact hbound (t, q.2) ⟨ht, mem_univ _⟩
  have hboundary : Icc (0 : ℝ) 1 ⊆
      {t : ℝ | |mixedDerivative (a + 6) b F (t, q.2)| ≤ M} := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact hclosed.closure_subset_iff.mpr hinner
  apply abs_mixedDerivative_of_twoEndpointCubicFactorization hF zero_lt_one
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using hz false)
    (by simpa only [↓reduceIte] using hz true)
    (fun p hp => ?_) a b (fun t ht => hboundary ht) hq.1
  have hp' : p ∈ unitStrip := ⟨hp, mem_univ _⟩
  simpa only [sub_zero] using (he hp').trans (hfactor p hp')

theorem n04PrincipalDivided_valueBounds
    {X ι : Type*} {U : Set X} (p : ℕ → X → ℝ) (hp : ∀ n x, 0 ≤ p n x)
    (E H : ι → ℝ) (hE : ∀ m, 0 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    (P : ι → Prop) (N g : X → ι → PolarPoint → ℝ)
    (hvalue : ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ U, ∀ m, P m → ∀ q : unitStrip, ∀ a b, a + b ≤ s →
        |mixedDerivative a b (N z m) q.val| ≤ B * E m ^ B * H m * p (s + loss) z)
    (hrep : ∀ m, P m → ∀ z ∈ U,
      ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧ EqOn F (N z m) unitStrip ∧
        ∀ side : Bool, ∀ θ i, i ≤ 2 →
          iteratedDeriv i (fun t : ℝ => F (t, θ)) (if side then 1 else 0) = 0)
    (hfactor : ∀ m, P m → ∀ z ∈ U, ∀ q ∈ unitStrip,
      N z m q = (q.1 * (1 - q.1)) ^ 3 * g z m q)
    (hnegative : ∀ m, ¬ P m → ∀ z ∈ U, ∀ q : unitStrip, ∀ a b,
      mixedDerivative a b (fun y => g z m y - 0) q.val = 0) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ U, ∀ m, True → ∀ q : unitStrip, ∀ a b, a + b ≤ s →
        |mixedDerivative a b (fun y => g z m y - 0) q.val| ≤
          B * E m ^ B * H m * p (s + loss) z := by
  classical
  obtain ⟨loss, hloss⟩ := hvalue
  refine ⟨loss + 6, fun s => ?_⟩
  obtain ⟨B, hB, hb⟩ := hloss (s + 6)
  refine ⟨B, hB, ?_⟩
  intro z hz m _ q a b hab
  let M := B * E m ^ B * H m * p (s + (loss + 6)) z
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg (hE m) _)) (hH m)) (hp _ _)
  by_cases hm : P m
  · have hb' : ∀ t ∈ unitStrip, |mixedDerivative (a + 6) b (N z m) t| ≤ M := by
      intro t ht
      have he : s + 6 + loss = s + (loss + 6) := by omega
      simpa only [M, he] using hb z hz m hm ⟨t, ht⟩ (a + 6) b (by omega)
    have hquot := n04PrincipalDivided_value_of_representative
      (hrep m hm z hz) (hfactor m hm z hz) a b hb' q.property
    have hbM : |mixedDerivative a b (g z m) q.val| ≤ M :=
      hquot.trans (div_le_self hM (by norm_num))
    exact (le_of_eq (congrArg (fun F => |mixedDerivative a b F q.val|)
      (funext fun y => sub_zero (g z m y)))).trans hbM
  · rw [hnegative m hm z hz q a b, abs_zero]
    exact hM

end ContinuousFlexibility.Analysis
