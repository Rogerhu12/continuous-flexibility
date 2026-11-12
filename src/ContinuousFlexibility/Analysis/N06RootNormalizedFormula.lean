import ContinuousFlexibility.Analysis.N06RootFiniteFields
import ContinuousFlexibility.Analysis.N06FiniteJetDifference

/-!
# The root formula with its actual normalized denominator

Dividing the three even or odd height entries by the reference profile
replaces the flat denominator Q by Q/w. N01 bounds this denominator away
from zero uniformly over all roots. Consequently all finite derivatives
of this exact root formula have uniform bounds on bounded input packets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff Topology BigOperators

abbrev N06RootNormalizedCoordinates := Fin 6 → ℝ

def n06RootNormalizedQ (v : N06RootNormalizedCoordinates) : ℝ :=
  1 + v 5 * (v 1 + (1 + v 0 ^ 2) * v 4)

def n06RootNormalizedDiscriminant (v : N06RootNormalizedCoordinates) : ℝ :=
  (1 + v 0 ^ 2) * (1 - (v 5 * v 2) ^ 2) - (v 0 * (1 + v 5 * v 1)) ^ 2

def n06RootNormalizedFields (v : N06RootNormalizedCoordinates) : PolarPoint :=
  (-(1 + v 0 ^ 2) * v 5 * v 3 / n06RootNormalizedQ v,
    Real.sqrt (n06RootNormalizedDiscriminant v) / n06RootNormalizedQ v)

def n06NormalizeRootCoordinates (v : N06NuJetCoordinates) : N06RootNormalizedCoordinates :=
  ![v 1, (v 1)⁻¹ * v 5, v 7, (v 1)⁻¹ * v 8, (v 1)⁻¹ * v 9, v 10]

theorem n06RootNormalizedQ_contDiff : ContDiff ℝ ∞ n06RootNormalizedQ := by
  have hc (i : Fin 6) : ContDiff ℝ ∞ (fun v : N06RootNormalizedCoordinates => v i) :=
    contDiff_apply ℝ ℝ i
  exact contDiff_const.add ((hc 5).mul ((hc 1).add
    ((contDiff_const.add ((hc 0).pow 2)).mul (hc 4))))

theorem n06RootNormalizedDiscriminant_contDiff :
    ContDiff ℝ ∞ n06RootNormalizedDiscriminant := by
  have hc (i : Fin 6) : ContDiff ℝ ∞ (fun v : N06RootNormalizedCoordinates => v i) :=
    contDiff_apply ℝ ℝ i
  exact ((contDiff_const.add ((hc 0).pow 2)).mul
    (contDiff_const.sub (((hc 5).mul (hc 2)).pow 2))).sub
      (((hc 0).mul (contDiff_const.add ((hc 5).mul (hc 1)))).pow 2)

theorem n06RootNormalizedFields_contDiffAt {v : N06RootNormalizedCoordinates}
    (hQ : n06RootNormalizedQ v ≠ 0) (hD : 0 < n06RootNormalizedDiscriminant v) :
    ContDiffAt ℝ ∞ n06RootNormalizedFields v := by
  have hc (i : Fin 6) : ContDiffAt ℝ ∞
      (fun w : N06RootNormalizedCoordinates => w i) v :=
    (contDiff_apply ℝ ℝ i).contDiffAt
  have hE : ContDiffAt ℝ ∞ (fun w : N06RootNormalizedCoordinates => 1 + w 0 ^ 2) v :=
    contDiffAt_const.add ((hc 0).pow 2)
  exact (((hE.neg.mul (hc 5)).mul (hc 3)).div
    n06RootNormalizedQ_contDiff.contDiffAt hQ).prodMk
      ((n06RootNormalizedDiscriminant_contDiff.contDiffAt.sqrt hD.ne').div
        n06RootNormalizedQ_contDiff.contDiffAt hQ)

theorem n06RootNormalizedFields_parameter_zero {v : N06RootNormalizedCoordinates}
    (hq : v 5 = 0) : n06RootNormalizedFields v = (0, 1) := by
  have hQ : n06RootNormalizedQ v = 1 := by simp only [n06RootNormalizedQ, hq, zero_mul, add_zero]
  have hD : n06RootNormalizedDiscriminant v = 1 := by
    simp only [n06RootNormalizedDiscriminant, hq, zero_mul,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, mul_one, add_zero]
    ring
  rw [n06RootNormalizedFields, hQ, hD]
  simp only [hq, mul_zero, zero_mul, zero_div, Real.sqrt_one, div_one]

theorem n06_normalizeRoot_denominators {v : N06NuJetCoordinates} (hw : v 1 ≠ 0) :
    n06RootNormalizedQ (n06NormalizeRootCoordinates v) = n06RootFiniteQ v / v 1 ∧
      n06RootNormalizedDiscriminant (n06NormalizeRootCoordinates v) =
        n06RootFiniteDiscriminant v := by
  constructor
  · change 1 + v 10 * ((v 1)⁻¹ * v 5 + (1 + v 1 ^ 2) * ((v 1)⁻¹ * v 9)) =
      (v 1 + v 10 * (v 5 + (1 + v 1 ^ 2) * v 9)) / v 1
    field_simp [hw] <;> ring
  · change (1 + v 1 ^ 2) * (1 - (v 10 * v 7) ^ 2) -
      (v 1 * (1 + v 10 * ((v 1)⁻¹ * v 5))) ^ 2 =
        (1 + v 1 ^ 2) * (1 - (v 10 * v 7) ^ 2) - (v 1 + v 10 * v 5) ^ 2
    have he : v 1 * (1 + v 10 * ((v 1)⁻¹ * v 5)) = v 1 + v 10 * v 5 := by
      calc
        _ = v 1 + v 10 * (v 1 * (v 1)⁻¹) * v 5 := by ring
        _ = _ := by rw [mul_inv_cancel₀ hw, mul_one]
    rw [he]

theorem n06_normalizeRoot_fields {v : N06NuJetCoordinates} (hw : v 1 ≠ 0) :
    n06RootNormalizedFields (n06NormalizeRootCoordinates v) = n06RootFiniteFields v := by
  obtain ⟨hQ, hD⟩ := n06_normalizeRoot_denominators hw
  apply Prod.ext
  · change -(1 + v 1 ^ 2) * v 10 * ((v 1)⁻¹ * v 8) /
      n06RootNormalizedQ (n06NormalizeRootCoordinates v) =
        -(1 + v 1 ^ 2) * v 10 * v 8 / n06RootFiniteQ v
    rw [hQ]
    have he : -(1 + v 1 ^ 2) * v 10 * ((v 1)⁻¹ * v 8) =
        (-(1 + v 1 ^ 2) * v 10 * v 8) / v 1 := by
      rw [div_eq_mul_inv]
      ring
    rw [he, div_div_div_cancel_right₀ hw]
  · change Real.sqrt (n06RootNormalizedDiscriminant (n06NormalizeRootCoordinates v)) /
      n06RootNormalizedQ (n06NormalizeRootCoordinates v) =
        v 1 * Real.sqrt (n06RootFiniteDiscriminant v) / n06RootFiniteQ v
    rw [hQ, hD, div_div_eq_mul_div, mul_comm (Real.sqrt _) (v 1)]

theorem n06RootNormalizedFields_iteratedFDeriv_bound (B : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : N06RootNormalizedCoordinates,
      ‖v‖ ≤ B → (7 / 8 : ℝ) ≤ n06RootNormalizedQ v →
      (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant v →
        ‖iteratedFDeriv ℝ n n06RootNormalizedFields v‖ ≤ C := by
  let K : Set N06RootNormalizedCoordinates := Metric.closedBall 0 B ∩
    ({v | (7 / 8 : ℝ) ≤ n06RootNormalizedQ v} ∩
      {v | (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant v})
  have hK : IsCompact K := (isCompact_closedBall (0 : N06RootNormalizedCoordinates) B).inter_right
    ((isClosed_le continuous_const n06RootNormalizedQ_contDiff.continuous).inter
      (isClosed_le continuous_const n06RootNormalizedDiscriminant_contDiff.continuous))
  have hc : ContinuousOn (fun v => ‖iteratedFDeriv ℝ n n06RootNormalizedFields v‖) K := by
    intro v hv
    have hQ : 0 < n06RootNormalizedQ v := lt_of_lt_of_le (by norm_num) hv.2.1
    have hD : 0 < n06RootNormalizedDiscriminant v := lt_of_lt_of_le (by norm_num) hv.2.2
    exact ((n06RootNormalizedFields_contDiffAt hQ.ne' hD).continuousAt_iteratedFDeriv
      (by simp)).norm.continuousWithinAt
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hc).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro v hv hQ hD
  have hvK : v ∈ K := ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hv, hQ, hD⟩
  exact (hC ⟨v, hvK, rfl⟩).trans (le_max_left _ _)

theorem n06RootNormalizedFields_finite_derivative_bound (M : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, k ≤ n → ∀ v : N06RootNormalizedCoordinates,
      ‖v‖ ≤ M → (7 / 8 : ℝ) ≤ n06RootNormalizedQ v →
      (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant v →
        ‖iteratedFDeriv ℝ k n06RootNormalizedFields v‖ ≤ C := by
  classical
  have hchoices (i : Fin (n + 1)) := n06RootNormalizedFields_iteratedFDeriv_bound M i.val
  choose c hc hb using hchoices
  refine ⟨∑ i : Fin (n + 1), c i, Finset.sum_nonneg (fun i _ => hc i), ?_⟩
  intro k hk v hv hQ hD
  let i : Fin (n + 1) := ⟨k, by omega⟩
  exact (hb i v hv hQ hD).trans
    (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i))

theorem n06RootNormalizedFields_composition_difference_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ (u v : E → N06RootNormalizedCoordinates) (x : E) (δ : ℝ),
      ContDiffAt ℝ ∞ u x → ContDiffAt ℝ ∞ v x → 0 ≤ δ →
      (∀ k, k ≤ n → ‖iteratedFDeriv ℝ k u x‖ ≤ M) →
      (∀ k, k ≤ n → ‖iteratedFDeriv ℝ k v x‖ ≤ M) →
      (∀ k, k ≤ n → ‖iteratedFDeriv ℝ k u x - iteratedFDeriv ℝ k v x‖ ≤ δ) →
      (∀ w ∈ segment ℝ (v x) (u x),
        (7 / 8 : ℝ) ≤ n06RootNormalizedQ w ∧
          (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant w) →
      ‖iteratedFDeriv ℝ n (n06RootNormalizedFields ∘ u) x -
        iteratedFDeriv ℝ n (n06RootNormalizedFields ∘ v) x‖ ≤ Q * δ := by
  obtain ⟨C, hC, houter⟩ := n06RootNormalizedFields_finite_derivative_bound M (n + 1)
  refine ⟨n06CompositionDifferenceCost n C M,
    n06CompositionDifferenceCost_nonneg n hC hM, ?_⟩
  intro u v x δ hu hv hδ hU hV hUV hpositive
  have hu₀ : ‖u x‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using hU 0 (Nat.zero_le n)
  have hv₀ : ‖v x‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using hV 0 (Nat.zero_le n)
  have hdiff₀ : ‖u x - v x‖ ≤ δ := by
    have he := iteratedFDeriv_sub_apply
      (hu.of_le (by simp : (0 : ℕ∞ω) ≤ ∞))
      (hv.of_le (by simp : (0 : ℕ∞ω) ≤ ∞))
    have h := hUV 0 (Nat.zero_le n)
    rw [← he, norm_iteratedFDeriv_zero] at h
    exact h
  have hvalue : ∀ w ∈ segment ℝ (v x) (u x), ‖w‖ ≤ M := by
    intro w hw
    have hvB : v x ∈ Metric.closedBall (0 : N06RootNormalizedCoordinates) M := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hv₀
    have huB : u x ∈ Metric.closedBall (0 : N06RootNormalizedCoordinates) M := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hu₀
    have hwB := (convex_closedBall (0 : N06RootNormalizedCoordinates) M).segment_subset hvB huB hw
    simpa only [Metric.mem_closedBall, dist_zero_right] using hwB
  have hsmooth : ∀ w ∈ segment ℝ (v x) (u x),
      ContDiffAt ℝ ∞ n06RootNormalizedFields w := by
    intro w hw
    have hp := hpositive w hw
    exact n06RootNormalizedFields_contDiffAt
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hp.1).ne'
      (lt_of_lt_of_le (by norm_num) hp.2)
  have hΦu := hsmooth (u x) (right_mem_segment ℝ _ _)
  have hΦv := hsmooth (v x) (left_mem_segment ℝ _ _)
  have houterValue (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k n06RootNormalizedFields (u x)‖ ≤ C := by
    have hp := hpositive (u x) (right_mem_segment ℝ _ _)
    exact houter k (by omega) (u x) hu₀ hp.1 hp.2
  have houterDifference (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k n06RootNormalizedFields (u x) -
        iteratedFDeriv ℝ k n06RootNormalizedFields (v x)‖ ≤ C * δ := by
    have h := n06_iteratedFDeriv_difference_le_segment k hsmooth
      (fun w hw => houter (k + 1) (by omega) w (hvalue w hw)
        (hpositive w hw).1 (hpositive w hw).2)
    exact h.trans (mul_le_mul_of_nonneg_left hdiff₀ hC)
  exact n06_iteratedFDeriv_comp_difference_le n hΦu hΦv hu hv hC hM hδ
    houterValue houterDifference hU hV hUV

end ContinuousFlexibility.Analysis
