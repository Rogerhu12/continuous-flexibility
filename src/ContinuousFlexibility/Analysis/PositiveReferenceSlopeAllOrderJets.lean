import ContinuousFlexibility.Analysis.PositiveCutoffAllOrderJets
import ContinuousFlexibility.Analysis.PositiveReferenceLinearJetEnvelope
import ContinuousFlexibility.Analysis.PositiveReferenceCoordinate

/-!
# All orders of the same normalized reference coordinate

The endpoint slopes, fixed cutoffs and actual integral normalizer are
used without changing the coordinate or width. High endpoint jets stay
linear; the cutoff cost is a power of the supplied inverse-width bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

/-- The genuine normalized slope has global all-order bounds from the
same local endpoint data and the value of its actual normalizer. -/
theorem exists_positiveReferenceSlope_allOrder_jet_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {l r δ U M : ℝ},
      0 < δ → 1 ≤ U → δ⁻¹ ≤ U → 0 ≤ M →
      ∀ a : Bool → ℝ → ℝ,
        (∀ (side : Bool) x, x ∈ Metric.ball (if side then r else l) δ →
          ContDiffAt ℝ ∞ (a side) x) →
        (∀ (side : Bool) k, k ≤ N →
          ∀ x ∈ Metric.ball (if side then r else l) δ,
            |iteratedDeriv k (a side) x| ≤ M) →
        |positiveReferenceScale l r δ (a false) (a true)| ≤ M →
        ∀ k, k ≤ N → ∀ x : ℝ,
          |iteratedDeriv k (positiveReferenceSlope l r δ (a false) (a true)) x| ≤
            C * U ^ N * M := by
  obtain ⟨Ccut, hCcut, hcut⟩ := exists_positiveEndpointCutoff_mul_jet_envelope N
  obtain ⟨Cmid, hCmid, hmid⟩ := exists_positiveReferenceMiddleWeight_jet_bound N
  refine ⟨2 * Ccut + Cmid, by linarith only [hCcut, hCmid], ?_⟩
  intro l r δ U M hδ hU hδU hM a ha hjet hscale k hk x
  let μ := positiveReferenceScale l r δ (a false) (a true)
  let W : ℝ → ℝ := fun t =>
    1 - positiveEndpointCutoff l δ t - positiveEndpointCutoff r δ t
  have hW : ContDiff ℝ ∞ W :=
    (contDiff_const.sub (contDiff_positiveEndpointCutoff l δ)).sub
      (contDiff_positiveEndpointCutoff r δ)
  have hL : ContDiff ℝ ∞ (fun t => positiveEndpointCutoff l δ t * a false t) :=
    contDiff_positiveEndpointCutoff_mul hδ (ha false)
  have hR : ContDiff ℝ ∞ (fun t => positiveEndpointCutoff r δ t * a true t) :=
    contDiff_positiveEndpointCutoff_mul hδ (ha true)
  have hb (side : Bool) :
      |iteratedDeriv k (fun t =>
        positiveEndpointCutoff (if side then r else l) δ t * a side t) x| ≤
        Ccut * U ^ N * M :=
    hcut hδ hU hδU hM _ _ (ha side) (hjet side) k hk x
  have hWb : |iteratedDeriv k W x| ≤ Cmid * U ^ N :=
    hmid hU hδ hδU l r k hk x
  have hscaled : |μ * iteratedDeriv k W x| ≤ M * (Cmid * U ^ N) := by
    rw [abs_mul]
    exact mul_le_mul hscale hWb (abs_nonneg _) hM
  change |iteratedDeriv k (fun t =>
    positiveEndpointCutoff l δ t * a false t +
    positiveEndpointCutoff r δ t * a true t + μ * W t) x| ≤ _
  rw [iteratedDeriv_fun_add
      ((hL.add hR).contDiffAt.of_le (by simp))
      ((contDiff_const.mul hW).contDiffAt.of_le (by simp)),
    iteratedDeriv_fun_add (hL.contDiffAt.of_le (by simp))
      (hR.contDiffAt.of_le (by simp)), iteratedDeriv_const_mul_field]
  calc
    _ ≤ |iteratedDeriv k (fun t => positiveEndpointCutoff l δ t * a false t) x| +
        |iteratedDeriv k (fun t => positiveEndpointCutoff r δ t * a true t) x| +
        |μ * iteratedDeriv k W x| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Ccut * U ^ N * M + Ccut * U ^ N * M + M * (Cmid * U ^ N) :=
      add_le_add (add_le_add (hb false) (hb true)) hscaled
    _ = (2 * Ccut + Cmid) * U ^ N * M := by ring

/-- The same positive-order bounds apply to the actual integral
coordinate, by its exact derivative formula. -/
theorem exists_positiveReferenceCoordinate_allOrder_positiveJet_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {l r δ U M : ℝ},
      0 < δ → 1 ≤ U → δ⁻¹ ≤ U → 0 ≤ M →
      ∀ a : Bool → ℝ → ℝ,
        (∀ (side : Bool) x, x ∈ Metric.ball (if side then r else l) δ →
          ContDiffAt ℝ ∞ (a side) x) →
        (∀ (side : Bool) k, k ≤ N →
          ∀ x ∈ Metric.ball (if side then r else l) δ,
            |iteratedDeriv k (a side) x| ≤ M) →
        |positiveReferenceScale l r δ (a false) (a true)| ≤ M →
        ∀ k, k ≤ N → ∀ x : ℝ,
          |iteratedDeriv (k + 1)
            (positiveReferenceCoordinate l r δ (a false) (a true)) x| ≤
            C * U ^ N * M := by
  obtain ⟨C, hC, hb⟩ := exists_positiveReferenceSlope_allOrder_jet_envelope N
  refine ⟨C, hC, ?_⟩
  intro l r δ U M hδ hU hδU hM a ha hjet hscale k hk x
  have he : deriv (positiveReferenceCoordinate l r δ (a false) (a true)) =
      positiveReferenceSlope l r δ (a false) (a true) :=
    funext fun t => (hasDerivAt_positiveReferenceCoordinate hδ (ha false) (ha true) t).deriv
  rw [iteratedDeriv_succ', he]
  exact hb hδ hU hδU hM a ha hjet hscale k hk x

end ContinuousFlexibility.Analysis
