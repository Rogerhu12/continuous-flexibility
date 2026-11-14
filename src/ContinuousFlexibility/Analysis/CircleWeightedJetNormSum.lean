module

public import ContinuousFlexibility.Analysis.N01EndpointSplitNorm
public import ContinuousFlexibility.Analysis.CircleFiniteEnergyEnvelopes
public import ContinuousFlexibility.Analysis.CircleJetBonding

/-!
# The finite jet sum of the physical circle norm

The infinite component sum is retained inside each weighted jet norm.
Only the finite angular-material index set is estimated by a sum of
separate norms.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open scoped ENNReal BigOperators

theorem circleNorm_monotone_of_member
    {T : MaterialData} {γ : ℝ} {v : ℕ → ℝ → ℝ}
    (hv : CircleMember T γ v) {s t : ℕ} (hst : s ≤ t) :
    circleNorm T γ s v ≤ circleNorm T γ t v := by
  classical
  have henergy : (∑' m : ℕ, ∑ j : CircleJetIndex s,
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2) ≤
      (∑' m : ℕ, ∑ j : CircleJetIndex t,
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2) := by
    apply ENNReal.tsum_le_tsum
    intro m
    let term : CircleJetIndex t → ℝ≥0∞ := fun j =>
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2
    calc
      _ = ∑ j : CircleJetIndex s, term (circleJetIndexOfLE hst j) := by
        simp only [term, circleJetIndexOfLE_val]
      _ = ∑ j ∈ Finset.univ.map (circleJetIndexOfLE hst), term j := by rw [Finset.sum_map]
      _ ≤ ∑ j : CircleJetIndex t, term j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => zero_le)
  exact Real.sqrt_le_sqrt (ENNReal.toReal_mono (hv.2.2 t).ne henergy)

theorem circleNorm_le_sum_weightedJetNorm
    {T : MaterialData} {γ : ℝ} {v : ℕ → ℝ → ℝ}
    (hv : CircleMember T γ v) (s : ℕ) :
    circleNorm T γ s v ≤ ∑ j : CircleJetIndex s,
      circleWeightedJetNorm T γ (j.val 0).val (j.val 1).val v := by
  classical
  let e : ℕ → CircleJetIndex s → ℝ≥0∞ := fun m j =>
    ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
      T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2
  have hcomm : (∑' m : ℕ, ∑ j : CircleJetIndex s, e m j) =
      ∑ j : CircleJetIndex s, ∑' m : ℕ, e m j := by
    simpa only [tsum_fintype] using (ENNReal.tsum_comm (f := e))
  have hfinite : ∀ j : CircleJetIndex s, (∑' m : ℕ, e m j) < ⊤ := by
    intro j
    apply lt_of_le_of_lt _ (hv.2.2 s)
    apply ENNReal.tsum_le_tsum
    intro m
    exact Finset.single_le_sum (f := e m) (fun _ _ => zero_le) (Finset.mem_univ j)
  have h := finiteEnergyEnvelope_sqrt_le (fun _ : CircleJetIndex s => (1 : ℝ))
    (fun j : CircleJetIndex s => ∑' m : ℕ, e m j)
    (fun _ => zero_le_one) hfinite
  change Real.sqrt (∑' m : ℕ, ∑ j : CircleJetIndex s, e m j).toReal ≤ _
  rw [hcomm]
  simpa only [one_pow, ENNReal.ofReal_one, one_mul, circleWeightedJetNorm, e] using h

end ContinuousFlexibility.Statements
