module

public import ContinuousFlexibility.Analysis.CircleJetBonding
public import ContinuousFlexibility.Analysis.CircleModelRealization
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Fixed derivative and weight losses in the actual circle norm

An angular derivative loss and a power of the sample weight occupy the
two components of `CircleJetIndex`. Shifting these components gives an
injection into one higher level. Consequently a uniform estimate for
the individual weighted jets controls the complete sum over all circles.
The finite-sum and infinite-sum arguments retain the actual norm from
`Statements.Analysis`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open MeasureTheory
open scoped BigOperators ENNReal ContDiff

/-- Shift angular order and sample-weight order by fixed amounts. -/
def circleJetShiftIndex (s d k : ℕ) : CircleJetIndex s ↪ CircleJetIndex (s + d + k) where
  toFun j := ⟨fun i =>
    ⟨(j.val i).val + if i = 0 then d else k, by
      have hi := (j.val i).isLt
      split_ifs <;> omega⟩, by
      simpa only [Fin.isValue, ↓reduceIte, show (1 : Fin 2) ≠ 0 from by decide] using
        (show (j.val 0).val + d + ((j.val 1).val + k) ≤ s + d + k by
          have hj := j.property
          omega)⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    funext t
    apply Fin.ext
    have h := congrArg (fun z : CircleJetIndex (s + d + k) => (z.val t).val) hij
    exact Nat.add_right_cancel h

@[simp] theorem circleJetShiftIndex_zero (s d k : ℕ) (j : CircleJetIndex s) :
    ((circleJetShiftIndex s d k j).val 0).val = (j.val 0).val + d := by
  simp only [circleJetShiftIndex, Function.Embedding.coeFn_mk, Fin.isValue, ↓reduceIte]

@[simp] theorem circleJetShiftIndex_one (s d k : ℕ) (j : CircleJetIndex s) :
    ((circleJetShiftIndex s d k j).val 1).val = (j.val 1).val + k := by
  simp only [circleJetShiftIndex, Function.Embedding.coeFn_mk, Fin.isValue,
    show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte]

/-- A bound on every weighted jet, with one common constant, controls
the actual complete energy sum. -/
theorem circleEnergy_le_of_jet_bound
    {T : MaterialData} {γ : ℝ} {u v : ℕ → ℝ → ℝ}
    (s d k : ℕ) (C : ℝ≥0∞)
    (hbound : ∀ m (j : CircleJetIndex s),
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2 ≤
      C * (ENNReal.ofReal ((T.M (T.sample m) ^ ((j.val 1).val + k) *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv ((j.val 0).val + d) (u m)) 2 angleMeasure ^ 2)) :
    (∑' m : ℕ, ∑ j : CircleJetIndex s,
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2) ≤
    C * (∑' m : ℕ, ∑ j : CircleJetIndex (s + d + k),
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (u m)) 2 angleMeasure ^ 2) := by
  classical
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro m
  let term (j : CircleJetIndex (s + d + k)) : ℝ≥0∞ :=
    ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
      T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv (j.val 0).val (u m)) 2 angleMeasure ^ 2
  calc
    _ ≤ ∑ j : CircleJetIndex s, C * term (circleJetShiftIndex s d k j) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [term, circleJetShiftIndex_zero, circleJetShiftIndex_one] using hbound m j
    _ = C * ∑ j : CircleJetIndex s, term (circleJetShiftIndex s d k j) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C * ∑ j : CircleJetIndex (s + d + k), term j := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      calc
        _ = ∑ j ∈ Finset.univ.map (circleJetShiftIndex s d k), term j := by
          rw [Finset.sum_map]
        _ ≤ ∑ j : CircleJetIndex (s + d + k), term j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => zero_le)

/-- The energy estimate also proves finiteness; this is required before
taking `toReal` or treating the field as an element of the model. -/
theorem circleMember_of_jet_bound
    {T : MaterialData} {γ : ℝ} {u v : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (d k : ℕ)
    (hv : ∀ m, ContDiff ℝ ∞ (v m) ∧ Function.Periodic (v m) Real.pi)
    (hvlp : ∀ m b, MemLp (iteratedDeriv b (v m)) 2 angleMeasure)
    (hbound : ∀ s, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ m (j : CircleJetIndex s),
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2 ≤
      C * (ENNReal.ofReal ((T.M (T.sample m) ^ ((j.val 1).val + k) *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv ((j.val 0).val + d) (u m)) 2 angleMeasure ^ 2)) :
    CircleMember T γ v := by
  refine ⟨hv, hvlp, ?_⟩
  intro s
  obtain ⟨C, hC, hCs⟩ := hbound s
  exact (circleEnergy_le_of_jet_bound s d k C hCs).trans_lt
    (ENNReal.mul_lt_top hC (hu.2.2 (s + d + k)))

/-- Passing through the square root gives the actual physical norm
estimate, with the same fixed increase in angular and weight orders. -/
theorem circleNorm_le_of_jet_bound
    {T : MaterialData} {γ : ℝ} {u v : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (s d k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ m (j : CircleJetIndex s),
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2 ≤
      ENNReal.ofReal (C ^ 2) *
        (ENNReal.ofReal ((T.M (T.sample m) ^ ((j.val 1).val + k) *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv ((j.val 0).val + d) (u m)) 2 angleMeasure ^ 2)) :
    circleNorm T γ s v ≤ C * circleNorm T γ (s + d + k) u := by
  have hb := circleEnergy_le_of_jet_bound s d k (ENNReal.ofReal (C ^ 2)) hbound
  have ht := ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := C ^ 2))
    (hu.2.2 (s + d + k))
  have hr := ENNReal.toReal_mono ht.ne hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg C)] at hr
  have hs := Real.sqrt_le_sqrt hr
  rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC] at hs
  exact hs

/-- A derivative estimate with a power of the actual sample weight gives
the weighted jet estimate used above. All constants remain independent of
the sample index. -/
theorem circleWeightedJet_le_of_derivative_bound
    {T : MaterialData} {γ : ℝ} {u v : ℕ → ℝ → ℝ}
    {s d k m : ℕ} (j : CircleJetIndex s) {C : ℝ} (hC : 0 ≤ C)
    (hM : 0 ≤ T.M (T.sample m)) (hH : 0 ≤ T.H (T.sample m))
    (hb : eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ≤
      ENNReal.ofReal (C * T.M (T.sample m) ^ k) *
        eLpNorm (iteratedDeriv ((j.val 0).val + d) (u m)) 2 angleMeasure) :
    ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
      T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2 ≤
    ENNReal.ofReal (C ^ 2) *
      (ENNReal.ofReal ((T.M (T.sample m) ^ ((j.val 1).val + k) *
      T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv ((j.val 0).val + d) (u m)) 2 angleMeasure ^ 2) := by
  have hCM : 0 ≤ C * T.M (T.sample m) ^ k := mul_nonneg hC (pow_nonneg hM k)
  have hcoeff :
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        ENNReal.ofReal (C * T.M (T.sample m) ^ k) ^ 2 =
      ENNReal.ofReal (C ^ 2) *
        ENNReal.ofReal ((T.M (T.sample m) ^ ((j.val 1).val + k) *
        T.H (T.sample m) ^ (-γ)) ^ 2) := by
    rw [← ENNReal.ofReal_pow hCM, ← ENNReal.ofReal_mul (sq_nonneg _),
      ← ENNReal.ofReal_mul (sq_nonneg C)]
    congr 1
    rw [pow_add]
    ring
  calc
    _ ≤ ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        (ENNReal.ofReal (C * T.M (T.sample m) ^ k) *
          eLpNorm (iteratedDeriv ((j.val 0).val + d) (u m)) 2 angleMeasure) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left' hb 2) zero_le
    _ = _ := by
      rw [mul_pow (ENNReal.ofReal (C * T.M (T.sample m) ^ k))
        (eLpNorm (iteratedDeriv ((j.val 0).val + d) (u m)) 2 angleMeasure) 2,
        ← mul_assoc, hcoeff, mul_assoc]

/-- Uniform derivative estimates with fixed losses produce an actual
weighted circle field, including finiteness of every complete norm sum. -/
theorem circleMember_of_L2_derivative_bound
    {T : MaterialData} {γ : ℝ} {u v : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (d k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (hv : ∀ m, ContDiff ℝ ∞ (v m) ∧ Function.Periodic (v m) Real.pi)
    (hb : ∀ m b, eLpNorm (iteratedDeriv b (v m)) 2 angleMeasure ≤
      ENNReal.ofReal (C * T.M (T.sample m) ^ k) *
        eLpNorm (iteratedDeriv (b + d) (u m)) 2 angleMeasure) :
    CircleMember T γ v := by
  apply circleMember_of_jet_bound hu d k hv
  · exact fun m b => memLp_angleMeasure_iteratedDeriv_of_contDiff (hv m).1 b
  · intro s
    exact ⟨ENNReal.ofReal (C ^ 2), ENNReal.ofReal_lt_top,
      fun m j => circleWeightedJet_le_of_derivative_bound j hC (hM m) (hH m) (hb m _)⟩

theorem circleNorm_le_of_L2_derivative_bound
    {T : MaterialData} {γ : ℝ} {u v : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (s d k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (hb : ∀ m b, eLpNorm (iteratedDeriv b (v m)) 2 angleMeasure ≤
      ENNReal.ofReal (C * T.M (T.sample m) ^ k) *
        eLpNorm (iteratedDeriv (b + d) (u m)) 2 angleMeasure) :
    circleNorm T γ s v ≤ C * circleNorm T γ (s + d + k) u := by
  apply circleNorm_le_of_jet_bound hu s d k hC
  exact fun m j => circleWeightedJet_le_of_derivative_bound j hC (hM m) (hH m) (hb m _)

end ContinuousFlexibility.Statements
