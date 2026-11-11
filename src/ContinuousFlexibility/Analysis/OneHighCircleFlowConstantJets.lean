import ContinuousFlexibility.Analysis.OneHighCircleFlowIntegrableMinkowski

/-!
# Subtracting an angle-independent reference from actual circle jets

Only the zeroth angular jet changes. This operation agrees exactly with
the canonical jets of the difference of the real lifts. Its elementary
supremum bound will establish time integrability even when the reference
speed is only integrable.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

variable {P : ℝ} [Fact (0 < P)]

def circleSubtractConstantJet (f : ℕ → C(AddCircle P, ℝ))
    (c : ℝ) (n : ℕ) : C(AddCircle P, ℝ) :=
  f n - if n = 0 then ContinuousMap.const (AddCircle P) c else 0

@[simp] theorem circleSubtractConstantJet_apply (f : ℕ → C(AddCircle P, ℝ))
    (c : ℝ) (n : ℕ) (x : AddCircle P) :
    circleSubtractConstantJet f c n x = f n x - if n = 0 then c else 0 := by
  by_cases hn : n = 0
  · simp only [circleSubtractConstantJet, if_pos hn,
      ContinuousMap.sub_apply, ContinuousMap.const_apply]
  · simp only [circleSubtractConstantJet, if_neg hn,
      ContinuousMap.sub_apply, ContinuousMap.zero_apply]

theorem circleSubtractConstantJet_hasDerivAt
    (f : ℕ → C(AddCircle P, ℝ))
    (hf : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (c : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => circleSubtractConstantJet f c n (y : AddCircle P))
      (circleSubtractConstantJet f c (n + 1) (x : AddCircle P)) x := by
  simp only [circleSubtractConstantJet_apply, if_neg (Nat.succ_ne_zero n), sub_zero]
  exact (hf n x).sub_const (if n = 0 then c else 0)

theorem circle_periodic_sub_const {v : ℝ → ℝ}
    (hp : Function.Periodic v P) (c : ℝ) :
    Function.Periodic (fun x => v x - c) P := by
  intro x
  exact congrArg (fun z : ℝ => z - c) (hp x)

/-- The operation is exactly the canonical circle jet of the actual
difference of the smooth real lift and a constant. -/
theorem periodicCircleJet_sub_const (v : ℝ → ℝ)
    (hp : Function.Periodic v P) (hv : ContDiff ℝ ∞ v) (c : ℝ) (n : ℕ) :
    circleSubtractConstantJet (periodicCircleJet v hp hv) c n =
      periodicCircleJet (fun x => v x - c)
        (circle_periodic_sub_const hp c) (hv.sub contDiff_const) n := by
  ext x
  induction x using QuotientAddGroup.induction_on
  rename_i x
  rw [circleSubtractConstantJet_apply, periodicCircleJet_coe_apply v hp hv n x,
    periodicCircleJet_coe_apply (fun x => v x - c)
      (circle_periodic_sub_const hp c) (hv.sub contDiff_const) n x]
  have hsub : iteratedDeriv n (fun y => v y - c) x =
      iteratedDeriv n v x - iteratedDeriv n (fun _ : ℝ => c) x :=
    iteratedDeriv_fun_sub (n := n) (hv.contDiffAt.of_le (by simp)) contDiffAt_const
  simpa only [iteratedDeriv_const] using hsub.symm

theorem circleSubtractConstantJet_norm_le (f : ℕ → C(AddCircle P, ℝ))
    (c : ℝ) (n : ℕ) :
    ‖circleSubtractConstantJet f c n‖ ≤ ‖f n‖ + |c| := by
  apply ((circleSubtractConstantJet f c n).norm_le
    (add_nonneg (norm_nonneg _) (abs_nonneg c))).mpr
  intro x
  rw [circleSubtractConstantJet_apply]
  have hc : ‖(if n = 0 then c else 0 : ℝ)‖ ≤ |c| := by
    by_cases hn : n = 0
    · simpa only [if_pos hn, Real.norm_eq_abs] using (le_rfl : |c| ≤ |c|)
    · simp only [if_neg hn, norm_zero]
      exact abs_nonneg c
  exact (norm_sub_le _ _).trans (add_le_add ((f n).norm_coe_le_norm x) hc)

theorem circleSubtractConstantJet_sobolev_le (f : ℕ → C(AddCircle P, ℝ))
    (hf : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (c : ℝ) (s : ℕ) :
    circleRealSobolevNorm (s : ℝ) (circleSubtractConstantJet f c 0) ≤
      (2 : ℝ) ^ s * (‖f 0‖ + ‖f s‖ + 2 * |c|) := by
  have hz := (circle_l2_le_supNorm _).trans (circleSubtractConstantJet_norm_le f c 0)
  have hs := (circle_l2_le_supNorm _).trans (circleSubtractConstantJet_norm_le f c s)
  calc
    _ ≤ (2 : ℝ) ^ s *
        ((eLpNorm (circleSubtractConstantJet f c 0) 2 AddCircle.haarAddCircle).toReal +
          (eLpNorm (circleSubtractConstantJet f c s) 2 AddCircle.haarAddCircle).toReal) :=
      circle_real_sobolevNorm_le_derivative_endpoints
        (circleSubtractConstantJet f c) (circleSubtractConstantJet_hasDerivAt f hf c) s
    _ ≤ (2 : ℝ) ^ s * ((‖f 0‖ + |c|) + (‖f s‖ + |c|)) :=
      mul_le_mul_of_nonneg_left (add_le_add hz hs) (by positivity)
    _ = _ := by ring

theorem continuous_circleSubtractConstantJet
    {X : Type*} [TopologicalSpace X] (f : X → ℕ → C(AddCircle P, ℝ)) (c : X → ℝ)
    (hf : ∀ n, Continuous (fun x => f x n)) (hc : Continuous c) (n : ℕ) :
    Continuous (fun x => circleSubtractConstantJet (f x) (c x) n) := by
  let L : ℝ →L[ℝ] C(AddCircle P, ℝ) := ContinuousLinearMap.const ℝ (AddCircle P)
  have hconst : Continuous (fun x => ContinuousMap.const (AddCircle P) (c x)) :=
    L.continuous.comp hc
  by_cases hn : n = 0
  · simpa only [circleSubtractConstantJet, if_pos hn, Pi.sub_def] using (hf n).sub hconst
  · simpa only [circleSubtractConstantJet, if_neg hn, sub_zero] using hf n

theorem continuous_circleSubtractConstantSobolevNorm
    {X : Type*} [TopologicalSpace X] (f : X → ℕ → C(AddCircle P, ℝ)) (c : X → ℝ)
    (hf : ∀ n, Continuous (fun x => f x n))
    (hderiv : ∀ x : X, ∀ n : ℕ, ∀ θ : ℝ,
      HasDerivAt (fun η : ℝ => f x n (η : AddCircle P))
        (f x (n + 1) (θ : AddCircle P)) θ)
    (hc : Continuous c) (s : ℕ) :
    Continuous (fun x => circleRealSobolevNorm (s : ℝ)
      (circleSubtractConstantJet (f x) (c x) 0)) :=
  continuous_circleRealSobolevNorm_of_derivatives
    (fun x => circleSubtractConstantJet (f x) (c x))
    (fun x => circleSubtractConstantJet_hasDerivAt (f x) (hderiv x) (c x)) s
    (continuous_circleSubtractConstantJet f c hf hc 0)
    (continuous_circleSubtractConstantJet f c hf hc s)

end ContinuousFlexibility.Analysis
