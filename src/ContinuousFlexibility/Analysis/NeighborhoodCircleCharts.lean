import ContinuousFlexibility.Analysis.OneHighCircleInverseGeometry
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Actual inverses for the neighborhood circle charts

A continuous increasing lift of a circle map has a genuine inverse on the
real line. The odd part of a composition of two increasing lifts is again
an increasing lift. These facts construct the return and right-chart
inverses from their defining maps; no inverse is supplied as a hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function Set

private theorem circleLift_add_nat_mul {P : ℝ} {f : ℝ → ℝ}
    (hlift : ∀ x, f (x + P) = f x + P) (n : ℕ) (x : ℝ) :
    f (x + (n : ℝ) * P) = f x + (n : ℝ) * P := by
  induction n with
  | zero => simp only [Nat.cast_zero, zero_mul, add_zero]
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hlift, ih]
    ring

/-- Continuity and the positive lift law alone give surjectivity. -/
theorem circleLift_surjective {P : ℝ} {f : ℝ → ℝ}
    (hP : 0 < P) (hf : Continuous f)
    (hlift : ∀ x, f (x + P) = f x + P) : Surjective f := by
  intro y
  obtain ⟨n, hn⟩ := exists_nat_gt (|y - f 0| / P)
  have hlarge : |y - f 0| < (n : ℝ) * P := (div_lt_iff₀ hP).mp hn
  have hplus : f ((n : ℝ) * P) = f 0 + (n : ℝ) * P := by
    simpa only [zero_add] using circleLift_add_nat_mul hlift n 0
  have hminus : f (-((n : ℝ) * P)) = f 0 - (n : ℝ) * P := by
    have h := circleLift_add_nat_mul hlift n (-((n : ℝ) * P))
    rw [neg_add_cancel] at h
    linarith
  apply mem_range_of_exists_le_of_exists_ge hf
  · refine ⟨-((n : ℝ) * P), ?_⟩
    rw [hminus]
    have h := neg_abs_le (y - f 0)
    linarith
  · refine ⟨(n : ℝ) * P, ?_⟩
    rw [hplus]
    have h := le_abs_self (y - f 0)
    linarith

theorem circleLift_bijective {P : ℝ} {f : ℝ → ℝ}
    (hP : 0 < P) (hf : Continuous f) (hmono : StrictMono f)
    (hlift : ∀ x, f (x + P) = f x + P) : Bijective f :=
  ⟨hmono.injective, circleLift_surjective hP hf hlift⟩

theorem circleLift_invFun_strictMono {f : ℝ → ℝ}
    (hmono : StrictMono f) (hsurj : Surjective f) : StrictMono (invFun f) := by
  intro x y hxy
  by_contra! h
  have hle := hmono.monotone h
  rw [rightInverse_invFun hsurj, rightInverse_invFun hsurj] at hle
  exact (not_le_of_gt hxy) hle

/-- The chosen inverse is continuous and increasing, has both inverse
identities, and has the same lift period. -/
theorem circleLift_invFun_properties {P : ℝ} {f : ℝ → ℝ}
    (hP : 0 < P) (hf : Continuous f) (hmono : StrictMono f)
    (hlift : ∀ x, f (x + P) = f x + P) :
    Continuous (invFun f) ∧ StrictMono (invFun f) ∧
      (∀ x, f (invFun f x) = x) ∧ (∀ x, invFun f (f x) = x) ∧
      (∀ x, invFun f (x + P) = invFun f x + P) := by
  have hsurj := circleLift_surjective hP hf hlift
  have hmonoInv := circleLift_invFun_strictMono hmono hsurj
  have hright := rightInverse_invFun hsurj
  have hleft := leftInverse_invFun hmono.injective
  exact ⟨hmonoInv.monotone.continuous_of_surjective (invFun_surjective hmono.injective),
    hmonoInv, hright, hleft, circleInverse_lift hright hleft hlift⟩

/-- The travel subtraction used by the right chart cancels in its odd part. -/
def circleOddPart (f : ℝ → ℝ) (travel : ℝ) (θ : ℝ) : ℝ :=
  ((f θ - travel) - (f (-θ) - travel)) / 2

theorem circleOddPart_eq (f : ℝ → ℝ) (travel θ : ℝ) :
    circleOddPart f travel θ = (f θ - f (-θ)) / 2 := by
  unfold circleOddPart
  ring

theorem circleOddPart_odd (f : ℝ → ℝ) (travel θ : ℝ) :
    circleOddPart f travel (-θ) = -circleOddPart f travel θ := by
  simp only [circleOddPart, neg_neg]
  ring

theorem circleOddPart_continuous {f : ℝ → ℝ} (hf : Continuous f) (travel : ℝ) :
    Continuous (circleOddPart f travel) :=
  ((hf.sub continuous_const).sub
    ((hf.comp continuous_neg).sub continuous_const)).div_const 2

theorem circleOddPart_strictMono {f : ℝ → ℝ} (hf : StrictMono f) (travel : ℝ) :
    StrictMono (circleOddPart f travel) := by
  intro x y hxy
  have h₁ := hf hxy
  have h₂ := hf (neg_lt_neg hxy)
  dsimp only [circleOddPart]
  linarith

theorem circleOddPart_lift {P : ℝ} {f : ℝ → ℝ}
    (hlift : ∀ x, f (x + P) = f x + P) (travel x : ℝ) :
    circleOddPart f travel (x + P) = circleOddPart f travel x + P := by
  have hneg : f (-(x + P)) = f (-x) - P := by
    have h := hlift (-(x + P))
    have he : -(x + P) + P = -x := by ring
    rw [he] at h
    linarith
  simp only [circleOddPart, hlift, hneg]
  ring

/-- The right chart built from a left chart and an actual return map has
a genuine two-sided inverse. This statement uses only order and continuity. -/
theorem circleOddPart_comp_invFun_properties {P : ℝ} {hL ret : ℝ → ℝ}
    (hP : 0 < P) (hLc : Continuous hL) (hLm : StrictMono hL)
    (hLl : ∀ x, hL (x + P) = hL x + P)
    (hRc : Continuous ret) (hRm : StrictMono ret)
    (hRl : ∀ x, ret (x + P) = ret x + P) (travel : ℝ) :
    let hR := circleOddPart (hL ∘ invFun ret) travel
    Continuous hR ∧ StrictMono hR ∧
      (∀ θ, hR (θ + P) = hR θ + P) ∧ (∀ θ, hR (-θ) = -hR θ) ∧
      (∀ θ, hR (invFun hR θ) = θ) ∧ (∀ θ, invFun hR (hR θ) = θ) := by
  obtain ⟨hic, him, _, _, hil⟩ := circleLift_invFun_properties hP hRc hRm hRl
  have hfc : Continuous (hL ∘ invFun ret) := hLc.comp hic
  have hfm : StrictMono (hL ∘ invFun ret) := hLm.comp him
  have hfl (x : ℝ) : (hL ∘ invFun ret) (x + P) = (hL ∘ invFun ret) x + P := by
    simp only [Function.comp_apply, hil, hLl]
  have hRc' := circleOddPart_continuous hfc travel
  have hRm' := circleOddPart_strictMono hfm travel
  have hRl' := circleOddPart_lift hfl travel
  have hbij := circleLift_bijective hP hRc' hRm' hRl'
  exact ⟨hRc', hRm', hRl', circleOddPart_odd _ travel,
    rightInverse_invFun hbij.surjective, leftInverse_invFun hbij.injective⟩

end ContinuousFlexibility.Analysis
