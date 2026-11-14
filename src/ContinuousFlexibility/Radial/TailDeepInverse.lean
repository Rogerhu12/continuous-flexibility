module

public import ContinuousFlexibility.Radial.TailActualLowProjection
public import ContinuousFlexibility.Radial.TailFormIdentification
public import ContinuousFlexibility.Radial.TailInverseTruncation
public import ContinuousFlexibility.Blueprint.Statements

/-!
# The deep-tail Friedrichs inverse and its Dirichlet limits

The actual low-mode projection satisfies the two half-energy estimates when
`η ≤ 1/10` and `10 Cstep + 2 ≤ K`. Reflection then constructs the bounded
inverse with norm at most `4 / Λ` on the whole tail and every node truncation.
The source restrictions and strong convergence are those of the frozen
operator statement, in its actual weighted `L²` space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem tail_low_half_energy (T : DeepTailData) (hT : DeepTailHypotheses T)
    (hK : 10 * tailSmoothStepConstant + 2 ≤ T.K) (cut : ℝ)
    (u : tailGradientSpace T cut) :
    ‖tailFormGradient T cut (tailActualLowProjection T hT cut u)‖ ^ 2 ≤
      (T.Λ / 2) * ‖tailFormBase T cut (tailActualLowProjection T hT cut u)‖ ^ 2 := by
  have hΛ : 0 < T.Λ := hT.2.2.1
  have hKpos : 0 < T.K := lt_trans zero_lt_one hT.2.2.2.2.2.2.1
  have hcoef : 5 * tailSmoothStepConstant * T.Λ / T.K ≤ T.Λ / 2 := by
    apply (div_le_iff₀ hKpos).mpr
    have h := mul_le_mul_of_nonneg_left hK hΛ.le
    nlinarith
  exact (tailActualLowProjection_low_energy T hT cut u).trans
    (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))

theorem tail_high_half_energy (T : DeepTailData) (hT : DeepTailHypotheses T)
    (hη : T.η ≤ 1 / 10) (cut : ℝ) (hcut : TailAdmissibleCut T cut)
    (u : tailGradientSpace T cut) :
    T.Λ * ‖tailFormBase T cut (u - tailActualLowProjection T hT cut u)‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖tailFormGradient T cut (u - tailActualLowProjection T hT cut u)‖ ^ 2 :=
  (tailActualLowProjection_high_energy T hT cut hcut u).trans
    (mul_le_mul_of_nonneg_right (by linarith : 5 * T.η ≤ (1 / 2 : ℝ)) (sq_nonneg _))

/-- Uniform inverse construction on the endpoint and all finite node walls. -/
theorem exists_tailDeepInverse (T : DeepTailData) (hT : DeepTailHypotheses T)
    (hη : T.η ≤ 1 / 10) (hK : 10 * tailSmoothStepConstant + 2 ≤ T.K)
    (cut : ℝ) (hcut : TailAdmissibleCut T cut) :
    ∃ G : DeepTailL2 T →L[ℝ] DeepTailL2 T,
      ‖G‖ ≤ 4 / T.Λ ∧
      (∀ f, TailFriedrichsGraph T cut (G f) (f + T.Λ • G f)) ∧
      (∀ u f, TailFriedrichsGraph T cut u (f + T.Λ • u) → G f = u) :=
  exists_tailInverse_of_lowModeProjection T cut hT.2.2.1
    (tailActualLowProjection T hT cut) (tailActualLowProjection_idempotent T hT cut)
    (tail_low_half_energy T hT hK cut) (tail_high_half_energy T hT hη cut hcut)

/-- All clauses of the deep-tail operator statement, with fixed universal
constants and no relative form or inverse hypothesis. -/
theorem deepTail_operator :
    ContinuousFlexibility.Blueprint.R06Operator 4 (1 / 10)
      (10 * tailSmoothStepConstant + 2) := by
  intro T hT hη hK
  have hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint) :=
    (deepTail_contDiffOn hT).mono Ioo_subset_Ico_self
  have hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x :=
    fun x hx => deepTail_pos hT x (Ioo_subset_Ico_self hx)
  obtain ⟨G, hGb, hGe, hGu⟩ := exists_tailDeepInverse T hT hη hK T.endpoint (Or.inl rfl)
  have hfinite (n : ℕ) : ∃ Gₙ : DeepTailL2 T →L[ℝ] DeepTailL2 T,
      ‖Gₙ‖ ≤ 4 / T.Λ ∧
      (∀ f, TailFriedrichsGraph T (T.node (n + 1)) (Gₙ f) (f + T.Λ • Gₙ f)) ∧
      (∀ u f, TailFriedrichsGraph T (T.node (n + 1)) u (f + T.Λ • u) → Gₙ f = u) :=
    exists_tailDeepInverse T hT hη hK (T.node (n + 1)) (Or.inr ⟨n, rfl⟩)
  choose Gₙ hGnb hGne hGnu using hfinite
  refine ⟨tailFormIdentification hp hpos le_rfl,
    fun n => tailFormIdentification hp hpos (deepTail_node_lt_endpoint hT (n + 1)).le,
    G, hGb, hGe, hGu, Gₙ,
    (fun n => tailIndicator T (Iio (T.node (n + 1))) measurableSet_Iio), ?_, ?_, ?_⟩
  · intro n f
    filter_upwards [tailIndicator_coeFn T (Iio (T.node (n + 1))) measurableSet_Iio f]
      with x hx
    rw [hx]
    by_cases hxn : x < T.node (n + 1)
    · rw [indicator_of_mem (s := Iio (T.node (n + 1))) hxn, if_pos hxn]
    · rw [indicator_of_notMem (s := Iio (T.node (n + 1))) hxn, if_neg hxn]
  · intro n f
    exact hGne n _
  · exact tailInverse_restricted_truncation_tendsto hT G Gₙ hGe hGne hGnu hGnb

end ContinuousFlexibility.Radial
