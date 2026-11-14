import ContinuousFlexibility.Analysis.N04NegativeGeometryMarkedProducts
import ContinuousFlexibility.Analysis.N01cFlowVariationForcingBounds

/-!
# Mixed spatial bounds for the actual state-variation forcing

The canonical forcing factors remain smooth when the external flow
parameters and initial angle vary together. Their original finite
product expansion can therefore be differentiated in all spatial
variables. A marked forcing weight survives once, while state-order
powers are kept outside the polynomial coefficient envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

section ActualFields

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {G Θ : E × PolarPoint → ℝ}

theorem n04NegativeChart_flowParameterField_joint_contDiff
    (hΘ : ContDiff ℝ ∞ Θ) (n : ℕ) (v : Fin n → E) :
    ContDiff ℝ ∞ (fun z : E × PolarPoint => flowParameterField Θ n z.1 v z.2) := by
  have he : (fun z : E × PolarPoint => flowParameterField Θ n z.1 v z.2) =
      fun z => iteratedFDeriv ℝ n Θ z (fun i => (v i, (0 : PolarPoint))) :=
    funext (fun z => flowParameterField_eq_joint hΘ n z.1 v z.2)
  rw [he]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E × PolarPoint) ℝ
    (fun i => (v i, (0 : PolarPoint)))).contDiff.comp
      (hΘ.iteratedFDeriv_right (m := ∞) (i := n) (by simp))

theorem n04NegativeChart_flowCoefficient_joint_contDiff
    (hG : ContDiff ℝ ∞ G) (hΘ : ContDiff ℝ ∞ Θ) :
    ContDiff ℝ ∞ (fun z : E × PolarPoint => flowVariationCoefficient G Θ z.1 z.2) :=
  ((hG.fderiv_right (m := ∞) (by simp)).comp
    (contDiff_fst.prodMk (contDiff_snd.fst.prodMk hΘ))).clm_apply contDiff_const

theorem n04NegativeChart_flowForcing_joint_contDiff
    (hG : ContDiff ℝ ∞ G) (J : ContinuousTimeSpeedTower (univ : Set E) G)
    (hΘ : ContDiff ℝ ∞ Θ) {n : ℕ} (hn : 0 < n) (v : Fin n → E) :
    ContDiff ℝ ∞ (fun z : E × PolarPoint => flowVariationForcing J hΘ n z.1 v z.2) := by
  have he : (fun z : E × PolarPoint => flowVariationForcing J hΘ n z.1 v z.2) =
      fun z => flowParameterField (fun y => G (y.1, (y.2.1, Θ y))) n z.1 v z.2 -
        flowVariationCoefficient G Θ z.1 z.2 * flowParameterField Θ n z.1 v z.2 :=
    funext (fun z => flowVariationForcing_eq_source_sub hG J hΘ hn z.1 v z.2)
  rw [he]
  exact (n04NegativeChart_flowParameterField_joint_contDiff
    (hG.comp (contDiff_fst.prodMk (contDiff_snd.fst.prodMk hΘ))) n v).sub
      ((n04NegativeChart_flowCoefficient_joint_contDiff hG hΘ).mul
        (n04NegativeChart_flowParameterField_joint_contDiff hΘ n v))

/-- Every factor is the actual selected speed jet or a strict lower
state variation of the same flow, even when its parameter point varies. -/
theorem n04NegativeChart_forcingFactor_joint_contDiff
    (hG : ContDiff ℝ ∞ G) (J : ContinuousTimeSpeedTower (univ : Set E) G)
    (hΘ : ContDiff ℝ ∞ Θ) {n : ℕ} (v : Fin n → E)
    (d : FlowForcingChoice n) (i : Fin (d.1.length + 1)) :
    ContDiff ℝ ∞ (fun z : E × PolarPoint =>
      canonicalFlowForcingFactors J hΘ z.1 v z.2.1 d i z.2.2) := by
  classical
  refine Fin.cases ?_ (fun j => ?_) i
  · let slots : Fin d.1.length → E × ℝ := fun j => if j ∈ d.2 then
      ((flowParameterIdentityJet (d.1.partSize j) (v ∘ d.1.emb j)).1, 0) else (0, 1)
    have he : (fun z : E × PolarPoint =>
        canonicalFlowForcingFactors J hΘ z.1 v z.2.1 d 0 z.2.2) =
        fun z => iteratedFDeriv ℝ d.1.length G (z.1, (z.2.1, Θ z))
          (fun j => speedTimeSliceInjection (slots j)) := by
      funext z
      change flowSpeedJointField J d.1.length z.1 slots (z.2.1, Θ z) = _
      exact flowSpeedJointField_eq_joint J hG d.1.length z.1 slots (z.2.1, Θ z)
    rw [he]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin d.1.length => E × PolarPoint) ℝ
      (fun j => speedTimeSliceInjection (slots j))).contDiff.comp
        ((hG.iteratedFDeriv_right (m := ∞) (i := d.1.length) (by simp)).comp
          (contDiff_fst.prodMk (contDiff_snd.fst.prodMk hΘ)))
  · by_cases hj : j ∈ d.2
    · simpa only [canonicalFlowForcingFactors, flowForcingFactors, Fin.cons_succ,
        flowSelectedLowerFactor, if_pos hj] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : E × PolarPoint => (1 : ℝ)))
    · by_cases hk : d.1.partSize j < n
      · simpa only [canonicalFlowForcingFactors, flowForcingFactors, Fin.cons_succ,
          flowSelectedLowerFactor, if_neg hj, lowerStateVariation, dif_pos hk,
          canonicalFlowVariation, flowInitialSlice, flowParameterField] using
          n04NegativeChart_flowParameterField_joint_contDiff hΘ (d.1.partSize j) (v ∘ d.1.emb j)
      · simpa only [canonicalFlowForcingFactors, flowForcingFactors, Fin.cons_succ,
          flowSelectedLowerFactor, if_neg hj, lowerStateVariation, dif_neg hk,
          zeroStateVariation, ContinuousMultilinearMap.zero_apply] using
          (contDiff_const : ContDiff ℝ ∞ (fun _ : E × PolarPoint => (0 : ℝ)))

end ActualFields

section WeightedForcing

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

private theorem finiteForcing_weighted_jet_bound (n K : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (f : ∀ d : FlowForcingChoice n, Fin (d.1.length + 1) → Q → ℝ) (x : Q),
      (∀ d i, ContDiffAt ℝ ∞ (f d i) x) →
      ∀ {W M ρ : ℝ} (D : ℕ), 0 ≤ W → 1 ≤ M → 1 ≤ ρ →
      (∀ d, ∃ i₀ : Fin (d.1.length + 1),
        (∀ j, j ≤ K → ‖iteratedFDeriv ℝ j (f d i₀) x‖ ≤ W * M * ρ ^ (D + j)) ∧
        (∀ i, i ≠ i₀ → ∀ j, j ≤ K →
          ‖iteratedFDeriv ℝ j (f d i) x‖ ≤ M * ρ ^ (D + j))) →
      ∀ k, k ≤ K →
        ‖iteratedFDeriv ℝ k (fun y : Q => ∑ d : FlowForcingChoice n, ∏ i, f d i y) x‖ ≤
          C * W * M ^ (n + 1) * ρ ^ (D * (n + 1) + k) := by
  classical
  let B : ℝ := ((2 : ℝ) ^ K) ^ (n + 1)
  have hB : 0 ≤ B := pow_nonneg (pow_nonneg (by norm_num) _) _
  let C : ℝ := 1 + (Fintype.card (FlowForcingChoice n) : ℝ) * B
  have hC : 1 ≤ C := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hB)
  refine ⟨C, hC, ?_⟩
  intro f x hf W M ρ D hW hM hρ hmarked k hk
  have hM' : 1 ≤ M * ρ ^ D := one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ hρ)
  have hterm (d : FlowForcingChoice n) :
      ‖iteratedFDeriv ℝ k (fun y : Q => ∏ i, f d i y) x‖ ≤
        B * W * M ^ (n + 1) * ρ ^ (D * (n + 1) + k) := by
    obtain ⟨i₀, hi₀, hother⟩ := hmarked d
    have hb := n04NegativeGeometry_marked_finiteProduct_jet_le (d.1.length + 1) K i₀
      (f d) x (hf d) hW (zero_le_one.trans hM') (zero_le_one.trans hρ)
      (fun j hj => (hi₀ j hj).trans_eq (by rw [pow_add]; ring))
      (fun i hi j hj => (hother i hi j hj).trans_eq (by rw [pow_add]; ring)) k hk
    have hlength : d.1.length + 1 ≤ n + 1 := Nat.add_le_add_right d.1.length_le 1
    have hscale : ((2 : ℝ) ^ K) ^ (d.1.length + 1) ≤ B :=
      pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hlength
    have hpow : (M * ρ ^ D) ^ (d.1.length + 1) ≤ (M * ρ ^ D) ^ (n + 1) :=
      pow_le_pow_right₀ hM' hlength
    calc
      _ ≤ ((2 : ℝ) ^ K) ^ (d.1.length + 1) * W *
          (M * ρ ^ D) ^ (d.1.length + 1) * ρ ^ k := hb
      _ ≤ B * W * (M * ρ ^ D) ^ (n + 1) * ρ ^ k :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_right hscale hW) hpow
            (pow_nonneg (zero_le_one.trans hM') _) (mul_nonneg hB hW))
          (pow_nonneg (zero_le_one.trans hρ) _)
      _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring
  rw [iteratedFDeriv_fun_sum_apply
    (fun d _ => (contDiffAt_prod (fun i _ => hf d i)).of_le (by simp))]
  calc
    _ ≤ ∑ d : FlowForcingChoice n,
        ‖iteratedFDeriv ℝ k (fun y : Q => ∏ i, f d i y) x‖ := norm_sum_le _ _
    _ ≤ ∑ _d : FlowForcingChoice n,
        B * W * M ^ (n + 1) * ρ ^ (D * (n + 1) + k) :=
      Finset.sum_le_sum (fun d _ => hterm d)
    _ = ((Fintype.card (FlowForcingChoice n) : ℝ) * B) *
        (W * M ^ (n + 1) * ρ ^ (D * (n + 1) + k)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ C * (W * M ^ (n + 1) * ρ ^ (D * (n + 1) + k)) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
        (mul_nonneg (mul_nonneg hW (pow_nonneg (zero_le_one.trans hM) _))
          (pow_nonneg (zero_le_one.trans hρ) _))
    _ = _ := by ring

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The genuine forcing is bounded through its original selected speed
and lower-variation factors. The exponent D records only state-order
loss, so it is not multiplied by the requested spatial order. -/
theorem n04NegativeChart_actualForcing_weighted_prefix (n K : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {G Θ : E × PolarPoint → ℝ},
      ∀ (hG : ContDiff ℝ ∞ G) (J : ContinuousTimeSpeedTower (univ : Set E) G)
        (hΘ : ContDiff ℝ ∞ Θ) (γ : Q → E) (α : Q → ℝ),
      ContDiff ℝ ∞ γ → ContDiff ℝ ∞ α →
      ∀ (v : Fin n → E) (t : ℝ) (x : Q) {W M ρ : ℝ} (D : ℕ),
      0 ≤ W → 1 ≤ M → 1 ≤ ρ →
      (∀ d : FlowForcingChoice n, ∃ i₀ : Fin (d.1.length + 1),
        (∀ j, j ≤ K → ‖iteratedFDeriv ℝ j (fun y : Q =>
          canonicalFlowForcingFactors J hΘ (γ y) v t d i₀ (α y)) x‖ ≤
            W * M * ρ ^ (D + j)) ∧
        (∀ i, i ≠ i₀ → ∀ j, j ≤ K → ‖iteratedFDeriv ℝ j (fun y : Q =>
          canonicalFlowForcingFactors J hΘ (γ y) v t d i (α y)) x‖ ≤
            M * ρ ^ (D + j))) →
      ∀ k, k ≤ K →
        ‖iteratedFDeriv ℝ k
          (fun y : Q => flowVariationForcing J hΘ n (γ y) v (t, α y)) x‖ ≤
            C * W * M ^ (n + 1) * ρ ^ (D * (n + 1) + k) := by
  obtain ⟨C, hC, hb⟩ := finiteForcing_weighted_jet_bound (Q := Q) n K
  refine ⟨C, hC, ?_⟩
  intro G Θ hG J hΘ γ α hγ hα v t x W M ρ D hW hM hρ hmarked k hk
  let f : ∀ d : FlowForcingChoice n, Fin (d.1.length + 1) → Q → ℝ :=
    fun d i y => canonicalFlowForcingFactors J hΘ (γ y) v t d i (α y)
  have hf (d : FlowForcingChoice n) (i : Fin (d.1.length + 1)) :
      ContDiffAt ℝ ∞ (f d i) x :=
    ((n04NegativeChart_forcingFactor_joint_contDiff hG J hΘ v d i).comp
      (hγ.prodMk (contDiff_const.prodMk hα))).contDiffAt
  have he : (fun y : Q => flowVariationForcing J hΘ n (γ y) v (t, α y)) =
      fun y : Q => ∑ d : FlowForcingChoice n, ∏ i, f d i y := by
    funext y
    exact truncatedFlowForcing_eq_finite_products J (flowInitialSlice Θ)
      (fun a k (_ : k < n) => canonicalFlowVariation (contDiff_flowInitialSlice hΘ a) k)
      (γ y, t) v (α y)
  rw [he]
  exact hb f x hf D hW hM hρ hmarked k hk

end WeightedForcing

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_actualForcing_weighted_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_actualForcing_weighted_prefix
