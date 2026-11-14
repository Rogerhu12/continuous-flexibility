import ContinuousFlexibility.Analysis.N04NegativeChartInteriorReference
import ContinuousFlexibility.Analysis.N07aReferenceReturn
import ContinuousFlexibility.Analysis.N01cStateHeightJets

/-!
# Spatial jets of the actual oriented reference travel in the interior

The original speed control is selected once before every derivative
order. Its parameter-zero estimate bounds the reference speed without a
height factor. Positive radial travel jets are the preceding speed jets;
positive angular jets vanish. The zeroth jet uses the actual total travel.
Both orientations and every material overlap radius use the same argument.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff Topology

private theorem endpointControl_reference_spatial
    {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {Ω : I → Set PolarPoint} {H E : I → PolarPoint → ℝ}
    {f : I → X → PolarPoint → ℝ}
    (F : EndpointPowerControl p center base loss U Ω (fun _ _ => 1) H E f)
    (hc : center ∈ U) (s : ℕ) :
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ ∀ i q, q ∈ Ω i → ∀ a b,
      a + b ≤ s → |mixedDerivative a b (f i center) q| ≤ C * E i q ^ A := by
  obtain ⟨C, A, hC, hA, hb⟩ := F.bounds 0 s
  refine ⟨C, A, hC, hA, fun i q hq a b hab => ?_⟩
  let J := (F.regular i).parameter a b q hq
  have hz (n : ℕ) : p n (center - center) ≤ 1 := by
    rw [sub_self]
    exact (p n).map_zero'.le.trans zero_le_one
  have h := hb i 0 le_rfl a b hab q hq J center hc (hz base)
    Fin.elim0 (fun i => i.elim0) 1 le_rfl (hz (s + loss)) (fun i => i.elim0)
  simpa only [one_pow, one_mul, smoothDirections_D_zero_apply J hc,
    Real.norm_eq_abs, parameterHeightWeight, ite_true, mul_one, Real.one_rpow] using h

private theorem primitive_successor_abs_eq_speed
    {f : ℝ → ℝ} {v : PolarPoint → ℝ} {l h r θ : ℝ}
    (hr : r ∈ Ioo l h)
    (hf : ∀ t ∈ Ioo l h, HasDerivAt f (-v (t, θ)) t) (a : ℕ) :
    |iteratedDeriv (a + 1) f r| = |mixedDerivative a 0 v (r, θ)| := by
  have he : deriv f =ᶠ[𝓝 r] (fun t => -v (t, θ)) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
    exact (hf t ht).deriv
  rw [iteratedDeriv_succ', he.iteratedDeriv_eq a, iteratedDeriv_fun_neg, abs_neg]
  simp only [mixedDerivative, iteratedDeriv_zero]

private theorem orientation_positive_jet_abs
    (f : ℝ → ℝ) (T : ℝ) (side : Bool) {a : ℕ} (ha : 0 < a) (r : ℝ) :
    |iteratedDeriv a (fun t => n04bTravelOrientation T side (f t)) r| =
      |iteratedDeriv a f r| := by
  cases side with
  | false => rfl
  | true =>
    simp only [n04bTravelOrientation, ↓reduceIte]
    rw [iteratedDeriv_const_sub ha, iteratedDeriv_neg, abs_neg]

private theorem orientation_abs_le {T t : ℝ} (side : Bool) (ht : t ∈ Icc 0 T) :
    |n04bTravelOrientation T side t| ≤ T := by
  cases side with
  | false => exact (abs_of_nonneg ht.1).le.trans ht.2
  | true =>
    change |T - t| ≤ T
    rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]
    exact sub_le_self T ht.1

private theorem material_sum_envelope {E C₀ C₁ A₀ A₁ : ℝ}
    (hE : 1 ≤ E) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) :
    C₀ * E ^ A₀ ≤ (C₀ + C₁) * E ^ (A₀ + A₁) ∧
      C₁ * E ^ A₁ ≤ (C₀ + C₁) * E ^ (A₀ + A₁) := by
  constructor
  · exact mul_le_mul (le_add_of_nonneg_right hC₁)
      (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_right hA₁))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (add_nonneg hC₀ hC₁)
  · exact mul_le_mul (le_add_of_nonneg_left hC₀)
      (Real.rpow_le_rpow_of_exponent_le hE
        (show A₁ ≤ A₀ + A₁ from le_add_of_nonneg_left hA₀))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (add_nonneg hC₀ hC₁)

namespace N04RealizationStart

set_option backward.isDefEq.respectTransparency true

variable (W : N04RealizationStart) (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ)
    (hρ : ∀ m side, 0 < ρ m side ∧ ρ m side ≤ W.negativeMaterialCollar m)
    (hρb : ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧ ∀ m side,
      (ρ m side)⁻¹ ≤ C * W.T.E0 (W.negativeHalfSample e m side) ^ P)

include hρ hρb in
private theorem negativeInterior_referenceSpeed_spatial :
    ∀ s : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ ∀ m side q,
      q ∈ W.negativeInteriorPhysicalDomain ρ (m, side) → ∀ a b, a + b ≤ s →
      |mixedDerivative a b (minusCharacteristicSpeed
        (originalCoefficients W.D W.S W.C (W.C.referenceState, 0))) q| ≤
        C * W.T.E0 (W.negativeHalfSample e m side) ^ A := by
  have hex := W.negativeInterior_stable_speedControl e ρ hρ hρb
  let base : ℕ := hex.choose
  let ε : ℝ := hex.choose_spec.choose
  let loss : ℕ := hex.choose_spec.choose_spec.choose
  have hs := hex.choose_spec.choose_spec.choose_spec
  let G : W.NegativeInteriorSpeedControl e ρ base loss ε :=
    Classical.choice (hs.2.2.2 base le_rfl ε hs.2.1 le_rfl)
  have hzero : (0 : Parameter W.S) ∈ sectorNeighborhood W.S base ε ε :=
    ⟨(sectorGrading W.S base).map_zero'.trans_lt hs.2.1,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hs.2.1⟩
  intro s
  have hb := endpointControl_reference_spatial G hzero s
  let C : ℝ := hb.choose
  let A : ℝ := hb.choose_spec.choose
  have h := hb.choose_spec.choose_spec
  refine ⟨C, A, h.1, h.2.1, fun m side q hq a b hab => ?_⟩
  simpa only [C, A, liftSectorParameter, Prod.fst_zero, Prod.snd_zero,
    ZeroMemClass.coe_zero, add_zero] using h.2.2 (m, side) q hq a b hab

private theorem negative_referenceTravel_successor_abs
    (m a : ℕ) {q : PolarPoint}
    (hq : q ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    |iteratedDeriv (a + 1) (opticalTravel W.D.w (W.C.left m)) q.1| =
      |mixedDerivative a 0 (minusCharacteristicSpeed
        (originalCoefficients W.D W.S W.C (W.C.referenceState, 0))) q| := by
  apply primitive_successor_abs_eq_speed hq.1
  intro r hr
  have hs : minusCharacteristicSpeed
      (originalCoefficients W.D W.S W.C (W.C.referenceState, 0)) (r, q.2) =
        -opticalSpeed W.D.w r :=
    n07a_minusCharacteristicSpeed_reference W.hS W.hT W.through03.1.1
      ⟨(W.through03.1.1.2.2.2.1.1 m).1.trans hr.1,
        hr.2.trans (W.through03.1.1.2.2.2.1.1 m).2.2⟩ q.2
  simpa only [hs, neg_neg] using n04b_referenceTravel_hasDerivAt
    W.radial.1.choose_spec.1 W.through03.1.1.2.2.2.1 m hr

private theorem negative_referenceTravel_mem_Icc (m : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (W.C.left m) (W.C.right m)) :
    opticalTravel W.D.w (W.C.left m) r ∈ Icc (0 : ℝ) (W.C.travel m) := by
  have hC := W.through03.1.1.2.2.2.1
  have hm := (n04b_referenceTravel_strictMonoOn W.radial.1.choose_spec.1 hC m).monotoneOn
  have hrc : r ∈ Icc (W.C.left m) (W.C.right m) := ⟨hr.1.le, hr.2.le⟩
  constructor
  · have h := hm (left_mem_Icc.mpr (hC.1 m).2.1.le) hrc hr.1.le
    simpa only [opticalTravel, intervalIntegral.integral_same] using h
  · exact (hm hrc (right_mem_Icc.mpr (hC.1 m).2.1.le) hr.2.le).trans_eq
      (n04b_referenceTravel_right hC m)

include hρ hρb in
/-- Every mixed physical jet of the actual oriented reference travel has
a uniform material bound on either selected interior half. The reference
speed neighborhood was chosen before the order `s`; no angle value is
estimated and no height weight is needed for this fixed reference family. -/
theorem negativeInterior_referenceTravel_mixed_bounds (s : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ m side q,
      q ∈ W.negativeInteriorPhysicalDomain ρ (m, side) → ∀ a b, a + b ≤ s →
      |mixedDerivative a b (fun p : PolarPoint =>
        n04bTravelOrientation (W.C.travel m) side
          (opticalTravel W.D.w (W.C.left m) p.1)) q| ≤
        B * W.T.E0 (W.negativeHalfSample e m side) ^ A := by
  have hex₀ := W.negativeInterior_referenceSpeed_spatial e ρ hρ hρb s
  let C₀ : ℝ := hex₀.choose
  let A₀ : ℝ := hex₀.choose_spec.choose
  have h₀ := hex₀.choose_spec.choose_spec
  have hex₁ := W.negativeTravel_material_upper e
  let C₁ : ℝ := hex₁.choose
  let A₁ : ℝ := hex₁.choose_spec.choose
  have h₁ := hex₁.choose_spec.choose_spec
  have hC₀ : 0 < C₀ := zero_lt_one.trans_le h₀.1
  refine ⟨C₀ + C₁, A₀ + A₁, add_pos hC₀ h₁.1, add_nonneg h₀.2.1 h₁.2.1, ?_⟩
  intro m side q hq a b hab
  have hcomp := W.negativeInteriorPhysicalDomain_subset ρ
    (fun m side => (hρ m side).1) (m, side) hq
  have henv := material_sum_envelope (W.floor (W.negativeHalfSample e m side))
    hC₀.le h₁.1.le h₀.2.1 h₁.2.1
  rw [mixedDerivative_radialFunction (fun r =>
    n04bTravelOrientation (W.C.travel m) side (opticalTravel W.D.w (W.C.left m) r)) a b q]
  by_cases hb : b = 0
  · rw [if_pos hb]
    by_cases ha : a = 0
    · subst a
      rw [iteratedDeriv_zero]
      exact ((orientation_abs_le side (W.negative_referenceTravel_mem_Icc m hcomp.1)).trans
        (h₁.2.2 m side)).trans henv.2
    · have hap : 0 < a := Nat.pos_of_ne_zero ha
      rw [orientation_positive_jet_abs _ _ side hap,
        show a = (a - 1) + 1 from (Nat.sub_add_cancel (by omega : 1 ≤ a)).symm,
        W.negative_referenceTravel_successor_abs m (a - 1) hcomp]
      exact (h₀.2.2 m side q hq (a - 1) 0 (by omega)).trans henv.1
  · rw [if_neg hb, abs_zero]
    exact mul_nonneg (add_nonneg hC₀.le h₁.1.le)
      (Real.rpow_nonneg (zero_le_one.trans (W.floor _)) _)

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeInterior_referenceTravel_mixed_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeInterior_referenceTravel_mixed_bounds
