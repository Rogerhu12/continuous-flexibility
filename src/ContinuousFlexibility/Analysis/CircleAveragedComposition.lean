module

public import ContinuousFlexibility.Analysis.CircleParameterIntegral
public import ContinuousFlexibility.Analysis.CircleWeightedProduct

/-!
# Averaging actual chart compositions on the unit segment

A decoded circle perturbation has uniformly bounded angular jets.
The same bounds hold for every lift theta + travel + a e(theta),
0 <= a <= 1.  Parameter integration consequently defines a linear
operator in the original weighted circle model.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff

def circleAffineLift (travel : ℕ → ℝ) (e : ℕ → ℝ → ℝ)
    (a : ℝ) : ℕ → ℝ → ℝ :=
  fun m θ => θ + travel m + a * e m θ

theorem circleAffineLift_contDiff
    {e : ℕ → ℝ → ℝ} (he : ∀ m, ContDiff ℝ ∞ (e m))
    (travel : ℕ → ℝ) (a : ℝ) (m : ℕ) :
    ContDiff ℝ ∞ (circleAffineLift travel e a m) := by
  have h : ContDiff ℝ ∞ (fun x : ℝ => x + travel m + a * e m x) :=
    (contDiff_id.add contDiff_const).add (contDiff_const.mul (he m))
  exact h

theorem circleAffineLift_periodic
    {e : ℕ → ℝ → ℝ} (he : ∀ m, Function.Periodic (e m) Real.pi)
    (travel : ℕ → ℝ) (a : ℝ) (m : ℕ) (θ : ℝ) :
    circleAffineLift travel e a m (θ + Real.pi) =
      circleAffineLift travel e a m θ + Real.pi := by
  simp only [circleAffineLift, he m θ]
  ring

theorem circleAffineLift_uniform_jets
    {e : ℕ → ℝ → ℝ} (he : ∀ m, ContDiff ℝ ∞ (e m))
    (travel : ℕ → ℝ) {s : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ m i θ, i ≤ s → |iteratedDeriv i (e m) θ| ≤ B)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    ∀ m i θ, 1 ≤ i → i ≤ s →
      |iteratedDeriv i (circleAffineLift travel e a m) θ| ≤ (1 + B) ^ i := by
  intro m i θ hi his
  have hshift : circleAffineLift travel e a m =
      (fun x => travel m + (x + a * e m x)) := by
    funext x
    dsimp only [circleAffineLift]
    ring
  have hsmooth : ContDiff ℝ ∞ (fun x => a * e m x) := contDiff_const.mul (he m)
  have hjet : iteratedDeriv i (circleAffineLift travel e a m) θ =
      iteratedDeriv i (fun x : ℝ => x) θ + a * iteratedDeriv i (e m) θ := by
    rw [hshift, iteratedDeriv_const_add (by omega : 0 < i) (travel m),
      iteratedDeriv_fun_add (f := fun x : ℝ => x)
        (g := fun x : ℝ => a * e m x) (n := i) (x := θ) contDiffAt_id
        (hsmooth.contDiffAt.of_le (by simp)), iteratedDeriv_const_mul_field]
  have hid : |iteratedDeriv i (fun x : ℝ => x) θ| ≤ 1 := by
    rw [iteratedDeriv_fun_id, if_neg (by omega : i ≠ 0)]
    split_ifs <;> norm_num
  have haabs : |a| ≤ 1 := by simpa only [abs_of_nonneg ha.1] using ha.2
  have hprod : |a * iteratedDeriv i (e m) θ| ≤ B := by
    rw [abs_mul]
    simpa only [one_mul] using
      mul_le_mul haabs (hb m i θ his) (abs_nonneg _) zero_le_one
  have hbase : 1 ≤ 1 + B := by linarith only [hB]
  calc
    _ ≤ |iteratedDeriv i (fun x : ℝ => x) θ| +
        |a * iteratedDeriv i (e m) θ| := by rw [hjet]; exact abs_add_le _ _
    _ ≤ 1 + B := add_le_add hid hprod
    _ ≤ (1 + B) ^ i := by
      simpa only [pow_one] using pow_le_pow_right₀ hbase hi

def circleAverageComposeField (u : ℕ → ℝ → ℝ) (travel : ℕ → ℝ)
    (e : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  circleParameterIntegralField (fun a m θ => u m (circleAffineLift travel e a m θ))

theorem circleMember_averageCompose
    {T : MaterialData} {γ : ℝ} {u e : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u)
    (he : ∀ m, ContDiff ℝ ∞ (e m) ∧ Function.Periodic (e m) Real.pi)
    (hM : ∀ m, 0 < T.M (T.sample m)) (hH : ∀ m, 0 < T.H (T.sample m))
    (hjets : ∀ s, ∃ B : ℝ, 0 ≤ B ∧
      ∀ m i θ, i ≤ s → |iteratedDeriv i (e m) θ| ≤ B)
    (travel : ℕ → ℝ) :
    CircleMember T γ (circleAverageComposeField u travel e) := by
  apply circleMember_unitParameterIntegral hu
  · intro m n
    have hg : ContDiff ℝ ∞ (fun p : PolarPoint =>
        p.2 + travel m + p.1 * e m p.2) :=
      (contDiff_snd.add contDiff_const).add
        (contDiff_fst.mul ((he m).1.comp contDiff_snd))
    exact angularRegular_of_contDiff ((hu.1 m).1.comp hg) n
  · intro a ha m θ
    change u m (circleAffineLift travel e a m (θ + Real.pi)) =
      u m (circleAffineLift travel e a m θ)
    rw [circleAffineLift_periodic (fun j => (he j).2)]
    exact (hu.1 m).2 _
  · exact fun m => (hM m).le
  · exact fun m => (hH m).le
  · intro s
    obtain ⟨B, hB, hb⟩ := hjets s
    have hbase : 0 ≤ 1 + B := by linarith only [hB]
    refine ⟨s + 1, circleCompositionJetConstant s (1 + B),
      circleCompositionJetConstant_nonneg s hbase, ?_⟩
    intro m b k horder a ha θ
    have hpoint := circleWeighted_comp_iteratedDeriv_abs_le hu (hM m) (hH m)
      (n := b) (k := k) (s := s + 1) (by omega)
      (circleAffineLift_contDiff (fun i => (he i).1) travel a m) θ
      (fun i hi hib => circleAffineLift_uniform_jets
        (fun j => (he j).1) travel hB hb ha m i θ hi (by omega))
    exact hpoint.trans (mul_le_mul_of_nonneg_right
      (circleCompositionJetConstant_term_le hbase (by omega)) (Real.sqrt_nonneg _))

def circleAverageComposeFieldLinear
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ) (e : ℕ → ℝ → ℝ) :
    S.Space →ₗ[ℝ] (ℕ → ℝ → ℝ) where
  toFun u := circleAverageComposeField (S.decode u) travel e
  map_add' u v := by
    funext m θ
    have hp : Continuous (fun a : ℝ => circleAffineLift travel e a m θ) := by
      unfold circleAffineLift
      fun_prop
    have hi (w : S.Space) : IntervalIntegrable
        (fun a => S.decode w m (circleAffineLift travel e a m θ)) volume 0 1 :=
      (((hS.2.2.2.1 w).1 m).1.continuous.comp hp).intervalIntegrable
        (μ := volume) 0 1
    change (∫ a in (0 : ℝ)..1, S.decode (u + v) m (circleAffineLift travel e a m θ)) =
      (∫ a in (0 : ℝ)..1, S.decode u m (circleAffineLift travel e a m θ)) +
        (∫ a in (0 : ℝ)..1, S.decode v m (circleAffineLift travel e a m θ))
    simp only [map_add, Pi.add_apply]
    exact intervalIntegral.integral_add (hi u) (hi v)
  map_smul' c u := by
    funext m θ
    change (∫ a in (0 : ℝ)..1, S.decode (c • u) m (circleAffineLift travel e a m θ)) =
      c * (∫ a in (0 : ℝ)..1, S.decode u m (circleAffineLift travel e a m θ))
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    exact intervalIntegral.integral_const_mul _ _

section Model

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
  (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
  (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
  (travel : ℕ → ℝ) (e : S.Space)

def circleAverageComposeLinear : S.Space →ₗ[ℝ] S.Space :=
  liftCircleLinear hS (circleAverageComposeFieldLinear hS travel (S.decode e))
    (fun u => circleMember_averageCompose (hS.2.2.2.1 u) (hS.2.2.2.1 e).1
      (material_circle_sample_weights_pos hT hD).1
      (material_circle_sample_weights_pos hT hD).2
      (circleModel_uniform_jets_of_material hS hT hD hγ e) travel)

theorem circleAverageComposeLinear_decode (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleAverageComposeLinear hS hT hD hγ travel e u) m θ =
      ∫ a in (0 : ℝ)..1, S.decode u m
        (θ + travel m + a * S.decode e m θ) := by
  have h := liftCircleLinear_decode hS
    (circleAverageComposeFieldLinear hS travel (S.decode e))
    (fun v => circleMember_averageCompose (hS.2.2.2.1 v) (hS.2.2.2.1 e).1
      (material_circle_sample_weights_pos hT hD).1
      (material_circle_sample_weights_pos hT hD).2
      (circleModel_uniform_jets_of_material hS hT hD hγ e) travel) u
  exact congrFun (congrFun h m) θ

include hS hT hD hγ in
theorem circleShiftedChart_uniform_jets (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m i θ, 1 ≤ i → i ≤ s →
      |iteratedDeriv i (circleAffineLift travel (S.decode e) 1 m) θ| ≤ B ^ i := by
  obtain ⟨B, hB, hb⟩ := circleModel_uniform_jets_of_material hS hT hD hγ e s
  refine ⟨1 + B, by linarith only [hB], ?_⟩
  exact circleAffineLift_uniform_jets (fun m => ((hS.2.2.2.1 e).1 m).1)
    travel hB hb (by norm_num : (1 : ℝ) ∈ Icc 0 1)

def circleShiftedChartComposeLinear : S.Space →ₗ[ℝ] S.Space :=
  circleComposeModelLinear hS (material_circle_sample_weights_pos hT hD).1
    (material_circle_sample_weights_pos hT hD).2
    (circleAffineLift travel (S.decode e) 1)
    (circleAffineLift_contDiff (fun m => ((hS.2.2.2.1 e).1 m).1) travel 1)
    (circleAffineLift_periodic (fun m => ((hS.2.2.2.1 e).1 m).2) travel 1)
    (circleShiftedChart_uniform_jets hS hT hD hγ travel e)

theorem circleShiftedChartComposeLinear_decode (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleShiftedChartComposeLinear hS hT hD hγ travel e u) m θ =
      S.decode u m (θ + travel m + S.decode e m θ) := by
  unfold circleShiftedChartComposeLinear
  have h := circleComposeModelLinear_decode hS (material_circle_sample_weights_pos hT hD).1
    (material_circle_sample_weights_pos hT hD).2
    (circleAffineLift travel (S.decode e) 1)
    (circleAffineLift_contDiff (fun m => ((hS.2.2.2.1 e).1 m).1) travel 1)
    (circleAffineLift_periodic (fun m => ((hS.2.2.2.1 e).1 m).2) travel 1)
    (circleShiftedChart_uniform_jets hS hT hD hγ travel e) u
  simpa only [circleComposeField_apply, circleAffineLift, one_mul] using
    congrFun (congrFun h m) θ

end Model

end ContinuousFlexibility.Statements
