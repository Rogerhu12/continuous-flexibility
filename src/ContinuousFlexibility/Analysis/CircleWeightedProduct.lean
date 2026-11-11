import ContinuousFlexibility.Analysis.CircleEnergyPointwiseBounds
import ContinuousFlexibility.Analysis.CircleCompositionModel
import ContinuousFlexibility.Analysis.CircleBilinearRealization
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Products in the actual weighted circle space

A uniformly smooth periodic multiplier acts on the supplied weighted
circle fields.  Leibniz's rule is estimated against the same circle's
complete energy, which proves finiteness after summing all components.
For positive decay weight, decoded circle fields are such multipliers.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators Topology

def circleProductJetConstant (s : ℕ) (B : ℝ) : ℝ :=
  ∑ b ∈ Finset.range (s + 1),
    ∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ) * (B * (2 * circleSobolevConstant))

theorem circleProductJetConstant_nonneg (s : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ circleProductJetConstant s B := by
  apply Finset.sum_nonneg
  intro b hb
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg hB (mul_nonneg (by norm_num) circleSobolevConstant_nonneg))

theorem circleProductJetConstant_row_le {b s : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hb : b ≤ s) :
    (∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ) * (B * (2 * circleSobolevConstant))) ≤
      circleProductJetConstant s B := by
  apply Finset.single_le_sum _ (Finset.mem_range.mpr (by omega))
  intro n hn
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg hB (mul_nonneg (by norm_num) circleSobolevConstant_nonneg))

theorem circleWeighted_product_iteratedDeriv_abs_le
    {T : MaterialData} {γ : ℝ} {u v : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (hv : ∀ m, ContDiff ℝ ∞ (v m))
    {m b k s : ℕ} (hM : 0 ≤ T.M (T.sample m)) (hH : 0 ≤ T.H (T.sample m))
    (horder : b + k ≤ s) {B : ℝ} (hB : 0 ≤ B)
    (hjets : ∀ i θ, i ≤ s → |iteratedDeriv i (v m) θ| ≤ B) (θ : ℝ) :
    (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
      |iteratedDeriv b (fun t => v m t * u m t) θ| ≤
      circleProductJetConstant s B *
        Real.sqrt (circleComponentEnergy T γ (s + 1) u m).toReal := by
  let w : ℝ := T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)
  let E : ℝ := Real.sqrt (circleComponentEnergy T γ (s + 1) u m).toReal
  have hw : 0 ≤ w := mul_nonneg (pow_nonneg hM k) (Real.rpow_nonneg hH _)
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  have hterm (i : ℕ) (hi : i ∈ Finset.range (b + 1)) :
      w * |(b.choose i : ℝ) *
        iteratedDeriv i (v m) θ * iteratedDeriv (b - i) (u m) θ| ≤
      ((b.choose i : ℝ) * (B * (2 * circleSobolevConstant))) * E := by
    have hi' : i ≤ b := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    have hvbound := hjets i θ (hi'.trans (Nat.le_add_right b k |>.trans horder))
    have hubound := circleWeighted_abs_le_componentEnergy hu hM hH
      (a := b - i) (b := k) (s := s + 1) (by omega) θ
    calc
      w * |(b.choose i : ℝ) *
          iteratedDeriv i (v m) θ * iteratedDeriv (b - i) (u m) θ| =
          (b.choose i : ℝ) *
            (|iteratedDeriv i (v m) θ| * (w * |iteratedDeriv (b - i) (u m) θ|)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        ring
      _ ≤ (b.choose i : ℝ) * (B * (2 * circleSobolevConstant * E)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hvbound hubound (mul_nonneg hw (abs_nonneg _)) hB)
          (Nat.cast_nonneg _)
      _ = _ := by ring
  calc
    w * |iteratedDeriv b (fun t => v m t * u m t) θ| =
        w * |∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ) *
          iteratedDeriv i (v m) θ * iteratedDeriv (b - i) (u m) θ| := by
      rw [iteratedDeriv_fun_mul ((hv m).contDiffAt.of_le (by simp))
        ((hu.1 m).1.contDiffAt.of_le (by simp))]
    _ ≤ w * ∑ i ∈ Finset.range (b + 1), |(b.choose i : ℝ) *
        iteratedDeriv i (v m) θ * iteratedDeriv (b - i) (u m) θ| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hw
    _ = ∑ i ∈ Finset.range (b + 1), w * |(b.choose i : ℝ) *
        iteratedDeriv i (v m) θ * iteratedDeriv (b - i) (u m) θ| := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ Finset.range (b + 1),
        ((b.choose i : ℝ) * (B * (2 * circleSobolevConstant))) * E :=
      Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (b + 1),
        (b.choose i : ℝ) * (B * (2 * circleSobolevConstant))) * E :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ circleProductJetConstant s B * E :=
      mul_le_mul_of_nonneg_right
        (circleProductJetConstant_row_le hB (by omega)) hE

theorem circleMember_mul_of_uniform_jets
    {T : MaterialData} {γ : ℝ} {u v : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u)
    (hv : ∀ m, ContDiff ℝ ∞ (v m) ∧ Function.Periodic (v m) Real.pi)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (hjets : ∀ s, ∃ B : ℝ, 0 ≤ B ∧
      ∀ m i θ, i ≤ s → |iteratedDeriv i (v m) θ| ≤ B) :
    CircleMember T γ (fun m θ => v m θ * u m θ) := by
  apply circleMember_of_component_pointwise hu
  · intro m
    refine ⟨(hv m).1.mul (hu.1 m).1, ?_⟩
    intro θ
    rw [(hv m).2 θ, (hu.1 m).2 θ]
  · exact hM
  · exact hH
  · intro s
    obtain ⟨B, hB, hBjets⟩ := hjets s
    refine ⟨s + 1, circleProductJetConstant s B, circleProductJetConstant_nonneg s hB, ?_⟩
    intro m b k horder θ
    exact circleWeighted_product_iteratedDeriv_abs_le hu (fun i => (hv i).1)
      (hM m) (hH m) horder hB (fun i θ hi => hBjets m i θ hi) θ

theorem circleModel_uniform_jets_of_material
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (u : S.Space) (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m i θ, i ≤ s →
      |iteratedDeriv i (S.decode u m) θ| ≤ B := by
  have hH := (material_circle_sample_weights_pos hT hD).2
  obtain ⟨_, hbounds⟩ := hD
  have hs := materialSample_mem_radialCore hT hbounds.2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdecay, _⟩ := hT
  obtain ⟨A, hA, hbound, _⟩ := hdecay 0 γ hγ
  have hHA (m : ℕ) : T.H (T.sample m) ^ γ ≤ A := by
    simpa only [Real.rpow_zero, mul_one] using hbound (T.sample m) (hs m)
  let B : ℝ := (2 * circleSobolevConstant * S.grading (s + 1) u) * A
  have hscale : 0 ≤ 2 * circleSobolevConstant :=
    mul_nonneg (by norm_num) circleSobolevConstant_nonneg
  refine ⟨B, mul_nonneg (mul_nonneg hscale (apply_nonneg _ _)) hA.le, ?_⟩
  intro m i θ hi
  have hgrade : S.grading (i + 1) u ≤ S.grading (s + 1) u :=
    gradedSeminorm_monotone (fun j => S.level j) S.bond (Nat.add_le_add_right hi 1) u
  exact (circleModel_iteratedDeriv_abs_le hS hH u m i θ).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hgrade hscale) (hHA m)
      (Real.rpow_nonneg (hH m).le _) (mul_nonneg hscale (apply_nonneg _ _)))

def circleProductFieldBilinear (S : CircleModelData) :
    S.Space →ₗ[ℝ] S.Space →ₗ[ℝ] (ℕ → ℝ → ℝ) where
  toFun u :=
    { toFun := fun v m θ => S.decode u m θ * S.decode v m θ
      map_add' := by
        intro v w
        funext m θ
        simp only [map_add, Pi.add_apply, mul_add]
      map_smul' := by
        intro c v
        funext m θ
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        ring }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    funext m θ
    simp only [LinearMap.add_apply, map_add, Pi.add_apply, add_mul]
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    funext m θ
    simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

def circleProductBilinear
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) :
    S.Space →ₗ[ℝ] S.Space →ₗ[ℝ] S.Space :=
  liftCircleBilinear hS (circleProductFieldBilinear S) (fun u v =>
    circleMember_mul_of_uniform_jets (hS.2.2.2.1 v) (hS.2.2.2.1 u).1
      (fun m => (material_circle_sample_weights_pos hT hD).1 m |>.le)
      (fun m => (material_circle_sample_weights_pos hT hD).2 m |>.le)
      (circleModel_uniform_jets_of_material hS hT hD hγ u))

theorem circleProductBilinear_decode
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (u v : S.Space) :
    S.decode (circleProductBilinear hS hT hD hγ u v) =
      fun m θ => S.decode u m θ * S.decode v m θ := by
  exact liftCircleBilinear_decode hS (circleProductFieldBilinear S) (fun u v =>
    circleMember_mul_of_uniform_jets (hS.2.2.2.1 v) (hS.2.2.2.1 u).1
      (fun m => (material_circle_sample_weights_pos hT hD).1 m |>.le)
      (fun m => (material_circle_sample_weights_pos hT hD).2 m |>.le)
      (circleModel_uniform_jets_of_material hS hT hD hγ u)) u v

end ContinuousFlexibility.Statements
