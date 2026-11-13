import ContinuousFlexibility.Analysis.N01cCoefficientBaseSelection
import ContinuousFlexibility.Analysis.N01cCoefficientPolarPowerInputs

/-!
# The fixed radial prefix interpolation step on an abstract graded space

All choices and scalar inequalities are proved before the physical
state space is specialized. This keeps the actual root producer small
while preserving its original towers and its fixed low order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- The unchanged finite normalized prefix, kept abstract until the
physical state space and its grading are supplied. -/
def N04PositiveGeometryRootHeightFiniteShiftPowerBound
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
    (p : ℕ → Seminorm ℝ Y) (F : Fin 4 → Y → PolarPoint → ℝ)
    (Ω : Set PolarPoint) (E H : PolarPoint → ℝ)
    (x0 : Y) (N requestedBase : ℕ) : Prop :=
    ∃ B loss : ℕ, requestedBase ≤ B ∧ ∀ K s : ℕ,
      ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ i : Fin 4, ∀ a d : ℕ, a + d ≤ N → ∀ b : ℕ, b ≤ s →
      ∀ q ∈ Ω, ∀ U : Set (Y × ℝ),
      ∀ J : SmoothDirections U (fun z => z.2 * mixedDerivative a (b + d) (F i z.1) q),
      ∀ k : ℕ, k ≤ K → ∀ z ∈ U, |z.2| ≤ 1 →
      pairGrading p realGrading B (z - (x0, 0)) ≤ 1 →
      ∀ v : Fin k → (Y × ℝ),
      (∀ j, pairGrading p realGrading B (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading p realGrading (s + loss) (z - (x0, 0)) ≤ R →
      (∀ j, pairGrading p realGrading (s + loss) (v j) ≤ R) →
        |J.D k z v| ≤ C * E q ^ A * H q * R ^ ((b : ℝ) / ((s : ℝ) + 1))

theorem n04PositiveGeometry_rootFiniteShift_power_of_raw
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
    (p : ℕ → Seminorm ℝ Y) (hp0 : Monotone p)
    (hI0 : HasInterpolation (pairGrading p realGrading))
    (F : Fin 4 → Y → PolarPoint → ℝ) (Ω : Set PolarPoint)
    (E H : PolarPoint → ℝ) (hE0 : ∀ q ∈ Ω, 1 ≤ E q) (hH0 : ∀ q ∈ Ω, 0 ≤ H q)
    (hraw : ∀ s : ℕ, ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ i : Fin 4, ∀ a b : ℕ, a + b ≤ s → ∀ q ∈ Ω,
      ∀ U : Set (Y × ℝ),
      ∀ J : SmoothDirections U (fun z => z.2 * mixedDerivative a b (F i z.1) q),
      ∀ k B : ℕ, ∀ x0 : Y, ∀ z ∈ U, |z.2| ≤ 1 → ∀ v : Fin k → (Y × ℝ),
        |J.D k z v| ≤ C * E q ^ A * H q * (1 + p (s + 7) x0) *
          oneHighVariationWeight (pairGrading p realGrading) B (s + 7)
            (z - (x0, 0)) v)
    (x0 : Y) (N requestedBase : ℕ) :
    N04PositiveGeometryRootHeightFiniteShiftPowerBound p F Ω E H x0 N requestedBase := by
  classical
  let pjoint := pairGrading p realGrading
  have hp : Monotone pjoint := tamePairGrading_monotone hp0 (fun _ _ _ => le_rfl)
  obtain ⟨B, loss, hB, hI⟩ := exists_base_ge_of_spatialPower_continuation
    pjoint hp hI0 requestedBase (N + 7)
    (fun B loss => ∀ s : ℕ, ∃ CI : ℝ, 1 ≤ CI ∧
      ∀ n : ℕ, n ≤ s → ∀ x : Y × ℝ, pjoint B x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → pjoint (s + loss) x ≤ R →
        pjoint (n + (N + 7)) x ≤ CI * R ^ ((n : ℝ) / ((s : ℝ) + 1)))
    (fun _ _ _ h => h)
  refine ⟨B, loss, hB, fun K s => ?_⟩
  choose c A hc hA hb using fun b : Fin (s + 1) =>
    hraw (N + b.val)
  let C0 : ℝ := 1 + ∑ b : Fin (s + 1), c b
  let A0 : ℝ := ∑ b : Fin (s + 1), A b
  have hC0 : 1 ≤ C0 := le_add_of_nonneg_right (Finset.sum_nonneg (fun b _ => hc b))
  have hA0 : 0 ≤ A0 := Finset.sum_nonneg (fun b _ => hA b)
  have hc0 (b : Fin (s + 1)) : c b ≤ C0 :=
    (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ b)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hAA (b : Fin (s + 1)) : A b ≤ A0 :=
    Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ b)
  obtain ⟨CI, hCI, hIb⟩ := hI s
  let Q : ℝ := 1 + (K + 1 : ℝ) * CI
  let M : ℝ := 1 + p (N + s + 7) x0
  have hM : 1 ≤ M := le_add_of_nonneg_right (apply_nonneg _ _)
  have hQ : 1 ≤ Q := le_add_of_nonneg_right
    (mul_nonneg (by positivity) (zero_le_one.trans hCI))
  refine ⟨C0 * M * Q, A0,
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hC0 hM) hQ, hA0, ?_⟩
  intro i a d had b hbs q hq U J k hk z hz hzq hzlow v hv R hR hzR hvR
  let j : Fin (s + 1) := ⟨b, Nat.lt_succ_of_le hbs⟩
  have hraw := hb j i a (b + d) (by change a + (b + d) ≤ N + b; omega)
    q hq U J k B x0 z hz hzq v
  have hcenter : 1 + p (N + b + 7) x0 ≤ M :=
    add_le_add le_rfl (hp0 (by omega) x0)
  have hpow : 1 ≤ R ^ ((b : ℝ) / ((s : ℝ) + 1)) :=
    Real.one_le_rpow hR (by positivity)
  have horder (x : Y × ℝ) (hx : pjoint B x ≤ 1)
      (hxR : pjoint (s + loss) x ≤ R) :
      pjoint (N + b + 7) x ≤ CI * R ^ ((b : ℝ) / ((s : ℝ) + 1)) := by
    have he : b + (N + 7) = N + b + 7 := by omega
    simpa only [he] using hIb b hbs x hx R hR hxR
  have hoh := oneHighVariationWeight_unit_le_power pjoint B (N + b + 7)
    hk (z - (x0, 0)) v hv (zero_le_one.trans hCI) hpow
    (horder _ hzlow hzR) (fun t => horder _ (hv t) (hvR t))
  have hH : 0 ≤ H q := hH0 q hq
  have hE0 : 1 ≤ E q := hE0 q hq
  have hCE : c j * E q ^ A j ≤ C0 * E q ^ A0 :=
    mul_le_mul (hc0 j) (Real.rpow_le_rpow_of_exponent_le hE0 (hAA j))
      (Real.rpow_nonneg (zero_le_one.trans hE0) _) (zero_le_one.trans hC0)
  have hCEH : 0 ≤ C0 * E q ^ A0 * H q :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hC0)
      (Real.rpow_nonneg (zero_le_one.trans hE0) _)) hH
  have hscaled := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_right hCE hH) hcenter
      (by positivity : 0 ≤ 1 + p (N + b + 7) x0) hCEH)
    hoh (oneHighVariationWeight_nonneg pjoint B (N + b + 7) (z - (x0, 0)) v)
    (mul_nonneg hCEH (zero_le_one.trans hM))
  exact hraw.trans (hscaled.trans_eq (by dsimp only [Q]; ring))


end ContinuousFlexibility.Analysis
