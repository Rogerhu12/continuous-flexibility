import ContinuousFlexibility.Analysis.N04PulledFieldsInverseJoint

/-!
# Finite positive parameter prefixes from the actual current data

The loss for each parameter order is chosen before every spatial order.
A finite parameter prefix takes one finite sum of these losses; the
sampled coefficient constants are collected only afterwards.  No low
parameter base is changed when the prefix is enlarged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

section Generic

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

/-- Collect finitely many genuine directional estimates without moving
their common low base.  Only the high-order loss depends on the prefix. -/
theorem n04PulledFields_finite_oneHigh_prefix
    {p : ℕ → Seminorm ℝ X} (hp : Monotone p)
    {U : Set X} {Ω : Set PolarPoint} {E H : ℕ → ℝ} {base : ℕ}
    {f : ℕ → ℕ → ℕ → Ω → X → ℝ}
    (J : ∀ m i j q, SmoothDirections U (f m i j q))
    (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    (hjet : ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      (0 < k → ∀ z ∈ U, ∀ v : Fin k → X, ∀ m, ∀ (q : Ω) (i j : ℕ),
        i + j ≤ s → |(J m i j q).D k z v| ≤ B * E m ^ B * H m *
          oneHighVariationWeight p base (s + loss) z v)) (K : ℕ) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ k : ℕ, k ≤ K → 0 < k → ∀ z ∈ U, ∀ v : Fin k → X,
      ∀ m, ∀ (q : Ω) (i j : ℕ), i + j ≤ s →
        |(J m i j q).D k z v| ≤ B * E m ^ B * H m *
          oneHighVariationWeight p base (s + loss) z v := by
  classical
  let d : Fin (K + 1) → ℕ := fun k => (hjet k.val).choose
  let loss : ℕ := ∑ k, d k
  have hd (k : Fin (K + 1)) : d k ≤ loss :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  refine ⟨loss, fun s => ?_⟩
  let Bk : Fin (K + 1) → ℝ := fun k => ((hjet k.val).choose_spec s).choose
  have hBk (k : Fin (K + 1)) : 0 < Bk k :=
    ((hjet k.val).choose_spec s).choose_spec.1
  let B : ℝ := 1 + ∑ k, Bk k
  have hsum : 0 ≤ ∑ k, Bk k := Finset.sum_nonneg (fun k _ => (hBk k).le)
  have hB : 0 < B := by dsimp only [B]; linarith
  have hBB (k : Fin (K + 1)) : Bk k ≤ B :=
    (Finset.single_le_sum (fun j _ => (hBk j).le) (Finset.mem_univ k)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨B, hB, fun k hk hkpos z hz v m q i j hij => ?_⟩
  let k' : Fin (K + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  have hraw := ((hjet k).choose_spec s).choose_spec.2 hkpos z hz v m q i j hij
  have hcoef : Bk k' * E m ^ (Bk k') ≤ B * E m ^ B :=
    mul_le_mul (hBB k') (Real.rpow_le_rpow_of_exponent_le (hE m) (hBB k'))
      (Real.rpow_nonneg (zero_le_one.trans (hE m)) _) hB.le
  have hcost : 0 ≤ Bk k' * E m ^ (Bk k') * H m :=
    mul_nonneg (mul_nonneg (hBk k').le
      (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) (hH m)
  have hweight := oneHighVariationWeight_mono (base := base) (base' := base)
    hp le_rfl (Nat.add_le_add_left (hd k') s) z v
  exact hraw.trans ((mul_le_mul_of_nonneg_left hweight hcost).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (hH m))
      (oneHighVariationWeight_nonneg p base (s + loss) z v)))

end Generic

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- Positive jets of the raw mixed fields have one loss for every fixed
parameter prefix.  The estimate uses the actual supplied mixed towers. -/
theorem n04PulledFields_currentData_rawPositive_prefix
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hdata : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hreg : ∀ m, ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (RF : ∀ m, MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
      (fun z => f z m)) (K : ℕ) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ k : ℕ, k ≤ K → 0 < k →
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
      ∀ m, ∀ (q : unitStrip) (i j : ℕ), i + j ≤ s →
        |((RF m).parameter i j q.val q.property).D k z v| ≤
          B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            oneHighVariationWeight (parameterGrading S) base (s + loss) z v := by
  letI : IsTopologicalAddGroup (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).continuousSMul
  have hp : Monotone (parameterGrading S) :=
    tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)
  refine n04PulledFields_finite_oneHigh_prefix hp
    (fun m i j q => (RF m).parameter i j q.val q.property) hE
    (fun m => Real.rpow_nonneg (hH m) (3 / 4 : ℝ)) ?_ K
  intro k
  have hd := hdata.2.choose_spec.2 k
  refine ⟨hd.choose, fun s => ?_⟩
  have hs := hd.choose_spec s
  refine ⟨hs.choose, hs.choose_spec.1, fun hk z hz v m q i j hij => ?_⟩
  let JD := (hdata.2.choose m i j q).congr (fun y hy =>
    mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ)
      (hdata.1 y hy m trivial).1 (hreg m) i j q.property)
  have heq := smoothDirections_D_sub_constant
    ((RF m).parameter i j q.val q.property) JD hk hz v
  exact (congrArg abs heq.symm).le.trans (hs.choose_spec.2 z hz v m trivial q i j hij)

end ContinuousFlexibility.Analysis
