import ContinuousFlexibility.Analysis.N04RealizationFixedBasePrefix
import ContinuousFlexibility.Analysis.N04RealizationFullWeightProductOneHigh

/-!
# A common interpolation base for finitely many weighted jet towers

The parameter-order losses may grow. Their order-zero values alone fix
the low seminorm; a finite prefix changes only the high order. Constants
are uniform in the spatial point and in the piece index.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {ι : Type*} {U : Set X} {Ω : Set PolarPoint}

/-- Uniform one-high bounds for a full mixed tower with one external
weight for every piece, including at parameter order zero. -/
def N04PrincipalWeightedTowerBounds (p : ℕ → Seminorm ℝ X) (base : ℕ)
    (E W : ι → ℝ) {f : ι → X → PolarPoint → ℝ}
    (R : ∀ m, MixedJetRegularity U Ω (f m)) : Prop :=
  ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
    ∀ m, ∀ a b : ℕ, a + b ≤ s → ∀ q (hq : q ∈ Ω),
    ∀ x ∈ U, p base x ≤ 1 → ∀ v : Fin k → X,
      ‖((R m).parameter a b q hq).D k x v‖ ≤
        B * E m ^ B * W m * oneHighVariationWeight p base (s + loss) x v

/-- Collect finitely many families before applying fixed-base
interpolation. The low order is chosen before the parameter prefix. -/
theorem n04Principal_weightedTower_prefix
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (oldBase requestedBase : ℕ) {r : ℕ}
    (E : ι → ℝ) (W : Fin r → ι → ℝ)
    (hE : ∀ m, 1 ≤ E m) (hW : ∀ i m, 0 ≤ W i m)
    (f : Fin r → ι → X → PolarPoint → ℝ)
    (R : ∀ i m, MixedJetRegularity U Ω (f i m))
    (hb : ∀ i, N04PrincipalWeightedTowerBounds p oldBase E (W i) (R i)) :
    ∃ base : ℕ, max oldBase requestedBase ≤ base ∧
      ∀ K : ℕ, ∃ shift : ℕ, ∀ s : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
        ∀ i m, ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s →
        ∀ q (hq : q ∈ Ω), ∀ x ∈ U, p base x ≤ 1 →
        ∀ v : Fin k → X, (∀ t, p base (v t) ≤ 1) →
        ∀ V : ℝ, 1 ≤ V → p (base + s + shift * K + 1) x ≤ V →
          (∀ t, p (base + s + shift * K + 1) (v t) ≤ V) →
          ‖((R i m).parameter a b q hq).D k x v‖ ≤
            C * E m ^ A * W i m *
              V ^ (((a + b + shift * k : ℕ) : ℝ) /
                (((s + shift * K : ℕ) : ℝ) + 1)) := by
  classical
  let L : ℕ → ℕ := fun k => ∑ i : Fin r, (hb i k).choose
  have hLi (i : Fin r) (k : ℕ) : (hb i k).choose ≤ L k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hinterp := n04Realization_fixedBase_prefix_power p hp hI
    (max oldBase requestedBase) L
  let base : ℕ := hinterp.choose
  have hbase : max oldBase requestedBase ≤ base := hinterp.choose_spec.1
  have hold : oldBase ≤ base := (le_max_left _ _).trans hbase
  refine ⟨base, hbase, fun K => ?_⟩
  have hpref := hinterp.choose_spec.2 K
  let shift : ℕ := hpref.choose
  refine ⟨shift, fun s => ?_⟩
  let I : Type := Fin r × Fin (K + 1) × Fin (s + 1)
  let B₀ : I → ℝ := fun i =>
    ((hb i.1 i.2.1.val).choose_spec i.2.2.val).choose
  have hB₀ : ∀ i : I, 0 < B₀ i := fun i =>
    ((hb i.1 i.2.1.val).choose_spec i.2.2.val).choose_spec.1
  let B : ℝ := 1 + ∑ i : I, B₀ i
  have hB : 1 ≤ B := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun i _ => (hB₀ i).le))
  have hB₀B (i : I) : B₀ i ≤ B :=
    (Finset.single_le_sum (fun j _ => (hB₀ j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hprefS := hpref.choose_spec s
  let C₀ : ℝ := hprefS.choose
  have hC₀ : 1 ≤ C₀ := hprefS.choose_spec.1
  let C : ℝ := B * C₀ + 1
  have hC : 1 ≤ C := by
    dsimp only [C]
    have hprod := mul_nonneg (zero_le_one.trans hB) (zero_le_one.trans hC₀)
    linarith
  refine ⟨C, B, hC, (zero_le_one.trans hB), ?_⟩
  intro i m k hk a b hab q hq x hx hlow v hv V hV hxV hvV
  let index : I := (i, ⟨k, Nat.lt_succ_of_le hk⟩,
    ⟨a + b, Nat.lt_succ_of_le hab⟩)
  have he0 : 0 ≤ E m := zero_le_one.trans (hE m)
  have hw0 : 0 ≤ W i m := hW i m
  have hbound := ((hb i k).choose_spec (a + b)).choose_spec.2
    m a b le_rfl q hq x hx ((hp hold x).trans hlow) v
  have hweight := oneHighVariationWeight_mono hp hold
    (Nat.add_le_add_left (hLi i k) (a + b)) x v
  have hcoef : B₀ index * E m ^ B₀ index * W i m ≤ B * E m ^ B * W i m :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul (hB₀B index)
        (Real.rpow_le_rpow_of_exponent_le (hE m) (hB₀B index))
        (Real.rpow_nonneg he0 _) (zero_le_one.trans hB)) hw0
  have hraw : ‖((R i m).parameter a b q hq).D k x v‖ ≤
      B * E m ^ B * W i m * oneHighVariationWeight p base (a + b + L k) x v :=
    hbound.trans (mul_le_mul hcoef hweight
      (oneHighVariationWeight_nonneg _ _ _ _ _)
      (mul_nonneg (mul_nonneg (zero_le_one.trans hB) (Real.rpow_nonneg he0 _)) hw0))
  have hpw := hprefS.choose_spec.2 k hk (a + b) hab x hlow v hv V hV hxV hvV
  have hCpow : B * E m ^ B * W i m *
      (C₀ * V ^ (((a + b + shift * k : ℕ) : ℝ) /
        (((s + shift * K : ℕ) : ℝ) + 1))) ≤
      C * E m ^ B * W i m *
        V ^ (((a + b + shift * k : ℕ) : ℝ) /
          (((s + shift * K : ℕ) : ℝ) + 1)) := by
    have hc : B * C₀ ≤ C := by dsimp only [C]; linarith
    have hnonneg : 0 ≤ E m ^ B * W i m *
        V ^ (((a + b + shift * k : ℕ) : ℝ) /
          (((s + shift * K : ℕ) : ℝ) + 1)) := by positivity
    have hh := mul_le_mul_of_nonneg_right hc hnonneg
    convert hh using 1 <;> ring
  exact hraw.trans ((mul_le_mul_of_nonneg_left hpw
    (mul_nonneg (mul_nonneg (zero_le_one.trans hB) (Real.rpow_nonneg he0 _)) hw0)).trans
      hCpow)

end ContinuousFlexibility.Analysis
