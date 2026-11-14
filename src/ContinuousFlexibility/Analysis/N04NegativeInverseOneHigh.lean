module

public import ContinuousFlexibility.Analysis.N04NegativeGeometryDataCollector
public import ContinuousFlexibility.Analysis.N04NegativeInverseCurrentData

/-!
# From raw inverse prefixes to the selected current-data interface

The complete coefficient, including the sampled height, remains
outside homogeneous normalization. The fixed low order is unchanged.
Only the finite prefix shift enters the loss at a given parameter order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- A fractional raw bound with exponent at most one yields exactly one
high seminorm, without changing its complete scalar coefficient. -/
theorem n04NegativeInverse_fractional_oneHigh
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (x : E)
    {k : ℕ} (A : E [×k]→L[ℝ] ℝ) {M α : ℝ} (hM : 0 ≤ M) (hα : α ≤ 1)
    (hraw : ∀ v : Fin k → E, (∀ i, p base (v i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p high x ≤ R → (∀ i, p high (v i) ≤ R) →
        |A v| ≤ M * R ^ α)
    (v : Fin k → E) :
    |A v| ≤ M * oneHighVariationWeight p base high x v := by
  have hn := multilinear_bound_of_unitBall A (normSeminorm ℝ ℝ)
    (p base) (p high) hM (a := 1 + p high x) (fun u hu => by
      let R : ℝ := (1 + p high x) + ∑ i, p high (u i)
      have hsum : 0 ≤ ∑ i, p high (u i) :=
        Finset.sum_nonneg (fun i _ => apply_nonneg _ _)
      have hR : 1 ≤ R := by
        dsimp only [R]
        linarith [apply_nonneg (p high) x]
      have hxR : p high x ≤ R := by
        dsimp only [R]
        linarith
      have huR (i : Fin k) : p high (u i) ≤ R :=
        (Finset.single_le_sum (fun j _ => apply_nonneg _ _) (Finset.mem_univ i)).trans
          (le_add_of_nonneg_left (by positivity))
      have h := (hraw u (fun i => (hu i).le) R hR hxR huR).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hR hα) hM)
      simpa only [coe_normSeminorm, Real.norm_eq_abs, R] using h)
  simpa only [coe_normSeminorm, Real.norm_eq_abs, multilinearTameSize,
    oneHighVariationWeight] using hn v

/-- Reorder the finite loss while the grading and the multilinear map
are abstract. This prevents rewriting from unfolding a concrete state
grading or a supplied mixed tower. -/
theorem n04NegativeInverse_fractional_prefix_oneHigh
    (p : ℕ → Seminorm ℝ E) (base shift s a b : ℕ) (x : E)
    {k : ℕ} (A : E [×k]→L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M) (hab : a + b ≤ s)
    (hraw : ∀ v : Fin k → E, (∀ i, p base (v i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p (base + s + shift * k + 1) x ≤ R →
        (∀ i, p (base + s + shift * k + 1) (v i) ≤ R) →
        |A v| ≤ M * R ^ (((a + b + shift * k : ℕ) : ℝ) /
          (((s + shift * k : ℕ) : ℝ) + 1)))
    (v : Fin k → E) :
    |A v| ≤ M * oneHighVariationWeight p base (s + (base + shift * k + 1)) x v := by
  have hα : ((a + b + shift * k : ℕ) : ℝ) /
      (((s + shift * k : ℕ) : ℝ) + 1) ≤ 1 :=
    spatialOrder_fraction_le_one (Nat.add_le_add_right hab (shift * k))
  have hn := n04NegativeInverse_fractional_oneHigh p base
    (base + s + shift * k + 1) x A hM hα hraw v
  have horder : base + s + shift * k + 1 = s + (base + shift * k + 1) := by omega
  rw [horder] at hn
  exact hn

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

variable {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

/-- Positive raw prefixes close the actual selected current data,
including the reference-difference value and the zero-order tower. -/
theorem CurrentJetDataOn.negativeInverse_of_positive_prefixes
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (RF : ∀ m, P m → MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
      (fun z => f z m))
    (hperiod : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m → ∀ q ∈ unitStrip,
      f z m (q + (0, Real.pi)) = f z m q)
    (h₀ : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (hzero : ∀ m, P m → ∀ q ∈ unitStrip, f 0 m q = f₀ m q)
    (hlow : ∀ z ∈ sectorNeighborhood S base ε ε, parameterGrading S base z ≤ 1)
    (hraw : ∀ k : ℕ, 0 < k → ∃ shift : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m (hm : P m) q (hq : q ∈ unitStrip) i j, i + j ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
      (∀ l, parameterGrading S base (v l) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → parameterGrading S (base + s + shift * k + 1) z ≤ R →
        (∀ l, parameterGrading S (base + s + shift * k + 1) (v l) ≤ R) →
        |((RF m hm).parameter i j q hq).D k z v| ≤
          B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            R ^ (((i + j + shift * k : ℕ) : ℝ) /
              (((s + shift * k : ℕ) : ℝ) + 1))) :
    CurrentJetDataOn S T cell P base ε f f₀ := by
  apply CurrentJetDataOn.of_positive_towers (S := S) (T := T) (cell := cell)
    (P := P) (base := base) (ε := ε) (f := f) (f₀ := f₀)
    hε hE hH RF hperiod h₀ hzero hlow
  intro k hk
  let orderData := hraw k hk
  let shift : ℕ := orderData.choose
  let hshift := orderData.choose_spec
  refine ⟨base + shift * k + 1, fun s => ?_⟩
  let boundData := hshift s
  let B : ℝ := boundData.choose
  have hB : 0 < B := boundData.choose_spec.1
  have hb := boundData.choose_spec.2
  refine ⟨B, hB, ?_⟩
  intro m hm q hq i j hij z hz v
  have hM : 0 ≤ B * T.E0 (T.sample (cell m)) ^ B *
      T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) :=
    mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _))
      (Real.rpow_nonneg (hH m) _)
  exact n04NegativeInverse_fractional_prefix_oneHigh (parameterGrading S) base
    shift s i j z (((RF m hm).parameter i j q hq).D k z) hM hij
    (hb m hm q hq i j hij z hz) v

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_of_positive_prefixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_of_positive_prefixes
