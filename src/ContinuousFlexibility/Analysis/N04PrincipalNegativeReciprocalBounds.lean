import ContinuousFlexibility.Analysis.N04PrincipalNegativeReciprocalOneHigh
import ContinuousFlexibility.Analysis.N04PrincipalWeightedPrefix

/-!
# Reciprocal closure of full mixed jet bounds

One uniform inverse-value envelope suffices. The source losses can
depend on the parameter order: finite-prefix interpolation fixes the
low order first, and reciprocal composition changes only the high loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {ι : Type*} {U : Set X} {Ω : Set PolarPoint}

def MixedJetRegularity.n04PrincipalNegative_inv
    {f : X → PolarPoint → ℝ} (F : MixedJetRegularity U Ω f)
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hnonzero : ∀ x ∈ U, ∀ q ∈ Ω, f x q ≠ 0) :
    MixedJetRegularity U Ω (fun x q => (f x q)⁻¹) :=
  F.scalarComp hU hΩ (isOpen_ne : IsOpen {t : ℝ | t ≠ 0})
    (fun t ht => (contDiffAt_inv ℝ ht).contDiffWithinAt) hnonzero

/-- Full reciprocal towers have unweighted one-high bounds whenever the
full original towers and reciprocal values have material envelopes. -/
theorem n04PrincipalNegative_reciprocal_weightedTower
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (oldBase requestedBase : ℕ) (E : ι → ℝ) (hE : ∀ m, 1 ≤ E m)
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (f : ι → X → PolarPoint → ℝ)
    (F : ∀ m, MixedJetRegularity U Ω (f m))
    (FI : ∀ m, MixedJetRegularity U Ω (fun x q => (f m x q)⁻¹))
    (hF : N04PrincipalWeightedTowerBounds p oldBase E (fun _ => 1) F)
    (hnonzero : ∀ m, ∀ x ∈ U, ∀ q ∈ Ω, f m x q ≠ 0)
    (hinverse : ∃ B : ℝ, 0 < B ∧ ∀ m, ∀ x ∈ U, ∀ q ∈ Ω,
      |(f m x q)⁻¹| ≤ B * E m ^ B) :
    ∃ base : ℕ, max oldBase requestedBase ≤ base ∧
      N04PrincipalWeightedTowerBounds p base E (fun _ => 1) FI := by
  classical
  have hprefix := n04Principal_weightedTower_prefix p hp hI oldBase requestedBase
    E (fun (_ : Fin 1) _ => 1) hE (fun _ _ => zero_le_one)
    (fun _ : Fin 1 => f) (fun _ : Fin 1 => F) (fun _ => hF)
  let base : ℕ := hprefix.choose
  have hbase : max oldBase requestedBase ≤ base := hprefix.choose_spec.1
  let BI : ℝ := hinverse.choose
  have hBI : 0 < BI := hinverse.choose_spec.1
  have hIb := hinverse.choose_spec.2
  refine ⟨base, hbase, fun k => ?_⟩
  have hprefK := hprefix.choose_spec.2 k
  let shift : ℕ := hprefK.choose
  refine ⟨base + shift * k + 1, fun s => ?_⟩
  have hprefS := hprefK.choose_spec s
  let C : ℝ := hprefS.choose
  let A : ℝ := hprefS.choose_spec.choose
  have hC : 1 ≤ C := hprefS.choose_spec.choose_spec.1
  have hA : 0 ≤ A := hprefS.choose_spec.choose_spec.2.1
  have hraw := hprefS.choose_spec.choose_spec.2.2
  let C1 : ℝ := 1 + C + BI
  let A1 : ℝ := max A BI
  have hC1 : 1 ≤ C1 := by dsimp only [C1]; linarith
  have hCC1 : C ≤ C1 := by dsimp only [C1]; linarith
  have hBIC1 : BI ≤ C1 := by dsimp only [C1]; linarith
  have hA1 : 0 ≤ A1 := hA.trans (le_max_left _ _)
  have hAI : A ≤ A1 := le_max_left _ _
  have hBIA : BI ≤ A1 := le_max_right _ _
  have hone := n04PrincipalNegative_reciprocal_oneHigh (X := X) k s shift
  let CB : ℝ := hone.choose
  let d : ℕ := hone.choose_spec.choose
  have hCB : 1 ≤ CB := hone.choose_spec.choose_spec.1
  have hb := hone.choose_spec.choose_spec.2.2
  let Q : ℝ := A1 * (d : ℝ)
  let K : ℝ := CB * C1 ^ d
  let B : ℝ := 1 + K + Q
  have hQ : 0 ≤ Q := mul_nonneg hA1 (Nat.cast_nonneg _)
  have hK : 0 ≤ K := mul_nonneg (zero_le_one.trans hCB)
    (pow_nonneg (zero_le_one.trans hC1) _)
  have hB : 0 < B := by dsimp only [B]; linarith
  have hKB : K ≤ B := by dsimp only [B]; linarith
  have hQB : Q ≤ B := by dsimp only [B]; linarith
  refine ⟨B, hB, ?_⟩
  intro m a b hab q hq x hx hlow v
  have he0 : 0 ≤ E m := zero_le_one.trans (hE m)
  let M : ℝ := C1 * E m ^ A1
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hC1
    (Real.one_le_rpow (hE m) hA1)
  have hsourceCoeff : C * E m ^ A ≤ M := mul_le_mul hCC1
    (Real.rpow_le_rpow_of_exponent_le (hE m) hAI)
    (Real.rpow_nonneg he0 _) (zero_le_one.trans hC1)
  have hinv (y : X) (hy : y ∈ U) (z : PolarPoint) (hz : z ∈ Ω) :
      |(f m y z)⁻¹| ≤ M := (hIb m y hy z hz).trans
    (mul_le_mul hBIC1 (Real.rpow_le_rpow_of_exponent_le (hE m) hBIA)
      (Real.rpow_nonneg he0 _) (zero_le_one.trans hC1))
  have hsource (j : ℕ) (hj : j ≤ k) (u w : ℕ) (huw : u + w ≤ s)
      (z : PolarPoint) (hz : z ∈ Ω) (y : X) (hy : y ∈ U) (hylo : p base y ≤ 1)
      (vv : Fin j → X) (hvv : ∀ t, p base (vv t) ≤ 1)
      (R : ℝ) (hR : 1 ≤ R)
      (hyR : p (base + s + shift * k + 1) y ≤ R)
      (hvvR : ∀ t, p (base + s + shift * k + 1) (vv t) ≤ R) :
      ‖((F m).parameter u w z hz).D j y vv‖ ≤
        M * R ^ (((u + w + shift * j : ℕ) : ℝ) /
          (((s + shift * k : ℕ) : ℝ) + 1)) := by
    have hh := hraw (0 : Fin 1) m j hj u w huw z hz y hy hylo vv hvv R hR hyR hvvR
    have hh' : ‖((F m).parameter u w z hz).D j y vv‖ ≤
        (C * E m ^ A) * R ^ (((u + w + shift * j : ℕ) : ℝ) /
          (((s + shift * k : ℕ) : ℝ) + 1)) := by
      simpa only [mul_one] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_right hsourceCoeff
      (Real.rpow_nonneg (zero_le_one.trans hR) _))
  have hh := hb p base (base + s + shift * k + 1) U hU Ω hΩ (f m) (F m)
    (hnonzero m) M hM hinv hsource a b hab q hq ((FI m).parameter a b q hq)
    x hx hlow v
  have hMpow : CB * M ^ d = K * E m ^ Q := by
    dsimp only [M, K, Q]
    rw [mul_pow, ← Real.rpow_mul_natCast he0]
    ring
  rw [hMpow] at hh
  have hcoef : K * E m ^ Q ≤ B * E m ^ B := mul_le_mul hKB
    (Real.rpow_le_rpow_of_exponent_le (hE m) hQB)
    (Real.rpow_nonneg he0 _) hB.le
  have hh' := hh.trans (mul_le_mul_of_nonneg_right hcoef
    (oneHighVariationWeight_nonneg p base (base + s + shift * k + 1) x v))
  have hhigh : base + s + shift * k + 1 = s + (base + shift * k + 1) := by omega
  simpa only [hhigh, mul_one] using hh'

end ContinuousFlexibility.Analysis
