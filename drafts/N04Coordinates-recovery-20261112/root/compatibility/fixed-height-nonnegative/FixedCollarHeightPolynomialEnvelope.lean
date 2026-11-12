import ContinuousFlexibility.Analysis.OneSidedEndpointHeight
import ContinuousFlexibility.Analysis.OneSidedLogAngularJets
import ContinuousFlexibility.Analysis.EndpointHeightPolynomialEnvelope

/-!
# All finite height jets on the same low-order collar

The actual collar depends only on the matching order and its fixed
low-order envelope. The high-order raw envelope is introduced after the
polynomial constant and never changes that collar or the height field.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem exists_fixedCollar_positiveHeight_polynomial_envelope
    {ι : Type*} (n N : ℕ) {Cbase : ℝ} (hCbase : 0 ≤ Cbase) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {U H₀ ρ : ℝ},
      1 ≤ H₀ → H₀ ≤ U → 0 < ρ → ρ⁻¹ ≤ U →
      ∀ (q : ι → Bool → PolarPoint → ℝ) (a b : Bool → ℝ) (l r : ℝ),
      (∀ side, a side < b side) →
      (∀ i side, ContDiffOn ℝ ∞ (q i side)
        (Ioo (a side) (b side) ×ˢ (univ : Set ℝ))) →
      (∀ side, (if side then r else l) ∈ Icc (a side) (b side)) →
      (∀ i side θ, ContDiffAt ℝ ∞ (q i side) (if side then r else l, θ)) →
      (∀ i side p ∈ Ioo (a side) (b side) ×ˢ (univ : Set ℝ), 0 < q i side p) →
      (∀ i side θ, 0 < q i side (if side then r else l, θ)) →
      (∀ i side θ, q i side (if side then r else l, θ) ≤ H₀) →
      (∀ i side θ, (q i side (if side then r else l, θ))⁻¹ ≤ H₀) →
      (∀ i side k, 1 ≤ k → k ≤ n + N → ∀ θ,
        ‖iteratedFDeriv ℝ k (q i side) (if side then r else l, θ)‖ ≤ U) →
      (∀ i side j, 0 < j → j ≤ n → ∀ θ,
        |positiveHeightTaylorData l r (fun _ => 1) (q i) side j θ| ≤
          Cbase * H₀ ^ (2 * n + 1)) →
      let δ := oneSidedEndpointHeightWidth n ρ (Cbase * H₀ ^ (2 * n + 1))
      ∀ i k, k ≤ N → ∀ p : PolarPoint,
        ‖iteratedFDeriv ℝ k
          (positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (q i)) p‖ ≤
            C * U ^ ((2 * (n + N) + 1) * ((N + 1) * N + 2)) ∧
        ‖iteratedFDeriv ℝ k
          (fun x => (positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (q i) x)⁻¹) p‖ ≤
            C * U ^ ((2 * (n + N) + 1) * ((N + 1) * N + 2)) := by
  obtain ⟨Clog, hClog, hLog⟩ :=
    exists_oneSidedHeightTaylorData_angular_envelope (ι := ι) n N
  obtain ⟨CH, hCH, hHeight⟩ :=
    exists_positiveHeightTaylorInterpolation_polynomial_envelope n N
  let r₀ : ℕ := 2 * n + 1
  let R : ℕ := 2 * (n + N) + 1
  let D : ℕ := (N + 1) * N + 2
  let B : ℝ := 2 + ((n + 1 : ℕ) : ℝ) * (Cbase + 1)
  let K : ℝ := 1 + Clog + B
  have hCbase0 : 0 ≤ Cbase := hCbase
  have hClog0 : 0 ≤ Clog := zero_le_one.trans hClog
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hK : 1 ≤ K := by dsimp only [K]; linarith only [hClog0, hB]
  have hKlog : Clog ≤ K := by dsimp only [K]; linarith only [hB]
  have hKB : B ≤ K := by dsimp only [K]; linarith only [hClog0]
  refine ⟨CH * K ^ D, one_le_mul_of_one_le_of_one_le hCH (one_le_pow₀ hK), ?_⟩
  intro U H₀ ρ hH₀ hH₀U hρ hρinv q a b l r hab hq hend hroot hpos
    hposroot hupper hinverse hjets hlow
  let M₀ : ℝ := Cbase * H₀ ^ r₀
  let δ : ℝ := oneSidedEndpointHeightWidth n ρ M₀
  let M : ℝ := K * U ^ R
  have hU : 1 ≤ U := hH₀.trans hH₀U
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hH₀0 : 0 ≤ H₀ := zero_le_one.trans hH₀
  have hR : 1 ≤ R := by dsimp only [R]; omega
  have hr₀R : r₀ ≤ R := by dsimp only [r₀, R]; omega
  have hUpow : 1 ≤ U ^ R := one_le_pow₀ hU
  have hUU : U ≤ U ^ R := by
    simpa only [pow_one] using pow_le_pow_right₀ hU hR
  have hHpow : H₀ ^ r₀ ≤ U ^ R :=
    (pow_le_pow_left₀ hH₀0 hH₀U r₀).trans (pow_le_pow_right₀ hU hr₀R)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hK hUpow
  have hUM : U ≤ M := hUU.trans (le_mul_of_one_le_left (pow_nonneg hU0 R) hK)
  have hM₀ : 0 ≤ M₀ := mul_nonneg hCbase0 (pow_nonneg hH₀0 _)
  obtain ⟨hδ, hδρ, hδone, hδinv, hsmall⟩ :=
    oneSidedEndpointHeightWidth_margins n hρ hM₀
  have hwidth : δ⁻¹ ≤ M := by
    calc
      δ⁻¹ = ρ⁻¹ + 1 + ((n + 1 : ℕ) : ℝ) * (M₀ + 1) := hδinv
      _ ≤ U ^ R + U ^ R + ((n + 1 : ℕ) : ℝ) * (Cbase * U ^ R + U ^ R) :=
        add_le_add (add_le_add (hρinv.trans hUU) hUpow)
          (mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left hHpow hCbase0) hUpow)
            (Nat.cast_nonneg _))
      _ = B * U ^ R := by dsimp only [B]; ring
      _ ≤ K * U ^ R := mul_le_mul_of_nonneg_right hKB (pow_nonneg hU0 _)
  obtain ⟨hdata, hcoeff⟩ := hLog U hU q a b l r hab hq hend hroot hpos hposroot
    (fun i side θ => (hupper i side θ).trans hH₀U)
    (fun i side θ => (hinverse i side θ).trans hH₀U) hjets
  have hcoeffM (i : ι) (side : Bool) (j : ℕ) (hj : j ≤ n)
      (k : ℕ) (hk : k ≤ N) (θ : ℝ) :
      |iteratedDeriv k (positiveHeightTaylorData l r (fun _ => 1) (q i) side j) θ| ≤ M :=
    (hcoeff i side j hj k hk θ).trans
      (mul_le_mul_of_nonneg_right hKlog (pow_nonneg hU0 _))
  dsimp only
  intro i k hk p
  have hbound := hHeight hM hH₀ (hH₀U.trans hUM) hM₀ hδ hδone hwidth l r (q i)
    (hdata i) (hcoeffM i) (hposroot i) (hupper i) (hinverse i) (hlow i) hsmall k hk p
  have hcost : CH * M ^ D = (CH * K ^ D) * U ^ (R * D) := by
    dsimp only [M]
    rw [mul_pow, ← pow_mul]
    ring
  simpa only [hcost] using hbound

end ContinuousFlexibility.Analysis
