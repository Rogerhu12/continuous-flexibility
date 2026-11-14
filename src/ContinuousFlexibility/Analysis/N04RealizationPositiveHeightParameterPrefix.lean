import ContinuousFlexibility.Analysis.N04RealizationPositiveHeightTaylorBounds
import ContinuousFlexibility.Analysis.N04RealizationParameterRescale

/-!+# The actual positive height with a finite parameter interpolation cost

The raw endpoint traces carry the cost assigned to each parameter slot
by fixed-base interpolation. Rescaling those slots removes their cost
before the actual logarithmic Taylor and exponential construction. The
genuine output multilinear map restores only the total parameter order.
The fixed collar, low order, and parameter domain are unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04Realization_positiveHeightTaylor_shifted_parameter_bound
    (n k a b : ℕ) (RH : ℝ) :
    ∃ B : ℝ, ∃ d : ℕ, 1 ≤ B ∧ 1 ≤ d ∧
      ∀ (U : Set X), IsOpen U → ∀ l r δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ h : X → Bool → PolarPoint → ℝ,
      (∀ y ∈ U, ∀ side θ, ContDiffAt ℝ ∞ (h y side) (if side then r else l, θ)) →
      (∀ y ∈ U, ∀ side θ, 0 < h y side (if side then r else l, θ)) →
      ∀ JH : ∀ side, ∀ j : ℕ, j ≤ n → ∀ u θ,
        SmoothDirections U (fun y => iteratedDeriv u
          (radialBoundaryJet (h y side) (if side then r else l) j) θ),
      ∀ x ∈ U, ∀ (P : X → Prop) (v : Fin k → X), (∀ i, P (v i)) →
      ∀ H M R : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ M → 1 ≤ R → δ⁻¹ ≤ M →
      ∀ s shift : ℕ,
      (∀ side θ, (h x side (if side then r else l, θ))⁻¹ ≤ M) →
      (∀ side, ∀ j : ℕ, ∀ hj : j ≤ n, ∀ e : ℕ, e ≤ k →
        ∀ u : ℕ, u ≤ a + b → ∀ θ, ∀ z : Fin e → X, (∀ i, P (z i)) →
        ‖(JH side j hj u θ).D e x z‖ ≤ M * parameterHeightWeight H e *
          R ^ (((u + shift * e : ℕ) : ℝ) / ((s : ℝ) + 1))) →
      ∀ Mlow : ℝ, 0 ≤ Mlow →
      (∀ side j, 0 < j → j ≤ n → ∀ θ,
        |positiveHeightTaylorData l r (fun _ => 1) (h x) side j θ| ≤ Mlow) →
      ((n + 1 : ℕ) : ℝ) * Mlow * δ ≤ 1 →
      ∀ inv : Bool, ∀ q : PolarPoint, ∀ J : SmoothDirections U
        (fun y => mixedDerivative a b (fun p => if inv then
          (positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y) p)⁻¹
          else positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y) p) q),
      ‖J.D k x v‖ ≤ B * M ^ d * parameterHeightWeight H k *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  obtain ⟨B, d, hB, hd, hb⟩ :=
    n04Realization_positiveHeightTaylor_parameter_bound (X := X) n k a b RH
  refine ⟨B, d, hB, hd, ?_⟩
  intro U hU l r δ hδ hδ1 h hroot hpos JH x hx P v hv H M R hH hHR hM hR hδM
    s shift hinv hraw Mlow hMlow hlow hsmall inv q J
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let α : ℝ := (shift : ℝ) / ((s : ℝ) + 1)
  let t : ℝ := R ^ (1 / ((s : ℝ) + 1))
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have htpow (u : ℕ) : t ^ u = R ^ ((u : ℝ) / ((s : ℝ) + 1)) := by
    dsimp only [t]
    rw [← Real.rpow_mul_natCast hRpos.le]
    congr 1
    ring
  have hcancel (w : X) : R ^ α • (R ^ (-α) • w) = w := by
    rw [smul_smul, ← Real.rpow_add hRpos, add_neg_cancel, Real.rpow_zero, one_smul]
  have hcancel' (w : X) : R ^ (-α) • (R ^ α • w) = w := by
    rw [smul_smul, ← Real.rpow_add hRpos, neg_add_cancel, Real.rpow_zero, one_smul]
  let P' : X → Prop := fun w => P (R ^ α • w)
  let v' : Fin k → X := fun i => R ^ (-α) • v i
  have hv' (i : Fin k) : P' (v' i) := by
    change P (R ^ α • (R ^ (-α) • v i))
    rw [hcancel]
    exact hv i
  have hraw' (side : Bool) (j : ℕ) (hj : j ≤ n) (e : ℕ) (he : e ≤ k)
      (u : ℕ) (hu : u ≤ a + b) (θ : ℝ) (z : Fin e → X) (hz : ∀ i, P' (z i)) :
      ‖(JH side j hj u θ).D e x z‖ ≤ M * parameterHeightWeight H e * t ^ u := by
    let z₀ : Fin e → X := fun i => R ^ α • z i
    have hz₀ (i : Fin e) : P (z₀ i) := hz i
    have hr := hraw side j hj e he u hu θ z₀ hz₀
    have hexp : (((u + shift * e : ℕ) : ℝ) / ((s : ℝ) + 1)) =
        (u : ℝ) / ((s : ℝ) + 1) + α * (e : ℝ) := by
      dsimp only [α]
      push_cast
      ring
    rw [hexp] at hr
    have hs := n04Realization_parameter_rescale_bound ((JH side j hj u θ).D e x)
      z₀ hRpos α ((u : ℝ) / ((s : ℝ) + 1)) (M * parameterHeightWeight H e) hr
    have hz_eq : (fun i => R ^ (-α) • z₀ i) = z := by
      funext i
      exact hcancel' (z i)
    rw [hz_eq] at hs
    rw [htpow]
    exact hs
  have hs := hb U hU l r δ hδ hδ1 h hroot hpos JH x hx P' v' hv'
    H M t hH hHR hM ht hδM hinv hraw' Mlow hMlow hlow hsmall inv q J
  rw [htpow] at hs
  have hout := n04Realization_parameter_unscale_bound (J.D k x) v hRpos α
    (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))
    (B * M ^ d * parameterHeightWeight H k) hs
  have hexp : (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) + α * (k : ℝ) =
      (((a + b + shift * k : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
    dsimp only [α]
    push_cast
    ring
  rw [hexp] at hout
  exact hout

end ContinuousFlexibility.Analysis
