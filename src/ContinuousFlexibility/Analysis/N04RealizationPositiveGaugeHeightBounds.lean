import ContinuousFlexibility.Analysis.N04RealizationPositiveHeightParameterPrefix
import ContinuousFlexibility.Analysis.N04RealizationPositivePulledHeight
import ContinuousFlexibility.Analysis.WholePositiveReferenceGauge
import ContinuousFlexibility.Analysis.PositiveReferenceCylinder

/-!
# Actual positive pulled-height bounds in the supplied reference gauge

The only current derivative inputs are the original finite root-axis
towers. The existing Taylor-height theorem estimates Q and its reciprocal.
The existing fixed radial product theorem then applies to the literal
reference-gauged height at its literal inverse point. Fixed reference
height jets and radial chain coefficients contribute two polynomial
factors; the parameter height gain and interpolation order are retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04Realization_positiveGaugeHeight_shifted_parameter_bound
    (n k a b : ℕ) (RH : ℝ) :
    ∃ B : ℝ, ∃ d : ℕ, 1 ≤ B ∧ 1 ≤ d ∧
      ∀ (U : Set X), IsOpen U → ∀ l r δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ h : X → Bool → PolarPoint → ℝ,
      (∀ y ∈ U, ∀ side θ, ContDiffAt ℝ ∞ (h y side) (if side then r else l, θ)) →
      (∀ y ∈ U, ∀ side θ, 0 < h y side (if side then r else l, θ)) →
      ∀ JH : ∀ side, ∀ j : ℕ, j ≤ n → ∀ u θ,
        SmoothDirections U (fun y => iteratedDeriv u
          (radialBoundaryJet (h y side) (if side then r else l) j) θ),
      ∀ Y H₀ : ℝ → ℝ, ContDiff ℝ ∞ (Function.invFun Y) →
        ContDiff ℝ ∞ H₀ → (∀ t, 0 < H₀ t) →
      ∀ τ σ : X → PolarPoint → PolarPoint,
        (∀ y ∈ U, Function.LeftInverse (σ y) (τ y)) →
      ∀ x ∈ U, ∀ (P : X → Prop) (v : Fin k → X), (∀ i, P (v i)) →
      ∀ W M R : ℝ, 0 ≤ W → W ≤ RH → 1 ≤ M → 1 ≤ R → δ⁻¹ ≤ M →
      ∀ budget shift : ℕ,
      (∀ side θ, (h x side (if side then r else l, θ))⁻¹ ≤ M) →
      (∀ side, ∀ j : ℕ, ∀ hj : j ≤ n, ∀ e : ℕ, e ≤ k →
        ∀ u : ℕ, u ≤ a + b → ∀ θ, ∀ z : Fin e → X, (∀ i, P (z i)) →
        ‖(JH side j hj u θ).D e x z‖ ≤ M * parameterHeightWeight W e *
          R ^ (((u + shift * e : ℕ) : ℝ) / ((budget : ℝ) + 1))) →
      ∀ Mlow : ℝ, 0 ≤ Mlow →
      (∀ side j, 0 < j → j ≤ n → ∀ θ,
        |positiveHeightTaylorData l r (fun _ => 1) (h x) side j θ| ≤ Mlow) →
      ((n + 1 : ℕ) : ℝ) * Mlow * δ ≤ 1 →
      ∀ inv : Bool, ∀ q ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ),
      (∀ u w : ℕ, u + w ≤ a + b →
        |mixedDerivative u w
          (fun p : PolarPoint => if inv then (H₀ p.1)⁻¹ else H₀ p.1)
          (Function.invFun Y q.1, q.2)| ≤ M) →
      (∑ i : Fin (a + 1), |radialChainCoefficient (Function.invFun Y) a i q.1|) ≤ M →
      ∀ J : SmoothDirections U (fun y => mixedDerivative a b
        (fun p => if inv then
          (wholePositiveReferenceGaugeHeight (fun z => H₀ z.1) (σ y)
            (positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y))
            (wholePositiveReferenceGaugeInverse (τ y) (positiveReferenceCylinderInverse Y) p))⁻¹
          else wholePositiveReferenceGaugeHeight (fun z => H₀ z.1) (σ y)
            (positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y))
            (wholePositiveReferenceGaugeInverse (τ y) (positiveReferenceCylinderInverse Y) p)) q),
      ‖J.D k x v‖ ≤ B * M ^ d * parameterHeightWeight W k *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := by
  classical
  let I : Type := Fin (a + b + 1) × Fin (a + b + 1)
  choose c d hc hd hb using fun i : I =>
    n04Realization_positiveHeightTaylor_shifted_parameter_bound (X := X)
      n k i.1.val i.2.val RH
  let B₀ : ℝ := 1 + ∑ i : I, c i
  let D₀ : ℕ := 1 + ∑ i : I, d i
  have hB₀ : 1 ≤ B₀ := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun i _ => zero_le_one.trans (hc i)))
  have hcB (i : I) : c i ≤ B₀ :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hc j)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hdD (i : I) : d i ≤ D₀ :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)).trans
      (Nat.le_add_left _ _)
  refine ⟨(2 : ℝ) ^ (a + b) * B₀, D₀ + 2,
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hB₀,
    by omega, ?_⟩
  intro U hU l r δ hδ hδ1 h hroot hpos JH Y H₀ hχ hH₀ hH₀pos τ σ hστ
    x hx P v hv W M R hW hWR hM hR hδM budget shift hinv hraw
    Mlow hMlow hTaylor hsmall inv q hq hfixed hchain
  let Q : X → PolarPoint → ℝ :=
    fun y => positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y)
  let height : X → PolarPoint → ℝ :=
    fun y => wholePositiveReferenceGaugeHeight (fun p => H₀ p.1) (σ y) (Q y)
  let inverse : X → PolarPoint → PolarPoint :=
    fun y => wholePositiveReferenceGaugeInverse (τ y) (positiveReferenceCylinderInverse Y)
  let g : X → PolarPoint → ℝ :=
    fun y p => if inv then (height y (inverse y p))⁻¹ else height y (inverse y p)
  let f : X → PolarPoint → ℝ := fun y p => if !inv then (Q y p)⁻¹ else Q y p
  let hfix : PolarPoint → ℝ := fun p => if inv then (H₀ p.1)⁻¹ else H₀ p.1
  let RF : MixedJetRegularity U univ f :=
    n04Realization_positiveHeightTaylor_mixedJetRegularity hU n l r δ
      h hroot hpos JH (!inv)
  have hhfix : ContDiffOn ℝ ∞ hfix univ := by
    cases inv with
    | false => exact (hH₀.comp contDiff_fst).contDiffOn
    | true => exact (hH₀.comp contDiff_fst).contDiffOn.inv
        (fun p _ => (hH₀pos p.1).ne')
  have hmap : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ θ : ℝ,
      (Function.invFun Y r, θ) ∈ (univ : Set PolarPoint) :=
    fun _ _ _ => mem_univ _
  have heq : ∀ y ∈ U, EqOn (g y)
      (fun p => hfix (Function.invFun Y p.1, p.2) *
        f y (Function.invFun Y p.1, p.2)) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
    intro y hy p _hp
    have hpull := n04Realization_positive_pulledHeight_identity
      (fun z => H₀ z.1) Q height σ τ inverse (Function.invFun Y) hστ
      (fun y _ p => wholePositiveReferenceGaugeHeight_eq _ _ _ p)
      (fun y _ p => by
        simp only [inverse, wholePositiveReferenceGaugeInverse,
          Function.comp_apply, positiveReferenceCylinderInverse]) hy p
    cases inv with
    | false => exact hpull.1
    | true => exact hpull.2
  intro J
  let Jg : SmoothDirections U (fun y => mixedDerivative a b (g y) q) := J
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let α : ℝ := ((shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)
  let ρ : ℝ := R ^ ((((a + b : ℕ) : ℝ) + 1) / ((budget : ℝ) + 1))
  have hρ : 1 ≤ ρ := Real.one_le_rpow hR (by positivity)
  have hρpow (u : ℕ) :
      ρ ^ ((u : ℝ) / (((a + b : ℕ) : ℝ) + 1)) =
        R ^ ((u : ℝ) / ((budget : ℝ) + 1)) :=
    n04Realization_rpow_change_budget hRpos.le (by positivity) _ _
  let M₀ : ℝ := B₀ * M ^ D₀ * parameterHeightWeight W k * R ^ α
  have hM₀ : 0 ≤ M₀ := mul_nonneg
    (mul_nonneg (mul_nonneg (zero_le_one.trans hB₀) (pow_nonneg (zero_le_one.trans hM) _))
      (parameterHeightWeight_nonneg hW k)) (Real.rpow_nonneg hRpos.le _)
  have hexp (u : ℕ) : (((u + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) =
      α + (u : ℝ) / ((budget : ℝ) + 1) := by
    dsimp only [α]
    push_cast
    ring
  have hsource (u w : ℕ) (huw : u + w ≤ a + b) :
      |(RF.parameter u w (Function.invFun Y q.1, q.2) (mem_univ _)).D k x v| ≤
        M₀ * ρ ^ (((u + w : ℕ) : ℝ) / (((a + b : ℕ) : ℝ) + 1)) := by
    let i : I := (⟨u, by omega⟩, ⟨w, by omega⟩)
    have ht := hb i U hU l r δ hδ hδ1 h hroot hpos JH x hx P v hv
      W M R hW hWR hM hR hδM budget shift hinv
      (fun side j hj e he t ht θ z hz =>
        hraw side j hj e he t (ht.trans huw) θ z hz)
      Mlow hMlow hTaylor hsmall (!inv) (Function.invFun Y q.1, q.2)
      (RF.parameter u w (Function.invFun Y q.1, q.2) (mem_univ _))
    have hcoef : c i * M ^ d i ≤ B₀ * M ^ D₀ :=
      mul_le_mul (hcB i) (pow_le_pow_right₀ hM (hdD i))
        (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hB₀)
    calc
      _ ≤ c i * M ^ d i * parameterHeightWeight W k *
          R ^ (((u + w + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := by
        simpa only [Real.norm_eq_abs, i] using ht
      _ ≤ B₀ * M ^ D₀ * parameterHeightWeight W k *
          R ^ (((u + w + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (parameterHeightWeight_nonneg hW k))
          (Real.rpow_nonneg hRpos.le _)
      _ = _ := by
        rw [hρpow, hexp, Real.rpow_add hRpos α]
        dsimp only [M₀]
        ring
  have hproduct := n04Realization_fixedRadialProduct_parameterJet_bound
    (χ := Function.invFun Y) (h := hfix) (f := f) (g := g)
    hU isOpen_Ioo isOpen_univ hχ hhfix RF hmap heq
    a b (a + b) k le_rfl hq Jg hx v (zero_le_one.trans hM) hM₀ hρ hfixed hsource
  have hrest : 0 ≤ (2 : ℝ) ^ (a + b) * M * M₀ :=
    mul_nonneg (mul_nonneg (by positivity) (zero_le_one.trans hM)) hM₀
  calc
    ‖J.D k x v‖ = |Jg.D k x v| := Real.norm_eq_abs _
    _ ≤ (∑ i : Fin (a + 1), |radialChainCoefficient (Function.invFun Y) a i q.1|) *
        ((2 : ℝ) ^ (a + b) * M * M₀) *
          ρ ^ (((a + b : ℕ) : ℝ) / (((a + b : ℕ) : ℝ) + 1)) := hproduct
    _ ≤ M * ((2 : ℝ) ^ (a + b) * M * M₀) *
          ρ ^ (((a + b : ℕ) : ℝ) / (((a + b : ℕ) : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hchain hrest)
        (Real.rpow_nonneg (zero_le_one.trans hρ) _)
    _ = _ := by
      rw [hρpow, hexp, Real.rpow_add hRpos α, pow_add M D₀ 2, pow_two]
      dsimp only [M₀]
      ring

end ContinuousFlexibility.Analysis
