module

public import ContinuousFlexibility.Analysis.N04RealizationFixedRadialPullback
public import ContinuousFlexibility.Analysis.N04RealizationFixedSpatialProduct
public import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus

/-!
# The actual positive pulled height in the fixed reference gauge

The relative transport cancels against its actual inverse. The pulled
height and its reciprocal are therefore fixed radial pullbacks of a
fixed reference multiplier times the raw relative height ratio or its
reciprocal. No parameter-dependent spatial composition is introduced.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {U : Set X} {I : Set ℝ} {Ω : Set PolarPoint}

/-- The same actual height and inverse have these two fixed-gauge
expressions, including their prescribed reciprocal values. -/
theorem n04Realization_positive_pulledHeight_identity
    (h₀ : PolarPoint → ℝ) (Q height : X → PolarPoint → ℝ)
    (σ τ inverse : X → PolarPoint → PolarPoint) (χ : ℝ → ℝ)
    (hστ : ∀ x ∈ U, Function.LeftInverse (σ x) (τ x))
    (hheight : ∀ x ∈ U, ∀ p, height x p = h₀ (σ x p) / Q x (σ x p))
    (hinverse : ∀ x ∈ U, ∀ q, inverse x q = τ x (χ q.1, q.2))
    {x : X} (hx : x ∈ U) (q : PolarPoint) :
    height x (inverse x q) = h₀ (χ q.1, q.2) * (Q x (χ q.1, q.2))⁻¹ ∧
      (height x (inverse x q))⁻¹ = (h₀ (χ q.1, q.2))⁻¹ * Q x (χ q.1, q.2) := by
  rw [hinverse x hx q, hheight x hx, hστ x hx]
  constructor
  · exact div_eq_mul_inv _ _
  · rw [inv_div, div_eq_mul_inv, mul_comm]

/-- Positivity gives the genuine mixed reciprocal tower on the same
parameter set and spatial domain. No reciprocal jet is postulated. -/
def n04Realization_mixedJetRegularity_positiveReciprocal
    {Q : X → PolarPoint → ℝ} (hU : IsOpen U) (hΩ : IsOpen Ω)
    (RQ : MixedJetRegularity U Ω Q)
    (hQ : ∀ x ∈ U, ∀ q ∈ Ω, 0 < Q x q) :
    MixedJetRegularity U Ω (fun x q => (Q x q)⁻¹) :=
  RQ.scalarComp hU hΩ isOpen_Ioi
    (contDiffOn_id.inv (fun t (ht : t ∈ Ioi (0 : ℝ)) => ht.ne'))
    (fun x hx q hq => hQ x hx q hq)

/-- Identify a fixed spatial product pullback with the actual field
before constructing its mixed parameter tower. -/
def n04Realization_mixedJetRegularity_fixedRadialProduct
    {χ : ℝ → ℝ} {h : PolarPoint → ℝ} {f g : X → PolarPoint → ℝ}
    (hU : IsOpen U) (hI : IsOpen I) (hΩ : IsOpen Ω)
    (hχ : ContDiff ℝ ∞ χ) (hh : ContDiffOn ℝ ∞ h Ω)
    (RF : MixedJetRegularity U Ω f)
    (hmap : ∀ r ∈ I, ∀ θ : ℝ, (χ r, θ) ∈ Ω)
    (heq : ∀ x ∈ U, EqOn (g x)
      (fun q => h (χ q.1, q.2) * f x (χ q.1, q.2)) (I ×ˢ (univ : Set ℝ))) :
    MixedJetRegularity U (I ×ˢ (univ : Set ℝ)) g := by
  let RP := (n04Realization_mixedJetRegularity_fixedSpatial hU hh).mul RF hU hΩ
  let RC := n04Realization_mixedJetRegularity_fixedRadial hU hI hΩ hχ RP hmap
  exact RC.congr (hI.prod isOpen_univ)
    (fun x hx => (RC.spatial x hx).congr (heq x hx))
    (fun x hx q hq => (heq x hx hq).symm)

/-- Both actual pulled-height towers are obtained from the raw positive
ratio tower, the fixed reference height, and the same inverse identity. -/
def n04Realization_positive_pulledHeight_regularity
    {h₀ : PolarPoint → ℝ} {Q height : X → PolarPoint → ℝ}
    {σ τ inverse : X → PolarPoint → PolarPoint} {χ : ℝ → ℝ}
    (hU : IsOpen U) (hI : IsOpen I) (hΩ : IsOpen Ω)
    (hχ : ContDiff ℝ ∞ χ) (hh₀ : ContDiffOn ℝ ∞ h₀ Ω)
    (hh₀ne : ∀ q ∈ Ω, h₀ q ≠ 0)
    (RQ : MixedJetRegularity U Ω Q)
    (hQ : ∀ x ∈ U, ∀ q ∈ Ω, 0 < Q x q)
    (hmap : ∀ r ∈ I, ∀ θ : ℝ, (χ r, θ) ∈ Ω)
    (hστ : ∀ x ∈ U, Function.LeftInverse (σ x) (τ x))
    (hheight : ∀ x ∈ U, ∀ p, height x p = h₀ (σ x p) / Q x (σ x p))
    (hinverse : ∀ x ∈ U, ∀ q, inverse x q = τ x (χ q.1, q.2)) :
    MixedJetRegularity U (I ×ˢ (univ : Set ℝ)) (fun x q => height x (inverse x q)) ×
      MixedJetRegularity U (I ×ˢ (univ : Set ℝ))
        (fun x q => (height x (inverse x q))⁻¹) := by
  let RQinv := n04Realization_mixedJetRegularity_positiveReciprocal hU hΩ RQ hQ
  have heq (x : X) (hx : x ∈ U) (q : PolarPoint) :=
    n04Realization_positive_pulledHeight_identity h₀ Q height σ τ inverse χ
      hστ hheight hinverse hx q
  exact ⟨n04Realization_mixedJetRegularity_fixedRadialProduct hU hI hΩ hχ hh₀ RQinv hmap
      (fun x hx q _ => (heq x hx q).1),
    n04Realization_mixedJetRegularity_fixedRadialProduct hU hI hΩ hχ
      (hh₀.inv hh₀ne) RQ hmap (fun x hx q _ => (heq x hx q).2)⟩

/-- Raw finite-prefix bounds pass to the same actual fixed-gauge field.
The fixed reference costs are explicit; the current height gain in `M`
is unchanged, as are the spatial exponent and parameter domain. -/
theorem n04Realization_fixedRadialProduct_parameterJet_bound
    {χ : ℝ → ℝ} {h : PolarPoint → ℝ} {f g : X → PolarPoint → ℝ}
    (hU : IsOpen U) (hI : IsOpen I) (hΩ : IsOpen Ω)
    (hχ : ContDiff ℝ ∞ χ) (hh : ContDiffOn ℝ ∞ h Ω)
    (RF : MixedJetRegularity U Ω f)
    (hmap : ∀ r ∈ I, ∀ θ : ℝ, (χ r, θ) ∈ Ω)
    (heq : ∀ x ∈ U, EqOn (g x)
      (fun q => h (χ q.1, q.2) * f x (χ q.1, q.2)) (I ×ˢ (univ : Set ℝ)))
    (a b s k : ℕ) (hab : a + b ≤ s) {q : PolarPoint}
    (hq : q ∈ I ×ˢ (univ : Set ℝ))
    (J : SmoothDirections U (fun x => mixedDerivative a b (g x) q))
    {x : X} (hx : x ∈ U) (v : Fin k → X)
    {A M R : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hfixed : ∀ u w : ℕ, u + w ≤ s → |mixedDerivative u w h (χ q.1, q.2)| ≤ A)
    (hbound : ∀ u w : ℕ, u + w ≤ s →
      |(RF.parameter u w (χ q.1, q.2) (hmap q.1 hq.1 q.2)).D k x v| ≤
        M * R ^ (((u + w : ℕ) : ℝ) / ((s : ℝ) + 1))) :
    |J.D k x v| ≤ (∑ i : Fin (a + 1), |radialChainCoefficient χ a i q.1|) *
      ((2 : ℝ) ^ s * A * M) * R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  let RP := (n04Realization_mixedJetRegularity_fixedSpatial hU hh).mul RF hU hΩ
  let JC := J.congr (fun y hy =>
    n07a_mixedDerivative_eqOn (hI.prod isOpen_univ) (heq y hy) a b hq)
  have hmajor : 0 ≤ (2 : ℝ) ^ s * A * M :=
    mul_nonneg (mul_nonneg (by positivity) hA) hM
  exact n04Realization_fixedRadial_parameterJet_bound hI hΩ hχ RP hmap a b s k hq JC
    hx v hmajor hR (fun i => by
      have hi : i.val + b ≤ s := by have := i.isLt; omega
      have hb := n04Realization_fixedSpatialProduct_parameterJet_bound hΩ hh RF
        i.val b s k hi (hmap q.1 hq.1 q.2)
        (RP.parameter i.val b (χ q.1, q.2) (hmap q.1 hq.1 q.2))
        hx v hA hM hR hfixed hbound
      have hpow : (2 : ℝ) ^ (i.val + b) ≤ (2 : ℝ) ^ s :=
        pow_le_pow_right₀ (by norm_num) hi
      have hrest : 0 ≤ A * M * R ^ (((i.val + b : ℕ) : ℝ) / ((s : ℝ) + 1)) :=
        mul_nonneg (mul_nonneg hA hM) (Real.rpow_nonneg (zero_le_one.trans hR) _)
      exact hb.trans (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hpow hrest))

end ContinuousFlexibility.Analysis
