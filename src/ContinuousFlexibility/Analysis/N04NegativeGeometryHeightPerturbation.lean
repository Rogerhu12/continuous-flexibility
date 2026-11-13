import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit

/-!
# Interior height freedom in the admissible positive transport

`WholePositiveTransportMatching` is a condition on a single state. It is
preserved by multiplying its height by a positive smooth factor which is
one near the two endpoints and the fixed middle. No regularity of this
factor with respect to a state parameter is part of the condition.

The last two lemmas identify the pulled positive height exactly. In this
expression the relative transport and its inverse cancel; an interior
height multiplier therefore remains visible after pulling back.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped Topology ContDiff

/-- Multiplicative interior height changes preserve every matching
condition. The original coordinate transport and all endpoint jets are
unchanged. The two-sided height bound is multiplied by the corresponding
bound of the factor. -/
theorem n04NegativeGeometry_matching_mul_height
    {n : ℕ} {F : Bool → PolarPoint → PolarPoint} {q : Bool → PolarPoint → ℝ}
    {τ σ : PolarPoint → PolarPoint} {Q φ : PolarPoint → ℝ}
    {l r c d J H B : ℝ}
    (h : WholePositiveTransportMatching n F q τ σ Q l r c d J H)
    (hφ : ContDiff ℝ ∞ φ) (hφpos : ∀ p, 0 < φ p)
    (hφbound : ∀ p, φ p ≤ B ∧ (φ p)⁻¹ ≤ B)
    (hφend : ∀ (side : Bool) θ,
      φ =ᶠ[𝓝 (if side then r else l, θ)] (fun _ => (1 : ℝ)))
    (hφperiod : ∀ x θ, φ (x, θ + Real.pi) = φ (x, θ))
    (hφeven : ∀ x θ, φ (x, -θ) = φ (x, θ))
    (hφmiddle : ∀ x ∈ Icc c d, ∀ θ,
      φ =ᶠ[𝓝 (x, θ)] (fun _ => (1 : ℝ))) :
    WholePositiveTransportMatching n F q τ σ (fun p => Q p * φ p)
      l r c d J (H * B) := by
  have hH : 0 ≤ H :=
    (h.height_positive (0, 0)).le.trans (h.height_bound (0, 0)).1
  refine {
    geometry := h.geometry
    height_smooth := h.height_smooth.mul hφ
    height_positive := fun p => mul_pos (h.height_positive p) (hφpos p)
    coordinate_jets := h.coordinate_jets
    height_jets := ?_
    height_period := ?_
    height_even := ?_
    height_middle_germ := ?_
    height_bound := ?_ }
  · intro side k hk θ
    have he : (fun p => Q p * φ p) =ᶠ[𝓝 (if side then r else l, θ)] Q := by
      filter_upwards [hφend side θ] with p hp
      exact (congrArg (fun t : ℝ => Q p * t) hp).trans (mul_one (Q p))
    exact ((he.iteratedFDeriv ℝ k).self_of_nhds).trans (h.height_jets side k hk θ)
  · intro x θ
    rw [h.height_period, hφperiod]
  · intro x θ
    rw [h.height_even, hφeven]
  · intro x hx θ
    filter_upwards [h.height_middle_germ x hx θ, hφmiddle x hx θ] with p hp hpφ
    change Q p * φ p = 1
    rw [hp, hpφ, mul_one]
  · intro p
    refine ⟨mul_le_mul (h.height_bound p).1 (hφbound p).1 (hφpos p).le hH, ?_⟩
    rw [mul_inv_rev, mul_comm (φ p)⁻¹ (Q p)⁻¹]
    exact mul_le_mul (h.height_bound p).2 (hφbound p).2
      (inv_nonneg.mpr (hφpos p).le) hH

/-- A fixed radial multiplier is automatically periodic and even. The
remaining hypotheses are scalar smoothness, positivity, bounds and the
three prescribed germs. -/
theorem n04NegativeGeometry_matching_mul_radial_height
    {n : ℕ} {F : Bool → PolarPoint → PolarPoint} {q : Bool → PolarPoint → ℝ}
    {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ} {φ : ℝ → ℝ}
    {l r c d J H B : ℝ}
    (h : WholePositiveTransportMatching n F q τ σ Q l r c d J H)
    (hφ : ContDiff ℝ ∞ φ) (hφpos : ∀ x, 0 < φ x)
    (hφbound : ∀ x, φ x ≤ B ∧ (φ x)⁻¹ ≤ B)
    (hφend : ∀ side : Bool, φ =ᶠ[𝓝 (if side then r else l)] (fun _ => (1 : ℝ)))
    (hφmiddle : ∀ x ∈ Icc c d, φ =ᶠ[𝓝 x] (fun _ => (1 : ℝ))) :
    WholePositiveTransportMatching n F q τ σ (fun p => Q p * φ p.1)
      l r c d J (H * B) := by
  apply n04NegativeGeometry_matching_mul_height h (hφ.comp contDiff_fst)
    (fun p => hφpos p.1) (fun p => hφbound p.1)
  · intro side θ
    exact (hφend side).comp_tendsto (continuous_fst.tendsto (if side then r else l, θ))
  · intro x θ
    rfl
  · intro x θ
    rfl
  · intro x hx θ
    exact (hφmiddle x hx).comp_tendsto (continuous_fst.tendsto (x, θ))

/-- At the inverse chart point, the relative chart cancels exactly.
This equality does not assume any parameter regularity of the height. -/
theorem n04NegativeGeometry_referenceGauge_pulledHeight
    (h₀ Q : PolarPoint → ℝ) (σ τ χ : PolarPoint → PolarPoint)
    (hστ : Function.LeftInverse σ τ) (y : PolarPoint) :
    wholePositiveReferenceGaugeHeight h₀ σ Q
        (wholePositiveReferenceGaugeInverse τ χ y) =
      h₀ (χ y) / Q (χ y) := by
  rw [wholePositiveReferenceGaugeHeight_eq]
  simp only [wholePositiveReferenceGaugeInverse, Function.comp_apply, hστ]

/-- The preceding identity for the literal pulled-height field of an
admissible-gauge record, including auxiliary-column replacement. The
positive inverse chart has canonical interval `(0,1)`, so its unit point
is precisely the supplied point `y`. -/
theorem n04NegativeGeometry_gauge_pulledHeight_positive
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (z : Parameter (G.S η)) (m : ℕ)
    (i : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w))
    (hi : G.e m = .inr i)
    (hστ : Function.LeftInverse (G.σ (G.lift η z) i) (G.τ (G.lift η z) i))
    (y : PolarPoint) :
    G.pulledHeight η z m y =
      G.H i (positiveReferenceCylinderInverse (G.Y i) y).1 /
        G.Q (G.lift η z) i (positiveReferenceCylinderInverse (G.Y i) y) := by
  have hf := n04WholeReferenceGaugeAtlasData_positive_fields
    G.W.C G.W.L (G.W.A G.X.e₀) G.e G.X.cell
    (fun j => positiveReferenceCylinderChart (G.Y j))
    (fun j => positiveReferenceCylinderInverse (G.Y j))
    (fun j p => G.H j p.1) G.τ G.σ G.Q G.N (G.lift η z) m i hi
  have hl : (G.V η).left m = 0 := hf.1
  have hr : (G.V η).right m = 1 := hf.2.1
  have hI : (G.V η).inverseChart (G.lift η z) m =
      wholePositiveReferenceGaugeInverse (G.τ (G.lift η z) i)
        (positiveReferenceCylinderInverse (G.Y i)) := hf.2.2.2.2.2.2.2.2.1
  have hH : (G.V η).height (G.lift η z) m =
      wholePositiveReferenceGaugeHeight (fun p => G.H i p.1)
        (G.σ (G.lift η z) i) (G.Q (G.lift η z) i) := hf.2.2.2.2.2.2.2.2.2.1
  have hy : canonicalUnitPoint (G.V η) m y = y := by
    simp only [canonicalUnitPoint, hl, hr, sub_zero, one_mul, zero_add, Prod.eta]
  change (G.V η).height (G.lift η z) m
    ((G.V η).inverseChart (G.lift η z) m (canonicalUnitPoint (G.V η) m y)) = _
  rw [hy, hH, hI]
  exact n04NegativeGeometry_referenceGauge_pulledHeight _ _ _ _ _ hστ y

end ContinuousFlexibility.Analysis
