module

public import ContinuousFlexibility.Analysis.N04NegativeGeometryHeightPerturbation

/-!
# Admissible gauges with a discontinuous interior height choice

The multiplier conditions in this file concern only the spatial
variable. Switching between the identity multiplier at scalar parameter
zero and a fixed interior multiplier elsewhere preserves admissibility.
The last theorem records the resulting exact change of the pulled height.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped Topology ContDiff

/-- An interior spatial multiplier, with a fixed numerical upper bound.
There is deliberately no state-parameter condition in this structure. -/
structure N04NegativeGeometryHeightFactor (φ : PolarPoint → ℝ) (l r c d : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  positive : ∀ p, 0 < φ p
  bound : ∀ p, φ p ≤ 2 ∧ (φ p)⁻¹ ≤ 2
  endpoint : ∀ (side : Bool) θ,
    φ =ᶠ[𝓝 (if side then r else l, θ)] (fun _ => (1 : ℝ))
  period : ∀ x θ, φ (x, θ + Real.pi) = φ (x, θ)
  even : ∀ x θ, φ (x, -θ) = φ (x, θ)
  middle : ∀ x ∈ Icc c d, ∀ θ,
    φ =ᶠ[𝓝 (x, θ)] (fun _ => (1 : ℝ))

/-- The identity spatial factor satisfies all multiplier conditions. -/
theorem n04NegativeGeometry_heightFactor_one (l r c d : ℝ) :
    N04NegativeGeometryHeightFactor (fun _ => (1 : ℝ)) l r c d where
  smooth := contDiff_const
  positive := fun _ => zero_lt_one
  bound := fun _ => by norm_num
  endpoint := fun _ _ => Filter.EventuallyEq.rfl
  period := fun _ _ => rfl
  even := fun _ _ => rfl
  middle := fun _ _ _ => Filter.EventuallyEq.rfl

/-- At each individual parameter value the switched factor remains
smooth in space and has the same endpoint and middle germs. -/
theorem n04NegativeGeometry_heightFactor_switch
    {φ : PolarPoint → ℝ} {l r c d : ℝ}
    (h : N04NegativeGeometryHeightFactor φ l r c d) (t : ℝ) :
    N04NegativeGeometryHeightFactor (fun p => if t = 0 then 1 else φ p) l r c d := by
  classical
  by_cases ht : t = 0
  · simpa only [if_pos ht] using n04NegativeGeometry_heightFactor_one l r c d
  · simpa only [if_neg ht] using h

/-- Change only the positive transport height. At the reference scalar
parameter the new height equals the original one exactly. -/
def n04NegativeGeometryPerturbedGauge (G : N04RealizationGauge)
    (φ : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w) → PolarPoint → ℝ) :
    N04RealizationGauge := by
  classical
  exact { G with Q := fun z i p => G.Q z i p * (if z.2 = 0 then 1 else φ i p) }

/-- No state regularity is needed to preserve the frozen admissibility
predicate. The original buffer and lower Jacobian bound are retained;
only the upper height bound is doubled. -/
theorem n04NegativeGeometry_perturbedGauge_admissible
    (G : N04RealizationGauge) {b : ℕ} {ε : ℝ} (h : G.Admissible b ε)
    (φ : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w) → PolarPoint → ℝ)
    (hφ : ∀ i, N04NegativeGeometryHeightFactor (φ i)
      (n04PositiveLeft i) (n04PositiveRight i)
      (h.2.2.2.2.2.choose.centerLeft i) (h.2.2.2.2.2.choose.centerRight i)) :
    (n04NegativeGeometryPerturbedGauge G φ).Admissible b ε := by
  classical
  let hm := h.2.2.2.2.2
  let B := hm.choose
  let lower := hm.choose_spec.choose
  let upper := hm.choose_spec.choose_spec.choose
  have hN : G.N = B.region := hm.choose_spec.choose_spec.choose_spec.1
  have hmatching := hm.choose_spec.choose_spec.choose_spec.2
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_,
    B, lower, (fun i => upper i * 2), hN, ?_⟩
  · intro i
    have href := h.2.2.2.2.1 i
    refine ⟨href.1, href.2.1, ?_⟩
    funext p
    change G.Q (G.W.C.referenceState, 0) i p * (if (0 : ℝ) = 0 then 1 else φ i p) = 1
    rw [if_pos (rfl : (0 : ℝ) = 0), mul_one]
    exact congrFun href.2.2 p
  · intro z hz hs i
    have hf : N04NegativeGeometryHeightFactor
        (fun p => if z.2 = 0 then 1 else φ i p)
        (n04PositiveLeft i) (n04PositiveRight i) (B.centerLeft i) (B.centerRight i) :=
      n04NegativeGeometry_heightFactor_switch (hφ i) z.2
    exact n04NegativeGeometry_matching_mul_height (hmatching z hz hs i)
      hf.smooth hf.positive hf.bound hf.endpoint hf.period hf.even hf.middle

/-- On a positive piece the switched factor survives as a reciprocal
factor of the literal pulled height. Both records use the same inverse
transport and the same reference radial chart. -/
theorem n04NegativeGeometry_perturbedGauge_pulledHeight_positive
    (G : N04RealizationGauge)
    (φ : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w) → PolarPoint → ℝ)
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (z : Parameter (G.S η)) (m : ℕ)
    (i : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w))
    (hi : G.e m = .inr i)
    (hστ : Function.LeftInverse (G.σ (G.lift η z) i) (G.τ (G.lift η z) i))
    (y : PolarPoint) :
    (n04NegativeGeometryPerturbedGauge G φ).pulledHeight η z m y =
      G.pulledHeight η z m y /
        (if z.2 = 0 then 1 else φ i (positiveReferenceCylinderInverse (G.Y i) y)) := by
  classical
  let x : PolarPoint := positiveReferenceCylinderInverse (G.Y i) y
  let A : ℝ := G.H i x.1
  let Q₀ : ℝ := G.Q (G.lift η z) i x
  let M : ℝ := if z.2 = 0 then 1 else φ i x
  have hnew : (n04NegativeGeometryPerturbedGauge G φ).pulledHeight η z m y =
      A / (Q₀ * M) := by
    exact n04NegativeGeometry_gauge_pulledHeight_positive
      (n04NegativeGeometryPerturbedGauge G φ) η z m i hi hστ y
  have hold : G.pulledHeight η z m y = A / Q₀ :=
    n04NegativeGeometry_gauge_pulledHeight_positive G η z m i hi hστ y
  calc
    (n04NegativeGeometryPerturbedGauge G φ).pulledHeight η z m y =
        A / (Q₀ * M) := hnew
    _ = (A / Q₀) / M := (div_div A Q₀ M).symm
    _ = G.pulledHeight η z m y / M := congrArg (fun t : ℝ => t / M) hold.symm

end ContinuousFlexibility.Analysis
