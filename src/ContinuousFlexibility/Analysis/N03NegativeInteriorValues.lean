module

public import ContinuousFlexibility.Analysis.ReturnCorrectionReferenceLower
public import ContinuousFlexibility.Analysis.N01RootRadialCoefficientValues

/-!
# State-independent denominators on each fixed negative interior

The actual corrected discriminant is bounded below by a positive
reference function. Compactness is applied to that reference function,
not to the varying state. The radial coefficient uses N01's actual
reference interval and the exact N03 equality of radial coefficients.
Thus every fixed compact subset of a negative component has two genuine
positive lower bounds on the same state neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem exists_positive_compact_lower
    {K : Set ℝ} (hK : IsCompact K) {f : ℝ → ℝ}
    (hf : ContinuousOn f K) (hpositive : ∀ r ∈ K, 0 < f r) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ K, c ≤ f r := by
  by_cases hne : K.Nonempty
  · obtain ⟨r, hr, hmin⟩ := hK.exists_isMinOn hne hf
    exact ⟨f r, hpositive r hr, fun x hx => hmin hx⟩
  · exact ⟨1, zero_lt_one, fun r hr => (hne ⟨r, hr⟩).elim⟩

def N03NegativeInteriorValueBounds
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (base : ℕ) (ε : ℝ)
    (J : Set ℝ) (l κ : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ p : PolarPoint, p.1 ∈ J → l ≤ (L.coefficients z).a p ∧
      κ ≤ (L.coefficients z).b p ^ 2 -
        (L.coefficients z).a p * (L.coefficients z).c p

/-- The two lower bounds are selected before the state and angle.
This concerns the explicitly controlled correction, using its actual
reference discriminant bound, and does not infer a uniform gap for an
arbitrary N03 witness. -/
theorem n03_exists_negativeInterior_value_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hL : N03Properties D T S C R L base ε)
    (χ : ℕ → ℝ → ℝ)
    (hcoeff : L.coefficients = returnCorrectedCoefficients D S C χ)
    (hgap : N04ReturnReferenceDiscriminantBound D S C χ base ε)
    (m : ℕ) {J : Set ℝ} (hJ : IsCompact J)
    (hJN : J ⊆ Ioo (C.left m) (C.right m)) :
    ∃ l κ : ℝ, 0 < l ∧ 0 < κ ∧
      N03NegativeInteriorValueBounds S C L base ε J l κ := by
  obtain ⟨_, hD⟩ := hN.1.1
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hAnn (r : ℝ) (hr : r ∈ J) : r ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans (hJN hr).1, (hJN hr).2.trans (hC.1 m).2.2⟩
  have hrpos (r : ℝ) (hr : r ∈ J) : 0 < r := hD.1.1.trans (hAnn r hr).1
  have hwpos (r : ℝ) (hr : r ∈ J) : 0 < D.w r :=
    hD.1.2.2.2.2.1 r (hAnn r hr)
  have hw : ContDiff ℝ ∞ D.w := hD.1.2.2.1.1
  have hderiv : Continuous (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  let f : ℝ → ℝ := fun r => D.w r ^ 2 * (-deriv D.w r / (r * D.w r)) / 128
  have hf : ContinuousOn f J :=
    ((hw.continuous.pow 2).continuousOn.mul
      (hderiv.neg.continuousOn.div (continuous_id.mul hw.continuous).continuousOn
        (fun r hr => mul_ne_zero (hrpos r hr).ne' (hwpos r hr).ne'))).div_const 128
  have hfpos (r : ℝ) (hr : r ∈ J) : 0 < f r :=
    div_pos (mul_pos (sq_pos_of_pos (hwpos r hr))
      (div_pos (neg_pos.mpr (hC.2.2.2.1 m r (hJN hr)))
        (mul_pos (hrpos r hr) (hwpos r hr)))) (by norm_num)
  obtain ⟨l, hl, hlow⟩ := exists_positive_compact_lower hJ
    ((hw.continuous.div_const 8).continuousOn)
    (fun r hr => div_pos (hwpos r hr) (by norm_num : (0 : ℝ) < 8))
  obtain ⟨κ, hκ, hdisc⟩ := exists_positive_compact_lower hJ hf hfpos
  refine ⟨l, κ, hl, hκ, ?_⟩
  intro z hz hs p hp
  have ha := n01_scaledRadialCoefficient_root_values (σ := 1)
    hN (hAnn p.1 hp) (by norm_num : (0 : ℝ) < 1) hz hs p.2
  have ha' : D.w p.1 / 8 ≤ (originalCoefficients D S C z).a p := by
    simpa only [rootScaledRadialCoefficient, mul_zero, add_zero, div_one, mul_one] using ha.1
  have hd := hgap z hz hs m p (hJN hp)
  rw [← hcoeff] at hd
  exact ⟨(hlow p.1 hp).trans (ha'.trans_eq (hL.1 z hz hs p).symm),
    (hdisc p.1 hp).trans hd⟩

end ContinuousFlexibility.Analysis
