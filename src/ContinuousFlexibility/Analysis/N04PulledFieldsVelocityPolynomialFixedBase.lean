module

public import ContinuousFlexibility.Analysis.N04PulledFieldsPolynomialFixedBase
public import ContinuousFlexibility.Analysis.N01CorrectionCoefficientPolynomialGrowth

/-!
# Reflection and the actual velocity correction polynomial

The existing angular-reflection towers and the exact division-free
coefficient formula preserve one common low base. The supplied output
tower is unchanged; in particular the two velocity inputs may be the
same actual N02-substituted velocity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

variable {I E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem n04PulledFields_polynomial_fixedBase_from_velocity
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hIp : HasInterpolation p)
    (W F : I → ℝ) (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {U : Set E} {V : I → Set PolarPoint}
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    (hmap : ∀ i y, y ∈ V i → (y.1, -y.2) ∈ V i)
    {a b q ve vr : I → E × PolarPoint → ℝ} {out : I → E × PolarPoint → ℝ × ℝ}
    (Ja : ∀ i, SmoothDirections (U ×ˢ V i) (a i))
    (Jb : ∀ i, SmoothDirections (U ×ˢ V i) (b i))
    (Jq : ∀ i, SmoothDirections (U ×ˢ V i) (q i))
    (Je : ∀ i, SmoothDirections (U ×ˢ V i) (ve i))
    (Jρ : ∀ i, SmoothDirections (U ×ˢ V i) (vr i))
    (Jout : ∀ i, SmoothDirections (U ×ˢ V i) (out i))
    (hfactor : N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Ja ∧
      N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Jb ∧
        N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Jq)
    (hJe : N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Je)
    (hJρ : N04PulledFieldsFixedBaseMixedGrowth p W F Jρ)
    (hpoly : ∀ i x, x ∈ U → ∀ y ∈ V i,
      out i (x, y) = correctionPolynomialValue
        (a i (x, y)) (b i (x, y)) (q i (x, y))
        (ve i (x, y)) (ve i (x, (y.1, -y.2)))
        (vr i (x, y)) (vr i (x, (y.1, -y.2)))) :
    N04PulledFieldsFixedBaseMixedGrowth p W F
      (fun i => solveSmoothDirectionsPostcomp (Jout i) (ContinuousLinearMap.fst ℝ ℝ ℝ)) ∧
    N04PulledFieldsFixedBaseMixedGrowth p W F
      (fun i => solveSmoothDirectionsPostcomp (Jout i) (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  let Jρr : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => vr i (z.1, (z.2.1, -z.2.2))) :=
    fun i => correctionPolynomial_reflectedDirections (Jρ i) hU (hV i) (hmap i)
  let Jer : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => ve i (z.1, (z.2.1, -z.2.2))) :=
    fun i => correctionPolynomial_reflectedDirections (Je i) hU (hV i) (hmap i)
  have hJρr : N04PulledFieldsFixedBaseMixedGrowth p W F Jρr :=
    hJρ.reflect_angle Jρr hU hV hmap (fun _ _ _ _ _ => rfl)
  have hJer : N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Jer :=
    hJe.reflect_angle Jer hU hV hmap (fun _ _ _ _ _ => rfl)
  let JD : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => ((vr i z - vr i (z.1, (z.2.1, -z.2.2))) / 2,
        (-vr i (z.1, (z.2.1, -z.2.2)) - vr i z) / 2)) :=
    fun i => reflectedVelocityDirections (Jρ i) (Jρr i)
  let JE : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => ((ve i z - ve i (z.1, (z.2.1, -z.2.2))) / 2,
        (-ve i (z.1, (z.2.1, -z.2.2)) - ve i z) / 2)) :=
    fun i => reflectedVelocityDirections (Je i) (Jer i)
  let Jrd : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => (vr i z - vr i (z.1, (z.2.1, -z.2.2))) / 2) :=
    fun i => solveSmoothDirectionsPostcomp (JD i) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let Jrv : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => (-vr i (z.1, (z.2.1, -z.2.2)) - vr i z) / 2) :=
    fun i => solveSmoothDirectionsPostcomp (JD i) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let Jed : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => (ve i z - ve i (z.1, (z.2.1, -z.2.2))) / 2) :=
    fun i => solveSmoothDirectionsPostcomp (JE i) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let Jev : ∀ i, SmoothDirections (U ×ˢ V i)
      (fun z => (-ve i (z.1, (z.2.1, -z.2.2)) - ve i z) / 2) :=
    fun i => solveSmoothDirectionsPostcomp (JE i) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hrd : N04PulledFieldsFixedBaseMixedGrowth p W F Jrd := by
    apply N04PulledFieldsFixedBaseMixedGrowth.linear_combination hp hW hF Jrd hV
      (1 / 2) (-1 / 2) (hJ := hJρ) (hK := hJρr)
    intro i x hx y hy
    ring
  have hrv : N04PulledFieldsFixedBaseMixedGrowth p W F Jrv := by
    apply N04PulledFieldsFixedBaseMixedGrowth.linear_combination hp hW hF Jrv hV
      (-1 / 2) (-1 / 2) (hJ := hJρ) (hK := hJρr)
    intro i x hx y hy
    ring
  have hed : N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Jed := by
    apply N04PulledFieldsFixedBaseMixedGrowth.linear_combination hp hW (fun _ => zero_le_one) Jed hV
      (1 / 2) (-1 / 2) (hJ := hJe) (hK := hJer)
    intro i x hx y hy
    ring
  have hev : N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Jev := by
    apply N04PulledFieldsFixedBaseMixedGrowth.linear_combination hp hW (fun _ => zero_le_one) Jev hV
      (-1 / 2) (-1 / 2) (hJ := hJe) (hK := hJer)
    intro i x hx y hy
    ring
  let JB : ∀ i, SmoothDirections (U ×ˢ V i) (fun z => (out i z).1) :=
    fun i => solveSmoothDirectionsPostcomp (Jout i) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let JC : ∀ i, SmoothDirections (U ×ˢ V i) (fun z => (out i z).2) :=
    fun i => solveSmoothDirectionsPostcomp (Jout i) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  exact n04PulledFields_polynomial_coefficient_fixedBaseGrowth
    (I := I) (E := E) (U := U) (V := V)
    p hp hIp W F hW hF hU hV hc Ja Jb Jq Jed Jev Jrd Jrv JB JC
    (fun i x hx y hy => by
      simpa only [correctionPolynomialValue] using congrArg (fun z : ℝ × ℝ => z.1) (hpoly i x hx y hy))
    (fun i x hx y hy => by
      simpa only [correctionPolynomialValue] using congrArg (fun z : ℝ × ℝ => z.2) (hpoly i x hx y hy))
    hfactor.1 hfactor.2.1 hfactor.2.2 hed hev hrd hrv


end ContinuousFlexibility.Statements
