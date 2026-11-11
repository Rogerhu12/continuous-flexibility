import ContinuousFlexibility.Analysis.N01cSpatialCoefficients
import ContinuousFlexibility.Analysis.N01cControlEndpointFactor

/-!
# The actual logarithmic control on a negative component

Disjointness of the component controls and the positive support of the
border identify the actual profile with one controlled exponential near
every point of a negative component. Differentiating this actual germ gives
the exact optical-square formula and the relative perturbation criterion.
The endpoint estimate is a numerical consequence of a reference optical
lower bound and the already proved linear endpoint factor for controls.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Blueprint
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- On a component only its own control contributes to the actual sum. -/
theorem stateControlSum_eq_single_on_component
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) (x : AnnularState S)
    (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    stateControlSum C x r = stateKappa S x m * C.control m r := by
  classical
  have hdisjoint := hC.2.2.1
  have hcontrols := hC.2.2.2.2.2.1
  unfold stateControlSum
  apply tsum_eq_single m
  intro n hnm
  have hn : C.control n r = 0 := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisjoint n m hnm) ((hcontrols n).2.2 hne) hr
  rw [hn, mul_zero]

/-- The compact positive-side border vanishes at every reference negative
point, without any quantitative support premise. -/
theorem referenceBorder_zero_on_negative
    {D : ReferenceData} (hborder : RadialTrueBorder D)
    {r : ℝ} (hr : deriv D.w r < 0) : D.chi r = 0 := by
  by_contra hne
  have hpos : 0 < deriv D.w r := (hborder.2.2.1 hne).2
  exact lt_asymm hr hpos

theorem stateProfile_eq_component_exponential
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hborder : RadialTrueBorder D) (hC : controlGeometryConditions D S C)
    (x : AnnularState S) (m : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m)) :
    stateProfile D S C x r =
      D.w r * Real.exp (stateKappa S x m * C.control m r) := by
  have hχ := referenceBorder_zero_on_negative hborder (hC.2.2.2.1 m r hr)
  have hsum := stateControlSum_eq_single_on_component hC x m hr
  change D.w r * Real.exp (x.2.1 * D.chi r + stateControlSum C x r) = _
  rw [hχ, hsum, mul_zero, zero_add]

/-- This is equality of actual germs, so it transports ordinary derivatives. -/
theorem stateProfile_eventuallyEq_component_exponential
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hborder : RadialTrueBorder D) (hC : controlGeometryConditions D S C)
    (x : AnnularState S) (m : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m)) :
    stateProfile D S C x =ᶠ[𝓝 r]
      (fun t => D.w t * Real.exp (stateKappa S x m * C.control m t)) := by
  filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
  exact stateProfile_eq_component_exponential hborder hC x m ht

/-- The logarithmic derivative of an actual exponential perturbation,
with its positive amplitude canceled exactly. -/
theorem logPerturbation_opticalSquare_eq
    {w f : ℝ → ℝ} {r wr fr : ℝ}
    (hw : HasDerivAt w wr r) (hf : HasDerivAt f fr r)
    (hr : r ≠ 0) (hw0 : w r ≠ 0) :
    -deriv (fun t => w t * Real.exp (f t)) r /
        (r * (w r * Real.exp (f r))) =
      -wr / (r * w r) - fr / r := by
  rw [deriv_fun_mul hw.differentiableAt hf.exp.differentiableAt,
    hw.deriv, hf.exp.deriv]
  have hexp : Real.exp (f r) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  <;> ring

/-- The genuine controlled profile has this exact reference-relative
optical square on each original component. -/
theorem n01_stateProfile_opticalSquare_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hA : N01PartA D T S C) (x : AnnularState S)
    (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    -deriv (stateProfile D S C x) r / (r * stateProfile D S C x r) =
      -deriv D.w r / (r * D.w r) -
        stateKappa S x m * deriv (C.control m) r / r := by
  obtain ⟨_, hprofile⟩ := hA.1.1
  have hC := hA.2.2.1
  have hcore : r ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  have hrad : 0 < r := hprofile.1.1.trans hcore.1
  have hw0 : 0 < D.w r := hprofile.1.2.2.2.2.1 r hcore
  have hwd : HasDerivAt D.w (deriv D.w r) r :=
    (hprofile.1.2.2.1.1.differentiable (by simp) r).hasDerivAt
  have hcd : HasDerivAt (C.control m) (deriv (C.control m) r) r :=
    ((hC.2.2.2.2.2.1 m).1.differentiable (by simp) r).hasDerivAt
  have heq := stateProfile_eventuallyEq_component_exponential
    hA.1.2.2.2.1 hC x m hr
  rw [heq.deriv_eq, heq.eq_of_nhds]
  exact logPerturbation_opticalSquare_eq hwd (hcd.const_mul (stateKappa S x m))
    hrad.ne' hw0.ne'

/-- Dividing two linear endpoint estimates cancels the endpoint distance.
One inequality works for both ends of the component. -/
theorem optical_relative_control_bound
    {δ r Q A c κ χ : ℝ}
    (hδ : 0 ≤ δ) (hr : 0 < r)
    (hQ : c * δ ≤ Q) (hχ : |χ| ≤ A * δ)
    (hκ : |κ| * A ≤ r * c / 2) :
    |κ * χ / r| ≤ Q / 2 := by
  rw [abs_div, abs_of_pos hr, abs_mul]
  apply (div_le_iff₀ hr).mpr
  calc
    |κ| * |χ| ≤ |κ| * (A * δ) :=
      mul_le_mul_of_nonneg_left hχ (abs_nonneg κ)
    _ = (|κ| * A) * δ := (mul_assoc _ _ _).symm
    _ ≤ (r * c / 2) * δ := mul_le_mul_of_nonneg_right hκ hδ
    _ ≤ Q / 2 * r := by nlinarith [mul_le_mul_of_nonneg_left hQ hr.le]

/-- The reference-relative perturbation preserves a two-sided optical
bound. No spatial derivative or parameter tower is postulated here. -/
theorem opticalSquare_sub_bounds {Q e : ℝ} (he : |e| ≤ Q / 2) :
    Q / 2 ≤ Q - e ∧ Q - e ≤ 3 * Q / 2 := by
  constructor <;> linarith [neg_abs_le e, le_abs_self e]

/-- The actual scalar relative estimate preserves negative type. -/
theorem n01_stateProfile_deriv_neg_of_relative_control
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hA : N01PartA D T S C) (x : AnnularState S)
    (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m))
    (hsmall : |D.w r * (stateKappa S x m * deriv (C.control m) r)| ≤
      -deriv D.w r / 2) :
    deriv (stateProfile D S C x) r < 0 := by
  obtain ⟨_, hprofile⟩ := hA.1.1
  have hC := hA.2.2.1
  have hwd : HasDerivAt D.w (deriv D.w r) r :=
    (hprofile.1.2.2.1.1.differentiable (by simp) r).hasDerivAt
  have hcd : HasDerivAt (C.control m) (deriv (C.control m) r) r :=
    ((hC.2.2.2.2.2.1 m).1.differentiable (by simp) r).hasDerivAt
  rw [(stateProfile_eventuallyEq_component_exponential
    hA.1.2.2.2.1 hC x m hr).deriv_eq]
  exact deriv_logPerturbation_neg_of_relative_bound hwd
    (hcd.const_mul (stateKappa S x m)) (hC.2.2.2.1 m r hr) hsmall

end ContinuousFlexibility.Statements
