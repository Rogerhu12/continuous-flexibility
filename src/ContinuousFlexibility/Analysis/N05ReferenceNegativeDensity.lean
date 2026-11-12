import ContinuousFlexibility.Analysis.N05ReferenceNegativeHeight

/-!
# Exact densities on the actual negative reference pieces

The closed reference chart is radial and preserves the angular coordinate.
Its actual Jacobian is therefore the actual derivative of its radial slice.
The closed principal-symbol and determinant identities fix both the height
normalization and the physical density, including at the two endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The exact reference normalization and both density identities use the
actual radial-slice derivative, rather than an independently chosen jet. -/
theorem n05_negative_reference_density_closed
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) {r : ℝ}
    (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i)) (θ : ℝ) :
    let z := (C.referenceState, 0)
    let ξ := fun t : ℝ => (K.chart z i (t, θ)).1
    let q := deriv ξ r
    let H := K.height z i (r, θ)
    planeJacobian (K.chart z i) (r, θ) = q ∧
      H ^ 2 * D.w r * |q| = 1 ∧
      ξ r * |q| ^ 2 = -deriv D.w r / (r * D.w r) ∧
      |planeJacobian (K.chart z i) (r, θ)| / H ^ 2 = D.w r * |q| ^ 2 := by
  let z : AnnularState S × ℝ := (C.referenceState, 0)
  let Ψ : PolarPoint → PolarPoint := K.chart z i
  let ξ : PolarPoint → ℝ := fun p => (Ψ p).1
  let φ : PolarPoint → ℝ := fun p => (Ψ p).2
  let q := deriv (fun t : ℝ => ξ (t, θ)) r
  let H := K.height z i (r, θ)
  change planeJacobian Ψ (r, θ) = q ∧ H ^ 2 * D.w r * |q| = 1 ∧
    ξ (r, θ) * |q| ^ 2 = -deriv D.w r / (r * D.w r) ∧
    |planeJacobian Ψ (r, θ)| / H ^ 2 = D.w r * |q| ^ 2
  have h01 := h.1.1.1
  rcases h.2.2.2.2 with ⟨_, _, _, _, _, _, _, _, hclosed, _⟩
  have hmem : z ∈ stateNeighborhood S C base ε := n05_referenceState_mem h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hc := hclosed z hmem hsector i (r, θ) hr
  have hΨ : DifferentiableAt ℝ Ψ (r, θ) := hc.1.differentiableAt (by simp)
  have hdξ : DifferentiableAt ℝ ξ (r, θ) := hΨ.fst
  have hdφ : DifferentiableAt ℝ φ (r, θ) := hΨ.snd
  have hradial (t : ℝ) : Ψ (r, t) = (ξ (r, 0), t) :=
    n05_negative_reference_chart_radial hT hS h hi hr t
  have hξslice : (fun t : ℝ => ξ (r, t)) = fun _ => ξ (r, 0) := by
    funext t
    simpa only using congrArg Prod.fst (hradial t)
  have hφslice : (fun t : ℝ => φ (r, t)) = fun t => t := by
    funext t
    simpa only using congrArg Prod.snd (hradial t)
  have hξθ : angularPartial ξ (r, θ) = 0 := by
    have hd := Radial.hasDerivAt_angularSlice hdξ
    rw [hξslice] at hd
    exact hd.unique (hasDerivAt_const θ (ξ (r, 0)))
  have hφθ : angularPartial φ (r, θ) = 1 := by
    have hd := Radial.hasDerivAt_angularSlice hdφ
    rw [hφslice] at hd
    exact hd.unique (hasDerivAt_id θ)
  have hq : radialPartial ξ (r, θ) = q :=
    (Radial.hasDerivAt_radialSlice hdξ).deriv.symm
  have hJ : planeJacobian Ψ (r, θ) = q := by
    rw [n05_planeJacobian_eq_partials hΨ]
    change radialPartial ξ (r, θ) * angularPartial φ (r, θ) -
      angularPartial ξ (r, θ) * radialPartial φ (r, θ) = q
    simp only [hξθ, hφθ, hq, mul_one, zero_mul, sub_zero]
  have hqne : q ≠ 0 := fun hq0 => hc.2.2.1 (hJ.trans hq0)
  have hH : H ≠ 0 := ne_of_gt hc.2.2.2
  have hs := (n05_negative_reference_symbol_closed hT hS h hi (x := (r, θ)) hr).1
  change H ^ 2 * n05PrincipalPair (n05RadialReferenceCoefficients D) ξ ξ (r, θ) =
    |planeJacobian Ψ (r, θ)| at hs
  simp only [n05PrincipalPair, n05RadialReferenceCoefficients, Prod.fst,
    hξθ, hq, zero_mul, mul_zero, add_zero, hJ] at hs
  have hp : H ^ 2 * D.w r * q ^ 2 = |q| := by
    calc
      H ^ 2 * D.w r * q ^ 2 = H ^ 2 * (D.w r * q * q) := by ring
      _ = |q| := hs
  have hn : H ^ 2 * D.w r * |q| = 1 := by
    apply mul_right_cancel₀ (abs_ne_zero.mpr hqne)
    calc
      (H ^ 2 * D.w r * |q|) * |q| = H ^ 2 * D.w r * |q| ^ 2 := by ring
      _ = H ^ 2 * D.w r * q ^ 2 := by rw [sq_abs]
      _ = |q| := hp
      _ = 1 * |q| := (one_mul _).symm
  have hwne : D.w r ≠ 0 := by
    intro hw0
    have hbad := hn
    rw [hw0, mul_zero, zero_mul] at hbad
    exact zero_ne_one hbad
  have hdet := n05_negative_reference_determinant_closed hT hS h hi (x := (r, θ)) hr
  change H ^ 4 * (D.w r * (deriv D.w r / r)) = -ξ (r, θ) at hdet
  have hξ : ξ (r, θ) = -(H ^ 4 * (D.w r * (deriv D.w r / r))) := by
    linarith only [hdet]
  have hm : ξ (r, θ) * |q| ^ 2 * D.w r = -(deriv D.w r / r) := by
    rw [hξ]
    calc
      -(H ^ 4 * (D.w r * (deriv D.w r / r))) * |q| ^ 2 * D.w r =
          -(deriv D.w r / r) * (H ^ 2 * D.w r * |q|) ^ 2 := by ring
      _ = -(deriv D.w r / r) := by rw [hn, one_pow, mul_one]
  refine ⟨hJ, hn, ?_, ?_⟩
  · calc
      ξ (r, θ) * |q| ^ 2 = (-(deriv D.w r / r)) / D.w r :=
        (eq_div_iff hwne).mpr hm
      _ = -deriv D.w r / (r * D.w r) := by simp only [neg_div, div_div]
  · apply (div_eq_iff (pow_ne_zero 2 hH)).mpr
    calc
      |planeJacobian Ψ (r, θ)| = |q| := congrArg abs hJ
      _ = H ^ 2 * D.w r * q ^ 2 := hp.symm
      _ = (D.w r * |q| ^ 2) * H ^ 2 := by rw [sq_abs]; ring

end ContinuousFlexibility.Statements
