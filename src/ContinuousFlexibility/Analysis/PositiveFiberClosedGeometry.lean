module

public import ContinuousFlexibility.Analysis.PositiveFiberCoordinates
public import ContinuousFlexibility.Analysis.CanonicalEndpointInverse

/-!
# Closed geometry and symmetries of positive fiber coordinates

The scalar interpolation supplies positive radial and angular derivatives.
The resulting actual global inverse maps the closed strips as well as the
open strips. Periodicity and reflection are inherited from the two scalar
fields, and their genuine global inverse supplies the boundary inverse germ.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem positiveFiberChart_period_add
    {φ Y : PolarPoint → ℝ} {T : ℝ}
    (hφ : ∀ r θ, φ (r, θ + T) = φ (r, θ) + T)
    (hY : ∀ r η, Y (r, η + T) = Y (r, η)) (p : PolarPoint) :
    positiveFiberChart φ Y (p + (0, T)) = positiveFiberChart φ Y p + (0, T) := by
  rcases p with ⟨r, θ⟩
  apply Prod.ext
  · simp only [positiveFiberChart, Prod.mk_add_mk, add_zero, hφ, hY]
  · simp only [positiveFiberChart, Prod.mk_add_mk, add_zero, hφ]

theorem positiveFiberChart_reflect
    {φ Y : PolarPoint → ℝ}
    (hφ : ∀ r θ, φ (r, -θ) = -φ (r, θ))
    (hY : ∀ r η, Y (r, -η) = Y (r, η)) (p : PolarPoint) :
    positiveFiberChart φ Y (p.1, -p.2) =
      ((positiveFiberChart φ Y p).1, -(positiveFiberChart φ Y p).2) := by
  apply Prod.ext
  · simp only [positiveFiberChart, hφ, hY]
  · exact hφ p.1 p.2

/-- Reflection of the inverse follows from the two genuine inverse
identities and reflection of the forward map. -/
theorem inverse_reflect_of_forward_reflect
    {F G : PolarPoint → PolarPoint}
    (hleft : Function.LeftInverse G F) (hright : Function.RightInverse G F)
    (hreflect : ∀ p, F (p.1, -p.2) = ((F p).1, -(F p).2))
    (p : PolarPoint) : G (p.1, -p.2) = ((G p).1, -(G p).2) := by
  apply hleft.injective
  rw [hright, hreflect, hright]

/-- The Jacobian of a genuinely reflection-equivariant differentiable
map is even. This uses the actual chain rule twice. -/
theorem planeJacobian_even_of_angle_reflection
    {F : PolarPoint → PolarPoint} (hF : Differentiable ℝ F)
    (hreflect : ∀ p, F (p.1, -p.2) = ((F p).1, -(F p).2))
    (p : PolarPoint) : planeJacobian F (p.1, -p.2) = planeJacobian F p := by
  let R : PolarPoint → PolarPoint := fun q => (q.1, -q.2)
  have hR (q : PolarPoint) : DifferentiableAt ℝ R q :=
    differentiableAt_fst.prodMk differentiableAt_snd.neg
  have hRJ (q : PolarPoint) : planeJacobian R q = -1 := by
    have hd : HasFDerivAt (fun x : PolarPoint => -x.2)
        (-(ContinuousLinearMap.snd ℝ ℝ ℝ)) q := hasFDerivAt_snd.fun_neg
    rw [planeJacobian_preserve_first hd.differentiableAt]
    unfold angularPartial
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_snd']
  have he : F ∘ R = R ∘ F := funext hreflect
  have hj := congrArg (fun H : PolarPoint → PolarPoint => planeJacobian H p) he
  rw [planeJacobian_comp (hR p) (hF (R p)),
    planeJacobian_comp (hF p) (hR (F p)), hRJ p, hRJ (F p)] at hj
  change planeJacobian F (R p) = planeJacobian F p
  linarith only [hj]

/-- The actual global left inverse agrees near the image point with the
smooth local inverse supplied by the ordinary inverse function theorem. -/
theorem canonicalBoundaryInverseGerm_of_global_leftInverse
    {F G : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F p) (hJ : planeJacobian F p ≠ 0)
    (hleft : Function.LeftInverse G F) : CanonicalBoundaryInverseGerm F G p := by
  obtain ⟨e, he, hp, hsmooth⟩ :=
    exists_smooth_localInverse_of_planeJacobian_ne_zero hF hJ
  refine ⟨e, he, hp, hsmooth, ?_⟩
  have htarget : F p ∈ e.target := by
    rw [← he]
    exact e.map_source hp
  filter_upwards [e.open_target.mem_nhds htarget] with q hq
  calc
    G q = G (F (e.symm q)) := by
      rw [← he, e.right_inv hq]
    _ = e.symm q := hleft _

/-- The exact endpoint values and the proved radial monotonicity control
both closed-strip maps. No boundary value is assigned to a total inverse. -/
theorem positiveFiberChart_maps_closedStrip
    {φ Y : PolarPoint → ℝ} (hY : ContDiff ℝ ∞ Y)
    {B l r α β : ℝ} (hB : 0 < B)
    (hYLower : ∀ x η, B ≤ deriv (fun t => Y (t, η)) x)
    (hleft : ∀ η, Y (l, η) = α) (hright : ∀ η, Y (r, η) = β) :
    MapsTo (positiveFiberChart φ Y) (Icc l r ×ˢ (univ : Set ℝ))
        (Icc α β ×ˢ (univ : Set ℝ)) ∧
      MapsTo (positiveFiberChartInverse φ Y) (Icc α β ×ˢ (univ : Set ℝ))
        (Icc l r ×ˢ (univ : Set ℝ)) := by
  have hmono (η : ℝ) : StrictMono (fun x => Y (x, η)) :=
    strictMono_of_deriv_pos (fun x => hB.trans_le (hYLower x η))
  have hR := (positiveFiberRadialInverse_properties hY hB hYLower).2.1
  constructor
  · intro p hp
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · change α ≤ Y (p.1, φ p)
      rw [← hleft (φ p)]
      exact (hmono (φ p)).monotone hp.1.1
    · change Y (p.1, φ p) ≤ β
      rw [← hright (φ p)]
      exact (hmono (φ p)).monotone hp.1.2
  · intro q hq
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · change l ≤ positiveFiberRadialInverse Y q
      by_contra hnot
      have hh := hmono q.2 (lt_of_not_ge hnot)
      dsimp only at hh
      rw [hR q, hleft q.2] at hh
      exact (not_lt_of_ge hq.1.1) hh
    · change positiveFiberRadialInverse Y q ≤ r
      by_contra hnot
      have hh := hmono q.2 (lt_of_not_ge hnot)
      dsimp only at hh
      rw [hR q, hright q.2] at hh
      exact (not_lt_of_ge hq.1.2) hh

end ContinuousFlexibility.Analysis
