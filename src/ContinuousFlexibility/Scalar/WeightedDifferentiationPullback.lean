module

public import ContinuousFlexibility.Scalar.WeightedMaterialScale
public import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
public import ContinuousFlexibility.Radial.RadialHeight

/-!
# Pullbacks of the actual ordinary coordinate derivatives

The chain rule uses the prescribed inverse material coordinate and its
actual derivative. The radial formula retains both the inverse scale and
the derivative of the logarithmic height weight. Angular differentiation
commutes with the radial weight.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ}
  {f : PolarPoint → ℝ}

private theorem hasDerivAt_materialWeight
    (hT : IsMaterialData D T) (γ x : ℝ) :
    HasDerivAt (fun t => T.H (T.radius t) ^ (-γ))
      ((-γ) * deriv (fun t => Real.log (T.H (T.radius t))) x *
        T.H (T.radius x) ^ (-γ)) x := by
  have hinside := hT.2.2.2.2.2.2.2.1
  have hpos (t : ℝ) : 0 < T.H (T.radius t) :=
    (hT.2.1 _ (hinside t).1).2.1
  let L : ℝ → ℝ := fun t => Real.log (T.H (T.radius t))
  have hL : ContDiff ℝ ∞ L :=
    contDiff_materialLog_pullback hT (hT.1 T.H (by simp))
      (fun r hr => (hT.2.1 r hr).2.1)
  have hd := ((hL.differentiable (by simp) x).hasDerivAt.mul_const (-γ)).exp
  have heq : (fun t => T.H (T.radius t) ^ (-γ)) =
      fun t => Real.exp (L t * (-γ)) :=
    funext (fun t => Real.rpow_def_of_pos (hpos t) (-γ))
  have hx := congrFun heq x
  simp only [heq, hx]
  convert hd using 1 <;> ring

/-- The ordinary radial partial has exactly the inverse-scale and
logarithmic-weight terms required by the actual material pullback. -/
theorem materialPullback_radialPartial
    (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (p : PolarPoint) :
    materialPullback T γ (radialPartial f) p =
      (T.ell (T.radius p.1))⁻¹ *
        (radialPartial (materialPullback T γ f) p +
          γ * deriv (fun t => Real.log (T.H (T.radius t))) p.1 *
            materialPullback T γ f p) := by
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _, hrad, _⟩ := hdata
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hp : (T.radius p.1, p.2) ∈ annularOpen D :=
    ⟨(hinside p.1).1, mem_univ _⟩
  have hdf : DifferentiableAt ℝ f (T.radius p.1, p.2) :=
    (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hs : HasDerivAt (fun t => f (T.radius t, p.2))
      (radialPartial f (T.radius p.1, p.2) * T.ell (T.radius p.1)) p.1 := by
    simpa only [Function.comp_def] using!
      (Radial.hasDerivAt_radialSlice hdf).comp p.1 (hrad p.1)
  have hd : HasDerivAt (fun t => materialPullback T γ f (t, p.2))
      (((-γ) * deriv (fun t => Real.log (T.H (T.radius t))) p.1 *
          T.H (T.radius p.1) ^ (-γ)) * f (T.radius p.1, p.2) +
        T.H (T.radius p.1) ^ (-γ) *
          (radialPartial f (T.radius p.1, p.2) * T.ell (T.radius p.1))) p.1 := by
    simpa only [materialPullback] using! (hasDerivAt_materialWeight hT γ p.1).mul hs
  have hg : HasDerivAt (fun t => materialPullback T γ f (t, p.2))
      (radialPartial (materialPullback T γ f) p) p.1 := by
    simpa only using! Radial.hasDerivAt_radialSlice
      ((contDiff_materialPullback hT hf).differentiable (by simp) p)
  have he : radialPartial (materialPullback T γ f) p =
      (-γ) * deriv (fun t => Real.log (T.H (T.radius t))) p.1 *
        materialPullback T γ f p +
      T.ell (T.radius p.1) * materialPullback T γ (radialPartial f) p := by
    calc
      _ = _ := hg.unique hd
      _ = _ := by unfold materialPullback; ring
  have hell : T.ell (T.radius p.1) ≠ 0 := (hpos _ (hinside p.1).1).1.ne'
  rw [he]
  field_simp [hell] <;> ring

/-- Angular partial differentiation commutes with the exact material
pullback, since both the weight and the coordinate are radial. -/
theorem materialPullback_angularPartial
    (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) :
    materialPullback T γ (angularPartial f) = angularPartial (materialPullback T γ f) := by
  funext p
  have hinside := hT.2.2.2.2.2.2.2.1
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hdf : DifferentiableAt ℝ f (T.radius p.1, p.2) :=
    (hf.contDiffAt (hU.mem_nhds ⟨(hinside p.1).1, mem_univ _⟩)).differentiableAt (by simp)
  have hd : HasDerivAt (fun t => materialPullback T γ f (p.1, t))
      (materialPullback T γ (angularPartial f) p) p.2 := by
    simpa only [materialPullback] using!
      (Radial.hasDerivAt_angularSlice hdf).const_mul (T.H (T.radius p.1) ^ (-γ))
  have hg : HasDerivAt (fun t => materialPullback T γ f (p.1, t))
      (angularPartial (materialPullback T γ f) p) p.2 := by
    simpa only using! Radial.hasDerivAt_angularSlice
      ((contDiff_materialPullback hT hf).differentiable (by simp) p)
  exact hd.unique hg

theorem materialPullback_angularPartial_twice
    (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) :
    materialPullback T γ (angularPartial (angularPartial f)) =
      angularPartial (angularPartial (materialPullback T γ f)) := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hfirst : ContDiffOn ℝ ∞ (angularPartial f) (annularOpen D) :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  rw [materialPullback_angularPartial hT hfirst, materialPullback_angularPartial hT hf]

end ContinuousFlexibility.Statements
