import ContinuousFlexibility.Analysis.N08ReferenceFlow
import ContinuousFlexibility.Analysis.StateControlCofiniteClosure

/-!
# The ordinary flow on every zero-parameter state

At `q = 0` the actual height is the radial primitive of the controlled
profile. Its ordinary flow is the optical rotation of that same profile.
Consequently the actual return residual depends only on the profile and
left chart, and is independent of the height coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08_stateRadialHeight_hasDerivAt_of_continuous (x : AnnularState S)
    (hw : Continuous (stateProfile D S C x)) (r : ℝ) :
    HasDerivAt (stateRadialHeight D S C x) (stateProfile D S C x r) r := by
  change HasDerivAt (fun u => ∫ t in D.b..u, stateProfile D S C x t)
    (stateProfile D S C x r) r
  exact intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable D.b r)
    hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt

theorem n08_originalCoefficients_zero_parameter (x : AnnularState S)
    (hw : ContDiff ℝ ∞ (stateProfile D S C x)) (p : PolarPoint) :
    (originalCoefficients D S C (x, 0)).a p = stateProfile D S C x p.1 ∧
      (originalCoefficients D S C (x, 0)).b p = 0 ∧
      (originalCoefficients D S C (x, 0)).c p = deriv (stateProfile D S C x) p.1 / p.1 := by
  change polarLinearA (stateProfile D S C x) (stateHeight D S C (x, 0)) p =
      stateProfile D S C x p.1 ∧
    polarLinearB (stateProfile D S C x) (stateHeight D S C (x, 0)) p = 0 ∧
    polarCorrectedC (stateProfile D S C x) (stateHeight D S C (x, 0)) p =
      deriv (stateProfile D S C x) p.1 / p.1
  rw [n08_stateHeight_zero_parameter]
  exact n08_radialHeight_coefficients
    (n08_stateRadialHeight_hasDerivAt_of_continuous x hw.continuous)
    (hw.differentiable (by simp) p.1)

theorem n08_stateProfile_pos (hD : RadialProfileGeometry D) (x : AnnularState S)
    {r : ℝ} (hr : r ∈ radialCore D) : 0 < stateProfile D S C x r :=
  mul_pos (hD.2.2.2.2.1 r hr) (Real.exp_pos _)

theorem n08_minusCharacteristicSpeed_zero_parameter
    (hD : RadialProfileGeometry D) (x : AnnularState S)
    (hw : ContDiff ℝ ∞ (stateProfile D S C x)) (r θ : ℝ) (hr : r ∈ radialCore D) :
    minusCharacteristicSpeed (originalCoefficients D S C (x, 0)) (r, θ) =
      -opticalSpeed (stateProfile D S C x) r :=
  n08_minusCharacteristicSpeed_of_radial_coefficients (hD.1.trans hr.1).ne'
    (n08_stateProfile_pos hD x hr) (n08_originalCoefficients_zero_parameter x hw (r, θ))

/-- This is the N01 flow itself, including its endpoint values. -/
theorem n08_minusFlow_zero_parameter_rotation
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (θ r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) :
    C.minusFlow (x, 0) m r θ =
      θ - ∫ s in C.left m..r, opticalSpeed (stateProfile D S C x) s := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN x
  obtain ⟨hD, _, _, hcontrol, _, _, hflow, _⟩ := hN
  obtain ⟨bounds, hbounds⟩ := hD.1
  have hg : RadialProfileGeometry D := hbounds.1
  have hinter := hcontrol.1 m
  have hcore : ∀ s ∈ Icc (C.left m) (C.right m), s ∈ radialCore D := by
    intro s hs
    exact ⟨hinter.1.trans_le hs.1, hs.2.trans_lt hinter.2.2⟩
  have hf := hflow (x, 0) hx m θ
  have hderiv : ∀ s ∈ Ioo (C.left m) (C.right m),
      HasDerivAt (fun t => C.minusFlow (x, 0) m t θ)
        (-opticalSpeed (stateProfile D S C x) s) s := by
    intro s hs
    exact (hf.2.2.1 s hs).congr_deriv
      (n08_minusCharacteristicSpeed_zero_parameter hg x hw s _
        (hcore s (Ioo_subset_Icc_self hs)))
  have ht := n08_radialFlow_eq_sub_integral hw
    (fun s hs => ⟨hg.1.trans (hcore s hs).1, n08_stateProfile_pos hg x (hcore s hs)⟩)
    hf.2.1 hderiv hr
  simpa only [hf.1] using ht

theorem n08_minusFlow_zero_parameter_return
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (θ : ℝ) :
    C.minusFlow (x, 0) m (C.right m) θ =
      θ - opticalTravel (stateProfile D S C x) (C.left m) (C.right m) :=
  n08_minusFlow_zero_parameter_rotation hS hT hN x hx m θ (C.right m)
    ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩

theorem n08_minusReturnInverse_zero_parameter
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S x) (m : ℕ) (θ : ℝ) :
    C.minusReturnInverse (x, 0) m θ =
      θ + opticalTravel (stateProfile D S C x) (C.left m) (C.right m) := by
  have hi : C.minusFlow (x, 0) m (C.right m) (C.minusReturnInverse (x, 0) m θ) = θ := by
    obtain ⟨_, _, _, _, _, _, _, _, hinverse, _⟩ := hN
    exact (hinverse (x, 0) hx hs m θ).1
  have hf := n08_minusFlow_zero_parameter_return hS hT hN x hx m
    (C.minusReturnInverse (x, 0) m θ)
  linarith only [hi, hf]

/-- Equal profiles and equal left charts give the same actual return
residual; the inverses used in that residual are fixed by N01. -/
theorem n08_returnResidualField_zero_parameter_eq
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {x y : AnnularState S}
    (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hy : (y, 0) ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hp : stateProfile D S C x = stateProfile D S C y)
    (hc : ∀ m θ, stateLeftChart S x m θ = stateLeftChart S y m θ)
    (m : ℕ) (θ : ℝ) :
    returnResidualField S C (x, 0) m θ = returnResidualField S C (y, 0) m θ := by
  have hm : ∀ t, C.minusReturnInverse (x, 0) m t = C.minusReturnInverse (y, 0) m t := by
    intro t
    rw [n08_minusReturnInverse_zero_parameter hS hT hN x hx hsx,
      n08_minusReturnInverse_zero_parameter hS hT hN y hy hsy, hp]
  have hchart : ∀ t, rightChartCandidate S C (x, 0) m t =
      rightChartCandidate S C (y, 0) m t := by
    intro t
    simp only [rightChartCandidate, oddPart, hm, hc]
  have hi : C.rightChartInverse (x, 0) m θ = C.rightChartInverse (y, 0) m θ := by
    have hleft : ∀ t, C.rightChartInverse (x, 0) m (rightChartCandidate S C (x, 0) m t) = t := by
      obtain ⟨_, _, _, _, _, _, _, _, hinverse, _⟩ := hN
      exact fun t => (hinverse (x, 0) hx hsx m t).2.2.2
    have hright : rightChartCandidate S C (y, 0) m (C.rightChartInverse (y, 0) m θ) = θ := by
      obtain ⟨_, _, _, _, _, _, _, _, hinverse, _⟩ := hN
      exact (hinverse (y, 0) hy hsy m θ).2.2.1
    calc
      _ = C.rightChartInverse (x, 0) m
          (rightChartCandidate S C (y, 0) m (C.rightChartInverse (y, 0) m θ)) :=
        congrArg (C.rightChartInverse (x, 0) m) hright.symm
      _ = C.rightChartInverse (x, 0) m
          (rightChartCandidate S C (x, 0) m (C.rightChartInverse (y, 0) m θ)) :=
        congrArg (C.rightChartInverse (x, 0) m) (hchart _).symm
      _ = _ := hleft _
  simp only [returnResidualField, evenPart, hi, hm, hc]

theorem n08_returnResidualField_zero_parameter_eq_of_tail
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {x y : AnnularState S}
    (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hy : (y, 0) ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y) (htail : x.2 = y.2)
    (m : ℕ) (θ : ℝ) :
    returnResidualField S C (x, 0) m θ = returnResidualField S C (y, 0) m θ := by
  apply n08_returnResidualField_zero_parameter_eq hS hT hN hx hy hsx hsy
  · funext r
    simp only [stateProfile, stateKappa, htail]
  · intro m θ
    simp only [stateLeftChart, htail]

theorem n08_returnResidual_zero_parameter_eq_of_tail {R : ReturnEquationData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε)
    {x y : AnnularState S}
    (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hy : (y, 0) ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y) (htail : x.2 = y.2) :
    R.residual (x, 0) = R.residual (y, 0) := by
  apply (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  funext m θ
  rw [hR.2.1 (x, 0) hx hsx, hR.2.1 (y, 0) hy hsy]
  exact n08_returnResidualField_zero_parameter_eq_of_tail hS hT hN hx hy hsx hsy htail m θ

end ContinuousFlexibility.Statements
