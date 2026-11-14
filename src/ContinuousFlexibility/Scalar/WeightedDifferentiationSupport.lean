module

public import ContinuousFlexibility.Scalar.WeightedDifferentiationPullback
public import ContinuousFlexibility.Scalar.Conservation

/-!
# Support and symmetry of the actual coordinate derivatives

At an exterior point a differentiable field has zero radial derivative
by uniqueness on a closed radial half-line. At a nondifferentiability
point its totalized Frechet derivative is zero. This proves support
preservation without imposing a boundary condition or positive weight.
The signed angular symmetry changes sign once per angular derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem scalar_contDiffOn_radialPartial
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (radialPartial f) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem scalar_contDiffOn_angularPartial
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (angularPartial f) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private theorem scalar_coordinatePartials_zero_on_radial_set
    {f : PolarPoint → ℝ} {s : Set ℝ} {r θ : ℝ}
    (hf : DifferentiableAt ℝ f (r, θ)) (hs : UniqueDiffOn ℝ s) (hr : r ∈ s)
    (hzero : ∀ t ∈ s, ∀ η, f (t, η) = 0) :
    radialPartial f (r, θ) = 0 ∧ angularPartial f (r, θ) = 0 := by
  have hrad := Radial.hasDerivAt_radialSlice hf
  have hz : HasDerivWithinAt (fun t => f (t, θ)) 0 s r :=
    (hasDerivWithinAt_const r s (0 : ℝ)).congr_of_mem
      (fun t ht => hzero t ht θ) hr
  have hrzero : radialPartial f (r, θ) = 0 :=
    (hs r hr).eq_deriv s hrad.hasDerivWithinAt hz
  have hang := Radial.hasDerivAt_angularSlice hf
  have he : (fun t => f (r, t)) = fun _ => (0 : ℝ) := funext (hzero r hr)
  rw [he] at hang
  exact ⟨hrzero, hang.unique (hasDerivAt_const θ (0 : ℝ))⟩

/-- Both actual partials preserve the zero extension. The same uniqueness
lemma handles either endpoint, including the endpoint itself. -/
theorem scalar_coordinatePartials_zero_outside
    {D : ReferenceData} {f : PolarPoint → ℝ}
    (hzero : ∀ p, p ∉ annularOpen D → f p = 0)
    (p : PolarPoint) (hp : p ∉ annularOpen D) :
    radialPartial f p = 0 ∧ angularPartial f p = 0 := by
  by_cases hd : DifferentiableAt ℝ f p
  · rcases p with ⟨r, θ⟩
    have hr : r ≤ D.a ∨ D.b ≤ r := by
      by_cases hleft : r ≤ D.a
      · exact Or.inl hleft
      · right
        by_contra hright
        exact hp ⟨⟨lt_of_not_ge hleft, lt_of_not_ge hright⟩, mem_univ _⟩
    rcases hr with hr | hr
    · exact scalar_coordinatePartials_zero_on_radial_set hd (uniqueDiffOn_Iic D.a) hr
        (fun t ht η => hzero (t, η) (fun h => (not_lt_of_ge ht) h.1.1))
    · exact scalar_coordinatePartials_zero_on_radial_set hd (uniqueDiffOn_Ici D.b) hr
        (fun t ht η => hzero (t, η) (fun h => (not_lt_of_ge ht) h.1.2))
  · simp only [radialPartial, angularPartial,
      fderiv_zero_of_not_differentiableAt hd, ContinuousLinearMap.zero_apply, and_self]

theorem scalar_radialPartial_even
    {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (heven : ∀ r θ, f (r, -θ) = f (r, θ))
    (hzero : ∀ p, p ∉ annularOpen D → f p = 0) :
    ∀ r θ, radialPartial f (r, -θ) = radialPartial f (r, θ) := by
  intro r θ
  by_cases hr : r ∈ Ioo D.a D.b
  · have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
    have hd (η : ℝ) : DifferentiableAt ℝ f (r, η) :=
      (hf.contDiffAt (hU.mem_nhds ⟨hr, mem_univ _⟩)).differentiableAt (by simp)
    have hleft := Radial.hasDerivAt_radialSlice (hd (-θ))
    have hright := Radial.hasDerivAt_radialSlice (hd θ)
    have he : (fun t => f (t, -θ)) = fun t => f (t, θ) :=
      funext (fun t => heven t θ)
    rw [he] at hleft
    exact hleft.unique hright
  · rw [(scalar_coordinatePartials_zero_outside hzero (r, -θ) (fun h => hr h.1)).1,
      (scalar_coordinatePartials_zero_outside hzero (r, θ) (fun h => hr h.1)).1]

/-- A signed reflection law changes sign after one angular partial. -/
theorem scalar_angularPartial_reflection
    {D : ReferenceData} {f : PolarPoint → ℝ} {σ : ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hpar : ∀ r θ, f (r, -θ) = σ * f (r, θ))
    (hzero : ∀ p, p ∉ annularOpen D → f p = 0) :
    ∀ r θ, angularPartial f (r, -θ) = -σ * angularPartial f (r, θ) := by
  intro r θ
  by_cases hr : r ∈ Ioo D.a D.b
  · have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
    have hd (η : ℝ) : DifferentiableAt ℝ f (r, η) :=
      (hf.contDiffAt (hU.mem_nhds ⟨hr, mem_univ _⟩)).differentiableAt (by simp)
    have hleft : HasDerivAt (fun t => f (r, -t))
        (-angularPartial f (r, -θ)) θ := by
      simpa only [Function.comp_def, mul_neg_one, id_eq] using!
        (Radial.hasDerivAt_angularSlice (hd (-θ))).comp θ (hasDerivAt_id θ).neg
    have hright : HasDerivAt (fun t => σ * f (r, t))
        (σ * angularPartial f (r, θ)) θ := by
      simpa only using! (Radial.hasDerivAt_angularSlice (hd θ)).const_mul σ
    have he : (fun t => f (r, -t)) = fun t => σ * f (r, t) := funext (hpar r)
    rw [he] at hleft
    have hresult := hleft.unique hright
    nlinarith only [hresult]
  · rw [(scalar_coordinatePartials_zero_outside hzero (r, -θ) (fun h => hr h.1)).2,
      (scalar_coordinatePartials_zero_outside hzero (r, θ) (fun h => hr h.1)).2, mul_zero]

theorem heightMember_radialPartial_of_weightedJets
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f)
    (hjets : ∀ a b c, MeasureTheory.MemLp
      (weightedPhysicalJet T γ a b c (radialPartial f)) 2 materialCylinderMeasure) :
    HeightMember D T γ (radialPartial f) := by
  refine ⟨scalar_contDiffOn_radialPartial (isOpen_Ioo.prod isOpen_univ) hf.1,
    scalar_radialPartial_even hf.1 hf.2.1 hf.2.2.2.1,
    periodic_radialPartial hf.2.2.1, ?_, hjets⟩
  exact fun p hp => (scalar_coordinatePartials_zero_outside hf.2.2.2.1 p hp).1

theorem heightMember_angularPartial_twice_of_weightedJets
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f)
    (hjets : ∀ a b c, MeasureTheory.MemLp
      (weightedPhysicalJet T γ a b c (angularPartial (angularPartial f)))
      2 materialCylinderMeasure) :
    HeightMember D T γ (angularPartial (angularPartial f)) := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hfirst := scalar_contDiffOn_angularPartial hU hf.1
  have hzero : ∀ p, p ∉ annularOpen D → angularPartial f p = 0 :=
    fun p hp => (scalar_coordinatePartials_zero_outside hf.2.2.2.1 p hp).2
  have hodd : ∀ r θ, angularPartial f (r, -θ) = (-1 : ℝ) * angularPartial f (r, θ) :=
    scalar_angularPartial_reflection hf.1
      (fun r θ => by simpa only [one_mul] using hf.2.1 r θ) hf.2.2.2.1
  have heven : ∀ r θ, angularPartial (angularPartial f) (r, -θ) =
      angularPartial (angularPartial f) (r, θ) := by
    intro r θ
    simpa only [neg_neg, one_mul] using scalar_angularPartial_reflection hfirst hodd hzero r θ
  exact ⟨scalar_contDiffOn_angularPartial hU hfirst, heven,
    periodic_angularPartial (periodic_angularPartial hf.2.2.1),
    fun p hp => (scalar_coordinatePartials_zero_outside hzero p hp).2, hjets⟩

end ContinuousFlexibility.Statements
