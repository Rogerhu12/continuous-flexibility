import ContinuousFlexibility.Radial.ReferenceGraphClosed

/-!
# Replacing the actual representative of a reference graph

The field may be replaced by an a.e. equal physical representative while
retaining the original scalar datum and pointwise angular symmetries.
All weak pairings and the border row remain their genuine integrals.
-/

open Set Filter MeasureTheory

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

noncomputable section

theorem referenceOutputRealization_congr_ae {D : ReferenceData}
    (hab : D.a ≤ D.b) {γ M aL : ℝ} {U : RadialUnknown} {v : PolarPoint → ℝ}
    (hU : OutputRealization D γ M aL U)
    (he : U.1 =ᵐ[radialPhysicalMeasure D] v)
    (hp : Function.Periodic v (0, Real.pi))
    (hv : ∀ r θ, v (r, -θ) = v (r, θ)) :
    OutputRealization D γ M aL (v, U.2) := by
  have hrem : outputRemainder D aL U =ᵐ[radialPhysicalMeasure D]
      outputRemainder D aL (v, U.2) := by
    filter_upwards [he] with x hx
    exact congrArg (fun z : ℝ => z - aL * D.chiLeft x.1) hx
  refine ⟨hU.1.congr_ae hrem, ?_, hp, hv⟩
  apply hU.2.1.congr
  intro m
  exact congrArg
    (fun z : ℝ => Real.exp (-2 * M * radialQ (D.cellIndex m) +
      2 * γ * radialS (D.cellIndex m)) * z)
    (referenceCellSquare_congr_ae hab m hU.1 hrem)

theorem reference_mean_pairing_congr_ae {D : ReferenceData} (hab : D.a ≤ D.b)
    {u v k : PolarPoint → ℝ}
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (he : u =ᵐ[radialPhysicalMeasure D] v)
    (hk : MemLp k 2 (radialPhysicalMeasure D)) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ) * k (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => v (r, θ) * k (r, θ)) := by
  have hv := (memLp_congr_ae he).mp hu
  have hleft := r11b_integral_angularMean_eq hab (hu.integrable_mul hk)
  have hright := r11b_integral_angularMean_eq hab (hv.integrable_mul hk)
  simp only [Pi.mul_apply] at hleft hright
  rw [hleft, hright]
  congr 1
  exact integral_congr_ae (he.mono fun x hx => congrArg (fun z : ℝ => z * k x) hx)

theorem referenceGraph_congr_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F) {v : PolarPoint → ℝ}
    (he : U.1 =ᵐ[radialPhysicalMeasure D] v)
    (hp : Function.Periodic v (0, Real.pi))
    (hv : ∀ r θ, v (r, -θ) = v (r, θ)) :
    ReferenceGraph D γ M₀ M₁ (v, U.2) F := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hu := r11b_output_memLp hD hborder hγ hgraph.1
  have hvLp := (memLp_congr_ae he).mp hu
  refine ⟨?_, hgraph.2.1, ?_, ?_⟩
  · obtain ⟨aL, hU⟩ := hgraph.1
    exact ⟨aL, referenceOutputRealization_congr_ae hgeom.2.1.le hU he hp hv⟩
  · have hrow : referenceRow D U.1 = referenceRow D v := by
      rw [referenceRow_eq_physical_pairing hgeom hborder hu,
        referenceRow_eq_physical_pairing hgeom hborder hvLp]
      congr 1
      exact integral_congr_ae (he.mono fun x hx =>
        congrArg (fun z : ℝ => z * (referenceColumn D x.1 * cosineMode 2 x.2)) hx)
    exact hrow.symm.trans hgraph.2.2.1
  · intro ψ hψ
    have hk := r11b_continuous_memLp (D := D) (r11b_continuous_radialPDE_test hgeom hψ.1)
    have hweak := reference_mean_pairing_congr_ae hgeom.2.1.le hu he hk
    change radialWeakPairing D U.1 ψ = radialWeakPairing D v ψ at hweak
    have h := hgraph.2.2.2 ψ hψ
    rw [hweak] at h
    exact h

end

end ContinuousFlexibility.Radial
