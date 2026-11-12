import ContinuousFlexibility.Analysis.N05CanonicalGraphRepresentatives
import ContinuousFlexibility.Analysis.N05ReferenceLeftConstant

/-!
# The canonical left scalar is fixed by physical endpoint integrability

The physical cutoff can differ from the radial reference cutoff. Its actual
left tail is sufficient: the reciprocal square root of the profile times
that cutoff cannot lie in L². Two physical remainders with this endpoint
integrability therefore have the same left scalar.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open ContinuousFlexibility.Radial

theorem n05_physicalCutoff_leftConstant_unique
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {χ : ℝ → ℝ} (hχ : CutoffConditions D χ)
    {η ζ : PolarPoint → ℝ} {a b : ℝ}
    (hηζ : η =ᵐ[radialPhysicalMeasure D] ζ)
    (ha : MemLp (fun p : PolarPoint =>
      Real.sqrt ((D.w p.1)⁻¹) * (η p - a * χ p.1)) 2 (radialPhysicalMeasure D))
    (hb : MemLp (fun p : PolarPoint =>
      Real.sqrt ((D.w p.1)⁻¹) * (ζ p - b * χ p.1)) 2 (radialPhysicalMeasure D)) :
    a = b := by
  by_contra hab
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hscaled := (ha.sub hb).const_mul ((b - a)⁻¹)
  have htailLp : MemLp (fun p : PolarPoint =>
      Real.sqrt ((D.w p.1)⁻¹) * χ p.1) 2 (radialPhysicalMeasure D) := by
    apply MemLp.ae_eq _ hscaled
    filter_upwards [hηζ] with p hp
    change (b - a)⁻¹ *
      (Real.sqrt ((D.w p.1)⁻¹) * (η p - a * χ p.1) -
        Real.sqrt ((D.w p.1)⁻¹) * (ζ p - b * χ p.1)) =
      Real.sqrt ((D.w p.1)⁻¹) * χ p.1
    rw [hp]
    have hd : Real.sqrt ((D.w p.1)⁻¹) * (ζ p - a * χ p.1) -
        Real.sqrt ((D.w p.1)⁻¹) * (ζ p - b * χ p.1) =
        (b - a) * (Real.sqrt ((D.w p.1)⁻¹) * χ p.1) := by ring
    rw [hd, ← mul_assoc, inv_mul_cancel₀ hba, one_mul]
  obtain ⟨ε, hε, _, htail, _⟩ := hχ.2.1
  apply n05_not_memLp_tailCutoff_inverse_sqrt hD.choose_spec.1
    ⟨ε, hε, fun r hr => htail r hr.2.le⟩
  simpa only [r11b_radialAngularMean_const] using
    (r11b_radialAngularMean_L2_bound htailLp).1

/-- Physical graph uniqueness and the actual endpoint L² class identify
all canonical coordinates and all three scalars. -/
theorem n05_canonicalGraph_unique_of_endpoint_memLp
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε γ M0 M1 : ℝ}
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    (h04 : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M0 M1 G)
    {U V : CanonicalUnknown S K} {F : CanonicalSequence S K}
    {η ζ f g : PolarPoint → ℝ}
    (hU : HasCanonicalRepresentation D S C K (C.referenceState, 0) U F η f)
    (hV : HasCanonicalRepresentation D S C K (C.referenceState, 0) V F ζ g)
    (hη : ReferenceGraph D γ M0 M1 (η, U.2.2.1)
      ((fun p => f p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p), 0))
    (hζ : ReferenceGraph D γ M0 M1 (ζ, V.2.2.1)
      ((fun p => g p - V.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p), 0))
    (hηLp : MemLp (fun p : PolarPoint =>
      Real.sqrt ((D.w p.1)⁻¹) * (η p - U.2.1 * S.chiLeft p.1))
        2 (radialPhysicalMeasure D))
    (hζLp : MemLp (fun p : PolarPoint =>
      Real.sqrt ((D.w p.1)⁻¹) * (ζ p - V.2.1 * S.chiLeft p.1))
        2 (radialPhysicalMeasure D)) : U = V := by
  obtain ⟨_, haux, hμ, hheight⟩ := n05_canonicalGraph_physical_representatives_unique
    hD hS h04 hcoordinates hγ hG hU hV hη hζ
  have ha := n05_physicalCutoff_leftConstant_unique hD hS.2.2.1 hheight hηLp hζLp
  have hrem : (fun p : PolarPoint => η p - U.2.1 * S.chiLeft p.1)
      =ᵐ[radialPhysicalMeasure D] (fun p => ζ p - V.2.1 * S.chiLeft p.1) := by
    filter_upwards [hheight] with p hp
    rw [hp, ha]
  apply Prod.ext
  · apply lp.ext
    funext m
    apply Lp.ext
    exact (hU.1 m).trans
      ((n05_referenceCanonical_representatives_congr_ae h04 hcoordinates hrem m).1.trans
        (hV.1 m).symm)
  · exact Prod.ext ha (Prod.ext hμ haux)

end ContinuousFlexibility.Statements
