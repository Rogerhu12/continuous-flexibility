module

public import ContinuousFlexibility.Analysis.N05CanonicalOutputL2

/-!
# One canonical L² height sequence independent of the weight

A physical field has at most one sequence of genuine canonical L²
representatives. Selecting that sequence where it exists gives one fixed
map, independent of an endpoint exponent, material exponent, or proof of
membership. Actual positively attenuated outputs always have this sequence.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory

/-- The unique L² sequence of actual canonical height representatives,
totalized by zero when no such sequence exists. -/
def n05CanonicalHeightL2Sequence (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (f : PolarPoint → ℝ) : CanonicalL2Sequence S K := by
  classical
  exact if h : ∃ v : CanonicalL2Sequence S K, ∀ m,
      (v m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalHeight S K (C.referenceState, 0) m f
    then h.choose else 0

theorem n05CanonicalHeightL2Sequence_unique
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {K : CanonicalData S}
    {f : PolarPoint → ℝ} {v w : CanonicalL2Sequence S K}
    (hv : ∀ m, (v m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m f)
    (hw : ∀ m, (w m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m f) : v = w := by
  apply lp.ext
  funext m
  exact Lp.ext ((hv m).trans (hw m).symm)

theorem n05CanonicalHeightL2Sequence_eq_of_rep
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {K : CanonicalData S}
    {f : PolarPoint → ℝ} {v : CanonicalL2Sequence S K}
    (hv : ∀ m, (v m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m f) :
    n05CanonicalHeightL2Sequence S C K f = v := by
  classical
  have hex : ∃ w : CanonicalL2Sequence S K, ∀ m,
      (w m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalHeight S K (C.referenceState, 0) m f := ⟨v, hv⟩
  rw [n05CanonicalHeightL2Sequence, dite_eq_left hex]
  exact n05CanonicalHeightL2Sequence_unique hex.choose_spec hv

/-- The fixed choice depends only on the actual physical equivalence class,
including the case where neither representative defines an L² sequence. -/
theorem n05CanonicalHeightL2Sequence_congr_ae
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {f g : PolarPoint → ℝ} (hfg : f =ᵐ[radialPhysicalMeasure D] g) :
    n05CanonicalHeightL2Sequence S C K f = n05CanonicalHeightL2Sequence S C K g := by
  classical
  have he (m : ℕ) := (n05_referenceCanonical_representatives_congr_ae h hcoordinates hfg m).1
  by_cases hf : ∃ v : CanonicalL2Sequence S K, ∀ m,
      (v m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalHeight S K (C.referenceState, 0) m f
  · obtain ⟨v, hv⟩ := hf
    exact (n05CanonicalHeightL2Sequence_eq_of_rep hv).trans
      (n05CanonicalHeightL2Sequence_eq_of_rep (fun m => (hv m).trans (he m))).symm
  · have hg : ¬ ∃ v : CanonicalL2Sequence S K, ∀ m,
        (v m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          canonicalHeight S K (C.referenceState, 0) m g := by
      rintro ⟨v, hv⟩
      exact hf ⟨v, fun m => (hv m).trans (he m).symm⟩
    simp only [n05CanonicalHeightL2Sequence, dite_eq_right hf, dite_eq_right hg]

/-- The same weight-independent choice represents every positively
weighted field, including odd angular derivatives of an output. -/
theorem n05_referenceOutput_canonicalHeight_choice_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ f : PolarPoint → ℝ,
      RadialCellIntegrable D f → Summable (outputCellSquare D γ M f) →
      (∀ m, (n05CanonicalHeightL2Sequence S C K f m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] canonicalHeight S K (C.referenceState, 0) m f) ∧
      ‖n05CanonicalHeightL2Sequence S C K f‖ ^ 2 ≤
        C0 * ∑' m, outputCellSquare D γ M f m := by
  obtain ⟨C0, hC0, hbound⟩ :=
    n05_referenceOutput_canonicalHeight_l2Sequence hD hT h hcoordinates hγ M
  refine ⟨C0, hC0, fun f hf hs => ?_⟩
  obtain ⟨v, hv, hnorm⟩ := hbound f hf hs
  simp only [n05CanonicalHeightL2Sequence_eq_of_rep hv]
  exact ⟨hv, hnorm⟩

/-- One fixed map represents every actual positively attenuated output;
the map itself is independent of all weight exponents. -/
theorem n05_outputRealization_canonicalHeight_choice_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (a : ℝ) (U : RadialUnknown),
      OutputRealization D γ M a U →
      (∀ m, (n05CanonicalHeightL2Sequence S C K (fun p => U.1 p - a * S.chiLeft p.1)
        m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          canonicalHeight S K (C.referenceState, 0) m
            (fun p => U.1 p - a * S.chiLeft p.1)) ∧
      ‖n05CanonicalHeightL2Sequence S C K (fun p => U.1 p - a * S.chiLeft p.1)‖ ^ 2 ≤
        C0 * outputNormSquare D γ M a U := by
  obtain ⟨C0, hC0, hbound⟩ :=
    n05_outputRealization_canonicalHeight_l2Sequence hD hT hS h hcoordinates hγ M
  refine ⟨C0, hC0, fun a U hU => ?_⟩
  obtain ⟨v, hv, hnorm⟩ := hbound a U hU
  simp only [n05CanonicalHeightL2Sequence_eq_of_rep hv]
  exact ⟨hv, hnorm⟩

end ContinuousFlexibility.Statements
