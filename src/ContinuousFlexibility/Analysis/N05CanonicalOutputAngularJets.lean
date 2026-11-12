import ContinuousFlexibility.Analysis.N05CanonicalOutputChoice
import ContinuousFlexibility.Analysis.N05ReferenceFullAngularSobolev
import ContinuousFlexibility.Analysis.N05ReferenceNormalizerJets
import ContinuousFlexibility.Analysis.N05ReferenceZeroRemainder

/-!
# Actual angular output jets and their canonical L² representatives

The same physical inverse supplies every positive angular jet. Its
periodic representative has a weighted physical bound and hence one
canonical height sequence. Subtracting any multiple of the prescribed
radial cutoff leaves these positive angular derivatives unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Radial

theorem n05_weakReferenceAngularJet_sub_radial
    {D : ReferenceData} (hab : D.a ≤ D.b) {u d : PolarPoint → ℝ}
    {j : ℕ} (hj : 0 < j)
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hd : MemLp d 2 (radialPhysicalMeasure D))
    (h : n05_weakReferenceAngularJet D u d j)
    (χ : ℝ → ℝ) (hχ : Continuous χ) (a : ℝ) :
    n05_weakReferenceAngularJet D (fun p => u p - a * χ p.1) d j := by
  have hχLp : MemLp (fun p : PolarPoint => χ p.1) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (hχ.comp continuous_fst)
  have hzLp : MemLp (fun _ : PolarPoint => (0 : ℝ)) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp continuous_const
  have hχjet : n05_weakReferenceAngularJet D (fun p => χ p.1)
      (fun _ => 0) j := by
    have hh := n05_referenceAngularJet_weak_of_smooth_slices D (fun p => χ p.1)
      (fun r => by
        simpa only using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => χ r)))
      (fun _ _ => rfl) j
    simpa only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_const,
      if_neg (Nat.ne_of_gt hj)] using hh
  have hs := n05_weakReferenceAngularJet_add hab hu (hχLp.const_mul (-a))
    hd (hzLp.const_mul (-a)) h (n05_weakReferenceAngularJet_const_mul hχjet (-a))
  convert hs using 1 <;> funext p <;> simp only [Pi.add_apply, mul_zero, add_zero] <;> ring

/-- Every positive angular jet of this physical inverse has an actual
canonical representative. The same field differentiates every radial
cutoff remainder, including the one used by the global canonical inverse.
The physical and canonical square bounds use the original material
exponents, chosen before the angular order. -/
theorem n05_referenceInverse_canonicalAngularJet_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {γ M0 M1 : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M0 M1 G) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ F, SourceMember D γ M0 F →
      ∀ (j : ℕ), 0 < j → ∀ fder : PolarPoint → ℝ,
      SourceDerivativeMember D γ M0 fder →
      n05_weakReferenceAngularJet D F.1 fder j →
      ∃ d : PolarPoint → ℝ,
        Function.Periodic d (0, Real.pi) ∧
        n05_weakReferenceAngularJet D (G F).1 d j ∧
        (∀ a : ℝ, n05_weakReferenceAngularJet D
          (fun p => (G F).1 p - a * S.chiLeft p.1) d j) ∧
        MemLp d 2 (referenceWeightedMeasure D γ (-M1)) ∧
        (∀ m, (n05CanonicalHeightL2Sequence S C K d m : PolarPoint → ℝ)
          =ᵐ[canonicalMeasure S K m] canonicalHeight S K (C.referenceState, 0) m d) ∧
        ‖n05CanonicalHeightL2Sequence S C K d‖ ^ 2 +
            outputNormSquare D γ M1 0 (d, 0) ≤
          C0 * (sourceNormSquare D γ M0 (fder, 0) +
            (2 : ℝ) ^ (2 * j) * sourceNormSquare D γ M0 F) := by
  obtain ⟨Cg, hCg, hjet⟩ :=
    n05_referenceInverse_positiveAngularSobolev_bound hD.1 hD.2.2.2.1 hγ hG
  obtain ⟨Cc, hCc, hchoice⟩ :=
    n05_referenceOutput_canonicalHeight_choice_bound hD.1 hT h hcoordinates hγ M1
  refine ⟨(Cc + 1) * Cg ^ 2, by positivity, fun F hF j hj fder hfd hweak => ?_⟩
  obtain ⟨d, hdweak, hd, hbound, hdperiodic⟩ := hjet F hF j hj fder hfd hweak
  have hab := hD.1.choose_spec.1.2.1.le
  have hpart := hD.1.choose_spec.2.1
  obtain ⟨hc, hs⟩ := (memLp_referenceWeightedMeasure_iff hab hpart).mp hd
  have hsout : Summable (outputCellSquare D γ M1 d) := by
    simpa only [sourceCellSquare_neg_fun] using hs
  obtain ⟨hrep, hnorm⟩ := hchoice d hc hsout
  have hnormOut : ‖n05CanonicalHeightL2Sequence S C K d‖ ^ 2 ≤
      Cc * outputNormSquare D γ M1 0 (d, 0) := by
    simpa only [outputNormSquare, n05_outputRemainder_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using hnorm
  have hu : MemLp (G F).1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD.1 hD.2.2.2.1 hγ (hG.1 F hF).1
  have hdp : MemLp d 2 (radialPhysicalMeasure D) :=
    r11b_sourceDerivative_memLp hD.1 hγ (show SourceDerivativeMember D γ (-M1) d from ⟨hc, hs⟩)
  refine ⟨d, hdperiodic, hdweak,
    fun a => n05_weakReferenceAngularJet_sub_radial hab hj hu hdp hdweak
      S.chiLeft hS.2.2.1.1.continuous a, hd, hrep, ?_⟩
  calc
    _ ≤ (Cc + 1) * outputNormSquare D γ M1 0 (d, 0) := by
      linarith only [hnormOut]
    _ ≤ (Cc + 1) * (Cg ^ 2 * (sourceNormSquare D γ M0 (fder, 0) +
        (2 : ℝ) ^ (2 * j) * sourceNormSquare D γ M0 F)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

end ContinuousFlexibility.Statements
