module

public import ContinuousFlexibility.Analysis.N05ReferenceZeroRemainder
public import ContinuousFlexibility.Analysis.N05ReferenceNormalFieldBounds
public import ContinuousFlexibility.Analysis.N05CanonicalRadialJetChoice
public import ContinuousFlexibility.Analysis.N05CanonicalRadialPairing
public import ContinuousFlexibility.Analysis.N05CanonicalOutputChoice

/-!
# The actual weighted physical field realizes the fixed canonical radial jet

The normal field uses the true height and Jacobian on each physical
piece. Its weak canonical derivative is identified with one fixed L²
sequence, and the material shift is chosen before any endpoint exponent
or angular order. No parity hypothesis is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial

theorem n05CanonicalRadialJetSequence_of_physical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K) :
    ∃ A : ℝ, 0 < A ∧ ∀ γ : ℝ, 0 < γ → ∀ M : ℝ, ∃ B : ℝ, 0 < B ∧
      ∀ u ur : PolarPoint → ℝ,
      Function.Periodic u (0, Real.pi) → Function.Periodic ur (0, Real.pi) →
      MemLp u 2 (referenceWeightedMeasure D γ (-M)) →
      MemLp ur 2 (referenceWeightedMeasure D γ (-M)) → WeakNormalDerivative D u ur →
      (∀ m, n05WeakCanonicalRadialDerivative S K m
        (n05CanonicalHeightL2Sequence S C K u m)
        (n05CanonicalRadialJetSequence S K (n05CanonicalHeightL2Sequence S C K u) m)) ∧
      n05CanonicalRadialJetSequence S K (n05CanonicalHeightL2Sequence S C K u) =
        n05CanonicalHeightL2Sequence S C K (n05ReferenceRadialNormalField S C K u ur) ∧
      MemLp (n05ReferenceRadialNormalField S C K u ur) 2
        (referenceWeightedMeasure D γ (-(M + A))) ∧
      ‖n05CanonicalRadialJetSequence S K (n05CanonicalHeightL2Sequence S C K u)‖ ^ 2 +
        outputNormSquare D γ (M + A) 0 (n05ReferenceRadialNormalField S C K u ur, 0) ≤
          B * (outputNormSquare D γ M 0 (u, 0) + outputNormSquare D γ M 0 (ur, 0)) := by
  obtain ⟨C0, A, hC0, hA, hfield⟩ :=
    n05ReferenceRadialNormalField_weighted_bound hD hT h hcoordinates
  refine ⟨A, hA, fun γ hγ M => ?_⟩
  obtain ⟨_, _, hbase⟩ := n05_referenceOutput_canonicalHeight_choice_bound hD hT h hcoordinates hγ M
  obtain ⟨Cg, hCg, hheight⟩ :=
    n05_referenceOutput_canonicalHeight_choice_bound hD hT h hcoordinates hγ (M + A)
  obtain ⟨_, _, hphysical⟩ := n05_referenceWeighted_physical_square_bound hD hγ (-M)
  obtain ⟨_, _, hphysicalg⟩ :=
    n05_referenceWeighted_physical_square_bound hD hγ (-(M + A))
  have hab := hD.choose_spec.1.2.1.le
  have hpart := hD.choose_spec.2.1
  refine ⟨(Cg + 1) * C0, by positivity, fun u ur hup hurp hu hur hweak => ?_⟩
  let g := n05ReferenceRadialNormalField S C K u ur
  obtain ⟨hg, hgnorm⟩ := hfield γ M u ur hu hur
  obtain ⟨huc, hus⟩ := (memLp_referenceWeightedMeasure_iff hab hpart).mp hu
  obtain ⟨hgc, hgs⟩ := (memLp_referenceWeightedMeasure_iff hab hpart).mp hg
  rw [sourceCellSquare_neg_fun] at hus hgs
  have hurep := (hbase u huc hus).1
  obtain ⟨hgrep, hseq⟩ := hheight g hgc hgs
  have hgp : Function.Periodic g (0, Real.pi) := n05ReferenceRadialNormalField_periodic hup hurp
  have hw (m : ℕ) : n05WeakCanonicalRadialDerivative S K m
      (n05CanonicalHeightL2Sequence S C K u m) (n05CanonicalHeightL2Sequence S C K g m) :=
    n05_weakCanonicalRadialDerivative_of_physical h hcoordinates hab m hup hgp
      (hphysical u hu).1 (hphysical ur hur).1 (hphysicalg g hg).1 hweak
      (fun p hp => n05ReferenceRadialNormalField_eq h hcoordinates m hp u ur)
      (hurep m) (hgrep m)
  have he := n05CanonicalRadialJetSequence_eq_of_weak hw
  refine ⟨n05CanonicalRadialJetSequence_weak hw, he, hg, ?_⟩
  rw [he]
  have hn : ‖n05CanonicalHeightL2Sequence S C K g‖ ^ 2 ≤
      Cg * outputNormSquare D γ (M + A) 0 (g, 0) := by
    simpa only [outputNormSquare, n05_outputRemainder_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using hseq
  calc
    _ ≤ (Cg + 1) * outputNormSquare D γ (M + A) 0 (g, 0) := by linarith only [hn]
    _ ≤ (Cg + 1) * (C0 *
        (outputNormSquare D γ M 0 (u, 0) + outputNormSquare D γ M 0 (ur, 0))) :=
      mul_le_mul_of_nonneg_left hgnorm (by positivity)
    _ = _ := by ring

end ContinuousFlexibility.Statements
