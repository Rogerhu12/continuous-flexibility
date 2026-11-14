import ContinuousFlexibility.Analysis.N04RealizationJetScalars
import ContinuousFlexibility.Analysis.N06PrimitiveJetRescaling
import ContinuousFlexibility.Analysis.N07aGeometryJetBounds
import ContinuousFlexibility.Analysis.MaterialSampleBounds
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# The same primitive atoms have absolute canonical-coordinate bounds

The actual reference jets and actual current difference jets are added before
undoing the fixed affine rescaling. The inverse length comes from the same
reference atom family. A sampled material floor is explicit throughout;
there is one state loss, chosen before every spatial order.

No canonical-potential bound, divided-field bound, or N04Properties premise
is used here. The primitive jet hypotheses are construction obligations.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}

/-- The absolute unit-strip estimate retains the actual state and atom. -/
def N04RealizationUnitAtomBoundAtOrder
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (K : CanonicalData S) (base loss : ℕ) (ε : ℝ) (s : ℕ) (B : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ m a p, p ∈ unitStrip → ∀ i j : ℕ, i + j ≤ s →
      |mixedDerivative i j (atom D T S C L K z m a) p| ≤
        B * T.E0 (T.sample (K.cell m)) ^ B *
          (1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|)

private theorem n04Realization_unitAtom_fixed_order
    (hrefState : referenceStateConditions D S C)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m)))
    {d s : ℕ} {A B M : ℝ} (hA : 0 < A) (hB : 0 < B) (hM : 0 ≤ M)
    (hrefbound : ∀ m a p, p ∈ unitStrip → ∀ i j : ℕ, i + j ≤ s →
      |mixedDerivative i j (atom D T S C L K (C.referenceState, 0) m a) p| ≤
        A * T.E0 (T.sample (K.cell m)) ^ A)
    (hheight : ∀ m, T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) ≤ M)
    (hdiff : ∀ z ∈ stateNeighborhood S C base ε, ∀ hs : stateSector S z.1,
      ∀ m a p, p ∈ unitStrip → ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j
          (fun q => atom D T S C L K z m a q -
            atom D T S C L K (C.referenceState, 0) m a q) p| ≤
          B * T.E0 (T.sample (K.cell m)) ^ B *
            T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
              (stateGrading S (s + d) (z.1 - C.referenceState) + |z.2|)) :
    ∃ Q : ℝ, 0 < Q ∧
      N04RealizationUnitAtomBoundAtOrder D T S C L K base d ε s Q := by
  obtain ⟨Q, hQ, hscalar⟩ := n04Realization_referenceAndDifferenceEnvelope hA.le hB.le hM
  refine ⟨Q, hQ, fun z hz hs m a p hp i j hij => ?_⟩
  let w : Parameter S := n06PrimitiveParameterOfState hrefState z hs
  have hw : w ∈ sectorNeighborhood S base ε ε :=
    n06PrimitiveParameterOfState_mem hrefState hz hs
  have he := n07a_geometryAtom_jet_decomposition href hcur w hw m a ⟨p, hp⟩ i j
  dsimp only [w] at he
  simp only [differenceJets, n06PrimitiveParameterOfState_lift] at he
  rw [he]
  have h := hscalar (T.E0 (T.sample (K.cell m)))
    (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ))
    (stateGrading S (s + d) (z.1 - C.referenceState) + |z.2|)
    _ _ (hfloor m) (hheight m)
    (add_nonneg (apply_nonneg _ _) (abs_nonneg _))
    (hrefbound m a p hp i j hij) (hdiff z hz hs m a p hp i j hij)
  simpa only [add_assoc] using h

/-- One fixed loss controls every current absolute atom at every spatial
order, on exactly the neighborhood in the primitive current certificate. -/
theorem n04Realization_unitAtom_jet_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hrefState : referenceStateConditions D S C)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m))) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      N04RealizationUnitAtomBoundAtOrder D T S C L K base d ε s B := by
  obtain ⟨M, hM, hheight⟩ := material_sample_height_coefficient_power_bounded
    hD hT K.cell 0 (by norm_num : 0 < (3 / 4 : ℝ))
  obtain ⟨d, hdiff⟩ := n06_primitive_currentAtom_difference_jets hrefState hcur
  refine ⟨d, fun s => ?_⟩
  obtain ⟨A, hA, hrefbound⟩ := href.2 s
  obtain ⟨B, hB, hdiffbound⟩ := hdiff s
  exact n04Realization_unitAtom_fixed_order hrefState href hcur hfloor hA hB hM.le
    hrefbound (fun m => by simpa only [Real.rpow_zero, mul_one] using hheight m)
    hdiffbound

/-- The affine lift retains the exact sum grading of the sector parameter. -/
theorem n04Realization_parameterGrading_lift (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (n : ℕ) (z : Parameter S) :
    stateGrading S n ((liftSectorParameter S C z).1 - C.referenceState) +
        |(liftSectorParameter S C z).2| = parameterGrading S n z := by
  simp only [liftSectorParameter, add_sub_cancel_left, parameterGrading,
    pairGrading_apply, sectorGrading, Seminorm.comp_apply, Submodule.subtype_apply,
    realGrading, coe_normSeminorm, Real.norm_eq_abs]

private theorem n04Realization_allOrderEnvelope_mono
    {P Q : ℕ → ℕ → ℝ → Prop}
    (hP : ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ P d s B)
    (hPQ : ∀ d s B, P d s B → Q d s B) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ Q d s B := by
  obtain ⟨d, hd⟩ := hP
  refine ⟨d, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hd s
  exact ⟨B, hB, hPQ d s B hbound⟩

/-- The all-atom bound in the native sector-parameter coordinates of
CurrentJets. This is the same estimate, with no extra loss. -/
theorem n04Realization_sectorAtom_jet_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hrefState : referenceStateConditions D S C)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m))) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m a (p : unitStrip) i j,
        i + j ≤ s →
          |mixedDerivative i j (atom D T S C L K (liftSectorParameter S C z) m a) p.val| ≤
            B * T.E0 (T.sample (K.cell m)) ^ B * (1 + parameterGrading S (s + d) z) := by
  refine n04Realization_allOrderEnvelope_mono
    (P := fun d s B => N04RealizationUnitAtomBoundAtOrder D T S C L K base d ε s B)
    (hP := n04Realization_unitAtom_jet_bounds
      (S := S) (C := C) (L := L) (K := K) (base := base) (ε := ε)
      hD hT hrefState href hcur hfloor) ?_
  intro d s B hb z hz m a p i j hij
  have h := hb (liftSectorParameter S C z)
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (hrefState.liftSectorParameter_sector z) m a p.val p.property i j hij
  simpa only [add_assoc, n04Realization_parameterGrading_lift] using h

/-- A complete-function identity on the unit strip identifies the field
whose actual jets are bounded on the original canonical interval. -/
def N04RealizationCanonicalAtomBoundAtOrder
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (K : CanonicalData S) (base loss : ℕ) (ε : ℝ) (s : ℕ) (B : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ m a (f : PolarPoint → ℝ),
      EqOn (f ∘ canonicalUnitPoint K m) (atom D T S C L K z m a) unitStrip →
      ∀ i j : ℕ, i + j ≤ s → ∀ p ∈ canonicalOpen S K m,
        |mixedDerivative i j f p| ≤
          B * T.E0 (T.sample (K.cell m)) ^ B *
            (1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|)

private theorem n04Realization_canonicalAtom_fixed_order
    (hlen : ∀ m, K.left m < K.right m)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m)))
    {d s : ℕ} {B P : ℝ} (hB : 0 < B) (hP : 0 < P)
    (hlength : ∀ m, 1 ≤ P * T.E0 (T.sample (K.cell m)) ^ P ∧
      |K.right m - K.left m| ≤ P * T.E0 (T.sample (K.cell m)) ^ P ∧
      |(K.right m - K.left m)⁻¹| ≤ P * T.E0 (T.sample (K.cell m)) ^ P)
    (hb : N04RealizationUnitAtomBoundAtOrder D T S C L K base d ε s B) :
    ∃ Q : ℝ, 0 < Q ∧
      N04RealizationCanonicalAtomBoundAtOrder D T S C L K base d ε s Q := by
  obtain ⟨Q, hQ, hcost⟩ := coefficientEnvelope_pack (B * P ^ s) (B + P * (s : ℝ))
  refine ⟨Q, hQ, fun z hz hs m a f heq i j hij p hp => ?_⟩
  let q : PolarPoint := n07aCanonicalUnitInversePoint K m p
  have hq : q ∈ unitStrip := n07aCanonicalUnitInversePoint_maps (hlen m) hp
  let rho : ℝ := 1 + stateGrading S (s + d) (z.1 - C.referenceState) + |z.2|
  have hrho : 0 ≤ rho :=
    add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (abs_nonneg _)
  have hE : 0 < T.E0 (T.sample (K.cell m)) := zero_lt_one.trans_le (hfloor m)
  have hunit : |mixedDerivative i j (atom D T S C L K z m a) q| ≤
      B * T.E0 (T.sample (K.cell m)) ^ B * 1 * rho := by
    simpa only [mul_one] using hb z hz hs m a q hq i j hij
  have hscaled := n06_inverseLength_weighted_jet_bound
    (sub_pos.mpr (hlen m)) hE zero_le_one hB.le hP.le hrho
    (by omega : i ≤ s) (hlength m).1 (hlength m).2.2 hunit
  have hjet := congrArg abs (n06_mixedJet_of_unit_identity m (hlen m) heq i j hp)
  calc
    |mixedDerivative i j f p| =
        |(K.right m - K.left m)⁻¹ ^ i *
          mixedDerivative i j (atom D T S C L K z m a) q| := hjet
    _ ≤ (B * P ^ s * rho) *
        (1 * T.E0 (T.sample (K.cell m)) ^ (B + P * (s : ℝ))) := hscaled
    _ = (B * P ^ s * T.E0 (T.sample (K.cell m)) ^ (B + P * (s : ℝ))) * rho := by ring
    _ ≤ (Q * T.E0 (T.sample (K.cell m)) ^ Q) * rho :=
      mul_le_mul_of_nonneg_right (hcost _ (hfloor m)) hrho

/-- The same primitive jet certificates imply absolute jets in the
original canonical variables. Only the numerical constants change with
spatial order; the state loss and neighborhood remain fixed. -/
theorem n04Realization_canonicalAtom_jet_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hrefState : referenceStateConditions D S C)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hlen : ∀ m, K.left m < K.right m)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m))) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      N04RealizationCanonicalAtomBoundAtOrder D T S C L K base d ε s B := by
  obtain ⟨P, hP, hlength⟩ := n06_referenceCanonicalLength_envelope href hlen
  obtain ⟨d, hunit⟩ := n04Realization_unitAtom_jet_bounds hD hT hrefState href hcur hfloor
  refine ⟨d, fun s => ?_⟩
  obtain ⟨B, hB, hb⟩ := hunit s
  exact n04Realization_canonicalAtom_fixed_order hlen hfloor hB hP hlength hb

end ContinuousFlexibility.Analysis
