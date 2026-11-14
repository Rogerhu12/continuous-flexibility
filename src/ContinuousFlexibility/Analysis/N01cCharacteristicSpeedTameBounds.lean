module

public import ContinuousFlexibility.Analysis.N01cWholeSpeedPowerBounds
public import ContinuousFlexibility.Analysis.N01cEndpointReferenceBounds
public import ContinuousFlexibility.Analysis.N01cEndpointSamplePowerBounds
public import ContinuousFlexibility.Analysis.N01cEndpointMixedPowerNormalization
public import ContinuousFlexibility.Analysis.N01cOpticalEndpointPowerBounds
public import ContinuousFlexibility.Analysis.N01cBoundsRestriction
public import ContinuousFlexibility.Analysis.N01cStateInterpolation
public import ContinuousFlexibility.Blueprint.N01c.Statements

/-!
# The actual characteristic-speed tame estimate

The normalized rational factors and the actual optical square root are
combined before multilinear normalization. Both the radial endpoint power
and the physical material sample are unchanged. Reference subtraction
uses the genuine first jet of the complete speed on the common segment.
-/

@[expose] public section

noncomputable section


namespace ContinuousFlexibility.Analysis

/-- Select the common indices and radius before the opaque endpoint
witness is specialized to the actual state space. -/
private theorem n01c_common_speed_selection
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hi : ContinuousFlexibility.Statements.HasInterpolation p)
    (oldBase oldLoss offset : ℕ) {ε : ℝ} (hε : 0 < ε)
    (Ready Result : ℕ → ℕ → ℝ → Prop)
    (hReady : ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₀ → ∀ base loss : ℕ, Ready base loss ε')
    (hResult : ∀ base loss ε', 0 < ε' → oldBase ≤ base → oldLoss ≤ loss →
      ε' ≤ ε → ε' ≤ 1 / 2 →
      (∀ s : ℕ, ∃ B : ℝ, 1 ≤ B ∧
        ∀ n : ℕ, n ≤ s → ∀ x : X, p base x ≤ 1 →
        ∀ R : ℝ, 1 ≤ R → p (s + loss) x ≤ R →
          p (n + offset) x ≤ B * R ^ ((n : ℝ) / ((s : ℝ) + 1))) →
      Ready base loss ε' → Result base loss ε') :
    ∃ base loss : ℕ, ∃ ε' : ℝ,
      0 < ε' ∧ oldBase ≤ base ∧ oldLoss ≤ loss ∧ ε' ≤ ε ∧
        Result base loss ε' := by
  obtain ⟨ε₀, hε₀, hready⟩ := hReady
  obtain ⟨b, l, hIb⟩ := exists_seminorm_spatialPower_bound p hp hi offset
  let base := max oldBase b
  let loss := max oldLoss l
  let ε' := min ε (min ε₀ (1 / 2))
  have hε' : 0 < ε' := lt_min hε (lt_min hε₀ (by norm_num))
  have hεε : ε' ≤ ε := min_le_left _ _
  have hεopt : ε' ≤ ε₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hεhalf : ε' ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hbase : oldBase ≤ base := le_max_left _ _
  have hloss : oldLoss ≤ loss := le_max_left _ _
  refine ⟨base, loss, ε', hε', hbase, hloss, hεε,
    hResult base loss ε' hε' hbase hloss hεε hεhalf ?_
      (hready ε' hε' hεopt base loss)⟩
  intro s
  obtain ⟨B, hB, hb⟩ := hIb s
  refine ⟨B, hB, fun n hn x hx R hR hh => ?_⟩
  exact hb n hn x (((hp (le_max_right oldBase b)) x).trans hx) R hR
    (((hp (show s + l ≤ s + loss from
      Nat.add_le_add_left (le_max_right oldLoss l) s)) x).trans hh)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

theorem characteristicSpeedTameBounds_of_endpointInputs
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b)
    (hI : ∀ s : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ n : ℕ, n ≤ s → ∀ x : AnnularState S × ℝ,
      pairGrading (stateGrading S) realGrading base x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → pairGrading (stateGrading S) realGrading (s + loss) x ≤ R →
        pairGrading (stateGrading S) realGrading (n + 4) x ≤
          B * R ^ ((n : ℝ) / ((s : ℝ) + 1)))
    (G : ∀ m, MixedJetRegularity (stateNeighborhood S C base ε)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) (stateOpticalRootField D S C))
    (hG : EndpointMixedPowerBounds (pairGrading (stateGrading S) realGrading)
      (C.referenceState, 0) base loss (stateNeighborhood S C base ε)
      (fun m => Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
      (fun m q => min (q.1 - C.left m) (C.right m - q.1))
      (fun m _ => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
      (fun m _ => T.E0 (T.sample (C.cell m))) (fun _ => stateOpticalRootField D S C)) :
    CharacteristicSpeedTameBounds D T S C base loss ε := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  let U := stateNeighborhood S C base ε
  let Ω : ℕ → Set PolarPoint := fun m => Ioo (C.left m) (C.right m) ×ˢ univ
  let δ : ℕ → PolarPoint → ℝ := fun m q => min (q.1 - C.left m) (C.right m - q.1)
  let H : ℕ → PolarPoint → ℝ := fun m _ => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ)
  let E : ℕ → PolarPoint → ℝ := fun m _ => T.E0 (T.sample (C.cell m))
  let p := pairGrading (stateGrading S) realGrading
  have hU : IsOpen U := isOpen_stateNeighborhood S C base ε
  have hΩ (m : ℕ) : IsOpen (Ω m) := isOpen_Ioo.prod isOpen_univ
  have hcore (m : ℕ) {q : PolarPoint} (hq : q ∈ Ω m) : q ∈ annularOpen D :=
    ⟨⟨(hA.2.2.1.1 m).1.trans hq.1.1, hq.1.2.trans (hA.2.2.1.1 m).2.2⟩, mem_univ _⟩
  have hs (m : ℕ) := materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
  have hδ (m : ℕ) (q : PolarPoint) (hq : q ∈ Ω m) : 0 ≤ δ m q :=
    le_min (sub_nonneg.mpr hq.1.1.le) (sub_nonneg.mpr hq.1.2.le)
  have hEs (m : ℕ) (q : PolarPoint) (_ : q ∈ Ω m) : 1 ≤ E m q := hE _ (hs m)
  let Wlam := wholeCharacteristicSpeed_powerControl
    hS hT hA hε (by linarith) hB hE hloc hχloc hI G hG
  exact Wlam.reference_difference_tame
    (H := fun m _ => T.H (T.sample (C.cell m))) hΩ hδ
    (fun m _ _ => (hT.2.1 _ (hs m)).2.1.le) hEs
    (reference_mem_stateNeighborhood S C base hε)
    (fun z hz => (jointStateGrading_displacement_lt_one hε2 hz).le)
    (fun z hz t ht => stateNeighborhood_reference_segment S C hz ht)
    (fun m q => q.1 ∈ Ioo (C.left m) (C.right m))
    (fun _ _ hq => ⟨hq, mem_univ _⟩)


private def n01cOpticalRootEndpointWitness
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base loss : ℕ) (ε : ℝ) : Prop :=
  Nonempty (∀ m, MixedJetRegularity (stateNeighborhood S C base ε)
    (Ioo (C.left m) (C.right m) ×ˢ univ) (stateOpticalRootField D S C)) ∧
  EndpointMixedPowerBounds (pairGrading (stateGrading S) realGrading)
    (C.referenceState, 0) base loss (stateNeighborhood S C base ε)
    (fun m => Ioo (C.left m) (C.right m) ×ˢ univ)
    (fun m q => min (q.1 - C.left m) (C.right m - q.1))
    (fun m _ => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
    (fun m _ => T.E0 (T.sample (C.cell m))) (fun _ => stateOpticalRootField D S C)

private theorem n01c_close_common_speed_data
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {oldBase oldLoss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C oldBase ε)
    (hCoeff : CoefficientFamilyTameBounds D T S C oldBase oldLoss ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b)
    (base loss : ℕ) (ε' : ℝ) (hε' : 0 < ε')
    (hbase : oldBase ≤ base) (hloss : oldLoss ≤ loss)
    (hεε : ε' ≤ ε) (hεhalf : ε' ≤ 1 / 2)
    (hI : ∀ s : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ n : ℕ, n ≤ s → ∀ x : AnnularState S × ℝ,
      pairGrading (stateGrading S) realGrading base x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → pairGrading (stateGrading S) realGrading (s + loss) x ≤ R →
        pairGrading (stateGrading S) realGrading (n + 4) x ≤
          B * R ^ ((n : ℝ) / ((s : ℝ) + 1)))
    (hOpt : n01cOpticalRootEndpointWitness D T S C base loss ε') :
    N01PartB D S C base ε' ∧ CoefficientFamilyTameBounds D T S C base loss ε' ∧
      CharacteristicSpeedTameBounds D T S C base loss ε' := by
  obtain ⟨⟨G⟩, hG⟩ := hOpt
  have hB' := n01PartB_mono hB hbase hεε
  exact ⟨hB', coefficientFamilyTameBounds_mono_of_accumulatingProfile
    hT hA.1.1 hCoeff hbase hloss hεε,
    characteristicSpeedTameBounds_of_endpointInputs
      hS hT hA hε' hεhalf hB' hE hloc hχloc hI G hG⟩

/-- The primitive geometry and the already established coefficient
clause produce the actual speed clause on one common smaller neighbourhood. -/
theorem n01_exists_common_characteristicSpeedTameBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {oldBase oldLoss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε)
    (hB : N01PartB D S C oldBase ε)
    (hCoeff : CoefficientFamilyTameBounds D T S C oldBase oldLoss ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b)
    (hlower : ∃ K : ℝ, 0 < K ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
        K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
          min (r - C.left m) (C.right m - r) ≤ -deriv D.w r / (r * D.w r)) :
    ∃ base loss : ℕ, ∃ ε' : ℝ,
      0 < ε' ∧ oldBase ≤ base ∧ oldLoss ≤ loss ∧ ε' ≤ ε ∧
        N01PartB D S C base ε' ∧ CoefficientFamilyTameBounds D T S C base loss ε' ∧
          CharacteristicSpeedTameBounds D T S C base loss ε' := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  exact n01c_common_speed_selection
    (pairGrading (stateGrading S) realGrading) (jointStateGrading_monotone S)
    (jointStateGrading_hasInterpolation hS) oldBase oldLoss 4 hε
    (n01cOpticalRootEndpointWitness D T S C)
    (fun base loss ε' => N01PartB D S C base ε' ∧
      CoefficientFamilyTameBounds D T S C base loss ε' ∧
      CharacteristicSpeedTameBounds D T S C base loss ε')
    (n01_exists_stateOpticalRoot_endpoint_powerBounds hS hT hA hE hloc hlower)
    (n01c_close_common_speed_data hS hT hA hB hCoeff hE hloc hχloc)

end ContinuousFlexibility.Statements
