import ContinuousFlexibility.Analysis.N07bScalarBridgeConstruction
import ContinuousFlexibility.Analysis.N07bPrimitiveGeometrySource
import ContinuousFlexibility.Analysis.N07bPrimitiveGeometryReference
import ContinuousFlexibility.Analysis.N07bNeighborhood

/-!
# One common neighborhood for the actual scalar/Banach bridge

Both finite geometric estimates choose their constants before the state
and source. Intersecting their neighborhoods preserves every chosen chart,
space, graph and inverse. The source norm has the requested original
grading, while the identification uses the actual reference source built
from the physical solution.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency true

theorem n07b_reference_mem_stateNeighborhood
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (base : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
  change stateGrading S base (C.referenceState - C.referenceState) < ε ∧ |(0 : ℝ)| < ε
  have hzero : stateGrading S base (0 : AnnularState S) = (0 : ℝ) :=
    map_zero (stateGrading S base)
  simpa only [sub_self, hzero, abs_zero] using And.intro hε hε

/-- The scalar norm enlargement does not inspect any state or volume model. -/
private theorem n07b_source_bound_with_state_factor
    {N C p t q : ℝ} (hN : N ≤ C * p) (hC : 0 ≤ C) (hp : 0 ≤ p) (ht : 0 ≤ t) :
    N ≤ C * (1 + t + |q|) * p := by
  have hfactor : (1 : ℝ) ≤ 1 + t + |q| :=
    (le_add_of_nonneg_right ht).trans (le_add_of_nonneg_right (abs_nonneg q))
  have hCfactor : C ≤ C * (1 + t + |q|) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor hC
  exact hN.trans (mul_le_mul_of_nonneg_right hCfactor hp)

/-- Uniform source lifts with their already proved scalar bound. -/
private def N07bUniformSourceLift (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (V : VolumeModelData S K)
    (b base : ℕ) (ε C₀ : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ f : S.Source,
    ∃ F : V.level (3 / 4 : ℝ) 0 b,
      ‖F‖ ≤ C₀ * S.sourceGrading (b + 1) f ∧
      N07bCanonicalSourceRepresentation S K V b z F
        ((S.height (3 / 4 : ℝ)).decode.toFun f.val)

/-- The reference coefficient estimate in its finite-index form. -/
private def N07bUniformReferenceBulkBound (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (b base : ℕ) (ε A : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    N07bReferenceBulkCoefficientBound D T S C K z b A

/-- Adapt the genuine angular estimate before any graph or scalar inverse
is present in the context. -/
private theorem n07b_uniform_referenceBulkBound_on_smaller
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hε : 0 < ε)
    (hgeom : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hsref : stateSector S C.referenceState) (b : ℕ) :
    ∃ br : ℕ, ∃ εr Ar : ℝ, base ≤ br ∧ 0 < εr ∧ εr ≤ ε ∧ 0 ≤ Ar ∧
      N07bUniformReferenceBulkBound D T S C K b br εr Ar := by
  have href := n07b_reference_mem_stateNeighborhood S C base hε
  obtain ⟨br, εr, Ar, hbr, hεr, hεrle, _, hAr, hcoeff⟩ :=
    n07b_referenceAngular_bound_of_geometric_contract hD hT hK hε href hsref hgeom b
  refine ⟨br, εr, Ar, hbr, hεr, hεrle, hAr, ?_⟩
  intro z hz hs m x hx j i
  have h := hcoeff z hz hs m x hx j.val (Nat.le_of_lt_succ j.isLt) i
  simpa only [n07bReferenceBulkCoefficient, n07b_canonicalPrimitiveDirection_one,
    n07b_canonicalPrimitiveDirection_two] using h

set_option diagnostics true in
/-- Choose the common source and coefficient neighborhood without a Banach
graph or scalar inverse in the elaboration context. -/
private theorem n07b_common_lifts_on_smaller
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {base : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hV : IsVolumeModel T S K V)
    (hK : N04PartA D S C K base ε) (hε : 0 < ε)
    (hgeom : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hsref : stateSector S C.referenceState) (b : ℕ) :
    ∃ base' : ℕ, ∃ ε' Cs Ar : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ 0 < Cs ∧ 0 ≤ Ar ∧
      N07bReferenceSourceLiftProperty S C K V b ∧
      N07bUniformSourceLift S C K V b base' ε' Cs ∧
      N07bUniformReferenceBulkBound D T S C K b base' ε' Ar := by
  run_tac Lean.logInfo "N07b common lifts: entered"
  obtain ⟨bs, εs, Cs, hbs, hεs, hεsle, _, hCs, hsource⟩ :=
    n07b_sourceLift_of_geometric_contract hD hT hS hV hK hε hgeom b
  have hsourceNamed : N07bUniformSourceLift S C K V b bs εs Cs := hsource
  run_tac Lean.logInfo "N07b common lifts: source constants obtained"
  obtain ⟨br, εr, Ar, hbr, hεr, hεrle, hAr, hcoeff⟩ :=
    n07b_uniform_referenceBulkBound_on_smaller hD hT hK hε hgeom hsref b
  let base' : ℕ := max bs br
  let ε' : ℝ := min εs εr
  have hbase' : base ≤ base' := hbs.trans (le_max_left _ _)
  have hε' : 0 < ε' := lt_min hεs hεr
  have hε'le : ε' ≤ ε := (min_le_left _ _).trans hεsle
  have hUs : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C bs εs :=
    n06_stateNeighborhood_mono (le_max_left _ _) (min_le_left _ _)
  have hUr : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C br εr :=
    n06_stateNeighborhood_mono (le_max_right _ _) (min_le_right _ _)
  run_tac Lean.logInfo "N07b common lifts: neighborhoods intersected"
  refine ⟨base', ε', Cs, Ar, hbase', hε', hε'le, hCs, hAr, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨F, _, hF⟩ := hsourceNamed (C.referenceState, 0)
      (n07b_reference_mem_stateNeighborhood S C bs hεs) hsref f
    exact ⟨F, hF⟩
  · exact fun z hz hs f => hsourceNamed z (hUs hz) hs f
  · exact fun z hz hs => hcoeff z (hUr hz) hs

set_option diagnostics true in
/-- Assemble the bridge from common actual source lifts and coefficient
bounds. All representation and identification goals keep their named forms. -/
private theorem n07b_scalarBanachBridge_of_uniform_lifts
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {b base base' : ℕ} {ε ε' : ℝ}
    {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}
    {G : ScalarInverseData S}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hborder : RadialTrueBorder D)
    (hK : N04PartA D S C K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (hgeom : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hsref : stateSector S C.referenceState)
    (hU : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε)
    {Cs Ar : ℝ} (hCs : 0 < Cs) (hAr : 0 ≤ Ar)
    (hreferenceSource : N07bReferenceSourceLiftProperty S C K V b)
    (hsource : N07bUniformSourceLift S C K V b base' ε' Cs)
    (hcoeff : N07bUniformReferenceBulkBound D T S C K b base' ε' Ar) :
    ScalarBanachBridgeProperties D S C K V b B P G base' ε' := by
  run_tac Lean.logInfo "N07b bridge assembly: entered"
  have href := n07b_reference_mem_stateNeighborhood S C base h06.1
  refine ⟨b + 1, Nat.le_succ b, Cs, hCs, ?_⟩
  intro z hz hs f
  change ∃ F : V.level (3 / 4 : ℝ) 0 b,
    ‖F‖ ≤ Cs * (1 + stateGrading S (b + 1) (z.1 - C.referenceState) + |z.2|) *
      S.sourceGrading (b + 1) f ∧
    N07bCanonicalSourceRepresentation S K V b z F
      ((S.height (3 / 4 : ℝ)).decode.toFun f.val) ∧
    N07bScalarBridgeConclusion D S C K V b B P z F
      ((G.G z).toLinearMap.toFun f) ((S.height (3 / 4 : ℝ)).decode.toFun f.val)
  obtain ⟨F, hFnorm, hF⟩ := hsource z hz hs f
  have hnorm : ‖F‖ ≤ Cs *
      (1 + stateGrading S (b + 1) (z.1 - C.referenceState) + |z.2|) *
        S.sourceGrading (b + 1) f :=
    n07b_source_bound_with_state_factor hFnorm hCs.le
      (apply_nonneg (S.sourceGrading (b + 1)) f)
      (apply_nonneg (stateGrading S (b + 1)) (z.1 - C.referenceState))
  run_tac Lean.logInfo "N07b bridge assembly: actual source and norm bound obtained"
  have hid : N07bScalarBridgeConclusion D S C K V b B P z F
      ((G.G z).toLinearMap.toFun f) ((S.height (3 / 4 : ℝ)).decode.toFun f.val) :=
    n07b_scalarInverse_banach_identification hD hT hS hborder hK h05 h06 hG
      hgeom href hsref hreferenceSource (hU hz) hs hAr (hcoeff z hz hs) f F hF
  run_tac Lean.logInfo "N07b bridge assembly: identification obtained"
  exact ⟨F, hnorm, hF, hid⟩

set_option diagnostics true in
theorem n07b_exists_scalarBanachBridge_on_smaller
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {b base : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}
    {G : ScalarInverseData S}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hborder : RadialTrueBorder D)
    (hK : N04PartA D S C K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (hgeom : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hsref : stateSector S C.referenceState) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ScalarBanachBridgeProperties D S C K V b B P G base' ε' := by
  run_tac Lean.logInfo "N07b final neighborhood: entered"
  obtain ⟨base', ε', Cs, Ar, hb, hε', hεle, hCs, hAr, hreferenceSource, hsource, hcoeff⟩ :=
    n07b_common_lifts_on_smaller hD hT hS h05.2.1 hK h06.1 hgeom hsref b
  run_tac Lean.logInfo "N07b final neighborhood: common data obtained"
  have hbridge : ScalarBanachBridgeProperties D S C K V b B P G base' ε' :=
    n07b_scalarBanachBridge_of_uniform_lifts hD hT hS hborder hK h05 h06 hG hgeom
      hsref (n06_stateNeighborhood_mono hb hεle) hCs hAr hreferenceSource hsource hcoeff
  run_tac Lean.logInfo "N07b final neighborhood: bridge obtained"
  exact ⟨base', ε', hb, hε', hεle, hbridge⟩

end ContinuousFlexibility.Analysis
