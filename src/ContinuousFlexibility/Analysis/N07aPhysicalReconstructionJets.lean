import ContinuousFlexibility.Analysis.N07aActualHeightBounds
import ContinuousFlexibility.Analysis.N07aStateLinearJetComposition
import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Jets of the original physical remainder

The original height factor and forward chart reconstruct the physical
remainder on each actual piece. The whole composition and product retain
one fixed loss, and equality on the open pieces identifies every jet.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

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

variable {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base geometryLoss : ℕ} {ε : ℝ}

theorem n07a_physicalReconstruction_sampleJets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base geometryLoss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hFirst : N07aActualForwardFirstBound T S C K base ε)
    (q : ℕ → Seminorm ℝ F) (hq : Monotone q) (hIq : HasSmoothing q)
    (U : Set (CanonicalGeometry.Parameter S))
    (hU : U ⊆ sectorNeighborhood S base ε ε)
    (w : ℕ → ℕ → ℝ) (hw : ∀ c m, 0 ≤ w c m)
    (u : CanonicalGeometry.Parameter S → F → ℕ → PolarPoint → ℝ)
    (r : CanonicalGeometry.Parameter S → F → PolarPoint → ℝ)
    (low du : ℕ)
    (hu : N07aSampleLinearJetBounds T K (CanonicalGeometry.parameterGrading S) q U
      (canonicalOpen S K) w low du u)
    (hus : ∀ z ∈ U, ∀ v m, ContDiffOn ℝ ∞ (u z v m) (canonicalOpen S K m))
    (hrep : ∀ z ∈ U, ∀ v m,
      EqOn (r z v) (fun x => K.height (liftSectorParameter S C z) m x *
        u z v m (K.chart (liftSectorParameter S C z) m x)) (physicalPieceOpen S K (liftSectorParameter S C z) m)) :
    ∃ low' loss : ℕ,
      N07aStateSampleLinearJetBounds T K (CanonicalGeometry.parameterGrading S) q
        {z | z ∈ U ∧ CanonicalGeometry.parameterGrading S low' z ≤ 1}
        (fun z m => physicalPieceOpen S K (liftSectorParameter S C z) m) w low' loss (fun z v _ => r z v) := by
  let p := CanonicalGeometry.parameterGrading S
  let W := fun z m => physicalPieceOpen S K (liftSectorParameter S C z) m
  let Φ := fun z m => K.chart (liftSectorParameter S C z) m
  let A := fun z m => K.height (liftSectorParameter S C z) m
  have hp : Monotone p := n07aParameterGrading_monotone S
  have hIp : HasSmoothing p :=
    hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading
  have hgeom (z : CanonicalGeometry.Parameter S) (hz : z ∈ U) (m : ℕ) :=
    h04.1.charts _
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) (hU hz) le_rfl)
      (hrefState.liftSectorParameter_sector z) m
  have hW (z : CanonicalGeometry.Parameter S) (hz : z ∈ U) (m : ℕ) : IsOpen (W z m) :=
    (h04.1.domains _
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) (hU hz) le_rfl)
      (hrefState.liftSectorParameter_sector z) m).1
  obtain ⟨lF, dF, hF⟩ := n07a_actualForward_positive_jets
    hD hT hS hrefState h04.1 href hcur hFirst
  obtain ⟨lA, dA, hA⟩ := n07a_actualHeight_sampleJetBounds
    hD hT hS hrefState h04.1 href hcur hFirst
  let lg := max lF lA
  let Ug := {z | z ∈ U ∧ p lg z ≤ 1}
  have hug := (hu.restrict (fun _ (hz : _ ∈ Ug) => hz.1)).to_state
  have hΦs (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ug) (m : ℕ) :
      ContDiffOn ℝ ∞ (Φ z m) (W z m) := (hgeom z hz.1 m).2.2.2.2.1
  have hΦmap (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ug) (m : ℕ) :
      MapsTo (Φ z m) (W z m) (canonicalOpen S K m) := (hgeom z hz.1 m).1
  have hchart : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ Ug, ∀ m x, x ∈ W z m →
          ‖iteratedFDeriv ℝ n (Φ z m) x‖ ≤ e m * (1 + p ((n - 1) + dF) z) := by
    intro n hn
    obtain ⟨e, he, he0, heb⟩ := hF n hn
    exact ⟨e, he, he0, fun z hz => heb z (hU hz.1)
      ((hp (le_max_left _ _) z).trans hz.2)⟩
  obtain ⟨lc, dc, hcomp⟩ := n07a_stateSampleLinearJetBounds_comp hD hT p q hp hq hIp hIq
    Ug W (fun _ => canonicalOpen S K) (fun z hz => hW z hz.1)
    (fun _ _ _ => isOpen_Ioo.prod isOpen_univ) w hw u Φ low du dF hug
    (fun z hz => hus z hz.1) hΦs hΦmap hchart
  let Uc := {z | z ∈ Ug ∧ p lc z ≤ 1}
  have hA' : N07aStateSampleJetBounds T K p Uc W dA A :=
    hA.restrict (fun z (hz : z ∈ Uc) =>
      ⟨hU hz.1.1, (hp (le_max_right _ _) z).trans hz.1.2⟩)
  have hAs (z : CanonicalGeometry.Parameter S) (hz : z ∈ Uc) (m : ℕ) :
      ContDiffOn ℝ ∞ (A z m) (W z m) := (hgeom z hz.1.1 m).2.2.2.2.2.2.1
  have hcs (z : CanonicalGeometry.Parameter S) (hz : z ∈ Uc) (v : F) (m : ℕ) :
      ContDiffOn ℝ ∞ (u z v m ∘ Φ z m) (W z m) :=
    (hus z hz.1.1 v m).comp (hΦs z hz.1 m) (hΦmap z hz.1 m)
  obtain ⟨lm, dm, hmul⟩ := n07a_stateSampleLinearJetBounds_mul hD hT p q hp hq hIp hIq
    Uc W (fun z hz => hW z hz.1.1) w hw A
    (fun z v m => u z v m ∘ Φ z m) dA lc dc hA' hcomp hAs hcs
  let low' := max lg (max lc lm)
  have hlg : lg ≤ low' := le_max_left _ _
  have hlc : lc ≤ low' := (le_max_left _ _).trans (le_max_right _ _)
  have hlm : lm ≤ low' := (le_max_right _ _).trans (le_max_right _ _)
  have hm := hmul.restrict (fun z (hz : z ∈ {z | z ∈ U ∧ p low' z ≤ 1}) =>
    ⟨⟨⟨hz.1, (hp hlg z).trans hz.2⟩, (hp hlc z).trans hz.2⟩,
      (hp hlm z).trans hz.2⟩)
  have hm' := hm.low_mono hq hw hlm
  refine ⟨low', dm, fun a b c => ?_⟩
  obtain ⟨e, he, he0, heb⟩ := hm' a b c
  refine ⟨e, he, he0, fun z hz v m x hx => ?_⟩
  have heq : EqOn (r z v) (fun y => A z m y * (u z v m ∘ Φ z m) y) (W z m) :=
    hrep z hz.1 v m
  rw [n07a_mixedDerivative_eqOn (hW z hz.1 m) heq a b hx]
  exact heb z hz v m x hx

end ContinuousFlexibility.Analysis
