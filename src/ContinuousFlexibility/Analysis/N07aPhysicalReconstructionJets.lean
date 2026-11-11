import ContinuousFlexibility.Analysis.N07aForwardChartBounds
import ContinuousFlexibility.Analysis.N07aLinearJetComposition
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
        u z v m (K.chart (liftSectorParameter S C z) m x)) (physicalPieceOpen S K m)) :
    ∃ low' loss : ℕ,
      N07aSampleLinearJetBounds T K (CanonicalGeometry.parameterGrading S) q
        {z | z ∈ U ∧ CanonicalGeometry.parameterGrading S low' z ≤ 1}
        (physicalPieceOpen S K) w low' loss (fun z v _ => r z v) := by
  let p := CanonicalGeometry.parameterGrading S
  have hp : Monotone p := n07aParameterGrading_monotone S
  have hIp : HasSmoothing p :=
    hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading
  have hinterval := h04.2.2.2.1
  let Φ := fun z m => K.chart (liftSectorParameter S C z) m
  have hgeom (z : CanonicalGeometry.Parameter S) (hz : z ∈ U) (m : ℕ) :=
    h04.2.2.2.2.2.2.2.1 _
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) (hU hz) le_rfl)
      (hrefState.liftSectorParameter_sector z) m
  have hΦs (z : CanonicalGeometry.Parameter S) (hz : z ∈ U) (m : ℕ) :
      ContDiffOn ℝ ∞ (Φ z m) (physicalPieceOpen S K m) :=
    (hgeom z hz m).2.2.2.2.1
  have hΦmap (z : CanonicalGeometry.Parameter S) (hz : z ∈ U) (m : ℕ) :
      MapsTo (Φ z m) (physicalPieceOpen S K m) (canonicalOpen S K m) :=
    (hgeom z hz m).1
  obtain ⟨dΦ, hΦ⟩ := n07a_forwardChart_positive_jets hD hT href hcur
    (fun m => (hinterval m).2.1) (fun m => (hinterval m).1)
  have hchart : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, ∀ m x, x ∈ physicalPieceOpen S K m →
          ‖iteratedFDeriv ℝ n (Φ z m) x‖ ≤ e m * (1 + p ((n - 1) + dΦ) z) := by
    intro n hn
    obtain ⟨e, he, he0, heb⟩ := hΦ n hn
    exact ⟨e, he, he0, fun z hz => heb z (hU hz)⟩
  obtain ⟨lc, dc, hcomp⟩ := n07a_sampleLinearJetBounds_comp hD hT p q hp hq hIp hIq U
    (physicalPieceOpen S K) (canonicalOpen S K)
    (fun _ => isOpen_Ioo.prod isOpen_univ) (fun _ => isOpen_Ioo.prod isOpen_univ)
    w hw u Φ low du dΦ hu hus hΦs hΦmap hchart
  let Uc : Set (CanonicalGeometry.Parameter S) := {z | z ∈ U ∧ p lc z ≤ 1}
  let A := n07aPhysicalAtomField D T S C L K .height
  obtain ⟨da, ha⟩ := n07a_physicalAtomFields_sampleJetBounds hD hT href hcur
    (fun m => (hinterval m).1)
  have ha' : N07aSampleJetBounds T K p Uc (physicalPieceOpen S K) da A :=
    (ha .height).restrict (fun _ hz => hU hz.1)
  have hAs (z : CanonicalGeometry.Parameter S) (hz : z ∈ Uc) (m : ℕ) :
      ContDiffOn ℝ ∞ (A z m) (physicalPieceOpen S K m) :=
    n07a_physicalAtomField_smooth hcur (fun m => (hinterval m).1) .height z (hU hz.1) m
  have hcs (z : CanonicalGeometry.Parameter S) (hz : z ∈ Uc) (v : F) (m : ℕ) :
      ContDiffOn ℝ ∞ (u z v m ∘ Φ z m) (physicalPieceOpen S K m) :=
    (hus z hz.1 v m).comp (hΦs z hz.1 m) (hΦmap z hz.1 m)
  obtain ⟨lm, dm, hmul⟩ := n07a_sampleLinearJetBounds_mul hD hT p q hp hq hIp hIq Uc
    (physicalPieceOpen S K) (fun _ => isOpen_Ioo.prod isOpen_univ) w hw A
    (fun z v m => u z v m ∘ Φ z m) da lc dc ha' hcomp hAs hcs
  let low' := max lc lm
  have hm := hmul.restrict (fun z (hz : z ∈ {z | z ∈ U ∧ p low' z ≤ 1}) =>
    ⟨⟨hz.1, (hp (le_max_left _ _) z).trans hz.2⟩,
      (hp (le_max_right _ _) z).trans hz.2⟩)
  have hm' := hm.low_mono hq hw (le_max_right lc lm)
  refine ⟨low', dm, fun a b c => ?_⟩
  obtain ⟨e, he, he0, heb⟩ := hm' a b c
  refine ⟨e, he, he0, fun z hz v m x hx => ?_⟩
  have heq : EqOn (r z v) (fun y => A z m y * (u z v m ∘ Φ z m) y)
      (physicalPieceOpen S K m) := by
    intro y hy
    dsimp only [A]
    rw [n07a_physicalAtomField_height (D := D) (T := T) (S := S) (C := C) (L := L)
      m (hinterval m).1 z]
    exact hrep z hz.1 v m hy
  rw [n07a_mixedDerivative_eqOn (isOpen_Ioo.prod isOpen_univ) heq a b hx]
  exact heb z hz v m x hx

end ContinuousFlexibility.Analysis
