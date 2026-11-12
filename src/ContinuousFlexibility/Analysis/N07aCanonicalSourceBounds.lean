import ContinuousFlexibility.Analysis.N07aHeightChartComposition
import ContinuousFlexibility.Analysis.N07aSampleLinearJets

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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε γ : ℝ}

theorem n07a_canonicalSource_eq_sourceFactor
    (m : ℕ) (hm : K.left m < K.right m)
    (z : CanonicalGeometry.Parameter S) (f : PolarPoint → ℝ) :
    canonicalSource S K (liftSectorParameter S C z) m f = fun y =>
      n07aCanonicalAtomField D T S C L K .sourceFactor z m y *
        f (K.inverseChart (liftSectorParameter S C z) m y) := by
  funext y
  have hy := n07aCanonicalUnitPoint_inverse hm y
  simp only [n07aCanonicalAtomField, Function.comp_apply, CanonicalGeometry.atom, hy,
    canonicalSource, mul_one]
  ring

/-- All actual canonical source jets have a common fixed loss, including
arbitrary material orders and the actual chart source factor. -/
theorem n07a_canonicalSource_height_sampleJets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε) :
    ∃ low outLoss : ℕ,
      N07aSampleLinearJetBounds T K (CanonicalGeometry.parameterGrading S)
        (S.height γ).grading
        {z | z ∈ sectorNeighborhood S base ε ε ∧
          CanonicalGeometry.parameterGrading S low z ≤ 1}
        (canonicalOpen S K)
        (fun c m => T.H (T.sample (K.cell m)) ^ γ *
          (T.M (T.sample (K.cell m)) ^ c)⁻¹) low outLoss
        (fun z u m => canonicalSource S K (liftSectorParameter S C z) m
          ((S.height γ).decode u)) := by
  let p := CanonicalGeometry.parameterGrading S
  let q := (S.height γ).grading
  let U := sectorNeighborhood S base ε ε
  let w := fun c m => T.H (T.sample (K.cell m)) ^ γ *
    (T.M (T.sample (K.cell m)) ^ c)⁻¹
  have hp : Monotone p := n07aParameterGrading_monotone S
  have hq : Monotone q := gradedSeminorm_monotone _ _
  have hIp : HasSmoothing p :=
    hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading
  have hIq : HasSmoothing q := (hS.2.2.2.1 γ).2.1
  have hinterval := h04.1.referenceBounds
  have hw (c m : ℕ) : 0 ≤ w c m := by
    have hpos := hT.2.1 _
      (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
    exact mul_nonneg (Real.rpow_pos_of_pos hpos.2.1 γ).le
      (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hpos.2.2.2) c))
  have hcomp := n07a_height_inverseChart_composition_bound hD hT hS hγ hγ1
    hrefState h04 href hcur hRatio
  let lf := hcomp.choose
  let df := hcomp.choose_spec.choose
  have hfb := hcomp.choose_spec.choose_spec
  let U₁ : Set (CanonicalGeometry.Parameter S) := {z | z ∈ U ∧ p lf z ≤ 1}
  let A := n07aCanonicalAtomField D T S C L K .sourceFactor
  let f := fun (z : CanonicalGeometry.Parameter S) (u : (S.height γ).Space) m =>
    (S.height γ).decode u ∘ K.inverseChart (liftSectorParameter S C z) m
  have hf : N07aSampleLinearJetBounds T K p q U₁ (canonicalOpen S K) w lf df f := by
    intro a b c
    have hfc := hfb a b c
    let e : ℕ → ℝ := hfc.choose
    exact ⟨e, hfc.choose_spec.1, hfc.choose_spec.2.1,
      fun z hz => hfc.choose_spec.2.2 z hz.1 hz.2⟩
  have ha := n07a_canonicalAtomFields_sampleJetBounds hD hT href hcur
    (fun m => (hinterval m).2.1)
  let da := ha.choose
  have hab : N07aSampleJetBounds T K p U₁ (canonicalOpen S K) da A :=
    (ha.choose_spec .sourceFactor).restrict (fun _ hz => hz.1)
  have hAs (z : CanonicalGeometry.Parameter S) (hz : z ∈ U₁) (m : ℕ) :
      ContDiffOn ℝ ∞ (A z m) (canonicalOpen S K m) :=
    n07a_canonicalAtomField_smooth hcur (fun m => (hinterval m).2.1) .sourceFactor z hz.1 m
  have hfs (z : CanonicalGeometry.Parameter S) (hz : z ∈ U₁)
      (u : (S.height γ).Space) (m : ℕ) :
      ContDiffOn ℝ ∞ (f z u m) (canonicalOpen S K m) := by
    have hgeom := h04.1.charts _
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz.1 le_rfl)
      (hrefState.liftSectorParameter_sector z) m
    apply ((hS.1 γ).2.2.2.1 u).1.comp hgeom.2.2.2.2.2.1
    intro y hy
    exact (h04.1.domains _
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz.1 le_rfl)
      (hrefState.liftSectorParameter_sector z) m).2.2.1 (hgeom.2.1 hy)
  have hmul := n07a_sampleLinearJetBounds_mul hD hT p q hp hq hIp hIq U₁
    (canonicalOpen S K) (fun _ => isOpen_Ioo.prod isOpen_univ) w hw A f
    da lf df hab hf hAs hfs
  let lm := hmul.choose
  let outLoss := hmul.choose_spec.choose
  have hmb := hmul.choose_spec.choose_spec
  let low := max lf lm
  have hm : N07aSampleLinearJetBounds T K p q {z | z ∈ U ∧ p low z ≤ 1}
      (canonicalOpen S K) w lm outLoss (fun z u m x => A z m x * f z u m x) :=
    hmb.restrict (fun z hz =>
      ⟨⟨hz.1, (hp (le_max_left lf lm) z).trans hz.2⟩,
        (hp (le_max_right lf lm) z).trans hz.2⟩)
  have hm' := hm.low_mono hq hw (le_max_right lf lm)
  refine ⟨low, outLoss, ?_⟩
  have he : (fun z u m => canonicalSource S K (liftSectorParameter S C z) m
      ((S.height γ).decode u)) = (fun z u m x => A z m x * f z u m x) := by
    funext z u m
    exact n07a_canonicalSource_eq_sourceFactor (D := D) (T := T) (S := S)
      (C := C) (L := L) m (hinterval m).2.1 z ((S.height γ).decode u)
  exact Eq.mpr (congrArg
    (N07aSampleLinearJetBounds T K p q {z | z ∈ U ∧ p low z ≤ 1}
      (canonicalOpen S K) w low outLoss) he) hm'

end ContinuousFlexibility.Analysis
