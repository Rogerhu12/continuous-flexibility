import ContinuousFlexibility.Analysis.N07aInverseChartBounds
import ContinuousFlexibility.Analysis.N07aSourceAtInverseChart
import ContinuousFlexibility.Analysis.N07aSampleComposition
import ContinuousFlexibility.Analysis.SolveStateSpaces

/-!
# Fixed-loss actual height pullback by the inverse chart

The actual geometric jets and actual decoded source derivatives supply
all inputs of the proved partition estimate. The low parameter order is
chosen once for all mixed and material orders.
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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε γ : ℝ}

theorem n07a_height_inverseChart_composition_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε) :
    ∃ low outLoss : ℕ, ∀ a b c : ℕ, ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ sectorNeighborhood S base ε ε,
          CanonicalGeometry.parameterGrading S low z ≤ 1 →
          ∀ (u : (S.height γ).Space) m y, y ∈ canonicalOpen S K m →
            |mixedDerivative a b ((S.height γ).decode u ∘
              K.inverseChart (liftSectorParameter S C z) m) y| ≤
              e m * (T.H (T.sample (K.cell m)) ^ γ *
                (T.M (T.sample (K.cell m)) ^ c)⁻¹) *
                ((S.height γ).grading (c + (a + b) + outLoss) u +
                  (1 + CanonicalGeometry.parameterGrading S (c + (a + b) + outLoss) z) *
                    (S.height γ).grading low u) := by
  let p := CanonicalGeometry.parameterGrading S
  let q := (S.height γ).grading
  let U := sectorNeighborhood S base ε ε
  let Φ := fun (z : CanonicalGeometry.Parameter S) m =>
    K.inverseChart (liftSectorParameter S C z) m
  let w := fun c m => T.H (T.sample (K.cell m)) ^ γ *
    (T.M (T.sample (K.cell m)) ^ c)⁻¹
  have hp : Monotone p := n07aParameterGrading_monotone S
  have hq : Monotone q := gradedSeminorm_monotone _ _
  have hIp : HasSmoothing p :=
    hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading
  have hIq : HasSmoothing q := (hS.2.2.2.1 γ).2.1
  have hinterval := h04.2.2.2.1
  have hInv := n07a_inverseChart_positive_jets hD hT href hcur
    (fun m => (hinterval m).2.1) (fun m => (hinterval m).1)
  let d₀ := hInv.choose
  have hInvb := hInv.choose_spec
  let d := max d₀ 3
  have hw (c m : ℕ) : 0 ≤ w c m := by
    have hpos := hT.2.1 _
      (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
    exact mul_nonneg (Real.rpow_pos_of_pos hpos.2.1 γ).le
      (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hpos.2.2.2) c))
  have hmaps (z : CanonicalGeometry.Parameter S) (hz : z ∈ U) (m : ℕ) :
      MapsTo (Φ z m) (canonicalOpen S K m) (annularOpen D) := by
    have hgeom := h04.2.2.2.2.2.2.2.1 _
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl)
      (hrefState.liftSectorParameter_sector z) m
    intro y hy
    exact ⟨(hinterval m).2.2 (hgeom.2.1 hy).1, mem_univ _⟩
  have hφs (z : CanonicalGeometry.Parameter S) (hz : z ∈ U) (m : ℕ) :
      ContDiffOn ℝ ∞ (Φ z m) (canonicalOpen S K m) :=
    (h04.2.2.2.2.2.2.2.1 _
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl)
      (hrefState.liftSectorParameter_sector z) m).2.2.2.2.2.1
  have houter (n c : ℕ) : ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, ∀ (u : (S.height γ).Space) m y, y ∈ canonicalOpen S K m →
          ‖iteratedFDeriv ℝ n ((S.height γ).decode u) (Φ z m y)‖ ≤
            e m * w c m * q (c + n + d) u := by
    have hout := n07a_source_jets_at_inverseChart (S := S) (C := C) (L := L) (K := K)
      (A := S.height γ) hD hT (hS.1 γ) hγ hγ1 hrefState h04 href n c
    let e : ℕ → ℝ := hout.choose
    have he := hout.choose_spec.1
    have he0 := hout.choose_spec.2.1
    have heb := hout.choose_spec.2.2
    refine ⟨e, he, he0, fun z hz u m y hy => (heb z hz u m y hy).trans ?_⟩
    exact mul_le_mul_of_nonneg_left (hq (Nat.add_le_add_left (le_max_right d₀ 3) _) u)
      (mul_nonneg (he0 m) (hw c m))
  have hchart (n : ℕ) (hn : 0 < n) : ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, ∀ m y, y ∈ canonicalOpen S K m →
          ‖iteratedFDeriv ℝ n (Φ z m) y‖ ≤ e m * (1 + p ((n - 1) + d) z) := by
    have hi := hInvb n hn
    let e : ℕ → ℝ := hi.choose
    have he := hi.choose_spec.1
    have he0 := hi.choose_spec.2.1
    have heb := hi.choose_spec.2.2
    refine ⟨e, he, he0, fun z hz m y hy => (heb z hz m y hy).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_left d₀ 3) _) z)) (he0 m)
  have hc := n07a_sampleComposition_fixedLoss hD hT p q hp hq hIp hIq
    U (canonicalOpen S K) d (fun u => (S.height γ).decode u) Φ w hw
    (fun z hz u m y hy => ((hS.1 γ).2.2.2.1 u).1.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds (hmaps z hz m hy)))
    (fun z hz m y hy => (hφs z hz m).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hy)) houter hchart
  let low := hc.choose
  let outLoss := hc.choose_spec.choose
  have hcb := hc.choose_spec.choose_spec
  refine ⟨low, outLoss, fun a b c => ?_⟩
  let e : ℕ → ℝ := (hcb (a + b) c).choose
  have he := (hcb (a + b) c).choose_spec
  refine ⟨e, he.1, he.2.1, fun z hz hlow u m y hy => ?_⟩
  have hs := ((hS.1 γ).2.2.2.1 u).1.comp (hφs z hz m) (hmaps z hz m)
  exact (n07a_mixedDerivative_norm_le_iteratedFDeriv (isOpen_Ioo.prod isOpen_univ)
    hs a b hy).trans (he.2.2 z hz hlow u m y hy)

end ContinuousFlexibility.Analysis
