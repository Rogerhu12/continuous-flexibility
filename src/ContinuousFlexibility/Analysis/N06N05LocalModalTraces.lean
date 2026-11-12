import ContinuousFlexibility.Analysis.N06N05ModalTraces

/-!
# Original N05 modal transmission using only the actual closed pieces

The total chart functions need not be regular outside their physical
pieces. The frozen N04 clauses give their actual smoothness on each closed
piece, which is sufficient to compare one-sided modal representatives
with the C1 representative forced by the original physical weak graph.
Thus no global regularity premise on a physical pullback is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem n06_adjacent_continuous_representatives
    {l r s : ℝ} (hlr : l < r) (hrs : r < s) {v vl vr : ℝ → ℝ}
    (hvl : ContinuousOn vl (Ioo l r)) (hvr : ContinuousOn vr (Ioo r s))
    (hvL : ContinuousOn v (Ioo l r)) (hvR : ContinuousOn v (Ioo r s))
    (hdl : DifferentiableAt ℝ vl r) (hdr : DifferentiableAt ℝ vr r)
    (hdv : DifferentiableAt ℝ v r)
    (hL : vl =ᵐ[volume.restrict (Ioo l r)] v)
    (hR : vr =ᵐ[volume.restrict (Ioo r s)] v) :
    vl r = vr r ∧ deriv vl r = deriv vr r := by
  have heL : EqOn vl v (Ioo l r) :=
    Measure.eqOn_open_of_ae_eq hL isOpen_Ioo hvl hvL
  have heR : EqOn vr v (Ioo r s) :=
    Measure.eqOn_open_of_ae_eq hR isOpen_Ioo hvr hvR
  have hleft : vl r = v r ∧ deriv vl r = deriv v r :=
    n06_cauchyData_eq_of_eqOn_Ioo_left hlr hdl hdv heL
  have hright : vr r = v r ∧ deriv vr r = deriv v r :=
    cauchyData_eq_of_eqOn_Ioo_right hrs hdr hdv heR
  exact ⟨hleft.1.trans hright.1.symm, hleft.2.trans hright.2.symm⟩

private theorem n06_radial_mode_pullback_contDiffAt
    {F : PolarPoint → PolarPoint} {H : PolarPoint → ℝ} {v : ℝ → ℝ} {x : ℝ}
    (hF : ContDiffAt ℝ ∞ F (x, 0)) (hH : ContDiffAt ℝ ∞ H (x, 0))
    (hv : ContDiff ℝ 1 v) :
    ContDiffAt ℝ 1 (fun r => H (r, 0) * v ((F (r, 0)).1)) x := by
  have hline : ContDiffAt ℝ 1 (fun r : ℝ => (r, (0 : ℝ))) x :=
    contDiffAt_id.prodMk contDiffAt_const
  have hh : ContDiffAt ℝ 1 (fun r => H (r, 0)) x :=
    (hH.of_le (by simp)).comp x hline
  have hFone : ContDiffAt ℝ 1 F (x, 0) := hF.of_le (by simp)
  have hFline : ContDiffAt ℝ 1 (fun r => F (r, 0)) x := hFone.comp x hline
  have hf : ContDiffAt ℝ 1 (fun r => (F (r, 0)).1) x := hFline.fst
  exact hh.mul (hv.contDiffAt.comp x hf)

private theorem n06_remainder_mode_C1_representative
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hb : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (aL : ℝ) (n : ℕ)
    {r₀ : ℝ} (hr₀ : r₀ ∈ radialCore D) :
    ∃ v : ℝ → ℝ,
      evenFourierCoefficient (n06ReferenceRemainder χ U.1 aL) n
        =ᵐ[volume.restrict (radialCore D)] v ∧
      ContDiffOn ℝ 1 v (radialCore D) := by
  have hU : MemLp U.1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hb hγ hgraph.1
  obtain ⟨w, _, hwAE, hw, _⟩ :=
    r11b_evenCoefficient_contDiffOn_one_representative hD hb hγ hgraph n r₀ hr₀
  let c : ℝ → ℝ := fun x => if n = 0 then aL * χ x else 0
  have hc : ContDiff ℝ 1 c := by
    by_cases hn : n = 0
    · simpa only [c, ite_eq_left hn] using
        (contDiff_const.mul hχ : ContDiff ℝ 1 (fun x => aL * χ x))
    · simpa only [c, ite_eq_right hn] using
        (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ)))
  refine ⟨fun x => w x - c x, ?_, hw.sub hc.contDiffOn⟩
  have hsub : evenFourierCoefficient (fun p : PolarPoint => U.1 p - aL * χ p.1) n
      =ᵐ[volume.restrict (radialCore D)]
        (fun x => evenFourierCoefficient U.1 n x - c x) := by
    exact n06_evenFourierCoefficient_sub_radial_ae hU (fun x => aL * χ x) n
  filter_upwards [hsub, hwAE] with x hx hwx
  change evenFourierCoefficient (fun p : PolarPoint => U.1 p - aL * χ p.1) n x =
    w x - c x
  exact hx.trans (congrArg (fun y : ℝ => y - c x) hwx)

/-- The same original N05 modes have matching physical endpoint jets.
Only their genuine C1 radial representatives are inputs; smoothness of
the actual physical pullbacks follows from the original N04 clauses. -/
theorem n06N05_canonicalModes_physical_traces_local
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (u : B.Space) (ml mr n : ℕ) (vl vr : ℝ → ℝ)
    (hjoin : K.physicalRight ml = K.physicalLeft mr)
    (hroot : K.physicalRight ml ∈ radialCore D)
    (hvl : ContDiff ℝ 1 vl) (hvr : ContDiff ℝ 1 vr)
    (hmodeL : n06HalfCosineCoefficient (u.val.1.1 ml) n
      =ᵐ[volume.restrict (Ioo (K.left ml) (K.right ml))] vl)
    (hmodeR : n06HalfCosineCoefficient (u.val.1.1 mr) n
      =ᵐ[volume.restrict (Ioo (K.left mr) (K.right mr))] vr) :
    let fl : ℝ → ℝ := fun r => K.height (C.referenceState, 0) ml (r, 0) *
      vl ((K.chart (C.referenceState, 0) ml (r, 0)).1)
    let fr : ℝ → ℝ := fun r => K.height (C.referenceState, 0) mr (r, 0) *
      vr ((K.chart (C.referenceState, 0) mr (r, 0)).1)
    fl (K.physicalRight ml) = fr (K.physicalRight ml) ∧
      deriv fl (K.physicalRight ml) = deriv fr (K.physicalRight ml) ∧
      D.w (K.physicalRight ml) * deriv fl (K.physicalRight ml) =
        D.w (K.physicalRight ml) * deriv fr (K.physicalRight ml) := by
  obtain ⟨η, f, hrep, hgraph, _⟩ := n06N05_exists_physical_modal_traces h u
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2
  have href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h01.2.2.1
  let fl : ℝ → ℝ := fun x => K.height (C.referenceState, 0) ml (x, 0) *
    vl ((K.chart (C.referenceState, 0) ml (x, 0)).1)
  let fr : ℝ → ℝ := fun x => K.height (C.referenceState, 0) mr (x, 0) *
    vr ((K.chart (C.referenceState, 0) mr (x, 0)).1)
  let rem : PolarPoint → ℝ := n06ReferenceRemainder S.chiLeft η u.val.1.2.1
  have hleft : K.physicalLeft ml < K.physicalRight ml := (h04.2.2.2.1 ml).1
  have hright : K.physicalRight ml < K.physicalRight mr :=
    hjoin.trans_lt (h04.2.2.2.1 mr).1
  have hη : MemLp η 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp h01.1.1 h01.1.2.2.2.1 h.2.2.2.1 hgraph.1
  have hχ : MemLp (fun p : PolarPoint => u.val.1.2.1 * S.chiLeft p.1) 2
      (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (continuous_const.mul (hS.2.2.1.1.continuous.comp continuous_fst))
  have hrem : MemLp rem 2 (radialPhysicalMeasure D) := hη.sub hχ
  obtain ⟨a, ha⟩ := hgraph.1
  have hp : Function.Periodic rem (0, Real.pi) :=
    n06_referenceRemainder_periodic ha.2.2.1 _
  have hL : evenFourierCoefficient rem n
      =ᵐ[volume.restrict (Ioo (K.physicalLeft ml) (K.physicalRight ml))] fl :=
    n06_controlledReference_modal_representation h.1 hcoordinates
      hrem hp ml n (hrep.1 ml) hmodeL
  have hR : evenFourierCoefficient rem n
      =ᵐ[volume.restrict (Ioo (K.physicalLeft mr) (K.physicalRight mr))] fr :=
    n06_controlledReference_modal_representation h.1 hcoordinates
      hrem hp mr n (hrep.1 mr) hmodeR
  obtain ⟨w, hcommon, hw⟩ := n06_remainder_mode_C1_representative
    h01.1.1 h01.1.2.2.2.1 h.2.2.2.1 hgraph
    (hS.2.2.1.1.of_le (by simp)) u.val.1.2.1 n hroot
  have hwroot : DifferentiableAt ℝ w (K.physicalRight ml) :=
    (hw.contDiffAt (isOpen_Ioo.mem_nhds hroot)).differentiableAt (by norm_num)
  have hpull (m : ℕ) (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v)
      (x : ℝ) (hx : x ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      ContDiffAt ℝ 1
        (fun r => K.height (C.referenceState, 0) m (r, 0) *
          v ((K.chart (C.referenceState, 0) m (r, 0)).1)) x := by
    exact n06_radial_mode_pullback_contDiffAt
      (h04.2.2.2.2.2.2.2.2.1 (C.referenceState, 0) href hs m (x, 0) hx).1
      (h04.2.2.2.2.2.2.2.2.1 (C.referenceState, 0) href hs m (x, 0) hx).2.1 hv
  have hsubL : Ioo (K.physicalLeft ml) (K.physicalRight ml) ⊆ radialCore D :=
    (h04.2.2.2.1 ml).2.2
  have hsubR : Ioo (K.physicalLeft mr) (K.physicalRight mr) ⊆ radialCore D :=
    (h04.2.2.2.1 mr).2.2
  have heL : fl =ᵐ[volume.restrict (Ioo (K.physicalLeft ml) (K.physicalRight ml))] w :=
    hL.symm.trans (ae_restrict_of_ae_restrict_of_subset hsubL hcommon)
  have heR : fr =ᵐ[volume.restrict (Ioo (K.physicalRight ml) (K.physicalRight mr))] w := by
    rw [hjoin]
    exact hR.symm.trans (ae_restrict_of_ae_restrict_of_subset hsubR hcommon)
  have hcL : ContinuousOn fl (Ioo (K.physicalLeft ml) (K.physicalRight ml)) :=
    fun x hx => (hpull ml vl hvl x ⟨hx.1.le, hx.2.le⟩).continuousAt.continuousWithinAt
  have hcR : ContinuousOn fr (Ioo (K.physicalRight ml) (K.physicalRight mr)) := by
    rw [hjoin]
    exact fun x hx => (hpull mr vr hvr x ⟨hx.1.le, hx.2.le⟩).continuousAt.continuousWithinAt
  have hwR : ContinuousOn w (Ioo (K.physicalRight ml) (K.physicalRight mr)) := by
    rw [hjoin]
    exact hw.continuousOn.mono hsubR
  have hlroot : DifferentiableAt ℝ fl (K.physicalRight ml) :=
    (hpull ml vl hvl (K.physicalRight ml) ⟨hleft.le, le_rfl⟩).differentiableAt (by norm_num)
  have hrroot : DifferentiableAt ℝ fr (K.physicalRight ml) :=
    (hpull mr vr hvr (K.physicalRight ml)
      ⟨hjoin.symm.le, hright.le⟩).differentiableAt (by norm_num)
  have hmatch : fl (K.physicalRight ml) = fr (K.physicalRight ml) ∧
      deriv fl (K.physicalRight ml) = deriv fr (K.physicalRight ml) :=
    n06_adjacent_continuous_representatives hleft hright hcL hcR
      (hw.continuousOn.mono hsubL) hwR hlroot hrroot hwroot heL heR
  exact ⟨hmatch.1, hmatch.2, congrArg (D.w (K.physicalRight ml) * ·) hmatch.2⟩

end ContinuousFlexibility.Statements
