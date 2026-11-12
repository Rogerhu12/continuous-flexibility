import ContinuousFlexibility.Analysis.N05CanonicalRadialTestTransport

/-!
# The actual first radial derivative of a transported test

The nonzero reference Jacobian has locally constant orientation. The
ordinary chain and quotient rules therefore give the exact height
correction in the canonical radial weak derivative, with no independent
coordinate-derivative assumptions.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

theorem n05_abs_div_eventually_constant {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {p : X} (hf : ContinuousAt f p) (hp : f p ≠ 0) :
    (fun q => |f q| / f q) =ᶠ[𝓝 p] (fun _ => |f p| / f p) := by
  rcases hp.lt_or_gt with hneg | hpos
  · filter_upwards [hf.eventually (eventually_lt_nhds hneg)] with q hq
    change |f q| / f q = |f p| / f p
    simp only [abs_of_neg hq, abs_of_neg hneg, neg_div,
      div_self hq.ne, div_self hneg.ne]
  · filter_upwards [hf.eventually (eventually_gt_nhds hpos)] with q hq
    change |f q| / f q = |f p| / f p
    rw [abs_of_pos hq, abs_of_pos hpos, div_self hq.ne', div_self hpos.ne']

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)

include h hcoordinates in
/-- The derivative of the genuine height slice at angle zero is the
actual physical radial partial at every point of the reference piece. -/
theorem n05_referenceHeight_radial_deriv (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) :
    deriv (fun r => K.height (C.referenceState, 0) m (r, 0)) p.1 =
      radialPartial (K.height (C.referenceState, 0) m) p := by
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h.1.1.1.2.2.1
  rcases h.2.2.2.2 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  obtain ⟨_, _, _, _, _, _, hh, _⟩ := hcharts (C.referenceState, 0) hz hs m
  have hd : DifferentiableAt ℝ (K.height (C.referenceState, 0) m) p :=
    (hh.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have he : (fun r => K.height (C.referenceState, 0) m (r, 0)) =ᶠ[𝓝 p.1]
      (fun r => K.height (C.referenceState, 0) m (r, p.2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.1] with r hr
    exact (hcoordinates.1 m (r, p.2) ⟨hr, mem_univ _⟩).2.symm
  exact ((Radial.hasDerivAt_radialSlice hd).congr_of_eventuallyEq he).deriv

include h hcoordinates in
/-- The actual reference chart preserves the angular coordinate, so its
radial chain rule contains exactly its genuine planar Jacobian. -/
theorem n05_referenceChart_radial_chain (m : ℕ) {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K m) :
    radialPartial (fun q => φ (K.chart (C.referenceState, 0) m q)) p =
      planeJacobian (K.chart (C.referenceState, 0) m) p *
        radialPartial φ (K.chart (C.referenceState, 0) m p) := by
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h.1.1.1.2.2.1
  rcases h.2.2.2.2 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  have hc := (hcharts (C.referenceState, 0) hz hs m).2.2.2.2.1
  let ξ : ℝ → ℝ := fun r => (K.chart (C.referenceState, 0) m (r, 0)).1
  have hp0 : (p.1, (0 : ℝ)) ∈ physicalPieceOpen S K m := ⟨hp.1, mem_univ _⟩
  have hc0 : ContDiffAt ℝ ∞ (K.chart (C.referenceState, 0) m) (p.1, 0) :=
    hc.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp0)
  have hline : ContDiff ℝ ∞ (fun r : ℝ => (r, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hξ : DifferentiableAt ℝ ξ p.1 :=
    (hc0.comp p.1 hline.contDiffAt).fst.differentiableAt (by simp)
  have hslice : HasDerivAt (fun r => K.chart (C.referenceState, 0) m (r, p.2))
      (deriv ξ p.1, 0) p.1 := by
    apply (hξ.hasDerivAt.prodMk (hasDerivAt_const p.1 p.2)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hp.1] with r hr
    exact (hcoordinates.1 m (r, p.2) ⟨hr, mem_univ _⟩).1
  have hφd : DifferentiableAt ℝ φ (K.chart (C.referenceState, 0) m p) :=
    hφ.differentiable (by simp) _
  have hcomp : HasDerivAt (fun r => φ (K.chart (C.referenceState, 0) m (r, p.2)))
      (fderiv ℝ φ (K.chart (C.referenceState, 0) m p) (deriv ξ p.1, 0)) p.1 := by
    simpa only [Function.comp_def, Prod.eta] using
      hφd.hasFDerivAt.comp_hasDerivAt p.1 hslice
  have hd : DifferentiableAt ℝ (fun q => φ (K.chart (C.referenceState, 0) m q)) p :=
    hφd.comp p ((hc.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt
      (by simp))
  have hvec : (deriv ξ p.1, (0 : ℝ)) = deriv ξ p.1 • ((1, 0) : PolarPoint) := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one, mul_zero]
  calc
    _ = fderiv ℝ φ (K.chart (C.referenceState, 0) m p) (deriv ξ p.1, 0) :=
      (Radial.hasDerivAt_radialSlice hd).unique hcomp
    _ = deriv ξ p.1 * radialPartial φ (K.chart (C.referenceState, 0) m p) := by
      rw [hvec, map_smul, smul_eq_mul]
      rfl
    _ = _ := by
      rw [n05_reference_planeJacobian_radial h hcoordinates m hp]

include h hcoordinates in
/-- The physical derivative of ψ is exactly the transported canonical
test derivative minus the actual logarithmic height derivative times ψ. -/
theorem n05CanonicalRadialTestTransport_radial (m : ℕ) {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K m) :
    radialPartial (n05CanonicalRadialTestTransport S C K m φ) p =
      n05CanonicalAngularTransport S C K m (radialPartial φ) p -
        (radialPartial (K.height (C.referenceState, 0) m) p /
          K.height (C.referenceState, 0) m p) * n05CanonicalRadialTestTransport S C K m φ p := by
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h.1.1.1.2.2.1
  rcases h.2.2.2.2 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  obtain ⟨_, _, _, _, hc, _, hh, hn⟩ := hcharts (C.referenceState, 0) hz hs m
  let Φ := K.chart (C.referenceState, 0) m
  let H := K.height (C.referenceState, 0) m
  let J := planeJacobian Φ
  let σ : ℝ := |J p| / J p
  have hnear := (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have hca : ContDiffAt ℝ ∞ Φ p := hc.contDiffAt hnear
  have hha : ContDiffAt ℝ ∞ H p := hh.contDiffAt hnear
  have hJa : ContDiffAt ℝ ∞ J p := contDiffAt_planeJacobian hca
  have hJ0 : J p ≠ 0 := (hn p hp).2.1
  have hH0 : H p ≠ 0 := (hn p hp).1.ne'
  have hcomp : DifferentiableAt ℝ (fun q => φ (Φ q)) p :=
    (hφ.contDiffAt.comp p hca).differentiableAt (by simp)
  have hheight : DifferentiableAt ℝ H p := hha.differentiableAt (by simp)
  have hinv : DifferentiableAt ℝ (fun q : PolarPoint => (H q)⁻¹) p :=
    hheight.inv hH0
  have hquot : DifferentiableAt ℝ (fun q : PolarPoint => φ (Φ q) / H q) p := by
    simpa only [Pi.mul_def, div_eq_mul_inv] using hcomp.mul hinv
  have hsign := n05_abs_div_eventually_constant hJa.continuousAt hJ0
  have he : n05CanonicalRadialTestTransport S C K m φ =ᶠ[𝓝 p]
      (fun q => σ * (φ (Φ q) / H q)) := by
    filter_upwards [hnear, hsign] with q hq hσ
    rw [n05CanonicalRadialTestTransport_eq_actual h hcoordinates m φ hq]
    exact congrArg (fun c : ℝ => c * (φ (Φ q) / H q)) hσ
  have hr : radialPartial (n05CanonicalRadialTestTransport S C K m φ) p =
      σ * radialPartial (fun q => φ (Φ q) / H q) p := by
    calc
      _ = radialPartial (fun q => σ * (φ (Φ q) / H q)) p :=
        congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0)) (he.fderiv_eq (𝕜 := ℝ))
      _ = _ := by
        rw [radialPartial_mul (differentiableAt_const σ) hquot,
          radialPartial_const, zero_mul, zero_add]
  rw [hr, radialPartial_div hcomp hheight hH0,
    n05_referenceChart_radial_chain h hcoordinates m hφ hp,
    n05CanonicalAngularTransport_eq_actual h hcoordinates m (radialPartial φ) hp,
    n05CanonicalRadialTestTransport_eq_actual h hcoordinates m φ hp]
  change σ * ((J p * radialPartial φ (Φ p) * H p - φ (Φ p) * radialPartial H p) / H p ^ 2) =
    |J p| / H p * radialPartial φ (Φ p) - (radialPartial H p / H p) *
      (|J p| / J p * (φ (Φ p) / H p))
  dsimp only [σ]
  field_simp [hJ0, hH0]
  ring

end ContinuousFlexibility.Statements
