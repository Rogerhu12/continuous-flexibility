module

public import ContinuousFlexibility.Analysis.N05PrimitiveReferenceValues
public import ContinuousFlexibility.Analysis.N05ReferenceResidual

/-!
# Actual first reference bounds from primitive geometric jets

The stored height and Jacobian atoms supply four zeroth bounds. The first
height jet is unscaled by the actual physical interval length, whose inverse
is another stored atom. No coordinate, height, label, or nonlinear witness
is replaced.

The radial identity is differentiated on the open reference rectangle.
ReferenceRadial and ReferenceJets remain explicit hypotheses in this
module. Producing them from a full nonlinear construction is a separate
obligation of the shared interface.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter CanonicalGeometry
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

/-- The physical derivative of the actual height is the first unit-strip
height jet multiplied by the inverse physical length. -/
theorem n05_reference_height_deriv_unitAtom
    (hJ : ReferenceJets D T S C L K) (m : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
    let p : PolarPoint := ((r - K.physicalLeft m) /
      (K.physicalRight m - K.physicalLeft m), 0)
    deriv (fun t => K.height (C.referenceState, 0) m (t, 0)) r =
      mixedDerivative 1 0 (atom D T S C L K (C.referenceState, 0) m .height) p *
        (K.physicalRight m - K.physicalLeft m)⁻¹ := by
  let a := K.physicalLeft m
  let ell := K.physicalRight m - K.physicalLeft m
  let x := (r - a) / ell
  let A := atom D T S C L K (C.referenceState, 0) m .height
  have hell : ell ≠ 0 := (sub_pos.mpr (hr.1.trans hr.2)).ne'
  have hx : (x, (0 : ℝ)) ∈ unitStrip :=
    (n05_reference_unitPoint_normalization K m (θ := 0) hr).1
  have hA : ContDiffAt ℝ ∞ A (x, 0) :=
    (hJ.1 m .height).1.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hx)
  have hline : ContDiff ℝ ∞ (fun t : ℝ => (t, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hphi : DifferentiableAt ℝ (fun t => A (t, 0)) x :=
    (ContDiffAt.fun_comp (𝕜 := ℝ) (f := fun t : ℝ => (t, (0 : ℝ)))
      (g := A) x hA hline.contDiffAt).differentiableAt (by simp)
  have hinv : HasDerivAt (fun t : ℝ => (t - a) / ell) ell⁻¹ r := by
    have hsub : HasDerivAt (fun t : ℝ => t - a) (1 : ℝ) r :=
      (hasDerivAt_id' r).sub_const a
    have hscale : HasDerivAt (fun t : ℝ => (ell⁻¹ : ℝ) • (t - a))
        ((ell⁻¹ : ℝ) • (1 : ℝ)) r :=
      HasDerivAt.fun_const_smul (ell⁻¹ : ℝ) hsub
    simpa only [smul_eq_mul, mul_one, one_mul, div_eq_mul_inv, mul_comm] using hscale
  have hd : HasDerivAt (fun t => A ((t - a) / ell, 0))
      (deriv (fun t => A (t, 0)) x * ell⁻¹) r := by
    have houter : HasFDerivAt (fun t : ℝ => A (t, 0))
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv (fun t : ℝ => A (t, 0)) x)) x :=
      hphi.hasDerivAt.hasFDerivAt
    have hchain := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ)
      (l := fun t : ℝ => A (t, 0)) (f := fun t : ℝ => (t - a) / ell)
      r houter hinv
    simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, mul_comm] using hchain
  have heq : (fun t => K.height (C.referenceState, 0) m (t, 0)) =
      (fun t => A ((t - a) / ell, 0)) := by
    funext t
    change K.height (C.referenceState, 0) m (t, 0) =
      K.height (C.referenceState, 0) m (a + ell * ((t - a) / ell), 0)
    congr 1
    apply Prod.ext
    · dsimp only
      field_simp [hell]
      ring
    · rfl
  have hderiv := hd.deriv
  rw [← heq] at hderiv
  simpa only [mixedDerivative, iteratedDeriv_one, iteratedDeriv_zero] using hderiv

private theorem n05_reference_radial_jacobian
    (hrad : ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      K.chart (C.referenceState, 0) m p =
        ((K.chart (C.referenceState, 0) m (p.1, 0)).1, p.2) ∧
      K.height (C.referenceState, 0) m p =
        K.height (C.referenceState, 0) m (p.1, 0)) (m : ℕ)
    (hc : ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m)
      (referencePhysicalPieceOpen S K m)) {p : PolarPoint}
    (hp : p ∈ referencePhysicalPieceOpen S K m) :
    planeJacobian (K.chart (C.referenceState, 0) m) p =
      deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1 := by
  let xi : ℝ → ℝ := fun r => (K.chart (C.referenceState, 0) m (r, 0)).1
  have hp0 : (p.1, (0 : ℝ)) ∈ referencePhysicalPieceOpen S K m :=
    ⟨hp.1, mem_univ _⟩
  have hc0 := hc.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp0)
  have hline : ContDiff ℝ ∞ (fun r : ℝ => (r, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hxi : DifferentiableAt ℝ xi p.1 :=
    (hc0.comp p.1 hline.contDiffAt).fst.differentiableAt (by simp)
  have hFD : HasFDerivAt (fun q : PolarPoint => (xi q.1, q.2))
      (((ContinuousLinearMap.toSpanSingleton ℝ (deriv xi p.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    (hxi.hasDerivAt.hasFDerivAt.comp p hasFDerivAt_fst).prodMk hasFDerivAt_snd
  have hnear : K.chart (C.referenceState, 0) m =ᶠ[𝓝 p]
      (fun q : PolarPoint => (xi q.1, q.2)) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact (hrad m q hq).1
  rw [planeJacobian, (hFD.congr_of_eventuallyEq hnear).fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    one_mul, zero_mul, mul_one, mul_zero, sub_zero, xi]

/-- One primitive bound, selected at order one before every piece and point,
controls all five actual quantities. No lower bound `E0 ≥ 1` is used. -/
theorem n05_reference_primitive_first_E0_bound
    {base loss : ℕ} {ε : ℝ}
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hrad : ReferenceRadial S C K) (hJ : ReferenceJets D T S C L K) :
    ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) →
      |K.height (C.referenceState, 0) m (r, 0)| +
      |(K.height (C.referenceState, 0) m (r, 0))⁻¹| +
      |deriv (fun t => K.height (C.referenceState, 0) m (t, 0)) r| +
      |deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r| +
      |(deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r)⁻¹| ≤
        4 * (B * T.E0 (T.sample (K.cell m)) ^ B) +
          (B * T.E0 (T.sample (K.cell m)) ^ B) ^ 2 := by
  obtain ⟨B, hB, hb⟩ := hJ.2 1
  have hz : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h01.2.2.1
  have hradial : ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      K.chart (C.referenceState, 0) m p =
        ((K.chart (C.referenceState, 0) m (p.1, 0)).1, p.2) ∧
      K.height (C.referenceState, 0) m p =
        K.height (C.referenceState, 0) m (p.1, 0) := by
    intro m
    simpa only [h04.1.referenceDomain m] using hrad.1 m
  refine ⟨B, hB, fun m r hr => ?_⟩
  let p : PolarPoint := ((r - K.physicalLeft m) /
    (K.physicalRight m - K.physicalLeft m), 0)
  let X : ℝ := B * T.E0 (T.sample (K.cell m)) ^ B
  obtain ⟨hp, hpoint⟩ := n05_reference_unitPoint_normalization K m (θ := 0) hr
  change physicalUnitPoint K m p = (r, (0 : ℝ)) at hpoint
  have hzero (a : Atom) : |atom D T S C L K (C.referenceState, 0) m a p| ≤ X := by
    simpa only [mixedDerivative, iteratedDeriv_zero, Prod.eta] using
      hb m a p hp 0 0 (by omega)
  have hh : |K.height (C.referenceState, 0) m (r, 0)| ≤ X := by
    have h := hzero .height
    simp only [atom] at h
    simpa only [hpoint] using h
  have hhi : |(K.height (C.referenceState, 0) m (r, 0))⁻¹| ≤ X := by
    have h := hzero .heightInverse
    simp only [atom] at h
    simpa only [hpoint] using h
  have hX : 0 ≤ X := (abs_nonneg _).trans hh
  have hwidth : |(K.physicalRight m - K.physicalLeft m)⁻¹| ≤ X :=
    hzero .physicalLengthInverse
  have hd : |deriv (fun t => K.height (C.referenceState, 0) m (t, 0)) r| ≤ X ^ 2 := by
    rw [n05_reference_height_deriv_unitAtom hJ m hr, abs_mul]
    exact (mul_le_mul (hb m .height p hp 1 0 (by omega)) hwidth
      (abs_nonneg _) hX).trans_eq (by ring)
  have hc : ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m)
      (referencePhysicalPieceOpen S K m) := by
    simpa only [h04.1.referenceDomain m] using
      (h04.1.charts (C.referenceState, 0) hz hs m).2.2.2.2.1
  have hJac := n05_reference_radial_jacobian hradial m hc
    (show (r, (0 : ℝ)) ∈ referencePhysicalPieceOpen S K m from ⟨hr, mem_univ _⟩)
  have hj : |deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r| ≤ X := by
    have h := hzero .jacobian
    simp only [atom] at h
    simpa only [hpoint, abs_abs, hJac] using h
  have hji : |(deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r)⁻¹| ≤ X := by
    have h := hzero .jacobianInverse
    simp only [atom] at h
    simpa only [hpoint, abs_inv, abs_abs, hJac] using h
  change _ ≤ 4 * X + X ^ 2
  linarith only [hh, hhi, hd, hj, hji]

/-- The five actual reference bounds have a fixed discrete coefficient
envelope at the original stored label. -/
theorem n05_reference_primitive_first_bounds
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hrad : ReferenceRadial S C K) (hJ : ReferenceJets D T S C L K) :
    ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) →
      |K.height (C.referenceState, 0) m (r, 0)| +
      |(K.height (C.referenceState, 0) m (r, 0))⁻¹| +
      |deriv (fun t => K.height (C.referenceState, 0) m (t, 0)) r| +
      |deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r| +
      |(deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r)⁻¹| ≤
        B * radialE (D.cellIndex (K.cell m)) ^ B := by
  obtain ⟨B0, hB0, hb⟩ := n05_reference_primitive_first_E0_bound h01 h04 hrad hJ
  obtain ⟨C0, A, hC0, hA, hE⟩ := n05_material_sample_E0_power_bound hD hT hB0.le
  let P : ℝ := B0 * C0
  have hP : 0 < P := mul_pos hB0 hC0
  let B : ℝ := (4 * P + P ^ 2) + 2 * A + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hcoef : 4 * P + P ^ 2 ≤ B := by dsimp only [B]; linarith only [hA]
  have hexponent : 2 * A ≤ B := by
    dsimp only [B]
    nlinarith only [hP, sq_nonneg P]
  refine ⟨B, hB, fun m r hr => ?_⟩
  let E : ℝ := radialE (D.cellIndex (K.cell m))
  let X : ℝ := B0 * T.E0 (T.sample (K.cell m)) ^ B0
  have hEpos : 0 < E := Real.exp_pos _
  have hEone : 1 ≤ E := Real.one_le_exp (Radial.radialQ_nonneg _)
  have hsample := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
  have hX : 0 ≤ X := mul_nonneg hB0.le
    (Real.rpow_nonneg (hT.2.1 _ hsample).2.2.1.le _)
  have hXE : X ≤ P * E ^ A := by
    exact (mul_le_mul_of_nonneg_left (hE (K.cell m)) hB0.le).trans_eq
      (by dsimp only [P, E]; ring)
  have hEA : 0 ≤ E ^ A := Real.rpow_nonneg hEpos.le A
  have hpow : E ^ (2 * A) = E ^ A * E ^ A := by
    rw [show 2 * A = A + A by ring, Real.rpow_add hEpos]
  have hsquare : X ^ 2 ≤ P ^ 2 * E ^ (2 * A) := by
    calc
      _ = X * X := by ring
      _ ≤ (P * E ^ A) * (P * E ^ A) :=
        mul_le_mul hXE hXE hX (mul_nonneg hP.le hEA)
      _ = _ := by rw [hpow]; ring
  have hpower : E ^ A ≤ E ^ (2 * A) :=
    Real.rpow_le_rpow_of_exponent_le hEone (by linarith only [hA])
  calc
    _ ≤ 4 * X + X ^ 2 := hb m r hr
    _ ≤ 4 * (P * E ^ A) + P ^ 2 * E ^ (2 * A) :=
      add_le_add (mul_le_mul_of_nonneg_left hXE (by norm_num)) hsquare
    _ ≤ 4 * (P * E ^ (2 * A)) + P ^ 2 * E ^ (2 * A) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpower hP.le) (by norm_num)) (le_refl _)
    _ = (4 * P + P ^ 2) * E ^ (2 * A) := by ring
    _ ≤ B * E ^ B := mul_le_mul hcoef
      (Real.rpow_le_rpow_of_exponent_le hEone hexponent)
      (Real.rpow_nonneg hEpos.le _) hB.le

end ContinuousFlexibility.Statements
