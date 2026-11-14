module

public import ContinuousFlexibility.Analysis.CanonicalBoundaryLift
public import ContinuousFlexibility.Analysis.CanonicalClosedInverseJets
public import ContinuousFlexibility.Analysis.CanonicalDomainConnected
public import ContinuousFlexibility.Analysis.CanonicalStripGeometry
public import ContinuousFlexibility.Geometry.EuclideanRigidity
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The actual orientations of the paired negative halves

The inverse chart has a straight canonical root boundary. Its angular
restriction is an increasing degree-one lift. Its radial restriction
enters the physical negative component, so its ordinary radial derivative
has the inward sign. The nonzero ordinary Jacobian makes that sign strict.
Actual inverse germs transfer the sign to the forward chart, and
connectedness propagates it throughout the closure of the current piece.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem deriv_nonneg_of_right_lower
    {f : ℝ → ℝ} {d R : ℝ} (hd : HasDerivAt f d 0) (hR : 0 < R)
    (hlower : ∀ t ∈ Ioo 0 R, f 0 ≤ f t) : 0 ≤ d := by
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [Ioo_mem_nhdsGT hR] with t ht
  simpa only [zero_add, smul_eq_mul] using
    mul_nonneg (inv_nonneg.mpr ht.1.le) (sub_nonneg.mpr (hlower t ht))

/-- A genuine boundary lift with inward radial values has the
corresponding strict Jacobian sign. The sign is derived from actual
one-sided difference quotients, not included in the hypotheses. -/
theorem boundaryLift_signed_planeJacobian_pos
    {G : PolarPoint → PolarPoint} {c R T σ : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hσ : σ ≠ 0)
    (hG : ∀ θ, DifferentiableAt ℝ G (0, θ))
    (hJ : ∀ θ, planeJacobian G (0, θ) ≠ 0)
    (hradial : ∀ θ, (G (0, θ)).1 = c)
    (hperiod : ∀ θ, (G (0, θ + T)).2 = (G (0, θ)).2 + T)
    (hinward : ∀ r ∈ Ioo 0 R, ∀ θ, 0 ≤ σ * ((G (r, θ)).1 - c)) :
    ∀ θ, 0 < σ * planeJacobian G (0, θ) := by
  have hangle := deriv_pos_of_periodic_lift_of_ne_zero hT hperiod
    (boundaryAngular_deriv_ne_zero hG hJ hradial)
  intro θ
  have hline : HasDerivAt (fun η : ℝ => ((0 : ℝ), η)) (0, 1) θ :=
    (hasDerivAt_const θ 0).prodMk (hasDerivAt_id' θ)
  have hcurve : HasDerivAt (fun η : ℝ => G (0, η))
      (fderiv ℝ G (0, θ) (0, 1)) θ := by
    simpa only [Function.comp_def] using
      (hG θ).hasFDerivAt.comp_hasDerivAt θ hline
  have hcurve₁ : HasDerivAt (fun η : ℝ => (G (0, η)).1)
      (fderiv ℝ G (0, θ) (0, 1)).1 θ := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      HasFDerivAt.hasDerivAt (HasFDerivAt.fst hcurve.hasFDerivAt)
  have hcurve₂ : HasDerivAt (fun η : ℝ => (G (0, η)).2)
      (fderiv ℝ G (0, θ) (0, 1)).2 θ := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      HasFDerivAt.hasDerivAt (HasFDerivAt.snd hcurve.hasFDerivAt)
  have he : (fun η : ℝ => (G (0, η)).1) = (fun _ : ℝ => c) :=
    funext hradial
  have hξ : (fderiv ℝ G (0, θ) (0, 1)).1 = 0 := by
    have hd := hcurve₁.deriv
    rw [he, deriv_const] at hd
    exact hd.symm
  have hη : 0 < (fderiv ℝ G (0, θ) (0, 1)).2 := by
    rw [← hcurve₂.deriv]
    exact hangle θ
  have hrline : HasDerivAt (fun r : ℝ => (r, θ)) (1, 0) 0 :=
    (hasDerivAt_id' 0).prodMk (hasDerivAt_const 0 θ)
  have hrcurve : HasDerivAt (fun r : ℝ => G (r, θ))
      (fderiv ℝ G (0, θ) (1, 0)) 0 := by
    simpa only [Function.comp_def] using
      (hG θ).hasFDerivAt.comp_hasDerivAt 0 hrline
  have hr : HasDerivAt (fun r : ℝ => (G (r, θ)).1)
      (fderiv ℝ G (0, θ) (1, 0)).1 0 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      HasFDerivAt.hasDerivAt (HasFDerivAt.fst hrcurve.hasFDerivAt)
  have hrad : 0 ≤ σ * (fderiv ℝ G (0, θ) (1, 0)).1 := by
    apply deriv_nonneg_of_right_lower (hr.const_mul σ) hR
    intro r hr
    have h := hinward r hr θ
    change σ * (G (0, θ)).1 ≤ σ * (G (r, θ)).1
    rw [hradial]
    nlinarith only [h]
  have hnonneg : 0 ≤ σ * planeJacobian G (0, θ) := by
    have h := mul_nonneg hrad hη.le
    simpa only [planeJacobian, hξ, mul_zero, sub_zero, mul_assoc] using h
  rcases eq_or_lt_of_le hnonneg with hzero | hpos
  · exact False.elim ((mul_ne_zero hσ (hJ θ)) hzero.symm)
  · exact hpos

/-- A root circle and inward image condition determine the sign of the
forward Jacobian on the whole current closed piece. Both actual inverse
germs and connectedness are supplied by the canonical geometry contract. -/
theorem canonicalClosed_signed_planeJacobian_pos_of_root
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (i : ℕ) {c σ : ℝ}
    (hleft : K.left i = 0) (hσ : σ ≠ 0)
    (hradial : ∀ θ, (K.inverseChart z i (0, θ)).1 = c)
    (hinward : ∀ p ∈ physicalPieceOpen S K z i, 0 ≤ σ * (p.1 - c)) :
    ∀ p ∈ physicalPieceClosed S K z i, 0 < σ * planeJacobian (K.chart z i) p := by
  have hcharts := hA.charts z hz hs i
  have hclosed := hA.boundary z hz hs i
  have hR : 0 < K.right i := by
    simpa only [hleft] using (hA.referenceBounds i).2.1
  have hzero (θ : ℝ) : ((0 : ℝ), θ) ∈ canonicalClosed S K i := by
    change (0 : ℝ) ∈ Icc (K.left i) (K.right i) ∧ θ ∈ (univ : Set ℝ)
    rw [hleft]
    exact ⟨⟨le_rfl, hR.le⟩, mem_univ _⟩
  have hG (θ : ℝ) : ContDiffAt ℝ ∞ (K.inverseChart z i) (0, θ) :=
    n04b_inverseChart_contDiffAt_closed hA hz hs i (hzero θ)
  have hJG (θ : ℝ) : planeJacobian (K.inverseChart z i) (0, θ) ≠ 0 := by
    rw [canonicalClosed_inverse_planeJacobian hA hz hs i (hzero θ)]
    exact inv_ne_zero (hclosed.2.2.2.2.1 _ (hclosed.2.1 (hzero θ))).2.2.1
  have hperiod (θ : ℝ) :
      (K.inverseChart z i (0, θ + Real.pi)).2 =
        (K.inverseChart z i (0, θ)).2 + Real.pi := by
    have hp : ((0 : ℝ), θ) ∈ closure (canonicalOpen S K i) := by
      rw [canonicalOpen, closure_prod_eq,
        closure_Ioo (hA.referenceBounds i).2.1.ne, closure_univ]
      exact hzero θ
    have hpv : ContinuousAt (K.inverseChart z i)
        (((0 : ℝ), θ) + (0, Real.pi)) := by
      simpa only [Prod.mk_add_mk, zero_add] using (hG (θ + Real.pi)).continuousAt
    have he := periodic_lift_at_closure hp (hG θ).continuousAt hpv
      (fun q hq => canonicalInverse_periodic_on_open hA hz hs i hq)
    simpa only [Prod.mk_add_mk, zero_add, Prod.snd_add] using congrArg Prod.snd he
  have hinside (r : ℝ) (hr : r ∈ Ioo 0 (K.right i)) (θ : ℝ) :
      0 ≤ σ * ((K.inverseChart z i (r, θ)).1 - c) := by
    apply hinward
    apply hcharts.2.1
    change r ∈ Ioo (K.left i) (K.right i) ∧ θ ∈ (univ : Set ℝ)
    rw [hleft]
    exact ⟨hr, mem_univ _⟩
  have hJGpos := boundaryLift_signed_planeJacobian_pos hR Real.pi_pos hσ
    (fun θ => (hG θ).differentiableAt (by simp)) hJG hradial hperiod hinside 0
  let p₀ : PolarPoint := K.inverseChart z i (0, 0)
  have hp₀ : p₀ ∈ physicalPieceClosed S K z i := hclosed.2.1 (hzero 0)
  have hJF : planeJacobian (K.chart z i) p₀ ≠ 0 :=
    (hclosed.2.2.2.2.1 _ hp₀).2.2.1
  have hinv : planeJacobian (K.inverseChart z i) (0, 0) =
      (planeJacobian (K.chart z i) p₀)⁻¹ :=
    canonicalClosed_inverse_planeJacobian hA hz hs i (hzero 0)
  have hbase : 0 < σ * planeJacobian (K.chart z i) p₀ := by
    have he : σ * planeJacobian (K.chart z i) p₀ =
        (σ * planeJacobian (K.inverseChart z i) (0, 0)) *
          planeJacobian (K.chart z i) p₀ ^ 2 := by
      rw [hinv, pow_two]
      calc
        σ * planeJacobian (K.chart z i) p₀ =
            σ * ((planeJacobian (K.chart z i) p₀)⁻¹ *
              planeJacobian (K.chart z i) p₀) *
              planeJacobian (K.chart z i) p₀ := by rw [inv_mul_cancel₀ hJF, mul_one]
        _ = _ := by ring
    rw [he]
    exact mul_pos hJGpos (sq_pos_of_ne_zero hJF)
  have hconnected : IsPreconnected (physicalPieceClosed S K z i) :=
    (canonicalPhysicalPiece_isPreconnected hA hz hs i).closure
  have hcont : ContinuousOn (fun p => σ * planeJacobian (K.chart z i) p)
      (physicalPieceClosed S K z i) := by
    apply continuousOn_const.mul
    intro p hp
    exact (contDiffAt_planeJacobian (hclosed.2.2.2.2.1 p hp).1).continuousAt.continuousWithinAt
  intro p hp
  by_contra hnot
  obtain ⟨q, hq, hzero⟩ := hconnected.intermediate_value hp hp₀ hcont
    ⟨le_of_not_gt hnot, hbase.le⟩
  exact (mul_ne_zero hσ (hclosed.2.2.2.2.1 q hq).2.2.1) hzero

/-- The genuine current cut geometry fixes the two orientations:
the left half has positive Jacobian and the right half negative Jacobian,
including the ordinary derivatives on both closed pieces. -/
theorem canonicalCutPair_planeJacobian_signs
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    (hcut : CanonicalCutGeometry S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    (∀ p ∈ physicalPieceClosed S K z (K.cutPair m).1,
      0 < planeJacobian (K.chart z (K.cutPair m).1) p) ∧
    (∀ p ∈ physicalPieceClosed S K z (K.cutPair m).2,
      planeJacobian (K.chart z (K.cutPair m).2) p < 0) := by
  obtain ⟨_, _, _, _, _, _, hleftL, hleftR, _, _⟩ := hcut.1 m
  obtain ⟨_, _, _, hunion, hrootL, hrootR⟩ := hcut.2 z hz hs m
  have hroot (i : ℕ) (c : ℝ)
      (himage : K.inverseChart z i '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
        ({c} ×ˢ (univ : Set ℝ))) :
      ∀ θ, (K.inverseChart z i (0, θ)).1 = c := by
    intro θ
    have hmem := mem_image_of_mem (K.inverseChart z i)
      (show ((0 : ℝ), θ) ∈ ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) from
        ⟨mem_singleton 0, mem_univ θ⟩)
    rw [himage] at hmem
    simpa only [mem_singleton_iff] using hmem.1
  have hinside {p : PolarPoint}
      (hp : p ∈ physicalPieceOpen S K z (K.cutPair m).1 ∪
        physicalPieceOpen S K z (K.cutPair m).2) :
      p.1 ∈ Ioo (C.left m) (C.right m) := by
    rw [hunion] at hp
    exact hp.1.1
  constructor
  · have h := canonicalClosed_signed_planeJacobian_pos_of_root hA hz hs
      (K.cutPair m).1 hleftL (one_ne_zero : (1 : ℝ) ≠ 0)
      (hroot _ _ hrootL) (fun p hp => by
        simpa only [one_mul] using sub_nonneg.mpr (hinside (Or.inl hp)).1.le)
    simpa only [one_mul] using h
  · have h := canonicalClosed_signed_planeJacobian_pos_of_root hA hz hs
      (K.cutPair m).2 hleftR (neg_ne_zero.mpr (one_ne_zero : (1 : ℝ) ≠ 0))
      (hroot _ _ hrootR) (fun p hp => by
        simpa only [neg_one_mul] using
          neg_nonneg.mpr (sub_nonpos.mpr (hinside (Or.inr hp)).2.le))
    simpa only [neg_one_mul, neg_pos] using h

end ContinuousFlexibility.Analysis
