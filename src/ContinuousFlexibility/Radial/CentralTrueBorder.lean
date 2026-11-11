import ContinuousFlexibility.Radial.BorderNormalization
import ContinuousFlexibility.Radial.CentralTurningPoints
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A true metric border supported in the central positive cap

The central kernel decreases throughout the right positive cap.  A smooth
nonnegative bump compactly contained in any subinterval of that cap therefore
has a strictly negative metric-variation pairing.  Dividing by that pairing
produces the genuine column `L'₂,w[wχ]φ`, normalized against the same kernel.

The normalization theorem is stated for globally smooth profiles which agree
with the central model on the cap.  This is the situation of the completed
reference.  It does not assume smoothness of the inverse central radius at
nonpositive radii, where that inverse has no geometric meaning.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The actual radial derivative of the central kernel. -/
theorem centralKernelHeight_deriv_radius (x : ℝ) :
    deriv centralKernelHeight (centralRadius x) =
      centralKernelHeight (centralRadius x) * (centralRadiusA - 2 * x) /
        deriv centralRadius x := by
  have ht := (hasStrictDerivAt_centralModelCoordinate x).hasDerivAt
  have hh := ((ht.const_mul centralRadiusA).sub (ht.pow 2)).exp
  change HasDerivAt centralKernelHeight _ (centralRadius x) at hh
  rw [hh.deriv, centralKernelHeight_pullback]
  simp only [centralModelCoordinate_radius, Pi.sub_apply, Pi.pow_apply,
    Nat.reduceSub, pow_one, Nat.cast_ofNat]
  ring

theorem centralRadiusA_lt_twice_right_turn :
    centralRadiusA < 2 * sqrt centralOscillatorA := by
  have hs := sqrt_pos.mpr centralOscillatorA_pos
  have hsq := sq_sqrt centralOscillatorA_pos.le
  have ha := centralRadiusA_pos
  have ha2 := centralRadiusA_sq
  nlinarith

/-- In the right positive cap the genuine kernel has negative derivative. -/
theorem centralKernelHeight_deriv_neg_of_right_cap {r : ℝ}
    (hr : centralRadius (sqrt centralOscillatorA) < r) :
    deriv centralKernelHeight r < 0 := by
  have hr0 : 0 < r := (centralRadius_pos _).trans hr
  have hR := centralRadius_modelCoordinate hr0
  have hx : sqrt centralOscillatorA < centralModelCoordinate r :=
    strictMono_centralRadius.lt_iff_lt.mp (by simpa only [hR] using hr)
  have hnum : centralRadiusA - 2 * centralModelCoordinate r < 0 := by
    linarith [centralRadiusA_lt_twice_right_turn]
  rw [← hR, centralKernelHeight_deriv_radius]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (centralKernelHeight_pos _) hnum)
    (deriv_centralRadius_pos _)

/-- The profile increases and the kernel decreases on every right positive cap. -/
theorem central_right_cap_signs {c r : ℝ} (hc : 0 < c)
    (hr : centralRadius (sqrt centralOscillatorA) < r) :
    0 < deriv (centralRadialProfile c) r ∧
      centralKernelHeight r * deriv centralKernelHeight r < 0 := by
  have hr0 : 0 < r := (centralRadius_pos _).trans hr
  have hR := centralRadius_modelCoordinate hr0
  have hx : sqrt centralOscillatorA < centralModelCoordinate r :=
    strictMono_centralRadius.lt_iff_lt.mp (by simpa only [hR] using hr)
  refine ⟨?_, mul_neg_of_pos_of_neg (centralKernelHeight_pos _)
    (centralKernelHeight_deriv_neg_of_right_cap hr)⟩
  rw [← hR]
  apply (centralRadialProfile_deriv_pos_iff hc _).mpr
  nlinarith [sqrt_nonneg centralOscillatorA, sq_sqrt centralOscillatorA_pos.le]

/-- A fixed bump occupying only the middle half of the chosen interval. -/
def centralTrueBorderBump (l h : ℝ) (hlh : l < h) : ContDiffBump ((l + h) / 2) :=
  ⟨(h - l) / 8, (h - l) / 4, by linarith, by linarith⟩

theorem centralTrueBorderBump_tsupport (l h : ℝ) (hlh : l < h) :
    tsupport (centralTrueBorderBump l h hlh : ℝ → ℝ) =
      Icc ((3 * l + h) / 4) ((l + 3 * h) / 4) := by
  rw [(centralTrueBorderBump l h hlh).tsupport_eq, Real.closedBall_eq_Icc]
  change Icc ((l + h) / 2 - (h - l) / 4) ((l + h) / 2 + (h - l) / 4) = _
  congr 1 <;> ring

theorem centralTrueBorderBump_tsupport_subset (l h : ℝ) (hlh : l < h) :
    tsupport (centralTrueBorderBump l h hlh : ℝ → ℝ) ⊆ Ioo l h := by
  rw [centralTrueBorderBump_tsupport]
  intro r hr
  constructor <;> linarith [hr.1, hr.2]

theorem centralTrueBorderBump_center (l h : ℝ) (hlh : l < h) :
    centralTrueBorderBump l h hlh ((l + h) / 2) = 1 :=
  (centralTrueBorderBump l h hlh).one_of_mem_closedBall
    (Metric.mem_closedBall_self (centralTrueBorderBump l h hlh).rIn_pos.le)

theorem centralTrueBorderBump_cap_signs {c l h : ℝ} (hc : 0 < c)
    (hl : centralRadius (sqrt centralOscillatorA) ≤ l) (hlh : l < h) :
    ∀ r ∈ tsupport (centralTrueBorderBump l h hlh : ℝ → ℝ),
      0 < deriv (centralRadialProfile c) r ∧
        centralKernelHeight r * deriv centralKernelHeight r < 0 := by
  intro r hr
  exact central_right_cap_signs hc
    (hl.trans_lt (centralTrueBorderBump_tsupport_subset l h hlh hr).1)

private theorem centralTrueBorder_local_signs
    {w φ : ℝ → ℝ} {scale amplitude l h : ℝ}
    (hscale : 0 < scale) (hamplitude : amplitude ≠ 0)
    (hl : centralRadius (sqrt centralOscillatorA) ≤ l)
    (hw : EqOn w (centralRadialProfile scale) (Ioo l h))
    (hφ : EqOn φ (fun r => amplitude * centralKernelHeight r) (Ioo l h)) :
    ∀ r ∈ Ioo l h, 0 < w r ∧ 0 < deriv w r ∧ φ r * deriv φ r < 0 := by
  intro r hr
  have hcap : centralRadius (sqrt centralOscillatorA) < r := hl.trans_lt hr.1
  have hr0 : 0 < r := (centralRadius_pos _).trans hcap
  have hsgn := central_right_cap_signs hscale hcap
  have hwd : deriv w r = deriv (centralRadialProfile scale) r := hw.deriv isOpen_Ioo hr
  have hφd : deriv φ r = amplitude * deriv centralKernelHeight r := by
    rw [hφ.deriv isOpen_Ioo hr, deriv_const_mul_field]
  refine ⟨?_, hwd.symm ▸ hsgn.1, ?_⟩
  · rw [hw hr]
    exact centralRadialProfile_pos hscale hr0
  · rw [hφ hr, hφd]
    have he : (amplitude * centralKernelHeight r) *
        (amplitude * deriv centralKernelHeight r) =
        amplitude ^ 2 * (centralKernelHeight r * deriv centralKernelHeight r) := by ring
    rw [he]
    exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hamplitude) hsgn.2

/-- A genuine compact border column is smooth even though the expression
contains `1 / r`: its support stays a positive distance from zero. -/
theorem contDiff_trueBorderColumn_of_support
    {w φ χ : ℝ → ℝ} {l h : ℝ}
    (hw : ContDiff ℝ ∞ w) (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ)
    (hl : 0 < l) (hsupp : Function.support χ ⊆ Icc l h) :
    ContDiff ℝ ∞ (fun r => radialJacobi 4 (fun t => w t * χ t) φ r) := by
  have hv : ContDiff ℝ ∞ (fun t => w t * χ t) := hw.mul hχ
  have hdφ : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hdv : ContDiff ℝ ∞ (deriv fun t => w t * χ t) :=
    (contDiff_infty_iff_deriv.mp hv).2
  have hflux : ContDiff ℝ ∞ (deriv fun t => (w t * χ t) * deriv φ t) :=
    (contDiff_infty_iff_deriv.mp (hv.mul hdφ)).2
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : 0 < r
  · exact hflux.contDiffAt.sub
      (((contDiffAt_const.mul hdv.contDiffAt).div contDiffAt_id hr.ne').mul hφ.contDiffAt)
  · have hrI : r ∉ Icc l h := fun hm => hr (hl.trans_le hm.1)
    have hn : ∀ᶠ t in 𝓝 r, t ∉ Icc l h :=
      isClosed_Icc.isOpen_compl.mem_nhds hrI
    have hzero : (fun r => radialJacobi 4 (fun t => w t * χ t) φ r) =ᶠ[𝓝 r]
        (fun _ => (0 : ℝ)) :=
      hn.mono fun t ht => border_column_support hsupp ht
    exact ContDiffAt.congr_of_eventuallyEq
      (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) r) hzero

/-- The metric border can be normalized before constructing any global inverse.
Only agreement with the central model on the chosen positive cap is needed.
The whole-line and annular pairings are both exactly one. -/
theorem exists_central_true_border
    {w φ : ℝ → ℝ} {scale amplitude a b l h : ℝ}
    (hw : ContDiff ℝ ∞ w) (hφ : ContDiff ℝ ∞ φ)
    (hscale : 0 < scale) (hamplitude : amplitude ≠ 0)
    (hal : a < l) (hlh : l < h) (hhb : h < b)
    (hl : centralRadius (sqrt centralOscillatorA) ≤ l)
    (hwmodel : EqOn w (centralRadialProfile scale) (Ioo l h))
    (hφmodel : EqOn φ (fun r => amplitude * centralKernelHeight r) (Ioo l h)) :
    ∃ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ioo l h ∧
      (∃ r, χ r ≠ 0) ∧
      (∀ r ∈ tsupport χ, 0 < deriv w r ∧ φ r * deriv φ r < 0) ∧
      ContDiff ℝ ∞ (fun r => radialJacobi 4 (fun t => w t * χ t) φ r) ∧
      HasCompactSupport (fun r => radialJacobi 4 (fun t => w t * χ t) φ r) ∧
      tsupport (fun r => radialJacobi 4 (fun t => w t * χ t) φ r) ⊆ Ioo l h ∧
      (∫ r : ℝ, radialJacobi 4 (fun t => w t * χ t) φ r * φ r) = 1 ∧
      (∫ r in a..b, radialJacobi 4 (fun t => w t * χ t) φ r * φ r) = 1 := by
  let bump := centralTrueBorderBump l h hlh
  let l' : ℝ := (3 * l + h) / 4
  let h' : ℝ := (l + 3 * h) / 4
  have hll' : l < l' := by dsimp [l']; linarith
  have hh'h : h' < h := by dsimp [h']; linarith
  have hl0 : 0 < l := (centralRadius_pos _).trans_le hl
  have hsupp : Function.support (bump : ℝ → ℝ) ⊆ Icc l' h' := by
    have ht := centralTrueBorderBump_tsupport l h hlh
    exact (subset_tsupport (bump : ℝ → ℝ)).trans (by simpa only [bump, l', h'] using ht.subset)
  have hbpos : ∃ r, 0 < bump r :=
    ⟨(l + h) / 2, by rw [show bump ((l + h) / 2) = 1 from centralTrueBorderBump_center l h hlh]; norm_num⟩
  have hsign := centralTrueBorder_local_signs hscale hamplitude hl hwmodel hφmodel
  let pairing : ℝ := borderPairing w φ bump l h
  have hpairing : pairing < 0 :=
    border_pairing_neg hw hφ bump.contDiff hl0 hll' hh'h hsupp
      bump.nonneg' hbpos (fun r hr => (hsign r hr).1)
      (fun r hr => (hsign r hr).2.2)
  have hpairing0 : pairing ≠ 0 := hpairing.ne
  let χ : ℝ → ℝ := fun r => bump r / pairing
  have hχsmooth : ContDiff ℝ ∞ χ := bump.contDiff.div_const pairing
  have hχsupport : Function.support χ ⊆ Function.support (bump : ℝ → ℝ) := by
    intro r hr
    change bump r ≠ 0
    intro hz
    exact hr (by simp only [χ, hz, zero_div])
  have hχcompact : HasCompactSupport χ := bump.hasCompactSupport.mono hχsupport
  have hχclosed : tsupport χ ⊆ Icc l' h' :=
    closure_minimal (hχsupport.trans hsupp) isClosed_Icc
  have hχcap : tsupport χ ⊆ Ioo l h := fun r hr =>
    ⟨hll'.trans_le (hχclosed hr).1, (hχclosed hr).2.trans_lt hh'h⟩
  have hχsupport' : Function.support χ ⊆ Icc l' h' := hχsupport.trans hsupp
  let g : ℝ → ℝ := fun r => radialJacobi 4 (fun t => w t * χ t) φ r
  have hgsupport : Function.support g ⊆ Icc l' h' := by
    intro r hr
    by_contra hm
    exact hr (border_column_support hχsupport' hm)
  have hgclosed : tsupport g ⊆ Icc l' h' := closure_minimal hgsupport isClosed_Icc
  have hgcompact : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hgsupport
  have hgcap : tsupport g ⊆ Ioo l h := fun r hr =>
    ⟨hll'.trans_le (hgclosed hr).1, (hgclosed hr).2.trans_lt hh'h⟩
  have hnormalized : (∫ r in l..h, g r * φ r) = 1 :=
    border_normalized hw hφ bump.contDiff hl0 hll' hh'h hsupp
      bump.nonneg' hbpos (fun r hr => (hsign r hr).1)
      (fun r hr => (hsign r hr).2.2)
  have hpairSupport : Function.support (fun r => g r * φ r) ⊆ Ioc l h := by
    intro r hr
    have hgr : r ∈ Function.support g := by
      intro hz
      exact hr (by change g r * φ r = 0; rw [hz, zero_mul])
    have hi := hgcap (subset_tsupport g hgr)
    exact ⟨hi.1, hi.2.le⟩
  have hwhole : (∫ r : ℝ, g r * φ r) = 1 := by
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hpairSupport]
    exact hnormalized
  have hannular : (∫ r in a..b, g r * φ r) = 1 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset
      (hpairSupport.trans (fun r hr => ⟨hal.trans hr.1, hr.2.trans hhb.le⟩))]
    exact hwhole
  refine ⟨χ, hχsmooth, hχcompact, hχcap, ?_, ?_, ?_, hgcompact, hgcap, hwhole, hannular⟩
  · refine ⟨(l + h) / 2, ?_⟩
    change bump ((l + h) / 2) / pairing ≠ 0
    rw [show bump ((l + h) / 2) = 1 from centralTrueBorderBump_center l h hlh]
    exact div_ne_zero one_ne_zero hpairing0
  · intro r hr
    exact (hsign r (hχcap hr)).2
  · exact contDiff_trueBorderColumn_of_support hw hφ hχsmooth
      (hl0.trans hll') hχsupport'

end ContinuousFlexibility.Radial
