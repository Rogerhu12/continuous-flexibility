module

public import ContinuousFlexibility.Analysis.ReturnCoefficientErrorMixedWeighted
public import ContinuousFlexibility.Analysis.ReturnOpticalCutoffPatching
public import ContinuousFlexibility.Analysis.N01ControlIndexBound
public import ContinuousFlexibility.Analysis.MaterialSampleRadialLoss

/-!
# Global bounds for the actual patched independent coefficient error

The closed optical collars include every active cutoff derivative.
Outside them the exact local coefficient map is zero on a neighborhood.
The global selector has the same local jet, or zero near a nonnegative
reference radius. The actual containing-cell index bound lets the
residual height factor absorb every remaining spatial derivative loss.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem norm_iteratedFDeriv_le_on_closed_radial_interval
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (ℝ × ℝ) → F} (hf : ContDiff ℝ ∞ f)
    {l h A : ℝ} (hlh : l < h) (n : ℕ)
    (hbound : ∀ p : ℝ × ℝ, p.1 ∈ Ioo l h → ‖iteratedFDeriv ℝ n f p‖ ≤ A)
    {p : ℝ × ℝ} (hp : p.1 ∈ Icc l h) :
    ‖iteratedFDeriv ℝ n f p‖ ≤ A := by
  have hc : Continuous (fun r : ℝ => ‖iteratedFDeriv ℝ n f (r, p.2)‖) :=
    (hf.continuous_iteratedFDeriv (by simp)).norm.comp
      (continuous_id.prodMk continuous_const)
  have hclosure : closure (Ioo l h) = Icc l h := closure_Ioo hlh.ne
  exact le_on_closure (fun r hr => hbound (r, p.2) hr)
    hc.continuousOn continuousOn_const (by simpa only [hclosure] using hp)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

theorem N01Properties.returnLabel_height_actualCell_radialE_envelope
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    {γ P : ℝ} (hγ : 0 < γ) (hP : 0 ≤ P) :
    ∃ K : ℝ, 0 < K ∧ ∀ m,
      T.H (T.sample m) ^ γ * radialE (D.cellIndex (j m)) ^ P ≤ K := by
  obtain ⟨A, hA, hindex⟩ := hN.control_actual_cell_index_bound hS hT
  obtain ⟨K, hK, hb⟩ := materialSample_radialE_rpow_le_M_of_index_bound
    hT hN.1.1 hA hP
  obtain ⟨L, hL, hHL⟩ := materialSample_H_M_envelope hT hN.1.1 hγ 1
  refine ⟨K * L, mul_pos hK hL, fun m => ?_⟩
  have hH : 0 ≤ T.H (T.sample m) ^ γ :=
    (Real.rpow_pos_of_pos ((material_circle_sample_weights_pos hT hN.1.1).2 m) γ).le
  have hHL' : T.H (T.sample m) ^ γ * T.M (T.sample m) ≤ L := by
    simpa only [Real.rpow_one] using hHL m
  calc
    _ ≤ T.H (T.sample m) ^ γ * (K * T.M (T.sample m)) :=
      mul_le_mul_of_nonneg_left (hb m (D.cellIndex (j m)) (hindex m (j m) (hcell m))) hH
    _ = K * (T.H (T.sample m) ^ γ * T.M (T.sample m)) := by ring
    _ ≤ K * L := mul_le_mul_of_nonneg_left hHL' hK.le

theorem returnCorrectionLocalCoefficientError_eventually_zero_of_radial_support
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (m : ℕ) (ρ : CircleSpace S) {l h : ℝ}
    (hsupp : Function.support (deriv (χ m)) ⊆ Icc l h)
    (p : PolarPoint) (hp : p.1 ∉ Icc l h) :
    (fun q => returnCorrectionLocalCoefficientError D S C R χ z m q ρ) =ᶠ[𝓝 p]
      fun _ => (0 : ℝ × ℝ) := by
  have hnear : ∀ᶠ r in 𝓝 p.1, r ∉ Icc l h :=
    isClosed_Icc.isOpen_compl.mem_nhds hp
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hnear] with q hq
  have hd : deriv (χ m) q.1 = 0 := by
    by_contra hne
    exact hq (hsupp hne)
  rw [returnCorrectionLocalCoefficientError_eq_zero_of_deriv_zero D S C R χ z m q hd,
    LinearMap.zero_apply]

section ActualCoefficients

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (R : ReturnEquationData S) {z : AnnularState S × ℝ}
  (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
  (j : ℕ → ℕ) (x δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m)
  (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
  (hinside : ∀ m, C.left m < x m - δ m ∧ x m + δ m < C.right m)
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, χ m r ∈ Icc (0 : ℝ) 1)
  (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Icc (x m - δ m) (x m + δ m))
  (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
    χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
  {lam P₀ : ℝ} (hlam : 0 < lam) (hP₀ : 0 ≤ P₀)
  (hlower : ∀ m : ℕ, ∀ p : PolarPoint,
    p.1 ∈ Icc (x m - δ m) (x m + δ m) →
    lam * radialE (D.cellIndex (j m)) ^ (-P₀) ≤
      (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

include hN hS hT hz hsector hinside hχ hχrange hsupp hlam hlower

theorem N01Properties.returnCorrectionLocalCoefficientError_contDiff_of_collar
    (ρ : CircleSpace S) (m : ℕ) :
    ContDiff ℝ ∞ (fun p => returnCorrectionLocalCoefficientError D S C R χ z m p ρ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.1 ∈ Icc (x m - δ m) (x m + δ m)
  · have hp' : p.1 ∈ Ioo (C.left m) (C.right m) :=
      ⟨(hinside m).1.trans_le hp.1, hp.2.trans_lt (hinside m).2⟩
    have hdisc : 0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p :=
      (mul_pos hlam (Real.rpow_pos_of_pos (Real.exp_pos _) _)).trans_le (hlower m p hp)
    exact hN.returnCorrectionLocalCoefficientError_contDiffAt hS hT R hz hsector
      χ m (hχ m) (fun r _ => hχrange m r) ρ p hp' hdisc
  · exact contDiffAt_const.congr_of_eventuallyEq
      (returnCorrectionLocalCoefficientError_eventually_zero_of_radial_support
        D S C R χ z m ρ (hsupp m) p hp)

include hδ hcell hend hP₀

theorem N01Properties.returnCorrectionCoefficientError_uniform_fderiv_bound
    (hV : ∀ ρ : CircleSpace S, ∀ m, ContDiff ℝ ∞
      (fun p => returnCorrectionVelocityLinear D S C χ z m p ρ))
    (hVbound : ∀ ρ : CircleSpace S, ∀ k : ℕ, ∃ A P : ℝ,
      0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      ‖iteratedFDeriv ℝ k (fun q => returnCorrectionVelocityLinear D S C χ z m q ρ) p‖ ≤
        A * T.H (T.sample m) ^ (3 / 4 : ℝ) * radialE (D.cellIndex (j m)) ^ P)
    (ρ : CircleSpace S) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n
        (fun q => returnCorrectionCoefficientError D S C R χ z q ρ) p‖ ≤ K := by
  obtain ⟨A, P, hA, hP, hb⟩ :=
    hN.returnCorrectionLocalCoefficientError_mixed_weighted_bound hS hT R hz hsector
      j x δ hcell hinside χ hlam hP₀ (fun m p hp => hlower m p ⟨hp.1.le, hp.2.le⟩)
      hV hVbound ρ n
  obtain ⟨M, hM, hweight⟩ := hN.returnLabel_height_actualCell_radialE_envelope
    hS hT j hcell (γ := (3 / 4 : ℝ)) (by norm_num) hP
  have hlocal (m : ℕ) (p : PolarPoint) :
      ‖iteratedFDeriv ℝ n
        (fun q => returnCorrectionLocalCoefficientError D S C R χ z m q ρ) p‖ ≤ A * M := by
    by_cases hp : p.1 ∈ Icc (x m - δ m) (x m + δ m)
    · have hs := hN.returnCorrectionLocalCoefficientError_contDiff_of_collar
        hS hT R hz hsector j x δ hinside χ hχ hχrange hsupp hlam hlower ρ m
      have hclosed := norm_iteratedFDeriv_le_on_closed_radial_interval hs
        (show x m - δ m < x m + δ m by linarith [hδ m]) n (hb m) hp
      calc
        _ ≤ A * T.H (T.sample m) ^ (3 / 4 : ℝ) * radialE (D.cellIndex (j m)) ^ P :=
          hclosed
        _ = A * (T.H (T.sample m) ^ (3 / 4 : ℝ) * radialE (D.cellIndex (j m)) ^ P) := by ring
        _ ≤ A * M := mul_le_mul_of_nonneg_left (hweight m) hA
    · have heq := returnCorrectionLocalCoefficientError_eventually_zero_of_radial_support
        D S C R χ z m ρ (hsupp m) p hp
      rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg hA hM.le
  have hsupp' (m : ℕ) : Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m) := by
    intro r hr
    exact ⟨(hinside m).1.trans_le (hsupp m hr).1,
      (hsupp m hr).2.trans_lt (hinside m).2⟩
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  refine ⟨A * M, mul_nonneg hA hM.le, fun p hp => ?_⟩
  by_cases hex : ∃ m, p.1 ∈ Ioo (C.left m) (C.right m)
  · obtain ⟨m, hm⟩ := hex
    have heq : (fun q => returnCorrectionCoefficientError D S C R χ z q ρ) =ᶠ[𝓝 p]
        (fun q => returnCorrectionLocalCoefficientError D S C R χ z m q ρ) := by
      filter_upwards [returnCorrectionCoefficientError_eventually_local
        (D := D) hC.2.2.1 R χ z m p hm] with q hq
      exact congrArg (fun L : CircleSpace S →ₗ[ℝ] ℝ × ℝ => L ρ) hq
    rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
    exact hlocal m p
  · have hn : 0 ≤ deriv D.w p.1 := by
      by_contra h
      exact hex (hC.2.2.2.2.1 p.1 hp.1 (lt_of_not_ge h))
    have hzero : (fun q => returnCorrectionCoefficientError D S C R χ z q ρ) =ᶠ[𝓝 p]
        fun _ => (0 : ℝ × ℝ) := by
      filter_upwards [returnCorrectionCoefficientError_eventually_zero D S C R χ z p
        (hN.cutoffs_deriv_eventually_zero_of_nonnegative χ hsupp' hend hp.1 hn)] with q hq
      rw [hq, LinearMap.zero_apply]
    rw [(hzero.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg hA hM.le


/-- The velocity regularity and bounds are supplied by the actual N01
flow, its actual inverse, and this very same cutoff family. -/
theorem N01Properties.returnCorrectionCoefficientError_uniform_fderiv_bound_of_collar
    {B₀ : ℝ} (hB₀ : 0 < B₀)
    (hspeed : ∀ m r, r ∈ Icc (x m - δ m) (x m + δ m) →
      radialE (D.cellIndex (j m)) ^ (-B₀) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r)
    (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
    (hflow : ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow z m r) θ ∧ deriv (C.minusFlow z m r) θ ≤ 3 / 2)
    (hinverse : ∀ k : ℕ, 1 ≤ k → ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
      |iteratedDeriv k (C.minusReturnInverse z m) θ| ≤ A)
    (ρ : CircleSpace S) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n
        (fun q => returnCorrectionCoefficientError D S C R χ z q ρ) p‖ ≤ K := by
  have hdisc (m : ℕ) (p : PolarPoint)
      (hp : p.1 ∈ Icc (x m - δ m) (x m + δ m)) :
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p :=
    (mul_pos hlam (Real.rpow_pos_of_pos (Real.exp_pos _) _)).trans_le (hlower m p hp)
  exact hN.returnCorrectionCoefficientError_uniform_fderiv_bound
    hS hT R hz hsector j x δ hδ hcell hinside χ hχ hχrange hsupp hend
    hlam hP₀ hlower
    (fun u m => hN.returnCorrectionVelocityLinear_contDiff_of_collar
      hS hT hz hsector x δ hinside hdisc χ hχ hχrange hsupp u m)
    (fun u k => hN.returnCorrectionVelocityLinear_global_weighted_bound
      hS hT hz hsector j x δ hδ hB₀ hcell hinside hspeed hdisc χ hχ hχrange
        hsupp hcutoff hflow hinverse u k)
    ρ n

end ActualCoefficients

end ContinuousFlexibility.Statements
