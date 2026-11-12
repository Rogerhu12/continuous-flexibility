import ContinuousFlexibility.Analysis.ReturnResidualVelocityMixedWeighted
import ContinuousFlexibility.Analysis.ReturnCorrectionErrorSmoothness
import Mathlib.Topology.Order.OrderClosed

/-!
# Global weighted velocity jets from the same optical collars

The independent correction velocity vanishes wherever the derivative of
the actual cutoff vanishes. Smoothness on the closed positive
discriminant collar and this support identity extend its open-collar
jet bounds to every point, including the collar boundary.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

theorem returnCorrectionVelocityLinear_eventually_zero_of_radial_support
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (ρ : CircleSpace S)
    {l h : ℝ} (hsupp : Function.support (deriv (χ m)) ⊆ Icc l h)
    (p : PolarPoint) (hp : p.1 ∉ Icc l h) :
    (fun q => returnCorrectionVelocityLinear D S C χ z m q ρ) =ᶠ[𝓝 p]
      fun _ => (0 : ℝ) := by
  have hnear : ∀ᶠ r in 𝓝 p.1, r ∉ Icc l h :=
    isClosed_Icc.isOpen_compl.mem_nhds hp
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hnear] with q hq
  have hd : deriv (χ m) q.1 = 0 := by
    by_contra hne
    exact hq (hsupp hne)
  rw [returnCorrectionVelocityLinear_apply, hd, mul_zero, zero_mul]

section ActualVelocity

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)
  (j : ℕ → ℕ) (x δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m)
  {B₀ : ℝ} (hB₀ : 0 < B₀)
  (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
  (hinside : ∀ m, C.left m < x m - δ m ∧ x m + δ m < C.right m)
  (hspeed : ∀ m r, r ∈ Icc (x m - δ m) (x m + δ m) →
    radialE (D.cellIndex (j m)) ^ (-B₀) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r)
  (hdisc : ∀ m : ℕ, ∀ p : PolarPoint, p.1 ∈ Icc (x m - δ m) (x m + δ m) →
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, χ m r ∈ Icc (0 : ℝ) 1)
  (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Icc (x m - δ m) (x m + δ m))
  (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
    |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
  (hflow : ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
    1 / 2 ≤ deriv (C.minusFlow z m r) θ ∧ deriv (C.minusFlow z m r) θ ≤ 3 / 2)
  (hinverse : ∀ k : ℕ, 1 ≤ k → ∃ A : ℝ, 0 ≤ A ∧ ∀ m θ,
    |iteratedDeriv k (C.minusReturnInverse z m) θ| ≤ A)

include hN hS hT hz hsector hinside hdisc hχ hχrange hsupp

theorem N01Properties.returnCorrectionVelocityLinear_contDiff_of_collar
    (ρ : CircleSpace S) (m : ℕ) :
    ContDiff ℝ ∞ (fun p => returnCorrectionVelocityLinear D S C χ z m p ρ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.1 ∈ Icc (x m - δ m) (x m + δ m)
  · have hp' : p.1 ∈ Ioo (C.left m) (C.right m) :=
      ⟨(hinside m).1.trans_le hp.1, hp.2.trans_lt (hinside m).2⟩
    exact hN.returnCorrectionVelocityLinear_contDiffAt hS hT hz hsector χ m
      (hχ m) (fun r _ => hχrange m r) ρ p hp' (hdisc m p hp)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (returnCorrectionVelocityLinear_eventually_zero_of_radial_support
        D S C χ z m ρ (hsupp m) p hp)

include hδ hB₀ hcell hspeed hcutoff hflow hinverse

theorem N01Properties.returnCorrectionVelocityLinear_closed_collar_weighted_bound
    (ρ : CircleSpace S) (n : ℕ) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      p.1 ∈ Icc (x m - δ m) (x m + δ m) →
      ‖iteratedFDeriv ℝ n
        (fun q => returnCorrectionVelocityLinear D S C χ z m q ρ) p‖ ≤
        A * T.H (T.sample m) ^ (3 / 4 : ℝ) * radialE (D.cellIndex (j m)) ^ P := by
  obtain ⟨A, P, hA, hP, hb⟩ :=
    hN.returnCorrectionVelocityLinear_mixed_weighted_bound
      hS hT hz hsector j x δ hB₀ hcell hinside hspeed
      (fun m p hp => hdisc m p ⟨hp.1.le, hp.2.le⟩)
      χ hχ hχrange hcutoff hflow hinverse ρ n
  refine ⟨A, P, hA, hP, fun m p hp => ?_⟩
  have hv := hN.returnCorrectionVelocityLinear_contDiff_of_collar
    hS hT hz hsector x δ hinside hdisc χ hχ hχrange hsupp ρ m
  have hc : Continuous (fun r : ℝ => ‖iteratedFDeriv ℝ n
      (fun q => returnCorrectionVelocityLinear D S C χ z m q ρ) (r, p.2)‖) :=
    (hv.continuous_iteratedFDeriv (by simp)).norm.comp
      (continuous_id.prodMk continuous_const)
  have hclosure : closure (Ioo (x m - δ m) (x m + δ m)) =
      Icc (x m - δ m) (x m + δ m) :=
    closure_Ioo (show x m - δ m ≠ x m + δ m by linarith [hδ m])
  exact le_on_closure (fun r hr => hb m (r, p.2) hr)
    hc.continuousOn continuousOn_const (by simpa only [hclosure] using hp)

theorem N01Properties.returnCorrectionVelocityLinear_global_weighted_bound
    (ρ : CircleSpace S) (n : ℕ) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      ‖iteratedFDeriv ℝ n
        (fun q => returnCorrectionVelocityLinear D S C χ z m q ρ) p‖ ≤
        A * T.H (T.sample m) ^ (3 / 4 : ℝ) * radialE (D.cellIndex (j m)) ^ P := by
  obtain ⟨A, P, hA, hP, hb⟩ :=
    hN.returnCorrectionVelocityLinear_closed_collar_weighted_bound
      hS hT hz hsector j x δ hδ hB₀ hcell hinside hspeed hdisc
      χ hχ hχrange hsupp hcutoff hflow hinverse ρ n
  refine ⟨A, P, hA, hP, fun m p => ?_⟩
  by_cases hp : p.1 ∈ Icc (x m - δ m) (x m + δ m)
  · exact hb m p hp
  · have heq := returnCorrectionVelocityLinear_eventually_zero_of_radial_support
      D S C χ z m ρ (hsupp m) p hp
    rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    exact mul_nonneg
      (mul_nonneg hA (Real.rpow_nonneg
        ((material_circle_sample_weights_pos hT hN.1.1).2 m).le _))
      (Real.rpow_nonneg (zero_le_one.trans (one_le_radialE_of_nat _)) _)

end ActualVelocity

end ContinuousFlexibility.Statements
