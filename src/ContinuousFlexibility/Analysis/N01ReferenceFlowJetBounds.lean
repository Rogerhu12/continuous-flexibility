import ContinuousFlexibility.Analysis.N01OpticalSpeedJetBounds
import ContinuousFlexibility.Analysis.N01OpticalCollarPositivity
import ContinuousFlexibility.Analysis.N01FlowSmallness
import ContinuousFlexibility.Analysis.MixedDerivativeLocality

/-!
# Positive-order mixed jets of the actual reference flow

The angular part of the actual radial reference flow is a translation.
Its first radial derivative is minus the reference optical speed by the
original ODE. The quantitative optical-collar estimates therefore bound
every positive-order mixed jet by a fixed component power.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem N01Properties.minusFlow_reference_radial_hasDerivAt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (m : ℕ) (θ : ℝ) {r : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m)) :
    HasDerivAt (fun s => C.minusFlow (C.referenceState, 0) m s θ)
      (-opticalSpeed D.w r) r := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hg : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hmem : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
    constructor
    · change stateGrading S base (C.referenceState - C.referenceState) < ε
      rw [sub_self, (stateGrading S base).map_zero']
      exact hN.2.1
    · simpa only [abs_zero] using hN.2.1
  have hcore : r ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  have hODE := (hN.2.2.2.2.2.2.1 (C.referenceState, 0) hmem m θ).2.2.1 r hr
  obtain ⟨ha, hb, hc⟩ := hN.reference_coefficients
    (r, C.minusFlow (C.referenceState, 0) m r θ)
  have hspeed := minusCharacteristicSpeed_of_radial_coefficients ha hb hc
    (hg.1.trans hcore.1).ne' (hg.2.2.2.2.1 r hcore)
  rw [hspeed] at hODE
  exact hODE

theorem N01Properties.reference_minusFlow_collar_mixed_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (x δ : ℕ → ℝ) {B : ℝ} (hB : 0 < B)
    (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (hinside : ∀ m, C.left m < x m - δ m ∧ x m + δ m < C.right m)
    (hspeed : ∀ m r, r ∈ Icc (x m - δ m) (x m + δ m) →
      radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r)
    (a b : ℕ) (hab : 1 ≤ a + b) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m p,
      p.1 ∈ Ioo (x m - δ m) (x m + δ m) →
      |mixedDerivative a b (fun q : PolarPoint =>
        C.minusFlow (C.referenceState, 0) m q.1 q.2) p| ≤
        A * radialE (D.cellIndex (j m)) ^ P := by
  have hcomponent (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (x m - δ m) (x m + δ m)) :
      r ∈ Ioo (C.left m) (C.right m) :=
    ⟨(hinside m).1.trans hr.1, hr.2.trans (hinside m).2⟩
  by_cases hb : b = 0
  · subst b
    have ha : 1 ≤ a := by omega
    obtain ⟨A, P, hA, hP, hb⟩ :=
      hN.reference_opticalSpeed_collar_jets j x δ hB hcell hinside hspeed (a - 1)
    refine ⟨A, P, hA, hP, fun m p hp => ?_⟩
    have hcomp := hcomponent m p.1 hp
    have hder : deriv (fun r => C.minusFlow (C.referenceState, 0) m r p.2) =ᶠ[𝓝 p.1]
        (fun r => -opticalSpeed D.w r) := by
      filter_upwards [Ioo_mem_nhds hcomp.1 hcomp.2] with r hr
      exact (hN.minusFlow_reference_radial_hasDerivAt m p.2 hr).deriv
    simp only [mixedDerivative, iteratedDeriv_zero]
    have ha' : a = a - 1 + 1 := (Nat.sub_add_cancel ha).symm
    rw [ha', iteratedDeriv_succ', hder.iteratedDeriv_eq (a - 1),
      iteratedDeriv_fun_neg, abs_neg]
    exact hb m p.1 hp
  · refine ⟨1, 0, zero_le_one, le_rfl, fun m p hp => ?_⟩
    have hcomp := hcomponent m p.1 hp
    have heq : (fun q : PolarPoint => C.minusFlow (C.referenceState, 0) m q.1 q.2)
        =ᶠ[𝓝 p] (fun q => q.2 - opticalTravel D.w (C.left m) q.1) := by
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
        (Ioo_mem_nhds hcomp.1 hcomp.2)] with q hq
      exact hN.minusFlow_reference_eq hS hT m ⟨hq.1.le, hq.2.le⟩ q.2
    rw [mixedDerivative_congr_of_eventuallyEq heq a b, Real.rpow_zero, mul_one]
    exact mixedDerivative_angular_translation_abs_le
      (opticalTravel D.w (C.left m)) a b (by omega) p

end ContinuousFlexibility.Statements
