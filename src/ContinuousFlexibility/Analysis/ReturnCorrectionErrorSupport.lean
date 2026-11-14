module

public import ContinuousFlexibility.Analysis.ReturnCorrectionResidualPeriodicity

/-!
# Support of the actual independent-residual error

The independent-residual coefficient map vanishes wherever the actual
cutoff derivative vanishes. On every negative component, the global
selector therefore equals the local formula even at inactive points.
At positive radii and simple turning points, all component corrections
vanish on a common neighborhood. The actual differential error is thus
supported in the union of the original negative components.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem returnCorrectionVelocityLinear_eq_zero_of_deriv_zero
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint)
    (hχ : deriv (χ m) p.1 = 0) :
    returnCorrectionVelocityLinear D S C χ z m p = 0 := by
  simp only [returnCorrectionVelocityLinear, hχ, mul_zero, zero_smul]

theorem returnCorrectionDriftSpeedLinear_eq_zero_of_deriv_zero
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint)
    (hχ : deriv (χ m) p.1 = 0) :
    returnCorrectionDriftLinear D S C χ z m p = 0 ∧
      returnCorrectionSpeedLinear D S C χ z m p = 0 := by
  have hv := returnCorrectionVelocityLinear_eq_zero_of_deriv_zero D S C χ z m p hχ
  have hr := returnCorrectionVelocityLinear_eq_zero_of_deriv_zero D S C χ z m
    (p.1, -p.2) hχ
  simp only [returnCorrectionDriftLinear, returnCorrectionSpeedLinear, hv, hr,
    sub_self, add_zero, smul_zero, and_self]

theorem returnCorrectionLocalCoefficientError_eq_zero_of_deriv_zero
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (m : ℕ) (p : PolarPoint) (hχ : deriv (χ m) p.1 = 0) :
    returnCorrectionLocalCoefficientError D S C R χ z m p = 0 := by
  have hs := returnCorrectionDriftSpeedLinear_eq_zero_of_deriv_zero D S C χ z m p hχ
  apply LinearMap.ext
  intro ρ
  simp only [returnCorrectionLocalCoefficientError, returnCoefficientError_apply,
    hs.1, hs.2, LinearMap.zero_apply, mul_zero, zero_add, Prod.mk_zero_zero]

theorem returnCorrectionCoefficientError_eq_local
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hdisj : ∀ m n, m ≠ n → Disjoint (Ioo (C.left m) (C.right m))
      (Ioo (C.left n) (C.right n)))
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    returnCorrectionCoefficientError D S C R χ z p =
      returnCorrectionLocalCoefficientError D S C R χ z m p := by
  classical
  by_cases hχ : deriv (χ m) p.1 = 0
  · have hn : ¬ ∃ n, p.1 ∈ Ioo (C.left n) (C.right n) ∧ deriv (χ n) p.1 ≠ 0 := by
      rintro ⟨n, hnp, hnd⟩
      by_cases hnm : n = m
      · subst n
        exact hnd hχ
      · exact Set.disjoint_left.mp (hdisj n m hnm) hnp hp
    rw [returnCorrectionLocalCoefficientError_eq_zero_of_deriv_zero D S C R χ z m p hχ]
    simp only [returnCorrectionCoefficientError, dif_neg hn]
  · have hex : ∃ n, p.1 ∈ Ioo (C.left n) (C.right n) ∧ deriv (χ n) p.1 ≠ 0 :=
      ⟨m, hp, hχ⟩
    have hm : Classical.choose hex = m := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj _ _ hne) (Classical.choose_spec hex).1 hp
    simp only [returnCorrectionCoefficientError, dif_pos hex, hm]

theorem returnCorrectionCoefficientError_eventually_local
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hdisj : ∀ m n, m ≠ n → Disjoint (Ioo (C.left m) (C.right m))
      (Ioo (C.left n) (C.right n)))
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    (fun q => returnCorrectionCoefficientError D S C R χ z q) =ᶠ[𝓝 p]
      (fun q => returnCorrectionLocalCoefficientError D S C R χ z m q) := by
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (Ioo_mem_nhds hp.1 hp.2)]
    with q hq
  exact returnCorrectionCoefficientError_eq_local hdisj R χ z m q hq

theorem returnCorrectionCoefficientError_eventually_zero
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (p : PolarPoint) (hχ : ∀ᶠ r in 𝓝 p.1, ∀ m, deriv (χ m) r = 0) :
    (fun q => returnCorrectionCoefficientError D S C R χ z q) =ᶠ[𝓝 p] fun _ => 0 := by
  classical
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hχ] with q hq
  have hn : ¬ ∃ m, q.1 ∈ Ioo (C.left m) (C.right m) ∧ deriv (χ m) q.1 ≠ 0 := by
    rintro ⟨m, _, hm⟩
    exact hm (hq m)
  simp only [returnCorrectionCoefficientError, dif_neg hn]

theorem N01Properties.returnCorrectionCutoffs_deriv_eventually_zero_of_nonnegative
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε) {r : ℝ}
    (hr : r ∈ Ioo D.a D.b) (hw' : 0 ≤ deriv D.w r) :
    ∀ᶠ s in 𝓝 r, ∀ m, deriv (returnCorrectionCutoffs C m) s = 0 := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  obtain ⟨bounds, hbounds⟩ := hN01.1.1
  rcases hw'.eq_or_lt with hzero | hpos
  · have hroot : deriv D.w r = 0 := hzero.symm
    have hsimple : deriv (deriv D.w) r ≠ 0 :=
      hbounds.1.2.2.2.2.2.2 r hr hroot
    have hne : ∀ᶠ s in 𝓝[≠] r, deriv D.w s ≠ 0 :=
      (differentiableAt_of_deriv_ne_zero hsimple).hasDerivAt.eventually_ne hsimple
    have hiso : ∀ᶠ s in 𝓝 r, deriv D.w s = 0 → s = r := by
      filter_upwards [eventually_nhdsWithin_iff.mp hne] with s hs
      intro hs0
      by_contra hsr
      exact hs hsr hs0
    exact returnCorrectionCutoff_deriv_eventually_zero_at_isolated_root
      C.left C.right (deriv D.w) r (fun m => (hC.1 m).2.1)
      (fun m => ⟨(hC.2.1 m).1, (hC.2.1 m).2.1⟩) hC.2.2.2.1 hroot hiso
  · have hw : ContDiff ℝ ∞ D.w := hbounds.1.2.2.1.1
    have hc : ContinuousAt (deriv D.w) r := (hw.continuous_deriv (by simp)).continuousAt
    filter_upwards [hc.preimage_mem_nhds (Ioi_mem_nhds hpos)] with s hs
    intro m
    by_contra hne
    have hm := returnCorrectionCutoff_deriv_support_subset_component (hC.1 m).2.1 hne
    exact (not_lt_of_ge hs.le) (hC.2.2.2.1 m s hm)

theorem N01Properties.returnCorrectionCoefficientError_eventually_zero_of_nonnegative
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (R : ReturnEquationData S) (z : AnnularState S × ℝ) (p : PolarPoint)
    (hp : p ∈ annularOpen D) (hw' : 0 ≤ deriv D.w p.1) :
    (fun q => returnCorrectionCoefficientError D S C R (returnCorrectionCutoffs C) z q)
      =ᶠ[𝓝 p] fun _ => 0 :=
  returnCorrectionCoefficientError_eventually_zero D S C R (returnCorrectionCutoffs C) z p
    (hN01.returnCorrectionCutoffs_deriv_eventually_zero_of_nonnegative hp.1 hw')

theorem returnCorrectionResidualErrorField_eq_zero_of_eventually_zero
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (ρ : CircleSpace S) (η : HeightPair S) (p : PolarPoint)
    (hzero : (fun q => returnCorrectionCoefficientError D S C R χ z q)
      =ᶠ[𝓝 p] fun _ => 0) :
    returnCorrectionResidualErrorField D S C R χ z ρ η p = 0 := by
  classical
  have hF : returnCorrectionRadialErrorFlux D S C R χ z ρ η =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [hzero] with q hq
    simp only [returnCorrectionRadialErrorFlux, hq, LinearMap.zero_apply,
      Prod.fst_zero, zero_mul]
  have hG : returnCorrectionAngularErrorFlux D S C R χ z ρ η =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [hzero] with q hq
    simp only [returnCorrectionAngularErrorFlux, hq, LinearMap.zero_apply,
      Prod.fst_zero, Prod.snd_zero, zero_mul, zero_add]
  have hr : radialPartial (returnCorrectionRadialErrorFlux D S C R χ z ρ η) p = 0 := by
    change (fderiv ℝ (returnCorrectionRadialErrorFlux D S C R χ z ρ η) p) (1, 0) = 0
    simpa only [fderiv_const_apply, ContinuousLinearMap.zero_apply] using
      congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) (hF.fderiv_eq (𝕜 := ℝ))
  have ht : angularPartial (returnCorrectionAngularErrorFlux D S C R χ z ρ η) p = 0 := by
    change (fderiv ℝ (returnCorrectionAngularErrorFlux D S C R χ z ρ η) p) (0, 1) = 0
    simpa only [fderiv_const_apply, ContinuousLinearMap.zero_apply] using
      congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) (hG.fderiv_eq (𝕜 := ℝ))
  by_cases hp : p ∈ annularOpen D
  · change (if p ∈ annularOpen D then
      radialPartial (returnCorrectionRadialErrorFlux D S C R χ z ρ η) p +
      angularPartial (returnCorrectionAngularErrorFlux D S C R χ z ρ η) p else 0) = 0
    rw [if_pos hp, hr, ht, zero_add]
  · exact returnCorrectionResidualErrorField_zero_outside D S C R χ z ρ η p hp

theorem N01Properties.returnCorrectionResidualErrorField_eq_zero_of_outside_components
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (R : ReturnEquationData S) (z : AnnularState S × ℝ)
    (ρ : CircleSpace S) (η : HeightPair S) (p : PolarPoint)
    (hp : p ∈ annularOpen D)
    (hout : ¬ ∃ m, p.1 ∈ Ioo (C.left m) (C.right m)) :
    returnCorrectionResidualErrorField D S C R (returnCorrectionCutoffs C) z ρ η p = 0 := by
  have hn : 0 ≤ deriv D.w p.1 := by
    by_contra h
    exact hout (hN01.2.2.2.1.2.2.2.2.1 p.1 hp.1 (lt_of_not_ge h))
  exact returnCorrectionResidualErrorField_eq_zero_of_eventually_zero
    D S C R (returnCorrectionCutoffs C) z ρ η p
    (hN01.returnCorrectionCoefficientError_eventually_zero_of_nonnegative R z p hp hn)

end ContinuousFlexibility.Statements
