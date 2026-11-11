import ContinuousFlexibility.Analysis.N08ControlSeries
import ContinuousFlexibility.Analysis.N08ControlProfileGain

/-!
# The actual logarithmic profile of a weak control vector

Every weak control vector defines the literal locally finite series with
amplitude `H_m^(3/4)`. Disjoint supports turn the coordinate norm bound into
uniform decay for every ordinary derivative of that same series.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n08WeakControlProfile (T : MaterialData) {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (b : ControlBanach) : ℝ → ℝ :=
  n08ControlSeries C (fun m => b m * T.H (T.sample m) ^ (3 / 4 : ℝ))

def n08WeakControlField (T : MaterialData) {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (b : ControlBanach) (p : PolarPoint) : ℝ :=
  n08WeakControlProfile T C b p.1

def n08WeakControlEvalCLM (T : MaterialData)
    (hC : controlGeometryConditions D S C) (r : ℝ) : ControlBanach →L[ℝ] ℝ :=
  ∑ m ∈ n08ActiveControls hC r,
    (T.H (T.sample m) ^ (3 / 4 : ℝ) * C.control m r) •
      lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 m

theorem n08WeakControlEvalCLM_apply (hC : controlGeometryConditions D S C)
    (b : ControlBanach) (r : ℝ) :
    n08WeakControlEvalCLM T hC r b = n08WeakControlProfile T C b r := by
  have heval (m : ℕ) : lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 m b = b m := rfl
  change (∑ m ∈ n08ActiveControls hC r,
    (T.H (T.sample m) ^ (3 / 4 : ℝ) * C.control m r) •
      lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 m) b =
    n08ControlSeries C (fun m => b m * T.H (T.sample m) ^ (3 / 4 : ℝ)) r
  rw [n08ControlSeries_eq_sum hC]
  simp only [sum_apply, smul_apply, heval, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m _
  ring

def n08WeakControlFieldCLM (T : MaterialData)
    (hC : controlGeometryConditions D S C) : ControlBanach →L[ℝ] (PolarPoint → ℝ) :=
  ContinuousLinearMap.pi (fun p => n08WeakControlEvalCLM T hC p.1)

theorem n08WeakControlFieldCLM_apply (hC : controlGeometryConditions D S C)
    (b : ControlBanach) (p : PolarPoint) :
    n08WeakControlFieldCLM T hC b p = n08WeakControlField T C b p :=
  n08WeakControlEvalCLM_apply hC b p.1

theorem n08WeakControlProfile_contDiffOn (hC : controlGeometryConditions D S C)
    (b : ControlBanach) :
    ContDiffOn ℝ ∞ (n08WeakControlProfile T C b) (Ioo D.a D.b) :=
  n08ControlSeries_contDiffOn hC _

theorem n08WeakControlField_contDiffOn (hC : controlGeometryConditions D S C)
    (b : ControlBanach) :
    ContDiffOn ℝ ∞ (n08WeakControlField T C b) (annularOpen D) :=
  (n08WeakControlProfile_contDiffOn hC b).comp contDiff_fst.contDiffOn (fun _ hp => hp.1)

theorem n08WeakControlField_zero_off_core (hC : controlGeometryConditions D S C)
    (b : ControlBanach) (p : PolarPoint) (hp : p ∉ annularOpen D) :
    n08WeakControlField T C b p = 0 := by
  apply n08ControlSeries_zero_off_core hC
  exact fun hr => hp ⟨hr, mem_univ _⟩

/-- The weak extension agrees with the original state control sum on every
physical circle input, including nonconstant control directions. -/
theorem n08WeakControlProfile_restriction
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    n08WeakControlProfile T C (n08ControlRestriction S x.2.2.1) = stateControlSum C x := by
  funext r
  apply tsum_congr
  intro m
  rw [n08ControlRestriction_apply hS]
  have hH := (n08_material_sample_bounds hD hT m).1
  change ((T.H (T.sample m) ^ (-(3 / 4 : ℝ)) * stateKappa S x m) *
      T.H (T.sample m) ^ (3 / 4 : ℝ)) * C.control m r = stateKappa S x m * C.control m r
  calc
    _ = (T.H (T.sample m) ^ (-(3 / 4 : ℝ)) * T.H (T.sample m) ^ (3 / 4 : ℝ)) *
        (stateKappa S x m * C.control m r) := by ring
    _ = _ := by rw [← Real.rpow_add hH, neg_add_cancel, Real.rpow_zero, one_mul]

/-- The constant is selected before the weak vector and the physical point.
The entire Banach norm is charged once, at every ordinary derivative order. -/
theorem n08WeakControlProfile_jet_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ControlBanach, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (n08WeakControlProfile T C b) r| ≤
        K * ‖b‖ * T.H r ^ (3 / 128 : ℝ) * T.M r := by
  obtain ⟨K, hK, hKb⟩ := n08_weightedControlProfile_decay_jet_bound hT hS hN s
  refine ⟨K, hK, fun b r hr => ?_⟩
  have hH : 0 ≤ T.H r ^ (3 / 128 : ℝ) := Real.rpow_nonneg (hT.2.1 r hr).2.1.le _
  have hM : 0 ≤ T.M r := zero_le_one.trans (hT.2.1 r hr).2.2.2
  apply n08ControlSeries_jet_bound hN.2.2.2.1 _ s hr
    (mul_nonneg (mul_nonneg (mul_nonneg hK (norm_nonneg _)) hH) hM)
  intro m _
  have hm : |b m| ≤ ‖b‖ := by
    simpa only [Real.norm_eq_abs] using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) b m
  have heq : (b m * T.H (T.sample m) ^ (3 / 4 : ℝ)) * iteratedDeriv s (C.control m) r =
      b m * iteratedDeriv s (n08WeightedControlProfile T C m) r := by
    change _ = b m * iteratedDeriv s (fun t => T.H (T.sample m) ^ (3 / 4 : ℝ) * C.control m t) r
    rw [iteratedDeriv_const_mul_field]
    ring
  rw [heq, abs_mul]
  exact (mul_le_mul hm (hKb m r hr) (abs_nonneg _) (norm_nonneg _)).trans_eq (by ring)

end ContinuousFlexibility.Statements
