import ContinuousFlexibility.Analysis.N01NormalizationRootSeparation
import ContinuousFlexibility.Analysis.CircleJetClosedGraph
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# One actual profile collar for every state at a fixed root

The exact circle model realizes a single angular-constant component.
Its small state excitation and the N01 profile germ force the corresponding
control to vanish near the root. Local finiteness then makes all controls
vanish on one neighborhood, independently of the state. The radius may
depend on the root; no uniform radius over components is asserted.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

def circleSingleConstant (m : ℕ) (c : ℝ) : ℕ → ℝ → ℝ :=
  fun n _ => if n = m then c else 0

/-- Finite component support satisfies the actual weighted circle contract. -/
theorem circleMember_singleConstant (T : MaterialData) (γ : ℝ) (m : ℕ) (c : ℝ) :
    CircleMember T γ (circleSingleConstant m c) := by
  classical
  have hs (n : ℕ) : ContDiff ℝ ∞ (circleSingleConstant m c n) := contDiff_const
  have hm (n b : ℕ) : MemLp (iteratedDeriv b (circleSingleConstant m c n)) 2 angleMeasure :=
    memLp_angleMeasure_iteratedDeriv_of_contDiff (hs n) b
  refine ⟨fun n => ⟨hs n, fun _ => rfl⟩, hm, ?_⟩
  intro s
  rw [tsum_eq_single m]
  · exact ENNReal.sum_lt_top.mpr fun j _ =>
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.pow_lt_top (hm m (j.val 0).val).eLpNorm_lt_top)
  · intro n hn
    have hf : circleSingleConstant m c n = fun _ : ℝ => 0 := by
      funext θ
      exact if_neg hn
    simp only [hf, iteratedDeriv_const_zero, eLpNorm_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]

private theorem angularMean_single_constant (a : ℝ) :
    angularMean (fun _ : ℝ => a) = a := by
  rw [angularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_div]
  exact inv_mul_cancel_left₀ Real.pi_ne_zero a

/-- Actual finite circle excitation makes each fixed control vanish on a
neighborhood of every interior critical root. -/
theorem n01_control_eventuallyEq_zero_at_critical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) (hcritical : deriv D.w r = 0) (m : ℕ) :
    C.control m =ᶠ[𝓝 r] fun _ => 0 := by
  classical
  obtain ⟨u, hu⟩ := (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.1
    (circleSingleConstant m 1) (circleMember_singleConstant T (3 / 4 : ℝ) m 1)
  have href : referenceStateConditions D S C := hN.2.2.1
  have hε : 0 < ε := hN.2.1
  let v : AnnularState S := (0, (0, (u, 0)))
  let t : ℝ := (ε / 2) / (stateGrading S base v + 1)
  have hv : 0 ≤ stateGrading S base v := apply_nonneg _ _
  have ht : 0 < t := div_pos (half_pos hε) (by linarith)
  have hmul : t * (stateGrading S base v + 1) = ε / 2 :=
    div_mul_cancel₀ _ (by linarith)
  have hsmall : stateGrading S base (t • v) < ε := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith only [hmul, ht, hε]
  have hz : (C.referenceState + t • v, (0 : ℝ)) ∈
      stateNeighborhood S C base ε := by
    change stateGrading S base ((C.referenceState + t • v) - C.referenceState) < ε ∧
      |(0 : ℝ)| < ε
    simpa only [add_sub_cancel_left, abs_zero] using And.intro hsmall hε
  have hk (n : ℕ) : stateKappa S (C.referenceState + t • v) n =
      if n = m then t else 0 := by
    change angularMean ((S.circle (3 / 4 : ℝ)).decode
      (C.referenceState.2.2.1 + t • u) n) = _
    rw [href.2.2.2.1, zero_add, map_smul, hu]
    simp only [Pi.smul_apply, smul_eq_mul, circleSingleConstant]
    by_cases hn : n = m
    · simp only [ite_eq_left hn, mul_one, angularMean_single_constant]
    · simp only [ite_eq_right hn, mul_zero, angularMean_single_constant]
  have hprofile : stateProfile D S C (C.referenceState + t • v) =
      fun s => D.w s * Real.exp (t * C.control m s) := by
    funext s
    change D.w s * Real.exp ((C.referenceState.2.1 + t * 0) * D.chi s +
      ∑' n, stateKappa S (C.referenceState + t • v) n * C.control n s) = _
    rw [href.2.2.1]
    simp only [mul_zero, zero_add]
    rw [tsum_eq_single m]
    · rw [hk, ite_eq_left rfl]
    · intro n hn
      simp only [hk, ite_eq_right hn, zero_mul]
  have he : stateProfile D S C (C.referenceState + t • v) =ᶠ[𝓝 r] D.w :=
    hN.2.2.2.2.2.2.2.2.2.2.1 (C.referenceState + t • v, 0) hz r hr hcritical
  rw [hprofile] at he
  obtain ⟨_, hD⟩ := hN.1.1
  filter_upwards [he, isOpen_Ioo.mem_nhds hr] with s hs hsi
  have hwpos : 0 < D.w s := hD.1.2.2.2.2.1 s hsi
  have hexp : Real.exp (t * C.control m s) = 1 :=
    mul_left_cancel₀ hwpos.ne' (hs.trans (mul_one (D.w s)).symm)
  have hzero : t * C.control m s = 0 := Real.exp_injective (hexp.trans Real.exp_zero.symm)
  exact (mul_eq_zero.mp hzero).resolve_left ht.ne'

/-- The same neighborhood works for every state, including states outside
the original small neighborhood: all fixed perturbing functions vanish there. -/
theorem n01_stateProfiles_eventuallyEq_reference_at_critical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) (hcritical : deriv D.w r = 0) :
    ∀ᶠ y in 𝓝 r, ∀ x : AnnularState S, stateProfile D S C x y = D.w y := by
  classical
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  obtain ⟨U, hU, hfinite⟩ := hC.2.2.2.2.2.2.1 ⟨r, hr⟩
  let J : Set ℕ := {m | ({q : Ioo D.a D.b |
    (q : ℝ) ∈ Function.support (C.control m)} ∩ U).Nonempty}
  have hJ : J.Finite := hfinite
  have hzeros : ∀ᶠ y in 𝓝 r, ∀ m ∈ J, C.control m y = 0 :=
    (eventually_all_finite hJ).mpr fun m _ =>
      n01_control_eventuallyEq_zero_at_critical hS hN hr hcritical m
  have hmem : (Subtype.val : Ioo D.a D.b → ℝ) '' U ∈ 𝓝 r :=
    isOpen_Ioo.isOpenMap_subtype_val.image_mem_nhds hU
  filter_upwards [hmem, hzeros,
    n01_chi_eventuallyEq_zero_at_critical hN hr hcritical] with y hy hz hχ
  rcases hy with ⟨q, hq, rfl⟩
  have hall (m : ℕ) : C.control m q = 0 := by
    by_cases hm : m ∈ J
    · exact hz m hm
    · by_contra hc
      exact hm ⟨q, hc, hq⟩
  intro x
  simp only [stateProfile, hall, hχ, mul_zero, tsum_zero, add_zero, Real.exp_zero, mul_one]

/-- A positive collar radius can be fixed before choosing the state. -/
theorem n01_exists_common_profile_root_collar
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) (hcritical : deriv D.w r = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y, |y - r| < δ →
      ∀ x : AnnularState S, stateProfile D S C x y = D.w y := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (n01_stateProfiles_eventuallyEq_reference_at_critical hS hN hr hcritical)
  refine ⟨δ, hδ, fun y hy => hball ?_⟩
  simpa only [Metric.mem_ball, Real.dist_eq] using hy

end ContinuousFlexibility.Analysis
