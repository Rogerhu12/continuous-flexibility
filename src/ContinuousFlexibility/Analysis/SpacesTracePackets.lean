import ContinuousFlexibility.Analysis.SpacesTraceGeometry
import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Smooth packets for a right inverse of the sample trace

One fixed smooth bump is translated and scaled to each material window.
The locally finite packet sum is an actual smooth function, has the
prescribed values at every sample, and differentiates term by term. The
algebraic map and all these identities precede the norm estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

def spacesTraceBaseBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def spacesTraceBump (center radius : ℝ) (x : ℝ) : ℝ :=
  spacesTraceBaseBump ((x - center) / radius)

theorem spacesTraceBump_contDiff (center radius : ℝ) :
    ContDiff ℝ ∞ (spacesTraceBump center radius) :=
  spacesTraceBaseBump.contDiff.comp ((contDiff_id.sub contDiff_const).div_const radius)

@[simp] theorem spacesTraceBump_center (center radius : ℝ) :
    spacesTraceBump center radius center = 1 := by
  apply spacesTraceBaseBump.one_of_mem_closedBall
  simp [spacesTraceBaseBump]

theorem spacesTraceBump_support {center radius : ℝ} (hradius : 0 < radius) :
    Function.support (spacesTraceBump center radius) ⊆ Ioo (center - radius) (center + radius) := by
  intro x hx
  have hb : (x - center) / radius ∈ Function.support spacesTraceBaseBump := hx
  rw [spacesTraceBaseBump.support_eq] at hb
  change (x - center) / radius ∈ Metric.ball (0 : ℝ) 1 at hb
  have hab : |x - center| < radius := by
    have h : |(x - center) / radius| < 1 := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hb
    rw [abs_div, abs_of_pos hradius, div_lt_one hradius] at h
    exact h
  exact ⟨by linarith [(abs_lt.mp hab).1], by linarith [(abs_lt.mp hab).2]⟩

theorem spacesTraceBump_zero {center radius x : ℝ} (hradius : 0 < radius)
    (hx : x ∉ Ioo (center - radius) (center + radius)) : spacesTraceBump center radius x = 0 := by
  by_contra h
  exact hx (spacesTraceBump_support hradius h)

theorem spacesTraceBump_iteratedDeriv (n : ℕ) (center radius x : ℝ) :
    iteratedDeriv n (spacesTraceBump center radius) x =
      radius⁻¹ ^ n * iteratedDeriv n spacesTraceBaseBump ((x - center) / radius) := by
  have he : spacesTraceBump center radius =
      fun t => (fun y => spacesTraceBaseBump (radius⁻¹ * y)) (t - center) := by
    funext t
    simp only [spacesTraceBump, div_eq_mul_inv, mul_comm]
  rw [he, congrFun (iteratedDeriv_comp_sub_const n
    (fun y : ℝ => spacesTraceBaseBump (radius⁻¹ * y)) center) x,
    iteratedDeriv_comp_const_mul (n := n) spacesTraceBaseBump.contDiff]
  simp only [div_eq_mul_inv, mul_comm]

private theorem spaces_iteratedDeriv_tsupport (f : ℝ → ℝ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, subset_refl]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem spacesTraceBump_iteratedDeriv_zero {center radius x : ℝ} (hradius : 0 < radius)
    (n : ℕ) (hx : x ∉ Icc (center - radius) (center + radius)) :
    iteratedDeriv n (spacesTraceBump center radius) x = 0 := by
  have hs : tsupport (spacesTraceBump center radius) ⊆ Icc (center - radius) (center + radius) :=
    closure_minimal ((spacesTraceBump_support hradius).trans Ioo_subset_Icc_self) isClosed_Icc
  by_contra hn
  exact hx (hs (spaces_iteratedDeriv_tsupport _ n (subset_closure hn)))

/-- Each derivative of the fixed bump has one bound. Scaling introduces
exactly the corresponding inverse power of the window radius. -/
theorem spacesTraceBump_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ center radius : ℝ, 0 < radius → ∀ x,
      |iteratedDeriv n (spacesTraceBump center radius) x| ≤ C * radius⁻¹ ^ n := by
  have hc : Continuous (iteratedDeriv n spacesTraceBaseBump) :=
    (spacesTraceBaseBump.contDiff : ContDiff ℝ ∞ spacesTraceBaseBump).continuous_iteratedDeriv n (by simp)
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    (hc.abs.continuousOn (s := Icc (-1 : ℝ) 1))
  have hbase (x : ℝ) : |iteratedDeriv n spacesTraceBaseBump x| ≤ max B 0 := by
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · exact (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · have hn : iteratedDeriv n spacesTraceBaseBump x = 0 := by
        by_contra hne
        have ht := spaces_iteratedDeriv_tsupport spacesTraceBaseBump n (subset_closure hne)
        rw [spacesTraceBaseBump.tsupport_eq] at ht
        have hab : |x| ≤ 1 := by
          simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, spacesTraceBaseBump] using ht
        exact hx ⟨(abs_le.mp hab).1, (abs_le.mp hab).2⟩
      rw [hn, abs_zero]
      exact le_max_right _ _
  refine ⟨max B 0, le_max_right _ _, fun center radius hradius x => ?_⟩
  rw [spacesTraceBump_iteratedDeriv, abs_mul,
    abs_of_nonneg (pow_nonneg (inv_pos.mpr hradius).le n)]
  exact (mul_le_mul_of_nonneg_left (hbase _) (pow_nonneg (inv_pos.mpr hradius).le n)).trans_eq
    (mul_comm _ _)

def spacesTracePacketSum (center radius : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (p : PolarPoint) : ℝ :=
  ∑' m, spacesTraceBump (center m) (radius m) p.1 * v m p.2

section Packets

variable (center radius : ℕ → ℝ) (hradius : ∀ m, 0 < radius m)
  (hlocal : LocallyFinite (fun m => Icc (center m - radius m) (center m + radius m)))

include hradius hlocal

theorem spacesTracePacketSum_summable (v : ℕ → ℝ → ℝ) (p : PolarPoint) :
    Summable (fun m => spacesTraceBump (center m) (radius m) p.1 * v m p.2) := by
  apply summable_of_hasFiniteSupport
  apply (hlocal.point_finite p.1).subset
  intro m hm
  exact Ioo_subset_Icc_self
    (spacesTraceBump_support (hradius m) (left_ne_zero_of_mul hm))

/-- On one radial neighborhood, the same finite sum works for every angle. -/
theorem spacesTracePacketSum_locally_finite (v : ℕ → ℝ → ℝ) (x : ℝ) :
    ∃ s : Finset ℕ, ∃ U ∈ 𝓝 x,
      (∀ y ∈ U, ∀ θ, spacesTracePacketSum center radius v (y, θ) =
        ∑ m ∈ s, spacesTraceBump (center m) (radius m) y * v m θ) ∧
      (∀ m, m ∉ s → ∀ y ∈ U, spacesTraceBump (center m) (radius m) y = 0) := by
  classical
  obtain ⟨U, hU, hfinite⟩ := hlocal x
  let s := hfinite.toFinset
  have hzero : ∀ m, m ∉ s → ∀ y ∈ U, spacesTraceBump (center m) (radius m) y = 0 := by
    intro m hm y hy
    by_contra hb
    exact hm (hfinite.mem_toFinset.mpr
      ⟨y, Ioo_subset_Icc_self (spacesTraceBump_support (hradius m) hb), hy⟩)
  refine ⟨s, U, hU, ?_, hzero⟩
  intro y hy θ
  apply tsum_eq_sum
  intro m hm
  rw [hzero m hm y hy, zero_mul]

/-- The locally finite sum is smooth for every sequence of smooth angular
functions; no convergence or smoothness is postulated for the resulting sum. -/
theorem spacesTracePacketSum_contDiff {v : ℕ → ℝ → ℝ}
    (hv : ∀ m, ContDiff ℝ ∞ (v m)) :
    ContDiff ℝ ∞ (spacesTracePacketSum center radius v) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro p
  obtain ⟨s, U, hU, heq, _⟩ := spacesTracePacketSum_locally_finite center radius hradius hlocal v p.1
  have he : spacesTracePacketSum center radius v =ᶠ[𝓝 p]
      (fun q => ∑ m ∈ s, spacesTraceBump (center m) (radius m) q.1 * v m q.2) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hU] with q hq
    exact heq q.1 hq q.2
  apply ContDiffAt.congr_of_eventuallyEq _ he
  exact ContDiffAt.sum (fun m _ =>
    ((spacesTraceBump_contDiff (center m) (radius m)).comp contDiff_fst).contDiffAt.mul
      ((hv m).comp contDiff_snd).contDiffAt)

def spacesTracePacketLinear : (ℕ → ℝ → ℝ) →ₗ[ℝ] (PolarPoint → ℝ) where
  toFun := spacesTracePacketSum center radius
  map_add' := by
    intro v w
    funext p
    simp only [spacesTracePacketSum, Pi.add_apply, mul_add]
    exact (spacesTracePacketSum_summable center radius hradius hlocal v p).tsum_add
      (spacesTracePacketSum_summable center radius hradius hlocal w p)
  map_smul' := by
    intro c v
    funext p
    simp only [spacesTracePacketSum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm _ c]
    exact (spacesTracePacketSum_summable center radius hradius hlocal v p).tsum_const_smul c

theorem spacesTracePacketSum_mixedDerivative {v : ℕ → ℝ → ℝ}
    (hv : ∀ m, ContDiff ℝ ∞ (v m)) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (spacesTracePacketSum center radius v) p =
      ∑' m, iteratedDeriv a (spacesTraceBump (center m) (radius m)) p.1 *
        iteratedDeriv b (v m) p.2 := by
  classical
  obtain ⟨s, U, hU, heq, hzero⟩ :=
    spacesTracePacketSum_locally_finite center radius hradius hlocal v p.1
  have he : (fun x => iteratedDeriv b (fun θ => spacesTracePacketSum center radius v (x, θ)) p.2)
      =ᶠ[𝓝 p.1] (fun x => ∑ m ∈ s,
        spacesTraceBump (center m) (radius m) x * iteratedDeriv b (v m) p.2) := by
    filter_upwards [hU] with x hx
    have hefun := funext (heq x hx)
    rw [hefun, iteratedDeriv_fun_sum]
    · apply Finset.sum_congr rfl
      intro m _
      exact iteratedDeriv_const_mul _ ((hv m).contDiffAt.of_le (by simp))
    · intro m _
      exact (contDiffAt_const.mul (hv m).contDiffAt).of_le (by simp)
  change iteratedDeriv a _ p.1 = _
  rw [he.iteratedDeriv_eq a, iteratedDeriv_fun_sum]
  · simp only [iteratedDeriv_mul_const_field]
    symm
    apply tsum_eq_sum
    intro m hm
    have hezero : spacesTraceBump (center m) (radius m) =ᶠ[𝓝 p.1] (0 : ℝ → ℝ) := by
      filter_upwards [hU] with x hx
      exact hzero m hm x hx
    have hd : iteratedDeriv a (spacesTraceBump (center m) (radius m)) p.1 = 0 := by
      simpa only [iteratedDeriv_const_zero] using hezero.iteratedDeriv_eq a
    rw [hd, zero_mul]
  · intro m _
    exact ((spacesTraceBump_contDiff (center m) (radius m)).contDiffAt.mul
      contDiffAt_const).of_le (by simp)

end Packets

theorem spacesTracePacketSum_periodic (center radius : ℕ → ℝ) {v : ℕ → ℝ → ℝ}
    (hv : ∀ m, Function.Periodic (v m) Real.pi) :
    Function.Periodic (spacesTracePacketSum center radius v) (0, Real.pi) := by
  intro p
  apply tsum_congr
  intro m
  simp only [Prod.fst_add, Prod.snd_add, add_zero]
  rw [hv m p.2]

theorem spacesTracePacketSum_even (center radius : ℕ → ℝ) {v : ℕ → ℝ → ℝ}
    (hv : ∀ m θ, v m (-θ) = v m θ) (x θ : ℝ) :
    spacesTracePacketSum center radius v (x, -θ) = spacesTracePacketSum center radius v (x, θ) := by
  apply tsum_congr
  intro m
  rw [hv m θ]

/-- The packet sum has exactly the prescribed angular data at each center. -/
theorem spacesTracePacketSum_center (center radius : ℕ → ℝ) (hradius : ∀ m, 0 < radius m)
    (hdisj : Pairwise (fun m n => Disjoint
      (Ioo (center m - radius m) (center m + radius m))
      (Ioo (center n - radius n) (center n + radius n))))
    (v : ℕ → ℝ → ℝ) (m : ℕ) (θ : ℝ) :
    spacesTracePacketSum center radius v (center m, θ) = v m θ := by
  rw [spacesTracePacketSum, tsum_eq_single m]
  · rw [spacesTraceBump_center, one_mul]
  · intro n hnm
    have hm : center m ∈ Ioo (center m - radius m) (center m + radius m) :=
      ⟨by linarith [hradius m], by linarith [hradius m]⟩
    have hn : center m ∉ Ioo (center n - radius n) (center n + radius n) := fun hn =>
      Set.disjoint_left.mp (hdisj hnm) hn hm
    rw [spacesTraceBump_zero (hradius n) hn, zero_mul]

end ContinuousFlexibility.Statements
