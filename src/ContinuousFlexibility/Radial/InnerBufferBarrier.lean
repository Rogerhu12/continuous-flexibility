import ContinuousFlexibility.Radial.InnerBufferPoisson
import ContinuousFlexibility.Radial.PositiveBufferComparison
import ContinuousFlexibility.Radial.InnerBufferDerivative

/-!
# Exponential decay of the actual buffer column

The inward coordinate is the coordinate of BufferData, at either end of
the retained interval. The maximum principle applies to the very same
Dirichlet buffer column used by compression. Its equation, endpoint values
and positive potential give exponential decay.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem innerBufferPoint_hasDerivAt (B : BufferData) (i : Fin 2) (t : ℝ) :
    HasDerivAt (positiveBufferPoint B i) (-bufferSign i / B.mass i) t := by
  convert (((hasDerivAt_id t).const_mul (bufferSign i)).div_const (B.mass i)).const_sub
    (bufferCut B i) using 1 <;> first | rfl | ring

theorem innerBufferPoint_contDiff (B : BufferData) (i : Fin 2) :
    ContDiff ℝ ∞ (positiveBufferPoint B i) := by
  unfold positiveBufferPoint
  fun_prop

theorem innerBufferPoint_mem_closed {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {t : ℝ} (ht : t ∈ Icc 0 (B.action i + 6)) :
    positiveBufferPoint B i t ∈ uIcc (bufferCut B i) (bufferInnerWall B i) := by
  by_cases hz : t = 0
  · rw [hz, positiveBufferPoint_zero]
    exact left_mem_uIcc
  by_cases hw : t = B.action i + 6
  · rw [hw, positiveBufferPoint_innerWall]
    exact right_mem_uIcc
  exact Ioo_subset_Icc_self (innerBufferPoint_mem_openSpan hB i
    (lt_of_le_of_ne ht.1 (Ne.symm hz)) (lt_of_le_of_ne ht.2 hw))

/-- The actual buffer solution, pulled back to mass units, solves a
positive equation whose potential is at least one. -/
theorem innerBuffer_column_coordinate_equation {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {p : ℝ → ℝ}
    (hp : ContDiffOn ℝ 2 p (uIcc (bufferCut B i) (bufferInnerWall B i)))
    (heq : ∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
      -deriv (deriv p) x + B.potential x * p x = 0) :
    let u := fun t => p (positiveBufferPoint B i t)
    let du := fun t => (-bufferSign i / B.mass i) * deriv p (positiveBufferPoint B i t)
    let q := fun t => B.potential (positiveBufferPoint B i t) / B.mass i ^ 2
    ContinuousOn u (Icc 0 (B.action i + 6)) ∧
      (∀ t ∈ Ioo 0 (B.action i + 6), HasDerivAt u (du t) t) ∧
      (∀ t ∈ Ioo 0 (B.action i + 6), HasDerivAt du (q t * u t) t) ∧
      (∀ t ∈ Ioo 0 (B.action i + 6), 1 ≤ q t) := by
  dsimp only
  have hm := buffer_mass_pos hB i
  have hpopen : ContDiffOn ℝ 2 p
      (radialOpenSpan (bufferCut B i) (bufferInnerWall B i)) :=
    hp.mono Ioo_subset_Icc_self
  have hpd : ContDiffOn ℝ 1 (deriv p)
      (radialOpenSpan (bufferCut B i) (bufferInnerWall B i)) :=
    hpopen.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hsquare : (-bufferSign i / B.mass i) ^ 2 = (B.mass i ^ 2)⁻¹ := by
    rw [div_pow, neg_sq, bufferSign_sq, one_div]
  refine ⟨hp.continuousOn.comp' (innerBufferPoint_contDiff B i).continuous.continuousOn
    (fun t ht => innerBufferPoint_mem_closed hB i ht), ?_, ?_, ?_⟩
  · intro t ht
    have hx := innerBufferPoint_mem_openSpan hB i ht.1 ht.2
    have hd := (hpopen.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)
    simpa only [Function.comp_def, mul_comm] using
      hd.hasDerivAt.comp t (innerBufferPoint_hasDerivAt B i t)
  · intro t ht
    have hx := innerBufferPoint_mem_openSpan hB i ht.1 ht.2
    have hd := (hpd.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)
    have he : deriv (deriv p) (positiveBufferPoint B i t) =
        B.potential (positiveBufferPoint B i t) * p (positiveBufferPoint B i t) := by
      linarith only [heq _ hx]
    have hcoeff :
        (-bufferSign i / B.mass i) *
            (deriv (deriv p) (positiveBufferPoint B i t) * (-bufferSign i / B.mass i)) =
          B.potential (positiveBufferPoint B i t) / B.mass i ^ 2 *
            p (positiveBufferPoint B i t) := by
      rw [he]
      calc
        _ = (-bufferSign i / B.mass i) ^ 2 *
            (B.potential (positiveBufferPoint B i t) * p (positiveBufferPoint B i t)) := by ring
        _ = _ := by rw [hsquare]; ring
    simpa only [Function.comp_def, hcoeff] using
      (hd.hasDerivAt.comp t (innerBufferPoint_hasDerivAt B i t)).const_mul
        (-bufferSign i / B.mass i)
  · intro t ht
    apply (le_div_iff₀ (sq_pos_of_pos hm)).mpr
    simpa only [one_mul] using positiveBufferPoint_potential_lower hB i ht.2.le

/-- The same Dirichlet buffer representative is nonnegative and bounded
by the inward exponential, uniformly in the action and in the cut side. -/
theorem innerBuffer_column_exponential {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {p : ℝ → ℝ}
    (hp : ContDiffOn ℝ 2 p (uIcc (bufferCut B i) (bufferInnerWall B i)))
    (heq : ∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
      -deriv (deriv p) x + B.potential x * p x = 0)
    (hcut : p (bufferCut B i) = 1) (hwall : p (bufferInnerWall B i) = 0) :
    ∀ t ∈ Icc 0 (B.action i + 6),
      0 ≤ p (positiveBufferPoint B i t) ∧
        p (positiveBufferPoint B i t) ≤ exp (-t) := by
  obtain ⟨hc, hd, hdd, hq⟩ := innerBuffer_column_coordinate_equation hB i hp heq
  have h₀ : p (positiveBufferPoint B i 0) = 1 := by
    rw [positiveBufferPoint_zero, hcut]
  have h₁ : p (positiveBufferPoint B i (B.action i + 6)) = 0 := by
    rw [positiveBufferPoint_innerWall, hwall]
  have hnonneg := positiveBuffer_solution_nonneg hc hd hdd
    (fun t ht => lt_of_lt_of_le zero_lt_one (hq t ht))
    (by rw [h₀]; norm_num) (by rw [h₁])
  have hupper := positiveBuffer_dirichlet_exponential_bound
    (m := 1) (A := 1) (by norm_num) (by norm_num) hc hd hdd
    (fun t ht => by simpa only [one_pow] using hq t ht)
    (by rw [h₀]) (by rw [h₁])
  intro t ht
  refine ⟨hnonneg t ht, ?_⟩
  simpa only [neg_one_mul, sub_zero, one_mul] using hupper t ht

/-- On the inner unit layers the height of this actual column is at most
exp (-action), the factor used in the commutator estimate. -/
theorem innerBuffer_column_inner_height {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {p : ℝ → ℝ}
    (hp : ContDiffOn ℝ 2 p (uIcc (bufferCut B i) (bufferInnerWall B i)))
    (heq : ∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
      -deriv (deriv p) x + B.potential x * p x = 0)
    (hcut : p (bufferCut B i) = 1) (hwall : p (bufferInnerWall B i) = 0)
    {t : ℝ} (ht : t ∈ Icc (B.action i) (B.action i + 6)) :
    |p (positiveBufferPoint B i t)| ≤ exp (-B.action i) := by
  have h := innerBuffer_column_exponential hB i hp heq hcut hwall t
    ⟨(buffer_action_pos hB i).le.trans ht.1, ht.2⟩
  rw [abs_of_nonneg h.1]
  exact h.2.trans (exp_le_exp.mpr (neg_le_neg ht.1))

/-- At every point of the cutoff source layer the derivative has the
mass factor and the same exponential smallness as the column. The
one-unit comparison interval lies inside the controlled inner layer. -/
theorem innerBuffer_column_inner_derivative {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {p : ℝ → ℝ}
    (hp : ContDiffOn ℝ 2 p (uIcc (bufferCut B i) (bufferInnerWall B i)))
    (heq : ∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
      -deriv (deriv p) x + B.potential x * p x = 0)
    (hcut : p (bufferCut B i) = 1) (hwall : p (bufferInnerWall B i) = 0)
    {t : ℝ} (ht : t ∈ Icc (B.action i + 3) (B.action i + 4)) :
    |deriv p (positiveBufferPoint B i t)| ≤
      (2 + B.layerBound) * B.mass i * exp (-B.action i) := by
  let u : ℝ → ℝ := fun y => p (positiveBufferPoint B i y)
  let du : ℝ → ℝ := fun y => (-bufferSign i / B.mass i) * deriv p (positiveBufferPoint B i y)
  let q : ℝ → ℝ := fun y => B.potential (positiveBufferPoint B i y) / B.mass i ^ 2
  let M : ℝ := exp (-B.action i)
  obtain ⟨_, hd, hdd, hq⟩ := innerBuffer_column_coordinate_equation hB i hp heq
  have hA := buffer_action_pos hB i
  have hm := buffer_mass_pos hB i
  have hC : 0 < B.layerBound := hB.2.2.2.1
  have hM : 0 ≤ M := (exp_pos _).le
  have hinside : ∀ y ∈ Icc t (t + 1), y ∈ Ioo 0 (B.action i + 6) := by
    intro y hy
    exact ⟨by linarith only [hA, ht.1, hy.1], by linarith only [ht.2, hy.2]⟩
  have hderiv (y : ℝ) (hy : y ∈ Ioo 0 (B.action i + 6)) :
      deriv u =ᶠ[𝓝 y] du := by
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
    exact (hd z hz).deriv
  have hsecond (y : ℝ) (hy : y ∈ Icc t (t + 1)) :
      HasDerivAt (deriv u) (q y * u y) y :=
    (hdd y (hinside y hy)).congr_of_eventuallyEq (hderiv y (hinside y hy))
  have hheight : ∀ y ∈ Icc t (t + 1), |u y| ≤ M := by
    intro y hy
    exact innerBuffer_column_inner_height hB i hp heq hcut hwall
      ⟨by linarith only [ht.1, hy.1], (hinside y hy).2.le⟩
  have hqUpper : ∀ y ∈ Icc t (t + 1), q y ≤ B.layerBound := by
    intro y hy
    apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
    apply positiveBufferPoint_potential_upper_inner hB i
    apply abs_le.mpr
    exact ⟨by linarith only [ht.1, hy.1], by linarith only [ht.2, hy.2]⟩
  have hsecondBound : ∀ y ∈ Icc t (t + 1),
      |deriv (deriv u) y| ≤ B.layerBound * M := by
    intro y hy
    rw [(hsecond y hy).deriv, abs_mul, abs_of_nonneg
      (zero_le_one.trans (hq y (hinside y hy)))]
    exact mul_le_mul (hqUpper y hy) (hheight y hy) (abs_nonneg _) hC.le
  have h := innerBuffer_local_derivative_bound (u := u) (x := t) (δ := 1)
    (by norm_num) (mul_nonneg hC.le hM)
    (fun y hy => (hd y (hinside y hy)).differentiableAt)
    (fun y hy => (hsecond y hy).differentiableAt) hheight hsecondBound
  have htopen := hinside t ⟨le_rfl, by linarith⟩
  have hbound : |deriv u t| ≤ (2 + B.layerBound) * M := by
    calc
      _ ≤ 2 * M / 1 + (B.layerBound * M) * 1 := h
      _ = _ := by ring
  rw [(hd t htopen).deriv, abs_mul, abs_div, abs_neg, abs_bufferSign,
    abs_of_pos hm] at hbound
  have hdiv : |deriv p (positiveBufferPoint B i t)| / B.mass i ≤
      (2 + B.layerBound) * M := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hbound
  calc
    _ ≤ ((2 + B.layerBound) * M) * B.mass i := (div_le_iff₀ hm).mp hdiv
    _ = _ := by ring

end ContinuousFlexibility.Radial
