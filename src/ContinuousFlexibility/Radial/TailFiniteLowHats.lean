import ContinuousFlexibility.Radial.TailLowHats
import ContinuousFlexibility.Radial.TailFiniteCoefficientBounds
import ContinuousFlexibility.Radial.TailHighFormBound

/-!
# Finite sums of the actual smooth low hats

The exact cell and gap formulas identify the physical mass and derivative
energy of every finite linear combination. The estimates are independent
of the support and of the position of a finite Dirichlet wall.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements

def tailFiniteLowHat (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) : ℝ → ℝ :=
  fun x => ∑ n ∈ a.support, a n * tailLowHat T hT n x

theorem tailFiniteLowHat_smooth (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) : ContDiff ℝ ∞ (tailFiniteLowHat T hT a) :=
  ContDiff.sum (fun n _ => contDiff_const.mul (tailLowHat_smooth T hT n))

theorem tailFiniteLowHat_compact (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) : HasCompactSupport (tailFiniteLowHat T hT a) := by
  have he : (∑ n ∈ a.support, fun x => a n * tailLowHat T hT n x) =
      tailFiniteLowHat T hT a := by
    funext x
    simp only [Finset.sum_apply, tailFiniteLowHat]
  rw [← he]
  exact HasCompactSupport.finset_sum (s := a.support)
    (f := fun n x => a n * tailLowHat T hT n x)
    (fun n _ => (tailLowHat_compact T hT n).mul_left)

theorem tailFiniteLowHat_support (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) :
    tsupport (tailFiniteLowHat T hT a) ⊆ Ioo T.entrance T.endpoint := by
  have hfinite : ∀ s : Finset ℕ,
      tsupport (fun x => ∑ n ∈ s, a n * tailLowHat T hT n x) ⊆
        Ioo T.entrance T.endpoint := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have hzero : (fun _ : ℝ => (0 : ℝ)) = (0 : ℝ → ℝ) := by
        funext x
        rw [Pi.zero_apply]
      simp only [Finset.sum_empty, hzero, tsupport_zero, empty_subset]
    | @insert n s hn ih =>
      simp only [Finset.sum_insert hn]
      exact (tsupport_add _ _).trans (union_subset
        (tsupport_mul_subset_right.trans (tailLowHat_support T hT n)) ih)
  exact hfinite a.support

theorem tailFiniteLowHat_support_cut (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) {N : ℕ} (ha : a.support ⊆ Finset.range N) :
    tsupport (tailFiniteLowHat T hT a) ⊆ Ioo T.entrance (T.node N) := by
  have hfinite : ∀ s : Finset ℕ, s ⊆ Finset.range N →
      tsupport (fun x => ∑ n ∈ s, a n * tailLowHat T hT n x) ⊆
        Ioo T.entrance (T.node N) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      have hzero : (fun _ : ℝ => (0 : ℝ)) = (0 : ℝ → ℝ) := by
        funext x
        rw [Pi.zero_apply]
      simp only [Finset.sum_empty, hzero, tsupport_zero, empty_subset]
    | @insert n s hn ih =>
      intro hs
      have hnN : n < N := Finset.mem_range.mp (hs (Finset.mem_insert_self n s))
      have hhat : tsupport (tailLowHat T hT n) ⊆ Ioo T.entrance (T.node N) :=
        (tailLowHat_support_truncation T hT n).trans (fun x hx =>
          ⟨hx.1, hx.2.trans_le
            ((deepTail_node_strictMono hT).monotone (Nat.succ_le_of_lt hnN))⟩)
      simp only [Finset.sum_insert hn]
      exact (tsupport_add _ _).trans (union_subset
        (tsupport_mul_subset_right.trans hhat)
        (ih (fun m hm => hs (Finset.mem_insert_of_mem hm))))
  exact hfinite a.support ha

theorem tail_finsupp_sum_ite (a : ℕ →₀ ℝ) (m : ℕ) (c : ℝ) :
    (∑ n ∈ a.support, a n * (if n = m then c else 0)) = a m * c := by
  classical
  calc
    _ = a m * (if m = m then c else 0) :=
      Finset.sum_eq_single (f := fun n => a n * (if n = m then c else 0)) m
        (fun n _ hnm => by simp only [if_neg hnm, mul_zero])
        (fun hm => by rw [Finsupp.notMem_support_iff.mp hm, zero_mul])
    _ = _ := by rw [if_pos rfl]

theorem tailFiniteLowHat_mass (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (ha : ∀ n ∈ a.support, tailFirstMassIndex T ≤ n) (m : ℕ)
    {x : ℝ} (hx : x ∈ Icc (T.node m) (T.massEnd m)) :
    tailFiniteLowHat T hT a x = a m := by
  unfold tailFiniteLowHat
  calc
    _ = ∑ n ∈ a.support, a n * (if n = m then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      try dsimp only
      rw [tailLowHat_mass T hT n (ha n hn) m hx]
    _ = a m := by rw [tail_finsupp_sum_ite, mul_one]

theorem tailFiniteLowHat_gap (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (ha : ∀ n ∈ a.support, tailFirstMassIndex T ≤ n) (m : ℕ)
    {x : ℝ} (hx : x ∈ Icc (T.massEnd m) (T.node (m + 1))) :
    tailFiniteLowHat T hT a x =
      a m * (1 - tailGapStep T hT m x) + a (m + 1) * tailGapStep T hT m x := by
  unfold tailFiniteLowHat
  calc
    _ = ∑ n ∈ a.support, a n *
        ((if n = m then 1 - tailGapStep T hT m x else 0) +
          (if n = m + 1 then tailGapStep T hT m x else 0)) := by
      apply Finset.sum_congr rfl
      intro n hn
      try dsimp only
      rw [tailLowHat_gap T hT n (ha n hn) m hx]
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib, tail_finsupp_sum_ite]

theorem tailFiniteLowHat_initial (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (ha : ∀ n ∈ a.support, tailFirstMassIndex T ≤ n)
    {x : ℝ} (hx : x ∈ Icc T.entrance (T.node 0)) :
    tailFiniteLowHat T hT a x = a 0 * tailEntryStep T hT x := by
  unfold tailFiniteLowHat
  calc
    _ = ∑ n ∈ a.support, a n * (if n = 0 then tailEntryStep T hT x else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      try dsimp only
      rw [tailLowHat_initial T hT n (ha n hn) hx]
    _ = _ := tail_finsupp_sum_ite a 0 _

theorem tailFiniteLowHat_deriv (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (x : ℝ) :
    deriv (tailFiniteLowHat T hT a) x =
      ∑ n ∈ a.support, a n * deriv (tailLowHat T hT n) x := by
  unfold tailFiniteLowHat
  rw [deriv_fun_sum (u := a.support) (fun n _ =>
    (((tailLowHat_smooth T hT n).differentiable (by simp)) x).const_mul (a n))]
  apply Finset.sum_congr rfl
  intro n _
  exact deriv_const_mul _ (((tailLowHat_smooth T hT n).differentiable (by simp)) x)

theorem tailFiniteLowHat_deriv_mass (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (ha : ∀ n ∈ a.support, tailFirstMassIndex T ≤ n) (m : ℕ)
    {x : ℝ} (hx : x ∈ Ioo (T.node m) (T.massEnd m)) :
    deriv (tailFiniteLowHat T hT a) x = 0 := by
  rw [tailFiniteLowHat_deriv]
  apply Finset.sum_eq_zero
  intro n hn
  try dsimp only
  rw [tailLowHat_deriv_mass T hT n (ha n hn) m hx, mul_zero]

theorem tailFiniteLowHat_deriv_gap (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (ha : ∀ n ∈ a.support, tailFirstMassIndex T ≤ n) (m : ℕ)
    {x : ℝ} (hx : x ∈ Ioo (T.massEnd m) (T.node (m + 1))) :
    deriv (tailFiniteLowHat T hT a) x =
      (a (m + 1) - a m) * deriv (tailGapStep T hT m) x := by
  rw [tailFiniteLowHat_deriv]
  calc
    _ = ∑ n ∈ a.support, a n *
        ((if n = m then -deriv (tailGapStep T hT m) x else 0) +
          (if n = m + 1 then deriv (tailGapStep T hT m) x else 0)) := by
      apply Finset.sum_congr rfl
      intro n hn
      try dsimp only
      rw [tailLowHat_deriv_gap T hT n (ha n hn) m hx]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, tail_finsupp_sum_ite]
      ring

theorem tailFiniteLowHat_deriv_initial (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (ha : ∀ n ∈ a.support, tailFirstMassIndex T ≤ n)
    {x : ℝ} (hx : x ∈ Ioo T.entrance (T.node 0)) :
    deriv (tailFiniteLowHat T hT a) x = a 0 * deriv (tailEntryStep T hT) x := by
  rw [tailFiniteLowHat_deriv]
  calc
    _ = ∑ n ∈ a.support, a n * (if n = 0 then deriv (tailEntryStep T hT) x else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      try dsimp only
      rw [tailLowHat_deriv_initial T hT n (ha n hn) hx]
    _ = _ := tail_finsupp_sum_ite a 0 _

theorem tail_interpolation_sq_le {t a b : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (a * (1 - t) + b * t) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have hconv : (a * (1 - t) + b * t) ^ 2 ≤ (1 - t) * a ^ 2 + t * b ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) (sq_nonneg (a - b))]
  have ha := mul_le_mul_of_nonneg_right (show 1 - t ≤ 1 by linarith) (sq_nonneg a)
  have hb := mul_le_mul_of_nonneg_right ht1 (sq_nonneg b)
  nlinarith [sq_nonneg a, sq_nonneg b]

theorem tailFiniteLowHat_mass_norm (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (ha : ∀ n ∈ a.support, tailFirstMassIndex T ≤ n) (m : ℕ) :
    tailMassNormSq T (tailFiniteLowHat T hT a) m = tailMass T m * a m ^ 2 := by
  unfold tailMassNormSq
  calc
    _ = ∫ x in T.node m..T.massEnd m, T.p x * a m ^ 2 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (deepTail_node_lt_massEnd hT m).le
      intro x hx
      try dsimp only
      rw [tailFiniteLowHat_mass T hT a ha m ⟨hx.1.le, hx.2.le⟩]
    _ = _ := intervalIntegral.integral_mul_const _ _

theorem tailFiniteLowHat_mass_energy (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (ha : ∀ n ∈ a.support, tailFirstMassIndex T ≤ n) (m : ℕ) :
    tailMassEnergy T (tailFiniteLowHat T hT a) m = 0 := by
  unfold tailMassEnergy
  calc
    _ = ∫ x in T.node m..T.massEnd m, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (deepTail_node_lt_massEnd hT m).le
      intro x hx
      try dsimp only
      rw [tailFiniteLowHat_deriv_mass T hT a ha m hx]
      ring
    _ = 0 := intervalIntegral.integral_zero

theorem tailFiniteLowHat_gap_norm (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (ha : ∀ n ∈ a.support, tailFirstMassIndex T ≤ n) (m : ℕ) :
    tailGapNormSq T (tailFiniteLowHat T hT a) m ≤
      2 * tailGapMass T m * (a m ^ 2 + a (m + 1) ^ 2) := by
  have hab := (deepTail_massEnd_lt_succ_node hT m).le
  have hs := deepTail_Icc_subset hT
    ((deepTail_entrance_le_node hT m).trans (deepTail_node_lt_massEnd hT m).le)
    (deepTail_node_lt_endpoint hT (m + 1))
  have hp := (deepTail_contDiffOn hT).continuousOn.mono hs
  have hu : ContinuousOn (tailFiniteLowHat T hT a)
      (Icc (T.massEnd m) (T.node (m + 1))) :=
    (tailFiniteLowHat_smooth T hT a).continuous.continuousOn
  unfold tailGapNormSq
  calc
    _ ≤ ∫ x in T.massEnd m..T.node (m + 1),
        T.p x * (2 * (a m ^ 2 + a (m + 1) ^ 2)) := by
      apply intervalIntegral.integral_mono_on hab
        ((hp.mul (hu.pow 2)).intervalIntegrable_of_Icc hab)
        ((hp.mul continuousOn_const).intervalIntegrable_of_Icc hab)
      intro x hx
      try dsimp only
      apply mul_le_mul_of_nonneg_left _ (deepTail_pos hT x (hs hx)).le
      simp only [Pi.pow_apply]
      rw [tailFiniteLowHat_gap T hT a ha m hx]
      exact tail_interpolation_sq_le (tailGapStep_range T hT m x).1
        (tailGapStep_range T hT m x).2
    _ = _ := by rw [intervalIntegral.integral_mul_const, tailGapMass] <;> ring

theorem tailFiniteLowHat_gap_energy (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (ha : ∀ n ∈ a.support, tailFirstMassIndex T ≤ n) (m : ℕ) :
    tailGapEnergy T (tailFiniteLowHat T hT a) m ≤
      2 * (tailSmoothStepConstant / tailResistance T m) *
        (a m ^ 2 + a (m + 1) ^ 2) := by
  have heq : tailGapEnergy T (tailFiniteLowHat T hT a) m =
      (a (m + 1) - a m) ^ 2 *
        ∫ x in T.massEnd m..T.node (m + 1), T.p x * deriv (tailGapStep T hT m) x ^ 2 := by
    unfold tailGapEnergy
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (deepTail_massEnd_lt_succ_node hT m).le
    intro x hx
    try dsimp only
    rw [tailFiniteLowHat_deriv_gap T hT a ha m hx]
    ring
  rw [heq]
  calc
    _ ≤ (a (m + 1) - a m) ^ 2 * (tailSmoothStepConstant / tailResistance T m) :=
      mul_le_mul_of_nonneg_left (tailGapStep_energy T hT m) (sq_nonneg _)
    _ ≤ (2 * (a m ^ 2 + a (m + 1) ^ 2)) *
        (tailSmoothStepConstant / tailResistance T m) := by
      apply mul_le_mul_of_nonneg_right
      · nlinarith [sq_nonneg (a m + a (m + 1))]
      · exact div_nonneg tailSmoothStepConstant_pos.le (tailResistance_pos hT m).le
    _ = _ := by ring

theorem tailFiniteLowHat_initial_norm (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (ha : ∀ n ∈ a.support, tailFirstMassIndex T ≤ n) :
    tailInitialNormSq T (tailFiniteLowHat T hT a) ≤ T.η * tailCoefficientMass T a := by
  rcases hT.2.2.2.1 with he | ⟨he, _, hmass, _⟩
  · simp only [tailInitialNormSq, he, intervalIntegral.integral_same]
    exact mul_nonneg hT.2.2.2.2.1.le (tailCoefficientMass_nonneg hT a)
  · have hs := deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0)
    have hp := (deepTail_contDiffOn hT).continuousOn.mono hs
    have hu : ContinuousOn (tailFiniteLowHat T hT a) (Icc T.entrance (T.node 0)) :=
      (tailFiniteLowHat_smooth T hT a).continuous.continuousOn
    have hbound : tailInitialNormSq T (tailFiniteLowHat T hT a) ≤
        tailInitialGapMass T * a 0 ^ 2 := by
      unfold tailInitialNormSq
      calc
        _ ≤ ∫ x in T.entrance..T.node 0, T.p x * a 0 ^ 2 := by
          apply intervalIntegral.integral_mono_on he.le
            ((hp.mul (hu.pow 2)).intervalIntegrable_of_Icc he.le)
            ((hp.mul continuousOn_const).intervalIntegrable_of_Icc he.le)
          intro x hx
          try dsimp only
          apply mul_le_mul_of_nonneg_left _ (deepTail_pos hT x (hs hx)).le
          simp only [Pi.pow_apply]
          rw [tailFiniteLowHat_initial T hT a ha hx, mul_pow]
          have ht := tailEntryStep_range T hT x
          have ht2 : tailEntryStep T hT x ^ 2 ≤ 1 := by nlinarith
          simpa only [mul_one] using mul_le_mul_of_nonneg_left ht2 (sq_nonneg (a 0))
        _ = _ := intervalIntegral.integral_mul_const _ _
    calc
      _ ≤ tailInitialGapMass T * a 0 ^ 2 := hbound
      _ ≤ (T.η * tailMass T 0) * a 0 ^ 2 :=
        mul_le_mul_of_nonneg_right hmass (sq_nonneg _)
      _ = T.η * (tailMass T 0 * a 0 ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (tailCoefficientMass_single_le hT a 0)
        hT.2.2.2.2.1.le

theorem tailFiniteLowHat_initial_energy (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (ha : ∀ n ∈ a.support, tailFirstMassIndex T ≤ n) :
    tailInitialEnergy T (tailFiniteLowHat T hT a) ≤
      (tailSmoothStepConstant * T.Λ / T.K) * tailCoefficientMass T a := by
  have hK : 0 < T.K := lt_trans zero_lt_one hT.2.2.2.2.2.2.1
  have hcoef : 0 ≤ tailSmoothStepConstant * T.Λ / T.K :=
    div_nonneg (mul_nonneg tailSmoothStepConstant_pos.le hT.2.2.1.le) hK.le
  rcases hT.2.2.2.1 with he | ⟨he, _, _, hlarge⟩
  · simp only [tailInitialEnergy, he, intervalIntegral.integral_same]
    exact mul_nonneg hcoef (tailCoefficientMass_nonneg hT a)
  · have hR : 0 < tailInitialResistance T :=
      deepTail_interval_resistance_pos hT le_rfl he (deepTail_node_lt_endpoint hT 0)
    have hinv : (tailInitialResistance T)⁻¹ ≤ T.Λ * tailMass T 0 / T.K := by
      exact tail_inverse_resistance_bound hK hR hlarge
    have heq : tailInitialEnergy T (tailFiniteLowHat T hT a) =
        a 0 ^ 2 * ∫ x in T.entrance..T.node 0, T.p x * deriv (tailEntryStep T hT) x ^ 2 := by
      unfold tailInitialEnergy
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le he.le
      intro x hx
      try dsimp only
      rw [tailFiniteLowHat_deriv_initial T hT a ha hx]
      ring
    rw [heq]
    calc
      _ ≤ a 0 ^ 2 * (tailSmoothStepConstant / tailInitialResistance T) :=
        mul_le_mul_of_nonneg_left (tailEntryStep_energy T hT he) (sq_nonneg _)
      _ ≤ a 0 ^ 2 * (tailSmoothStepConstant * (T.Λ * tailMass T 0 / T.K)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hinv tailSmoothStepConstant_pos.le
      _ = (tailSmoothStepConstant * T.Λ / T.K) * (tailMass T 0 * a 0 ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (tailCoefficientMass_single_le hT a 0) hcoef

/-- Uniform bounds on the actual full-tail integrals of a finite low-mode
combination, including the separate initial resistance interval. -/
theorem tailFiniteLowHat_bounds (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ →₀ ℝ) (ha : ∀ n ∈ a.support, tailFirstMassIndex T ≤ n) :
    tailCoefficientMass T a ≤
        (∫ x, tailFiniteLowHat T hT a x ^ 2 ∂deepTailMeasure T) ∧
      (∫ x, tailFiniteLowHat T hT a x ^ 2 ∂deepTailMeasure T) ≤
        (1 + 5 * T.η) * tailCoefficientMass T a ∧
      (∫ x, deriv (tailFiniteLowHat T hT a) x ^ 2 ∂deepTailMeasure T) ≤
        (5 * tailSmoothStepConstant * T.Λ / T.K) * tailCoefficientMass T a := by
  let N := a.support.sup id + 1
  have haN : a.support ⊆ Finset.range N := by
    intro n hn
    apply Finset.mem_range.mpr
    exact lt_of_le_of_lt (Finset.le_sup (f := id) hn) (Nat.lt_succ_self _)
  have hs := tailFiniteLowHat_support_cut T hT a haN
  have hsq : Function.support (fun x => tailFiniteLowHat T hT a x ^ 2) ⊆
      Ioo T.entrance (T.node N) := by
    intro x hx
    apply hs
    apply subset_tsupport (tailFiniteLowHat T hT a)
    intro hz
    exact hx (by simp only [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
  have hdsq : Function.support (fun x => deriv (tailFiniteLowHat T hT a) x ^ 2) ⊆
      Ioo T.entrance (T.node N) := by
    intro x hx
    apply hs
    apply support_deriv_subset
    intro hz
    exact hx (by simp only [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
  have hp : ContinuousOn T.p (Icc T.entrance (T.node N)) :=
    (deepTail_contDiffOn hT).continuousOn.mono
      (deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT N))
  have hu : ContinuousOn (tailFiniteLowHat T hT a) (Icc T.entrance (T.node N)) :=
    (tailFiniteLowHat_smooth T hT a).continuous.continuousOn
  have hd : ContinuousOn (deriv (tailFiniteLowHat T hT a)) (Icc T.entrance (T.node N)) :=
    ((tailFiniteLowHat_smooth T hT a).continuous_deriv (by simp)).continuousOn
  have hnorm : (∫ x, tailFiniteLowHat T hT a x ^ 2 ∂deepTailMeasure T) =
      tailInitialNormSq T (tailFiniteLowHat T hT a) + tailCoefficientMass T a +
        ∑ n ∈ Finset.range N, tailGapNormSq T (tailFiniteLowHat T hT a) n := by
    rw [tail_integral_eq_interval_of_support hT (deepTail_entrance_le_node hT N)
      (deepTail_node_lt_endpoint hT N).le hsq,
      tail_integral_partition (f := fun x => T.p x * tailFiniteLowHat T hT a x ^ 2)
        hT N (hp.mul (hu.pow 2))]
    change tailInitialNormSq T (tailFiniteLowHat T hT a) +
      (∑ n ∈ Finset.range N, (tailMassNormSq T (tailFiniteLowHat T hT a) n +
        tailGapNormSq T (tailFiniteLowHat T hT a) n)) = _
    simp only [Finset.sum_add_distrib, tailFiniteLowHat_mass_norm T hT a ha,
      ← tailCoefficientMass_eq_range a haN, add_assoc]
  have henergy : (∫ x, deriv (tailFiniteLowHat T hT a) x ^ 2 ∂deepTailMeasure T) =
      tailInitialEnergy T (tailFiniteLowHat T hT a) +
        ∑ n ∈ Finset.range N, tailGapEnergy T (tailFiniteLowHat T hT a) n := by
    rw [tail_integral_eq_interval_of_support hT (deepTail_entrance_le_node hT N)
      (deepTail_node_lt_endpoint hT N).le hdsq,
      tail_integral_partition (f := fun x => T.p x * deriv (tailFiniteLowHat T hT a) x ^ 2)
        hT N (hp.mul (hd.pow 2))]
    change tailInitialEnergy T (tailFiniteLowHat T hT a) +
      (∑ n ∈ Finset.range N, (tailMassEnergy T (tailFiniteLowHat T hT a) n +
        tailGapEnergy T (tailFiniteLowHat T hT a) n)) = _
    simp only [tailFiniteLowHat_mass_energy T hT a ha, zero_add]
  have hgap : (∑ n ∈ Finset.range N, tailGapNormSq T (tailFiniteLowHat T hT a) n) ≤
      4 * T.η * tailCoefficientMass T a :=
    (Finset.sum_le_sum (fun n _ => tailFiniteLowHat_gap_norm T hT a ha n)).trans
      (tail_finite_gap_mass_bound hT a _)
  have hgapE : (∑ n ∈ Finset.range N, tailGapEnergy T (tailFiniteLowHat T hT a) n) ≤
      (4 * tailSmoothStepConstant * T.Λ / T.K) * tailCoefficientMass T a :=
    (Finset.sum_le_sum (fun n _ => tailFiniteLowHat_gap_energy T hT a ha n)).trans
      (tail_finite_gap_energy_bound hT tailSmoothStepConstant_pos.le a _)
  have hinitial := tailFiniteLowHat_initial_norm T hT a ha
  have hinitialE := tailFiniteLowHat_initial_energy T hT a ha
  have hnonnegI : 0 ≤ tailInitialNormSq T (tailFiniteLowHat T hT a) := by
    apply intervalIntegral.integral_nonneg hT.2.1
    intro x hx
    exact mul_nonneg (deepTail_pos hT x
      (deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0) hx)).le (sq_nonneg _)
  have hnonnegG : 0 ≤ ∑ n ∈ Finset.range N,
      tailGapNormSq T (tailFiniteLowHat T hT a) n := by
    apply Finset.sum_nonneg
    intro n _
    apply intervalIntegral.integral_nonneg (deepTail_massEnd_lt_succ_node hT n).le
    intro x hx
    exact mul_nonneg (deepTail_pos hT x
      (deepTail_Icc_subset hT
        ((deepTail_entrance_le_node hT n).trans (deepTail_node_lt_massEnd hT n).le)
        (deepTail_node_lt_endpoint hT (n + 1)) hx)).le (sq_nonneg _)
  constructor
  · rw [hnorm]
    linarith
  constructor
  · rw [hnorm]
    nlinarith
  · rw [henergy]
    calc
      _ ≤ (tailSmoothStepConstant * T.Λ / T.K) * tailCoefficientMass T a +
          (4 * tailSmoothStepConstant * T.Λ / T.K) * tailCoefficientMass T a :=
        add_le_add hinitialE hgapE
      _ = _ := by ring

end ContinuousFlexibility.Radial
