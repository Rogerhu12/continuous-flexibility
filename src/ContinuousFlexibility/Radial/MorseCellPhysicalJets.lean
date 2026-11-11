import ContinuousFlexibility.Radial.MorseCellModelJets
import ContinuousFlexibility.Radial.MorseCellJoinCollars

/-!
# Physical derivatives on a Morse cell

The inverse velocity is estimated on the actual model interval by
differentiating the local identity between the velocity and its reciprocal.
The inverse radius coordinate transports the iterates of this vector
field to ordinary derivatives in the physical radius.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private structure PhysicalJetCell where
  A : ℝ
  B : ℝ
  a : ℝ
  b : ℝ
  r : ℝ → ℝ
  hA : 0 < A
  hA₁ : A ≤ 1
  hB : 0 ≤ B
  hBA : B ≤ A
  hab : a < b
  hr : ContDiff ℝ ∞ r
  hexp : ∀ x ∈ Icc a b, exp (-x) ≤ 3
  hbounded : ∀ x ∈ Icc a b, |r x| ≤ 2 ∧ |deriv r x| ≤ 8
  hEq : ∀ x ∈ Icc a b, deriv (deriv r) x = -morseRho A B x * r x
  hspeed : ∀ x ∈ Ioo a b, A ^ 5 / 200 ≤ deriv r x

private def PhysicalJetCell.velocity (M : PhysicalJetCell) : ℝ → ℝ := deriv M.r

private def PhysicalJetCell.inverseVelocity (M : PhysicalJetCell) : ℝ → ℝ := M.velocity⁻¹

private theorem PhysicalJetCell.velocity_pos (M : PhysicalJetCell) {x : ℝ} (hx : x ∈ Ioo M.a M.b) :
    0 < M.velocity x :=
  (div_pos (pow_pos M.hA 5) (by norm_num)).trans_le (M.hspeed x hx)

private theorem PhysicalJetCell.invA_one_le (M : PhysicalJetCell) : 1 ≤ M.A⁻¹ :=
  (one_le_inv₀ M.hA).mpr M.hA₁

private theorem PhysicalJetCell.invA_nonneg (M : PhysicalJetCell) : 0 ≤ M.A⁻¹ :=
  zero_le_one.trans M.invA_one_le

private theorem PhysicalJetCell.velocity_smooth (M : PhysicalJetCell) : ContDiff ℝ ∞ M.velocity :=
  (contDiff_infty_iff_deriv.mp M.hr).2

private theorem PhysicalJetCell.inverseVelocity_smooth (M : PhysicalJetCell) :
    ContDiffOn ℝ ∞ M.inverseVelocity (Ioo M.a M.b) :=
  M.velocity_smooth.contDiffOn.inv (fun _ hx => (M.velocity_pos hx).ne')

private theorem velocity_modelJet_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : PhysicalJetCell) (x : ℝ), x ∈ Ioo M.a M.b →
      |iteratedDeriv k M.velocity x| ≤ C := by
  obtain ⟨C, hC, h⟩ := exists_morseRadius_modelJet_bound (k + 1)
  refine ⟨C, hC, fun M x hx => ?_⟩
  change |iteratedDeriv k (deriv M.r) x| ≤ C
  simpa only [iteratedDeriv_succ'] using
    h M.hA.le M.hA₁ M.hB M.hBA M.hab M.hr M.hexp M.hbounded M.hEq x (Ioo_subset_Icc_self hx)

private def UniformPhysicalJets (p : ℕ) (f : PhysicalJetCell → ℝ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : PhysicalJetCell) (x : ℝ), x ∈ Ioo M.a M.b →
    |iteratedDeriv k (f M) x| ≤ C * M.A⁻¹ ^ (p + 5 * k)

private theorem uniformPhysicalJets_velocity : UniformPhysicalJets 0 PhysicalJetCell.velocity := by
  intro k
  obtain ⟨C, hC, hb⟩ := velocity_modelJet_bound k
  refine ⟨C, hC, fun M x hx => (hb M x hx).trans ?_⟩
  calc
    C = C * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (one_le_pow₀ M.invA_one_le) hC

private theorem uniformPhysicalJets_deriv {p : ℕ} {f : PhysicalJetCell → ℝ → ℝ}
    (hf : UniformPhysicalJets p f) : UniformPhysicalJets (p + 5) (fun M => deriv (f M)) := by
  intro k
  obtain ⟨C, hC, hb⟩ := hf (k + 1)
  refine ⟨C, hC, fun M x hx => ?_⟩
  simpa only [iteratedDeriv_succ', show p + 5 * (k + 1) = p + 5 + 5 * k by omega]
    using hb M x hx

private theorem uniformPhysicalJets_mul {p q : ℕ} {f g : PhysicalJetCell → ℝ → ℝ}
    (hfC : ∀ M, ContDiffOn ℝ ∞ (f M) (Ioo M.a M.b))
    (hgC : ∀ M, ContDiffOn ℝ ∞ (g M) (Ioo M.a M.b))
    (hf : UniformPhysicalJets p f) (hg : UniformPhysicalJets q g) :
    UniformPhysicalJets (p + q) (fun M => f M * g M) := by
  classical
  intro k
  choose Cf hCf hfb using hf
  choose Cg hCg hgb using hg
  let c (i : Fin (k + 1)) : ℝ :=
    (k.choose i.val : ℝ) * Cf i.val * Cg (k - i.val)
  have hc (i : Fin (k + 1)) : 0 ≤ c i :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCf i.val)) (hCg (k - i.val))
  refine ⟨∑ i, c i, Finset.sum_nonneg (fun i _ => hc i), ?_⟩
  intro M x hx
  let term (i : ℕ) : ℝ :=
    (k.choose i : ℝ) * iteratedDeriv i (f M) x * iteratedDeriv (k - i) (g M) x
  have hleibniz : iteratedDeriv k (f M * g M) x = ∑ i : Fin (k + 1), term i.val := by
    rw [Fin.sum_univ_eq_sum_range term]
    exact iteratedDeriv_mul
      (((hfC M).contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le (by simp))
      (((hgC M).contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le (by simp))
  change |iteratedDeriv k (f M * g M) x| ≤ _
  rw [hleibniz, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  unfold term
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (k.choose i.val))]
  have hi : i.val ≤ k := Nat.le_of_lt_succ i.isLt
  have he : (p + 5 * i.val) + (q + 5 * (k - i.val)) = (p + q) + 5 * k := by omega
  calc
    _ ≤ (k.choose i.val : ℝ) * (Cf i.val * M.A⁻¹ ^ (p + 5 * i.val)) *
        (Cg (k - i.val) * M.A⁻¹ ^ (q + 5 * (k - i.val))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hfb i.val M x hx) (Nat.cast_nonneg _))
        (hgb (k - i.val) M x hx) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (hCf i.val) (pow_nonneg M.invA_nonneg _)))
    _ = c i * (M.A⁻¹ ^ (p + 5 * i.val) * M.A⁻¹ ^ (q + 5 * (k - i.val))) := by
      dsimp only [c]
      ring
    _ = _ := by rw [← pow_add, he]

private theorem inverseVelocity_zero_bound (M : PhysicalJetCell) {x : ℝ} (hx : x ∈ Ioo M.a M.b) :
    |M.inverseVelocity x| ≤ 200 * M.A⁻¹ ^ 5 := by
  have h : 0 < M.A ^ 5 / 200 := div_pos (pow_pos M.hA 5) (by norm_num)
  change |(M.velocity x)⁻¹| ≤ _
  rw [abs_of_nonneg (inv_nonneg.mpr (M.velocity_pos hx).le)]
  calc
    _ ≤ (M.A ^ 5 / 200)⁻¹ := (inv_le_inv₀ (M.velocity_pos hx) h).mpr (M.hspeed x hx)
    _ = _ := by rw [inv_div, div_eq_mul_inv, inv_pow]

private theorem inverseVelocity_derivative_formula (M : PhysicalJetCell)
    {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : x ∈ Ioo M.a M.b) :
    iteratedDeriv k M.inverseVelocity x = -(M.velocity x)⁻¹ *
      ∑ i ∈ Finset.range k, (k.choose (i + 1) : ℝ) *
        iteratedDeriv (i + 1) M.velocity x * iteratedDeriv (k - (i + 1)) M.inverseVelocity x := by
  have hprod := iteratedDeriv_mul
    (M.velocity_smooth.contDiffAt.of_le (by simp : (k : ℕ∞ω) ≤ ∞))
    ((M.inverseVelocity_smooth.contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le
      (by simp : (k : ℕ∞ω) ≤ ∞))
  have he : M.velocity * M.inverseVelocity =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    change M.velocity y * (M.velocity y)⁻¹ = 1
    exact mul_inv_cancel₀ (M.velocity_pos hy).ne'
  have hzero := Filter.EventuallyEq.iteratedDeriv_eq k he
  rw [iteratedDeriv_const, ite_eq_right (Nat.ne_of_gt hk), hprod, Finset.sum_range_succ'] at hzero
  simp only [Nat.choose_zero_right, Nat.cast_one, iteratedDeriv_zero, Nat.sub_zero,
    one_mul] at hzero
  have hrec : M.velocity x * iteratedDeriv k M.inverseVelocity x =
      -(∑ i ∈ Finset.range k, (k.choose (i + 1) : ℝ) *
        iteratedDeriv (i + 1) M.velocity x * iteratedDeriv (k - (i + 1)) M.inverseVelocity x) := by
    linarith only [hzero]
  calc
    _ = ((M.velocity x)⁻¹ * M.velocity x) * iteratedDeriv k M.inverseVelocity x := by
      rw [inv_mul_cancel₀ (M.velocity_pos hx).ne', one_mul]
    _ = (M.velocity x)⁻¹ * (M.velocity x * iteratedDeriv k M.inverseVelocity x) := by ring
    _ = _ := by rw [hrec]; ring

private theorem uniformPhysicalJets_inverseVelocity :
    UniformPhysicalJets 5 PhysicalJetCell.inverseVelocity := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · subst k
      exact ⟨200, by norm_num, fun M x hx => by
        simpa only [iteratedDeriv_zero, Nat.mul_zero, add_zero] using inverseVelocity_zero_bound M hx⟩
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    choose C hC hCb using velocity_modelJet_bound
    have hprev (j : Fin k) := ih j.val j.isLt
    choose D hD hDb using hprev
    let d (i : ℕ) : Fin k := ⟨k - (i + 1), Nat.sub_lt hkpos (Nat.succ_pos i)⟩
    let c (i : ℕ) : ℝ := (k.choose (i + 1) : ℝ) * C (i + 1) * D (d i)
    let S : ℝ := ∑ i ∈ Finset.range k, c i
    have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC (i + 1))) (hD (d i)))
    refine ⟨200 * S, mul_nonneg (by norm_num) hS, ?_⟩
    intro M x hx
    let term (i : ℕ) : ℝ := (k.choose (i + 1) : ℝ) * iteratedDeriv (i + 1) M.velocity x *
      iteratedDeriv (k - (i + 1)) M.inverseVelocity x
    have hsum : |∑ i ∈ Finset.range k, term i| ≤ S * M.A⁻¹ ^ (5 * k) := by
      dsimp only [S]
      rw [Finset.sum_mul]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      have hp : 5 + 5 * (k - (i + 1)) ≤ 5 * k := by omega
      have hb : |iteratedDeriv (k - (i + 1)) M.inverseVelocity x| ≤ D (d i) * M.A⁻¹ ^ (5 * k) :=
        (hDb (d i) M x hx).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ M.invA_one_le hp) (hD (d i)))
      unfold term
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (k.choose (i + 1)))]
      calc
        _ ≤ (k.choose (i + 1) : ℝ) * C (i + 1) * (D (d i) * M.A⁻¹ ^ (5 * k)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hCb (i + 1) M x hx) (Nat.cast_nonneg _))
            hb (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC (i + 1)))
        _ = _ := by dsimp only [c]; ring
    rw [inverseVelocity_derivative_formula M hkpos hx, abs_mul, abs_neg]
    calc
      _ ≤ (200 * M.A⁻¹ ^ 5) * (S * M.A⁻¹ ^ (5 * k)) :=
        mul_le_mul (inverseVelocity_zero_bound M hx) hsum (abs_nonneg _)
          (mul_nonneg (by norm_num) (pow_nonneg M.invA_nonneg _))
      _ = (200 * S) * (M.A⁻¹ ^ 5 * M.A⁻¹ ^ (5 * k)) := by ring
      _ = _ := by rw [← pow_add]

def morseCellModelDerivative (r f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv r)⁻¹ * deriv f

private abbrev modelRadiusDerivative (M : PhysicalJetCell) := morseCellModelDerivative M.r

private theorem contDiffOn_modelRadiusDerivative (M : PhysicalJetCell) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo M.a M.b)) :
    ContDiffOn ℝ ∞ (modelRadiusDerivative M f) (Ioo M.a M.b) :=
  M.inverseVelocity_smooth.mul ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp hf).2

private theorem contDiffOn_iterate_modelRadiusDerivative (M : PhysicalJetCell) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo M.a M.b)) (k : ℕ) :
    ContDiffOn ℝ ∞ ((modelRadiusDerivative M)^[k] f) (Ioo M.a M.b) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact contDiffOn_modelRadiusDerivative M ih

private theorem uniformPhysicalJets_iterate {p : ℕ} {f : PhysicalJetCell → ℝ → ℝ}
    (hfC : ∀ M, ContDiffOn ℝ ∞ (f M) (Ioo M.a M.b))
    (hf : UniformPhysicalJets p f) (k : ℕ) :
    UniformPhysicalJets (p + 10 * k) (fun M => (modelRadiusDerivative M)^[k] (f M)) := by
  induction k with
  | zero => simpa only [Nat.mul_zero, add_zero, Function.iterate_zero, id_eq] using hf
  | succ k ih =>
    have hC (M : PhysicalJetCell) :
        ContDiffOn ℝ ∞ (deriv ((modelRadiusDerivative M)^[k] (f M))) (Ioo M.a M.b) :=
      (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp
        (contDiffOn_iterate_modelRadiusDerivative M (hfC M) k) |>.2
    have h := uniformPhysicalJets_mul (fun M => M.inverseVelocity_smooth) hC
      uniformPhysicalJets_inverseVelocity (uniformPhysicalJets_deriv ih)
    have hexp : 5 + (p + 10 * k + 5) = p + 10 * (k + 1) := by omega
    rw [hexp] at h
    have hnext : UniformPhysicalJets (p + 10 * (k + 1))
        (fun M => modelRadiusDerivative M ((modelRadiusDerivative M)^[k] (f M))) := h
    simpa only [Function.iterate_succ_apply'] using hnext

/-- The actual inverse radius chart has the correct domain, left inverse,
and ordinary first derivative. It is smooth on the open physical image. -/
theorem morseCollarCoordinate_physicalChart {s a b : ℝ} {r : ℝ → ℝ}
    (hab : a ≤ b) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ x ∈ Ioo a b, 0 < deriv r x) :
    let X := morseCollarCoordinate r s a b
    let V := Ioo (s * r a) (s * r b)
    LeftInvOn X (fun x => s * r x) (Ioo a b) ∧ MapsTo X V (Ioo a b) ∧
      ContDiffOn ℝ ∞ X V ∧
      ∀ y ∈ V, HasDerivAt X (s⁻¹ * (deriv r (X y))⁻¹) y := by
  dsimp only
  let R : ℝ → ℝ := fun x => s * r x
  let X := morseCollarCoordinate r s a b
  have hR : ContDiff ℝ ∞ R := contDiff_const.mul hr
  have hD (x : ℝ) : HasDerivAt R (s * deriv r x) x :=
    ((hr.differentiable (by simp) x).hasDerivAt).const_mul s
  have hmono : StrictMonoOn R (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) hR.continuous.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hD x).deriv]
    exact mul_pos hs (hv x hx)
  have himage : R '' Ioo a b = Ioo (R a) (R b) :=
    ContinuousOn.image_Ioo_of_strictMonoOn hab hR.continuous.continuousOn hmono
  have hleft : LeftInvOn X R (Ioo a b) :=
    (hmono.mono Ioo_subset_Icc_self).injOn.leftInvOn_invFunOn
  have hlocal (y : ℝ) (hy : y ∈ Ioo (R a) (R b)) :
      X y ∈ Ioo a b ∧ ContDiffAt ℝ ∞ X y ∧
        HasDerivAt X (s⁻¹ * (deriv r (X y))⁻¹) y := by
    rw [← himage] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hXx : X (R x) = x := hleft hx
    have hnear : (fun t => X (R t)) =ᶠ[𝓝 x] (fun t => t) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
      exact hleft ht
    have hstrict : HasStrictDerivAt R (s * deriv r x) x := by
      rw [← (hD x).deriv]
      exact hR.hasStrictDerivAt (by simp)
    have hn : s * deriv r x ≠ 0 := (mul_pos hs (hv x hx)).ne'
    let hd := hstrict.hasStrictFDerivAt_equiv hn
    let e := hd.toOpenPartialHomeomorph R
    have he : e.symm (R x) = x := hd.localInverse_apply_image
    have heD : HasDerivAt e (s * deriv r x) (e.symm (R x)) := by
      rw [he]
      exact hD x
    have heC : ContDiffAt ℝ ∞ (e : ℝ → ℝ) (e.symm (R x)) := by
      rw [he]
      exact hR.contDiffAt
    have hXlocal : ContDiffAt ℝ ∞ (e.symm : ℝ → ℝ) (R x) :=
      e.contDiffAt_symm_deriv hn hd.image_mem_toOpenPartialHomeomorph_target heD heC
    have hX : ContDiffAt ℝ ∞ X (R x) :=
      hXlocal.congr_of_eventuallyEq (hd.localInverse_unique hnear)
    refine ⟨?_, hX, ?_⟩
    · rw [hXx]
      exact hx
    · rw [hXx]
      exact (hstrict.to_local_left_inverse hn hnear).hasDerivAt.congr_deriv
        (by rw [mul_inv_rev, mul_comm])
  exact ⟨hleft, fun y hy => (hlocal y hy).1, fun y hy => (hlocal y hy).2.1.contDiffWithinAt,
    fun y hy => (hlocal y hy).2.2⟩

/-- Iterates of the actual inverse-velocity vector field give ordinary
derivatives on the open physical image, with the radius scaling retained. -/
theorem morseCellPhysical_iteratedDeriv {s a b : ℝ} {r f : ℝ → ℝ}
    (hab : a ≤ b) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ x ∈ Ioo a b, 0 < deriv r x) (hf : ContDiffOn ℝ ∞ f (Ioo a b)) (k : ℕ) :
    EqOn (iteratedDeriv k (fun y => f (morseCollarCoordinate r s a b y)))
      (fun y => s⁻¹ ^ k * ((morseCellModelDerivative r)^[k] f) (morseCollarCoordinate r s a b y))
      (Ioo (s * r a) (s * r b)) := by
  let X := morseCollarCoordinate r s a b
  let T := morseCellModelDerivative r
  let V := Ioo (s * r a) (s * r b)
  change EqOn (iteratedDeriv k (fun y => f (X y))) (fun y => s⁻¹ ^ k * (T^[k] f) (X y)) V
  obtain ⟨_, hmap, _, hX⟩ := morseCollarCoordinate_physicalChart hab hs hr hv
  have hq : ContDiffOn ℝ ∞ (deriv r)⁻¹ (Ioo a b) :=
    ((contDiff_infty_iff_deriv.mp hr).2.contDiffOn).inv (fun x hx => (hv x hx).ne')
  have hsmooth (j : ℕ) : ContDiffOn ℝ ∞ (T^[j] f) (Ioo a b) := by
    induction j with
    | zero => exact hf
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hq.mul ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp ih).2
  induction k with
  | zero =>
    intro y _
    simp only [iteratedDeriv_zero, pow_zero, Function.iterate_zero, id_eq, one_mul]
  | succ k ih =>
    intro y hy
    have hnear : iteratedDeriv k (fun z => f (X z)) =ᶠ[𝓝 y]
        (fun z => s⁻¹ ^ k * (T^[k] f) (X z)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
      exact ih hz
    have hfs : ContDiffAt ℝ ∞ (T^[k] f) (X y) :=
      (hsmooth k).contDiffAt (isOpen_Ioo.mem_nhds (hmap hy))
    have hdF : HasDerivAt (T^[k] f) (deriv (T^[k] f) (X y)) (X y) :=
      (hfs.differentiableAt (by simp)).hasDerivAt
    have hd : HasDerivAt (fun z => s⁻¹ ^ k * (T^[k] f) (X z))
        (s⁻¹ ^ k * (deriv (T^[k] f) (X y) * (s⁻¹ * (deriv r (X y))⁻¹))) y :=
      (hdF.comp y (hX y hy)).const_mul (s⁻¹ ^ k)
    change iteratedDeriv (k + 1) (fun z => f (X z)) y = s⁻¹ ^ (k + 1) * (T^[k + 1] f) (X y)
    rw [iteratedDeriv_succ, hnear.deriv_eq, hd.deriv, Function.iterate_succ_apply', pow_succ]
    change s⁻¹ ^ k * (deriv (T^[k] f) (X y) * (s⁻¹ * (deriv r (X y))⁻¹)) =
      (s⁻¹ ^ k * s⁻¹) * ((deriv r (X y))⁻¹ * deriv (T^[k] f) (X y))
    ring

def morseCellPhysicalHeight (r : ℝ → ℝ) (lam s a b y : ℝ) : ℝ :=
  lam * s * deriv r (morseCollarCoordinate r s a b y)

theorem morseCellPhysicalHeight_smooth {lam s a b : ℝ} {r : ℝ → ℝ}
    (hab : a ≤ b) (hLam : 0 < lam) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ x ∈ Ioo a b, 0 < deriv r x) :
    let w := morseCellPhysicalHeight r lam s a b
    let V := Ioo (s * r a) (s * r b)
    ContDiffOn ℝ ∞ w V ∧ (∀ y ∈ V, 0 < w y) ∧ ContDiffOn ℝ ∞ w⁻¹ V := by
  dsimp only
  obtain ⟨_, hmap, hX, _⟩ := morseCollarCoordinate_physicalChart hab hs hr hv
  have hw : ContDiffOn ℝ ∞ (morseCellPhysicalHeight r lam s a b) (Ioo (s * r a) (s * r b)) :=
    contDiffOn_const.mul ((contDiff_infty_iff_deriv.mp hr).2.contDiffOn.comp hX hmap)
  have hpos (y : ℝ) (hy : y ∈ Ioo (s * r a) (s * r b)) :
      0 < morseCellPhysicalHeight r lam s a b y :=
    mul_pos (mul_pos hLam hs) (hv _ (hmap hy))
  exact ⟨hw, hpos, hw.inv (fun y hy => (hpos y hy).ne')⟩

theorem morseCellPhysicalHeight_value_bounds {lam s a b lo hi : ℝ} {r : ℝ → ℝ}
    (hab : a ≤ b) (hLam : 0 < lam) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ x ∈ Ioo a b, 0 < deriv r x)
    (hbound : ∀ x ∈ Ioo a b, lo ≤ deriv r x ∧ deriv r x ≤ hi)
    {y : ℝ} (hy : y ∈ Ioo (s * r a) (s * r b)) :
    lam * s * lo ≤ morseCellPhysicalHeight r lam s a b y ∧
      morseCellPhysicalHeight r lam s a b y ≤ lam * s * hi := by
  obtain ⟨_, hmap, _, _⟩ := morseCollarCoordinate_physicalChart hab hs hr hv
  have h := hbound _ (hmap hy)
  exact ⟨mul_le_mul_of_nonneg_left h.1 (mul_nonneg hLam.le hs.le),
    mul_le_mul_of_nonneg_left h.2 (mul_nonneg hLam.le hs.le)⟩

private theorem abs_const_mul_physicalJet {c s a b y : ℝ} {r f : ℝ → ℝ}
    (hab : a ≤ b) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ x ∈ Ioo a b, 0 < deriv r x) (hf : ContDiffOn ℝ ∞ f (Ioo a b))
    (hy : y ∈ Ioo (s * r a) (s * r b)) (k : ℕ) :
    |iteratedDeriv k (fun z => c * f (morseCollarCoordinate r s a b z)) y| =
      |c| * s⁻¹ ^ k * |((morseCellModelDerivative r)^[k] f) (morseCollarCoordinate r s a b y)| := by
  rw [iteratedDeriv_const_mul_field c (fun z => f (morseCollarCoordinate r s a b z)),
    morseCellPhysical_iteratedDeriv hab hs hr hv hf k hy, abs_mul, abs_mul,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hs.le) k)]
  ring

/-- The constants precede the model, the two scales and the point of
evaluation. Both estimates are for ordinary physical derivatives. -/
theorem exists_morseCellPhysicalJet_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {A B a b lam s : ℝ} {r : ℝ → ℝ}, 0 < A → A ≤ 1 → 0 ≤ B → B ≤ A →
        a < b → ContDiff ℝ ∞ r →
        (∀ x ∈ Icc a b, exp (-x) ≤ 3) →
        (∀ x ∈ Icc a b, |r x| ≤ 2 ∧ |deriv r x| ≤ 8) →
        (∀ x ∈ Icc a b, deriv (deriv r) x = -morseRho A B x * r x) →
        (∀ x ∈ Ioo a b, A ^ 5 / 200 ≤ deriv r x) →
        0 < lam → 0 < s →
        ∀ y ∈ Ioo (s * r a) (s * r b),
          |iteratedDeriv k (morseCellPhysicalHeight r lam s a b) y| ≤
            C * (lam * s) * s⁻¹ ^ k * A⁻¹ ^ (10 * k) ∧
          |iteratedDeriv k ((morseCellPhysicalHeight r lam s a b)⁻¹) y| ≤
            C * (lam * s)⁻¹ * s⁻¹ ^ k * A⁻¹ ^ (5 + 10 * k) := by
  obtain ⟨Cv, hCv, hbv⟩ := (uniformPhysicalJets_iterate
    (fun M => M.velocity_smooth.contDiffOn) uniformPhysicalJets_velocity k) 0
  obtain ⟨Ci, hCi, hbi⟩ := (uniformPhysicalJets_iterate
    (fun M => M.inverseVelocity_smooth) uniformPhysicalJets_inverseVelocity k) 0
  refine ⟨Cv + Ci, add_nonneg hCv hCi, ?_⟩
  intro A B a b lam s r hA hA₁ hB hBA hab hr hexp hbounded hEq hspeed hLam hs y hy
  let M : PhysicalJetCell := ⟨A, B, a, b, r, hA, hA₁, hB, hBA, hab, hr, hexp, hbounded, hEq, hspeed⟩
  let X := morseCollarCoordinate r s a b
  have hv (x : ℝ) (hx : x ∈ Ioo a b) : 0 < deriv r x := M.velocity_pos hx
  obtain ⟨_, hmap, _, _⟩ := morseCollarCoordinate_physicalChart hab.le hs hr hv
  have hV : |((modelRadiusDerivative M)^[k] M.velocity) (X y)| ≤ Cv * A⁻¹ ^ (10 * k) := by
    simpa only [iteratedDeriv_zero, Nat.mul_zero, add_zero, zero_add] using hbv M (X y) (hmap hy)
  have hI : |((modelRadiusDerivative M)^[k] M.inverseVelocity) (X y)| ≤
      Ci * A⁻¹ ^ (5 + 10 * k) := by
    simpa only [iteratedDeriv_zero, Nat.mul_zero, add_zero] using hbi M (X y) (hmap hy)
  have hV' := hV.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCi)
    (pow_nonneg M.invA_nonneg (10 * k)))
  have hI' := hI.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCv)
    (pow_nonneg M.invA_nonneg (5 + 10 * k)))
  have hS : 0 ≤ s⁻¹ ^ k := pow_nonneg (inv_nonneg.mpr hs.le) k
  have hLamS : 0 < lam * s := mul_pos hLam hs
  have hWinv : (morseCellPhysicalHeight r lam s a b)⁻¹ =
      fun z => (lam * s)⁻¹ * M.inverseVelocity (X z) := by
    funext z
    change (lam * s * deriv r (X z))⁻¹ = (lam * s)⁻¹ * (deriv r (X z))⁻¹
    rw [mul_inv_rev, mul_comm]
  constructor
  · calc
      |iteratedDeriv k (morseCellPhysicalHeight r lam s a b) y| =
          (lam * s) * s⁻¹ ^ k * |((modelRadiusDerivative M)^[k] M.velocity) (X y)| := by
        change |iteratedDeriv k (fun z => (lam * s) * M.velocity (X z)) y| = _
        rw [abs_const_mul_physicalJet (c := lam * s) (f := M.velocity)
          hab.le hs hr hv M.velocity_smooth.contDiffOn hy k, abs_of_pos hLamS]
      _ ≤ (lam * s) * s⁻¹ ^ k * ((Cv + Ci) * A⁻¹ ^ (10 * k)) :=
        mul_le_mul_of_nonneg_left hV' (mul_nonneg hLamS.le hS)
      _ = _ := by ring
  · rw [hWinv]
    calc
      |iteratedDeriv k (fun z => (lam * s)⁻¹ * M.inverseVelocity (X z)) y| =
          (lam * s)⁻¹ * s⁻¹ ^ k * |((modelRadiusDerivative M)^[k] M.inverseVelocity) (X y)| := by
        rw [abs_const_mul_physicalJet (c := (lam * s)⁻¹) (f := M.inverseVelocity)
          hab.le hs hr hv M.inverseVelocity_smooth hy k, abs_of_pos (inv_pos.mpr hLamS)]
      _ ≤ (lam * s)⁻¹ * s⁻¹ ^ k * ((Cv + Ci) * A⁻¹ ^ (5 + 10 * k)) :=
        mul_le_mul_of_nonneg_left hI' (mul_nonneg (inv_nonneg.mpr hLamS.le) hS)
      _ = _ := by ring

/-- A single enlarged model radius carries the physical bounds at every
order and for every positive height and radius scale. -/
theorem exists_morseRadius_with_physicalJets :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ {A B : ℝ}, 0 < B → 4 * B < A → A ≤ 1 / 1000 →
        A ^ 9 / (9 : ℝ) ^ 9 ≤ B → B ≤ A ^ 9 →
        let a := morseCellLeftCut - morseJoinCollarWidth
        let b := morseRightCapEnd A B (1 / 100) + morseJoinCollarWidth
        ∃ r : ℝ → ℝ, ContDiff ℝ ∞ r ∧ r (morseRightTurn A B) = 1 ∧
          deriv r (morseRightTurn A B) = (1 / 100 : ℝ) * A ^ 5 ∧
          (∀ x ∈ Icc a b, deriv (deriv r) x = -morseRho A B x * r x) ∧
          (∀ x ∈ Icc a b, exp (-x) ≤ 3 ∧ |r x| ≤ 2 ∧
            A ^ 5 / 200 ≤ deriv r x ∧ |deriv r x| ≤ 8) ∧
          ∀ (lam s : ℝ), 0 < lam → 0 < s → ∀ k : ℕ, ∀ y ∈ Ioo (s * r a) (s * r b),
            |iteratedDeriv k (morseCellPhysicalHeight r lam s a b) y| ≤
              C k * (lam * s) * s⁻¹ ^ k * A⁻¹ ^ (10 * k) ∧
            |iteratedDeriv k ((morseCellPhysicalHeight r lam s a b)⁻¹) y| ≤
              C k * (lam * s)⁻¹ * s⁻¹ ^ k * A⁻¹ ^ (5 + 10 * k) := by
  choose C hC hb using exists_morseCellPhysicalJet_bound
  refine ⟨C, hC, ?_⟩
  intro A B hB hAB hA₀ hBAlo hBAhi
  let a := morseCellLeftCut - morseJoinCollarWidth
  let b := morseRightCapEnd A B (1 / 100) + morseJoinCollarWidth
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hA₁ : A ≤ 1 := hA₀.trans (by norm_num)
  have hBA : B ≤ A := by linarith only [hB, hAB]
  have hab : a < b := by
    have hleft := morseCellLeftCut_lt_rightTurn hB hAB
    have hright := morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)
    have hh : 0 < morseJoinCollarWidth := by norm_num [morseJoinCollarWidth]
    dsimp only [a, b, morseRightCapEnd]
    linarith only [hleft, hright, hh]
  obtain ⟨_, _, he⟩ := exists_morseRadius_with_modelJets
  obtain ⟨r, hr, hr₀, hv₀, hEq, hpoint, _⟩ := he hB hAB hA₀ hBAlo hBAhi
  refine ⟨r, hr, hr₀, hv₀, hEq, hpoint, ?_⟩
  intro lam s hLam hs k y hy
  exact hb k hA hA₁ hB.le hBA hab hr (fun x hx => (hpoint x hx).1)
    (fun x hx => ⟨(hpoint x hx).2.1, (hpoint x hx).2.2.2⟩) hEq
    (fun x hx => (hpoint x (Ioo_subset_Icc_self hx)).2.2.1) hLam hs y hy

end ContinuousFlexibility.Radial
