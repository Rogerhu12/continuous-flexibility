import ContinuousFlexibility.Radial.InnerDirichletDomain

/-!
# The exact local Poisson cutoff decomposition

The Poisson column and the Dirichlet inverse below are witnesses for the same
actual interval problem. Subtracting a smooth boundary lift gives a genuine
zero-endpoint field; the Dirichlet domain theorem and uniqueness then identify
its correction. The single symmetric scalar border is retained, and in the
unbordered case the scalar remains zero.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

/-- The inside and outside representative statements used by R09 combine
into one global equality with the actual zero extension. -/
theorem innerPoisson_eq_indicator {a b : ℝ} {P : RadialL2} {p : ℝ → ℝ}
    (hin : (P : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] p)
    (hout : (P : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0)) :
    (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p := by
  have hi := (ae_restrict_iff' measurableSet_Ioo).mp hin
  have ho := (ae_restrict_iff' measurableSet_Ioo.compl).mp hout
  filter_upwards [hi, ho] with x hx hy
  by_cases hxi : x ∈ Ioo a b
  · rw [Set.indicator_of_mem hxi]
    exact hx hxi
  · rw [Set.indicator_of_notMem hxi]
    exact hy hxi

/-- R09's endpoint germs and open-interval smoothness give precisely the
closed-interval regularity required by the Dirichlet domain bridge. -/
theorem innerPoisson_contDiff_closed {a b : ℝ} {p : ℝ → ℝ}
    (hleft : ContDiffAt ℝ ∞ p a) (hright : ContDiffAt ℝ ∞ p b)
    (hinside : ContDiffOn ℝ ∞ p (Ioo a b)) :
    ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x := by
  intro x hx
  by_cases ha : x = a
  · simpa only [ha] using hleft
  by_cases hb : x = b
  · simpa only [hb] using hright
  exact hinside.contDiffAt (isOpen_Ioo.mem_nhds
    ⟨lt_of_le_of_ne hx.1 (Ne.symm ha), lt_of_le_of_ne hx.2 hb⟩)

/-- The classical buffer equation upgrades the `C²` regularity supplied for
the buffer minimizer to smoothness in the open buffer. -/
theorem innerPoisson_contDiffOn_of_secondOrder {s : Set ℝ} (hs : IsOpen s)
    {V p : ℝ → ℝ} (hV : ContDiffOn ℝ ∞ V s) (hp : ContDiffOn ℝ 2 p s)
    (heq : ∀ x ∈ s, deriv (deriv p) x = V x * p x) :
    ContDiffOn ℝ ∞ p s := by
  have hpD : DifferentiableOn ℝ p s := hp.differentiableOn (by norm_num)
  have hpd : ContDiffOn ℝ 1 (deriv p) s := hp.deriv_of_isOpen hs (by norm_num)
  have hpdD : DifferentiableOn ℝ (deriv p) s := hpd.differentiableOn (by norm_num)
  have hnat : ∀ n : ℕ, ContDiffOn ℝ n p s ∧ ContDiffOn ℝ n (deriv p) s := by
    intro n
    induction n with
    | zero =>
      exact ⟨contDiffOn_zero.mpr hp.continuousOn, contDiffOn_zero.mpr hpd.continuousOn⟩
    | succ n ih =>
      have hnext : ContDiffOn ℝ ((n : ℕ∞ω) + 1) p s :=
        (contDiffOn_succ_iff_deriv_of_isOpen hs).mpr ⟨hpD, by simp, ih.2⟩
      have hdnext : ContDiffOn ℝ ((n : ℕ∞ω) + 1) (deriv p) s := by
        apply (contDiffOn_succ_iff_deriv_of_isOpen hs).mpr
        refine ⟨hpdD, by simp, ?_⟩
        exact ((hV.of_le (by simp)).mul ih.1).congr heq
      exact ⟨by simpa only [Nat.cast_add, Nat.cast_one] using hnext,
        by simpa only [Nat.cast_add, Nat.cast_one] using hdnext⟩
  exact contDiffOn_infty.mpr (fun n => (hnat n).1)

/-- A cutoff needs regularity of the buffer representative only on its
closed support. Outside that support the product vanishes on a neighbourhood. -/
theorem innerPoisson_cutoff_smooth {a b : ℝ} {χ pin : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hpin : ∀ x ∈ Icc a b, x ∈ tsupport χ → ContDiffAt ℝ ∞ pin x) :
    ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ (fun y => χ y * pin y) x := by
  intro x hx
  by_cases hs : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hpin x hx hs)
  · apply contDiffAt_const.congr_of_eventuallyEq
    have hz : χ =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hs
    filter_upwards [hz] with y hy
    change χ y * pin y = 0
    rw [hy, zero_mul]

private theorem innerPoisson_second_deriv_mul {x : ℝ} {χ pin : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hp : ContDiffAt ℝ ∞ pin x) :
    deriv (deriv (fun y => χ y * pin y)) x =
      deriv (deriv χ) x * pin x + 2 * deriv χ x * deriv pin x +
        χ x * deriv (deriv pin) x := by
  have hχd := (contDiff_infty_iff_deriv.mp hχ).2
  have hχD := hχ.differentiable (by simp)
  have hpinD := hp.differentiableAt (by simp)
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ pin y := by
    have hc : ContDiffAt ℝ 1 pin x := hp.of_le (by simp)
    filter_upwards [hc.eventually (by simp)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hfirst : deriv (fun y => χ y * pin y) =ᶠ[𝓝 x]
      (fun y => deriv χ y * pin y + χ y * deriv pin y) := by
    filter_upwards [hnear] with y hy
    exact deriv_mul (hχD y) hy
  have hsecond :=
    (((hχd.differentiable (by simp) x).hasDerivAt.fun_mul hpinD.hasDerivAt).fun_add
      ((hχD x).hasDerivAt.fun_mul
        ((hp.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt)).deriv
  rw [hfirst.deriv_eq, hsecond]
  ring

/-- The cutoff source is the actual ordinary commutator, including points
outside the buffer where the cutoff vanishes on a neighbourhood. -/
theorem innerPoisson_cutoff_expression {a b : ℝ} {V χ pin : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hpin : ∀ x ∈ Icc a b, x ∈ tsupport χ → ContDiffAt ℝ ∞ pin x)
    (heq : ∀ x ∈ Ioo a b, x ∈ tsupport χ →
      -deriv (deriv pin) x + V x * pin x = 0) :
    ∀ x ∈ Ioo a b,
      -deriv (deriv (fun y => χ y * pin y)) x + V x * (χ x * pin x) =
        -deriv (deriv χ) x * pin x - 2 * deriv χ x * deriv pin x := by
  intro x hx
  by_cases hs : x ∈ tsupport χ
  · rw [innerPoisson_second_deriv_mul hχ (hpin x (Ioo_subset_Icc_self hx) hs)]
    have h := heq x hx hs
    nlinarith
  · have hz : χ =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hs
    have hprod : (fun y => χ y * pin y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hz] with y hy
      change χ y * pin y = 0
      rw [hy, zero_mul]
    have hz₀ : χ x = 0 := hz.eq_of_nhds
    have hz₁ : deriv χ x = 0 := hz.deriv_eq.trans (deriv_const x 0)
    have hz₂ : deriv (deriv χ) x = 0 := by
      rw [hz.deriv.deriv_eq]
      simp only [deriv_const, deriv_zero, Pi.zero_apply]
    have hp₂ : deriv (deriv (fun y => χ y * pin y)) x = 0 := by
      rw [hprod.deriv.deriv_eq]
      simp only [deriv_const, deriv_zero, Pi.zero_apply]
    rw [hz₀, hz₁, hz₂, hp₂]
    ring

private theorem innerPoisson_second_deriv_sub {a b x : ℝ} {u v : ℝ → ℝ}
    (hu : ∀ y ∈ Icc a b, ContDiffAt ℝ ∞ u y)
    (hv : ∀ y ∈ Icc a b, ContDiffAt ℝ ∞ v y) (hx : x ∈ Ioo a b) :
    deriv (deriv (fun y => u y - v y)) x = deriv (deriv u) x - deriv (deriv v) x := by
  have hfirst : deriv (fun y => u y - v y) =ᶠ[𝓝 x]
      (fun y => deriv u y - deriv v y) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact deriv_sub ((hu y (Ioo_subset_Icc_self hy)).differentiableAt (by simp))
      ((hv y (Ioo_subset_Icc_self hy)).differentiableAt (by simp))
  rw [hfirst.deriv_eq]
  exact deriv_sub
    (((hu x (Ioo_subset_Icc_self hx)).derivWithin (m := ∞) (by simp)).differentiableAt (by simp))
    (((hv x (Ioo_subset_Icc_self hx)).derivWithin (m := ∞) (by simp)).differentiableAt (by simp))

private theorem innerPoisson_lift_border_pairing_zero {a b : ℝ}
    {g L : RadialL2} {column lift : ℝ → ℝ}
    (hg : (g : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator column)
    (hL : (L : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator lift)
    (hdisjoint : Disjoint (Function.support column) (Function.support lift)) :
    ⟪g, L⟫_ℝ = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hg, hL] with x hgx hLx
  rw [hgx, hLx]
  by_cases hx : x ∈ Ioo a b
  · simp only [Set.indicator_of_mem hx, RCLike.inner_apply, conj_trivial]
    by_cases hc : column x = 0
    · rw [hc, mul_zero]
    · have hl : lift x = 0 := by
        by_contra hn
        exact Set.disjoint_left.mp hdisjoint hc hn
      rw [hl, zero_mul]
  · simp only [Set.indicator_of_notMem hx, inner_zero_left]

/-- A Poisson column is its actual boundary lift minus the correction by the
same Dirichlet inverse. The source is the differential expression of the
lift; the decomposition itself is derived from the true interval graph.

For a buffer cutoff, `lift = χ * pin` and the source is the ordinary cutoff
commutator. The support separation is the geometric fact that the temporary
border is strictly beyond the buffer. -/
theorem innerPoisson_lift_sub_dirichlet {a b : ℝ}
    {V column p lift : ℝ → ℝ} {g P L f : RadialL2} {scalar : ℝ} (bordered : Bool)
    (G : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
    (hab : a < b) (hV : ContinuousOn V (Icc a b))
    (hp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    (hlift : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ lift x)
    (hleft : lift a = p a) (hright : lift b = p b)
    (hg : (g : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator column)
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p)
    (hL : (L : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator lift)
    (hf : (f : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (fun x => -deriv (deriv lift) x + V x * lift x))
    (hdisjoint : Disjoint (Function.support column) (Function.support lift))
    (hrow : if bordered then ⟪g, P⟫_ℝ = 0 else scalar = 0)
    (heq : ∀ x ∈ Ioo a b,
      -deriv (deriv p) x + V x * p x + scalar * column x = 0)
    (hunique : ∀ U F : RadialL2 × ℝ,
      BorderedIntervalGraph V g bordered a b U F → G F = U) :
    (P, scalar) = (L, 0) - G (f, 0) := by
  let ψ : ℝ → ℝ := fun x => lift x - p x
  have hψ : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ ψ x :=
    fun x hx => (hlift x hx).sub (hp x hx)
  have hψa : ψ a = 0 := sub_eq_zero.mpr hleft
  have hψb : ψ b = 0 := sub_eq_zero.mpr hright
  have hLP : ((L - P : RadialL2) : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator ψ := by
    filter_upwards [Lp.coeFn_sub L P, hL, hP] with x hsub hLx hPx
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hLx, hPx]
    by_cases hx : x ∈ Ioo a b
    · simp only [Set.indicator_of_mem hx, ψ]
    · simp only [Set.indicator_of_notMem hx, sub_self]
  have hsource : ((f + scalar • g : RadialL2) : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (fun x => -deriv (deriv ψ) x + V x * ψ x) := by
    filter_upwards [Lp.coeFn_add f (scalar • g), Lp.coeFn_smul scalar g, hf, hg]
      with x hadd hsmul hfx hgx
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hfx, hgx]
    by_cases hx : x ∈ Ioo a b
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      rw [show deriv (deriv ψ) x = deriv (deriv lift) x - deriv (deriv p) x from
        innerPoisson_second_deriv_sub hlift hp hx]
      have h := heq x hx
      dsimp only [ψ]
      nlinarith
    · simp only [Set.indicator_of_notMem hx, mul_zero, add_zero]
  have hgraph : IntervalFormGraph V a b (L - P) (f + scalar • g) :=
    intervalFormGraph_of_smooth_zero_endpoints hab hV hψ hψa hψb hLP hsource
  have hLrow := innerPoisson_lift_border_pairing_zero hg hL hdisjoint
  have hsolution : BorderedIntervalGraph V g bordered a b ((L, 0) - (P, scalar)) (f, 0) := by
    cases bordered with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hrow
      simp only [BorderedIntervalGraph, Bool.false_eq_true, ite_false, Prod.mk_sub_mk, zero_sub]
      refine ⟨?_, by rw [hrow, neg_zero], rfl⟩
      simpa only [hrow, zero_smul, add_zero] using hgraph
    | true =>
      simp only [ite_true] at hrow
      simp only [BorderedIntervalGraph, ite_true, Prod.mk_sub_mk, zero_sub]
      refine ⟨?_, ?_⟩
      · simpa only [neg_smul, sub_neg_eq_add] using hgraph
      · rw [inner_sub_right, hLrow, hrow, sub_self]
  rw [hunique _ _ hsolution]
  abel

/-- Specialization to the genuine cutoff of a buffer solution. The forcing
is the commutator, not an assumed inverse residual or decomposition. -/
theorem innerPoisson_cutoff_sub_dirichlet {a b : ℝ}
    {V column p χ pin : ℝ → ℝ} {g P L f : RadialL2} {scalar : ℝ} (bordered : Bool)
    (G : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
    (hab : a < b) (hV : ContinuousOn V (Icc a b))
    (hp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x) (hχ : ContDiff ℝ ∞ χ)
    (hpin : ∀ x ∈ Icc a b, x ∈ tsupport χ → ContDiffAt ℝ ∞ pin x)
    (hpinEq : ∀ x ∈ Ioo a b, x ∈ tsupport χ →
      -deriv (deriv pin) x + V x * pin x = 0)
    (hleft : χ a * pin a = p a) (hright : χ b * pin b = p b)
    (hg : (g : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator column)
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p)
    (hL : (L : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (fun x => χ x * pin x))
    (hf : (f : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (fun x =>
        -deriv (deriv χ) x * pin x - 2 * deriv χ x * deriv pin x))
    (hdisjoint : Disjoint (Function.support column) (Function.support χ))
    (hrow : if bordered then ⟪g, P⟫_ℝ = 0 else scalar = 0)
    (heq : ∀ x ∈ Ioo a b,
      -deriv (deriv p) x + V x * p x + scalar * column x = 0)
    (hunique : ∀ U F : RadialL2 × ℝ,
      BorderedIntervalGraph V g bordered a b U F → G F = U) :
    (P, scalar) = (L, 0) - G (f, 0) := by
  apply innerPoisson_lift_sub_dirichlet bordered G hab hV hp
    (innerPoisson_cutoff_smooth hχ hpin) hleft hright hg hP hL
  · have hformula := innerPoisson_cutoff_expression hχ hpin hpinEq
    filter_upwards [hf] with x hfx
    rw [hfx]
    by_cases hx : x ∈ Ioo a b
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hformula x hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  · apply Set.disjoint_left.mpr
    intro x hx hprod
    have hχx : χ x ≠ 0 := by
      intro hz
      exact hprod (show χ x * pin x = 0 by rw [hz, zero_mul])
    exact Set.disjoint_left.mp hdisjoint hx hχx
  · exact hrow
  · exact heq
  · exact hunique

end ContinuousFlexibility.Radial
