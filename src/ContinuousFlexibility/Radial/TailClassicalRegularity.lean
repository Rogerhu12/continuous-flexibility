import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Classical regularity of the tail first-order system

The state consists of a value `u` and its flux `v = p u'`. The equations
`u' = v / p` and `v' = -Λ p u` bootstrap finite differentiability orders
together. The within-set formulation also applies at a regular entrance:
it asserts one-sided smoothness there and does not assert a smooth
extension across that entrance.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology ContDiff NNReal

def TailFirstOrderSystem (p : ℝ → ℝ) (Λ : ℝ) (u v : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt u (v x / p x) x ∧ HasDerivAt v (-Λ * p x * u x) x

def TailFirstOrderSystemWithin (p : ℝ → ℝ) (Λ : ℝ)
    (u v : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivWithinAt u (v x / p x) s x ∧
    HasDerivWithinAt v (-Λ * p x * u x) s x

theorem TailFirstOrderSystem.mono {p u v : ℝ → ℝ} {Λ : ℝ} {s t : Set ℝ}
    (h : TailFirstOrderSystem p Λ u v s) (ht : t ⊆ s) :
    TailFirstOrderSystem p Λ u v t := fun x hx => h x (ht hx)

theorem TailFirstOrderSystem.within {p u v : ℝ → ℝ} {Λ : ℝ} {s : Set ℝ}
    (h : TailFirstOrderSystem p Λ u v s) : TailFirstOrderSystemWithin p Λ u v s :=
  fun x hx => ⟨(h x hx).1.hasDerivWithinAt, (h x hx).2.hasDerivWithinAt⟩

/-- Simultaneous finite-order induction gives smoothness on any set with
unique derivatives, including a half-open entrance interval. -/
theorem tailFirstOrderSystemWithin_contDiffOn {p u v : ℝ → ℝ} {Λ : ℝ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hp : ContDiffOn ℝ ∞ p s)
    (hp₀ : ∀ x ∈ s, p x ≠ 0) (h : TailFirstOrderSystemWithin p Λ u v s) :
    ContDiffOn ℝ ∞ u s ∧ ContDiffOn ℝ ∞ v s := by
  have hdu : DifferentiableOn ℝ u s := fun x hx => (h x hx).1.differentiableWithinAt
  have hdv : DifferentiableOn ℝ v s := fun x hx => (h x hx).2.differentiableWithinAt
  have hreg : ∀ n : ℕ, ContDiffOn ℝ n u s ∧ ContDiffOn ℝ n v s := by
    intro n
    induction n with
    | zero =>
      exact ⟨contDiffOn_zero.mpr hdu.continuousOn, contDiffOn_zero.mpr hdv.continuousOn⟩
    | succ n ih =>
      have hpn : ContDiffOn ℝ n p s := (contDiffOn_infty.mp hp) n
      have hu' : ContDiffOn ℝ n (derivWithin u s) s :=
        (ih.2.div hpn hp₀).congr (fun x hx => (h x hx).1.derivWithin (hs x hx))
      have hv_rhs : ContDiffOn ℝ n (fun x => -Λ * p x * u x) s :=
        (contDiffOn_const.mul hpn).mul ih.1
      have hv' : ContDiffOn ℝ n (derivWithin v s) s :=
        hv_rhs.congr (fun x hx => (h x hx).2.derivWithin (hs x hx))
      have hu_next : ContDiffOn ℝ ((n : ℕ∞ω) + 1) u s :=
        (contDiffOn_succ_iff_derivWithin hs).mpr ⟨hdu, by simp, hu'⟩
      have hv_next : ContDiffOn ℝ ((n : ℕ∞ω) + 1) v s :=
        (contDiffOn_succ_iff_derivWithin hs).mpr ⟨hdv, by simp, hv'⟩
      exact ⟨by simpa only [Nat.cast_add, Nat.cast_one] using hu_next,
        by simpa only [Nat.cast_add, Nat.cast_one] using hv_next⟩
  exact ⟨contDiffOn_infty.mpr (fun n => (hreg n).1),
    contDiffOn_infty.mpr (fun n => (hreg n).2)⟩

theorem tailFirstOrderSystem_contDiffOn {p u v : ℝ → ℝ} {Λ : ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hp : ContDiffOn ℝ ∞ p s)
    (hp₀ : ∀ x ∈ s, p x ≠ 0) (h : TailFirstOrderSystem p Λ u v s) :
    ContDiffOn ℝ ∞ u s ∧ ContDiffOn ℝ ∞ v s :=
  tailFirstOrderSystemWithin_contDiffOn hs.uniqueDiffOn hp hp₀ h.within

/-- On an open set the first-order state has its actual conormal flux. -/
theorem tailFirstOrderSystem_flux_eq {p u v : ℝ → ℝ} {Λ : ℝ} {s : Set ℝ}
    (hp₀ : ∀ x ∈ s, p x ≠ 0) (h : TailFirstOrderSystem p Λ u v s) :
    EqOn (fun x => p x * deriv u x) v s := by
  intro x hx
  rw [(h x hx).1.deriv]
  field_simp [hp₀ x hx] <;> ring

theorem tailFirstOrderSystem_hasDerivAt_flux {p u v : ℝ → ℝ} {Λ : ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hp₀ : ∀ x ∈ s, p x ≠ 0)
    (h : TailFirstOrderSystem p Λ u v s) :
    ∀ x ∈ s, HasDerivAt (fun y => p y * deriv u y) (-Λ * p x * u x) x := by
  intro x hx
  apply (h x hx).2.congr_of_eventuallyEq
  exact Filter.eventually_of_mem (hs.mem_nhds hx)
    (fun y hy => tailFirstOrderSystem_flux_eq hp₀ h hy)

/-- The smooth first-order state solves the stated physical second-order
equation on the open interval. -/
theorem tailFirstOrderSystem_equation {p u v : ℝ → ℝ} {Λ : ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hp₀ : ∀ x ∈ s, p x ≠ 0)
    (h : TailFirstOrderSystem p Λ u v s) :
    ∀ x ∈ s, deriv (fun y => p y * deriv u y) x + Λ * p x * u x = 0 := by
  intro x hx
  rw [(tailFirstOrderSystem_hasDerivAt_flux hs hp₀ h x hx).deriv]
  ring

/-- A derivative which agrees with a continuous right-hand side on both
sides of an interior node also exists at that node. -/
theorem tail_hasDerivAt_of_punctured_Ioo {a b x : ℝ} {f g : ℝ → ℝ}
    (hx : x ∈ Ioo a b) (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hd : ∀ y ∈ Ioo a b, y ≠ x → HasDerivAt f (g y) y) :
    HasDerivAt f (g x) x := by
  have hleft (y : ℝ) (hy : y ∈ Ioo a x) : HasDerivAt f (g y) y :=
    hd y ⟨hy.1, hy.2.trans hx.2⟩ (ne_of_lt hy.2)
  have hright (y : ℝ) (hy : y ∈ Ioo x b) : HasDerivAt f (g y) y :=
    hd y ⟨hx.1.trans hy.1, hy.2⟩ (ne_of_gt hy.1)
  have hlimleft : Tendsto (deriv f) (𝓝[<] x) (𝓝 (g x)) := by
    apply (hg.mono_left nhdsWithin_le_nhds).congr'
    exact Filter.eventually_of_mem (Ioo_mem_nhdsLT hx.1)
      (fun y hy => (hleft y hy).deriv.symm)
  have hlimright : Tendsto (deriv f) (𝓝[>] x) (𝓝 (g x)) := by
    apply (hg.mono_left nhdsWithin_le_nhds).congr'
    exact Filter.eventually_of_mem (Ioo_mem_nhdsGT hx.2)
      (fun y hy => (hright y hy).deriv.symm)
  have hL := hasDerivWithinAt_Iic_of_tendsto_deriv
    (fun y hy => (hleft y hy).differentiableAt.differentiableWithinAt)
    hf.continuousWithinAt (Ioo_mem_nhdsLT hx.1) hlimleft
  have hR := hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun y hy => (hright y hy).differentiableAt.differentiableWithinAt)
    hf.continuousWithinAt (Ioo_mem_nhdsGT hx.2) hlimright
  simpa using hL.union hR

/-- Matching continuous values and fluxes across a node preserves the
first-order equations there. No differentiability at that node is assumed. -/
theorem tailFirstOrderSystem_at_of_punctured_Ioo
    {a b x Λ : ℝ} {p u v : ℝ → ℝ}
    (hx : x ∈ Ioo a b) (hp : ContinuousAt p x) (hp₀ : p x ≠ 0)
    (hu : ContinuousAt u x) (hv : ContinuousAt v x)
    (h : ∀ y ∈ Ioo a b, y ≠ x →
      HasDerivAt u (v y / p y) y ∧ HasDerivAt v (-Λ * p y * u y) y) :
    HasDerivAt u (v x / p x) x ∧ HasDerivAt v (-Λ * p x * u x) x := by
  constructor
  · exact tail_hasDerivAt_of_punctured_Ioo hx hu (hv.div hp hp₀)
      (fun y hy hne => (h y hy hne).1)
  · exact tail_hasDerivAt_of_punctured_Ioo hx hv
      ((continuousAt_const.mul hp).mul hu) (fun y hy hne => (h y hy hne).2)

/-- The Wronskian in value-and-flux coordinates. -/
def tailFirstOrderWronskian (u v U V : ℝ → ℝ) (x : ℝ) : ℝ :=
  u x * V x - v x * U x

theorem tailFirstOrderSystem_hasDerivAt_wronskian
    {p u v U V : ℝ → ℝ} {Λ : ℝ} {s : Set ℝ}
    (h : TailFirstOrderSystem p Λ u v s) (h' : TailFirstOrderSystem p Λ U V s) :
    ∀ x ∈ s, HasDerivAt (tailFirstOrderWronskian u v U V) 0 x := by
  intro x hx
  exact (((h x hx).1.mul (h' x hx).2).sub
    ((h x hx).2.mul (h' x hx).1)).congr_deriv (by ring)

theorem tailFirstOrderSystem_wronskian_const
    {p u v U V : ℝ → ℝ} {Λ : ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hc : IsPreconnected s)
    (h : TailFirstOrderSystem p Λ u v s) (h' : TailFirstOrderSystem p Λ U V s) :
    ∀ x ∈ s, ∀ y ∈ s,
      tailFirstOrderWronskian u v U V x = tailFirstOrderWronskian u v U V y := by
  have hd := tailFirstOrderSystem_hasDerivAt_wronskian h h'
  exact hs.is_const_of_deriv_eq_zero hc
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv)

private def tailFirstOrderField (p : ℝ → ℝ) (Λ x : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((p x)⁻¹ * z.2, -(Λ * p x) * z.1)

private theorem tailFirstOrderField_lipschitz {p : ℝ → ℝ} {Λ x : ℝ} {K : ℝ≥0}
    (hp : ‖(p x)⁻¹‖ ≤ (K : ℝ)) (hΛp : ‖Λ * p x‖ ≤ (K : ℝ)) :
    LipschitzWith K (tailFirstOrderField p Λ x) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm, tailFirstOrderField, Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
  rw [← mul_sub, ← mul_sub, norm_mul, norm_mul, norm_neg]
  exact max_le
    (mul_le_mul hp (le_max_right _ _) (norm_nonneg _) K.2)
    (mul_le_mul hΛp (le_max_left _ _) (norm_nonneg _) K.2)

private theorem tailFirstOrderSystem_hasDerivAt_state
    {p u v : ℝ → ℝ} {Λ : ℝ} {s : Set ℝ}
    (h : TailFirstOrderSystem p Λ u v s) {x : ℝ} (hx : x ∈ s) :
    HasDerivAt (fun t => (u t, v t)) (tailFirstOrderField p Λ x (u x, v x)) x := by
  have heq : tailFirstOrderField p Λ x (u x, v x) =
      (v x / p x, -Λ * p x * u x) := by
    apply Prod.ext <;> dsimp only [tailFirstOrderField] <;> ring
  rw [heq]
  exact (h x hx).1.prodMk (h x hx).2

/-- On a compact interval, initial value and initial flux determine the
whole state. The coefficient bound is obtained from continuity on that
interval and the standard ODE uniqueness theorem. -/
theorem tailFirstOrderSystem_eqOn_Icc
    {p u v U V : ℝ → ℝ} {Λ a b x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc a b) (hp : ContinuousOn p (Icc a b))
    (hp₀ : ∀ x ∈ Icc a b, p x ≠ 0)
    (h : TailFirstOrderSystem p Λ u v (Icc a b))
    (h' : TailFirstOrderSystem p Λ U V (Icc a b))
    (hu₀ : u x₀ = U x₀) (hv₀ : v x₀ = V x₀) :
    ∀ x ∈ Icc a b, u x = U x ∧ v x = V x := by
  have hcoeff : ContinuousOn (fun x => ((p x)⁻¹, Λ * p x)) (Icc a b) :=
    (hp.inv₀ hp₀).prodMk (continuousOn_const.mul hp)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hcoeff
  let K : ℝ≥0 := ⟨max 0 C, le_max_left _ _⟩
  have hLip (x : ℝ) (hx : x ∈ Icc a b) :
      LipschitzWith K (tailFirstOrderField p Λ x) := by
    have hmax : max ‖(p x)⁻¹‖ ‖Λ * p x‖ ≤ (K : ℝ) := by
      simpa only [Prod.norm_def] using (hC x hx).trans (le_max_right 0 C)
    exact tailFirstOrderField_lipschitz
      ((le_max_left _ _).trans hmax) ((le_max_right _ _).trans hmax)
  have hd (x : ℝ) (hx : x ∈ Icc a b) := tailFirstOrderSystem_hasDerivAt_state h hx
  have hd' (x : ℝ) (hx : x ∈ Icc a b) := tailFirstOrderSystem_hasDerivAt_state h' hx
  have hstart : (u x₀, v x₀) = (U x₀, V x₀) := Prod.ext hu₀ hv₀
  have hleft : Icc a x₀ ⊆ Icc a b := Icc_subset_Icc_right hx₀.2
  have hright : Icc x₀ b ⊆ Icc a b := Icc_subset_Icc_left hx₀.1
  have hL := ODE_solution_unique_of_mem_Icc_left
    (v := tailFirstOrderField p Λ) (s := fun _ => univ)
    (f := fun x => (u x, v x)) (g := fun x => (U x, V x)) (a := a) (b := x₀)
    (fun x hx => (hLip x (hleft (Ioc_subset_Icc_self hx))).lipschitzOnWith)
    ((HasDerivAt.continuousOn hd).mono hleft)
    (fun x hx => (hd x (hleft (Ioc_subset_Icc_self hx))).hasDerivWithinAt)
    (fun _ _ => mem_univ _)
    ((HasDerivAt.continuousOn hd').mono hleft)
    (fun x hx => (hd' x (hleft (Ioc_subset_Icc_self hx))).hasDerivWithinAt)
    (fun _ _ => mem_univ _) hstart
  have hR := ODE_solution_unique_of_mem_Icc_right
    (v := tailFirstOrderField p Λ) (s := fun _ => univ)
    (f := fun x => (u x, v x)) (g := fun x => (U x, V x)) (a := x₀) (b := b)
    (fun x hx => (hLip x (hright (Ico_subset_Icc_self hx))).lipschitzOnWith)
    ((HasDerivAt.continuousOn hd).mono hright)
    (fun x hx => (hd x (hright (Ico_subset_Icc_self hx))).hasDerivWithinAt)
    (fun _ _ => mem_univ _)
    ((HasDerivAt.continuousOn hd').mono hright)
    (fun x hx => (hd' x (hright (Ico_subset_Icc_self hx))).hasDerivWithinAt)
    (fun _ _ => mem_univ _) hstart
  intro x hx
  have hstate : (u x, v x) = (U x, V x) := by
    by_cases hxx₀ : x ≤ x₀
    · exact hL ⟨hx.1, hxx₀⟩
    · exact hR ⟨le_of_lt (lt_of_not_ge hxx₀), hx.2⟩
  exact ⟨congrArg Prod.fst hstate, congrArg Prod.snd hstate⟩

/-- Initial-value uniqueness on the whole open interval follows by
restricting to the compact interval between the two points. No global
bound on the possibly singular coefficient is required. -/
theorem tailFirstOrderSystem_eq_of_initial
    {p u v U V : ℝ → ℝ} {Λ a b x₀ : ℝ}
    (hx₀ : x₀ ∈ Ioo a b) (hp : ContinuousOn p (Ioo a b))
    (hp₀ : ∀ x ∈ Ioo a b, p x ≠ 0)
    (h : TailFirstOrderSystem p Λ u v (Ioo a b))
    (h' : TailFirstOrderSystem p Λ U V (Ioo a b))
    (hu₀ : u x₀ = U x₀) (hv₀ : v x₀ = V x₀) :
    ∀ x ∈ Ioo a b, u x = U x ∧ v x = V x := by
  intro x hx
  have hsubset : Icc (min x₀ x) (max x₀ x) ⊆ Ioo a b := by
    intro t ht
    exact ⟨(lt_min hx₀.1 hx.1).trans_le ht.1,
      ht.2.trans_lt (max_lt hx₀.2 hx.2)⟩
  have hx₀' : x₀ ∈ Icc (min x₀ x) (max x₀ x) :=
    ⟨min_le_left _ _, le_max_left _ _⟩
  have hx' : x ∈ Icc (min x₀ x) (max x₀ x) :=
    ⟨min_le_right _ _, le_max_right _ _⟩
  exact tailFirstOrderSystem_eqOn_Icc hx₀' (hp.mono hsubset)
    (fun t ht => hp₀ t (hsubset ht)) (h.mono hsubset) (h'.mono hsubset) hu₀ hv₀ x hx'

theorem tailFirstOrderSystem_zero_of_initial
    {p u v : ℝ → ℝ} {Λ a b x₀ : ℝ}
    (hx₀ : x₀ ∈ Ioo a b) (hp : ContinuousOn p (Ioo a b))
    (hp₀ : ∀ x ∈ Ioo a b, p x ≠ 0)
    (h : TailFirstOrderSystem p Λ u v (Ioo a b))
    (hu₀ : u x₀ = 0) (hv₀ : v x₀ = 0) :
    ∀ x ∈ Ioo a b, u x = 0 ∧ v x = 0 := by
  have hz : TailFirstOrderSystem p Λ (fun _ => 0) (fun _ => 0) (Ioo a b) := by
    intro x _
    constructor <;> simpa only [zero_div, mul_zero] using hasDerivAt_const x (0 : ℝ)
  exact tailFirstOrderSystem_eq_of_initial hx₀ hp hp₀ h hz hu₀ hv₀

end ContinuousFlexibility.Radial
