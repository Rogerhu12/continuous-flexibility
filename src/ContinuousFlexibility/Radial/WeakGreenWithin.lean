import ContinuousFlexibility.Radial.IntervalWeakPrimitiveStrict
import ContinuousFlexibility.Radial.RadialGreenBoundary
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Weak Green identity with one-sided cut traces

A C1 function on a closed interval has a continuous within-derivative
there. The weak divergence equation makes its corresponding flux
absolutely continuous, including at both cuts. Green's identity then
uses only these within-derivative traces; no extension across a cut is
assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

/-- Almost every point of a nondegenerate closed interval is interior. -/
theorem weakInterval_ae_interior {a b : ℝ} (hab : a < b) :
    ∀ᵐ x ∂volume, x ∈ uIcc a b → x ∈ Ioo a b := by
  filter_upwards [volume.ae_ne a, volume.ae_ne b] with x hxa hxb hx
  rw [uIcc_of_le hab.le] at hx
  constructor
  · by_contra hn
    exact hxa (le_antisymm (le_of_not_gt hn) hx.1)
  · by_contra hn
    exact hxb (le_antisymm hx.2 (le_of_not_gt hn))

/-- Within-derivatives give the same integrands as ordinary derivatives
almost everywhere, while retaining the correct one-sided endpoint values. -/
theorem derivWithin_Icc_ae_eq_deriv {a b : ℝ} (hab : a < b) (u : ℝ → ℝ) :
    ∀ᵐ x ∂volume, x ∈ uIcc a b →
      derivWithin u (Icc a b) x = deriv u x := by
  filter_upwards [weakInterval_ae_interior hab] with x hx hxi
  exact derivWithin_of_mem_nhds
    (Icc_mem_nhds (hx hxi).1 (hx hxi).2)

/-- A C1 weak solution on a closed interval has an absolutely continuous
within-flux, with its prescribed source as the weak and almost everywhere
classical derivative. -/
theorem weakPrincipal_withinFlux_regular
    {a b : ℝ} (hab : a < b) {u g w : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Icc a b))
    (hg : IntervalIntegrable g volume a b)
    (hw : ContDiff ℝ ∞ w)
    (hweak : ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ x in a..b, u x * deriv (fun y => w y * deriv ψ y) x) =
        ∫ x in a..b, g x * ψ x) :
    let p := fun x => w x * derivWithin u (Icc a b) x
    (∀ x ∈ Icc a b, p x = p a + ∫ t in a..x, g t) ∧
      AbsolutelyContinuousOnInterval p a b ∧
      (deriv p =ᵐ[volume.restrict (Ioo a b)] g) := by
  let p (x : ℝ) : ℝ := w x * derivWithin u (Icc a b) x
  change (∀ x ∈ Icc a b, p x = p a + ∫ t in a..x, g t) ∧
    AbsolutelyContinuousOnInterval p a b ∧
    (deriv p =ᵐ[volume.restrict (Ioo a b)] g)
  have hu' : ContDiffOn ℝ 1 u (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using hu
  have huac := hu'.absolutelyContinuousOnInterval
  have hdu : ContinuousOn (derivWithin u (Icc a b)) (Icc a b) :=
    ((contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)).mp hu).2
  have hpc : ContinuousOn p (Icc a b) :=
    hw.continuous.continuousOn.mul hdu
  have hpweak : ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ x in a..b, p x * deriv ψ x) =
        -(∫ x in a..b, g x * ψ x) := by
    intro ψ hψ hcψ hψs
    have hda : deriv ψ a = 0 :=
      deriv_of_notMem_tsupport (fun ha => (lt_irrefl a) (hψs ha).1)
    have hdb : deriv ψ b = 0 :=
      deriv_of_notMem_tsupport (fun hb => (lt_irrefl b) (hψs hb).2)
    have hq : ContDiff ℝ ∞ (fun x => w x * deriv ψ x) :=
      hw.mul (contDiff_infty_iff_deriv.mp hψ).2
    have hq' : ContDiffOn ℝ 1 (fun x => w x * deriv ψ x) (uIcc a b) :=
      (hq.of_le (by simp)).contDiffOn
    have hi := huac.integral_mul_deriv_eq_deriv_mul hq'.absolutelyContinuousOnInterval
    have hrew :
        (∫ x in a..b, deriv u x * (w x * deriv ψ x)) =
          ∫ x in a..b, p x * deriv ψ x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [derivWithin_Icc_ae_eq_deriv hab u] with x hx hxi
      dsimp only [p]
      rw [hx (uIoc_subset_uIcc hxi)]
      ring
    rw [hrew, hda, hdb] at hi
    simp only [mul_zero, sub_zero, zero_sub] at hi
    have he := hweak ψ hψ hcψ hψs
    linarith only [hi, he]
  have hpoint : ∀ x ∈ Icc a b, p x = p a + ∫ t in a..x, g t :=
    eq_add_intervalIntegral_of_weakDeriv_tsupport hab hpc hg hpweak
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => p a) a b :=
    (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ => p a) (uIcc a b)).absolutelyContinuousOnInterval
  have hP : AbsolutelyContinuousOnInterval (fun x => p a + ∫ t in a..x, g t) a b :=
    hconst.fun_add (hg.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp))
  have hpac : AbsolutelyContinuousOnInterval p a b := by
    apply hP.congr
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    exact (hpoint x hx).symm
  refine ⟨hpoint, hpac, ?_⟩
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hg.ae_hasDerivAt_integral] with x hx hxi
  have hxi' : x ∈ uIcc a b := by
    simpa only [uIcc_of_le hab.le] using mem_Icc_of_Ioo hxi
  have hd : HasDerivAt (fun y => p a + ∫ t in a..y, g t) (g x) x :=
    (hx hxi' a (by simp)).const_add (p a)
  apply HasDerivAt.deriv
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hxi] with y hy
  exact hpoint y (mem_Icc_of_Ioo hy)

/-- Green's identity for two C1 weak solutions, including one-sided
flux values at the interval endpoints. -/
theorem integral_green_of_weak_principal
    {a b : ℝ} (hab : a < b) {u v g k w : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Icc a b))
    (hv : ContDiffOn ℝ 1 v (Icc a b))
    (hg : IntervalIntegrable g volume a b)
    (hk : IntervalIntegrable k volume a b)
    (hw : ContDiff ℝ ∞ w)
    (hweakU : ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ x in a..b, u x * deriv (fun y => w y * deriv ψ y) x) =
        ∫ x in a..b, g x * ψ x)
    (hweakV : ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ x in a..b, v x * deriv (fun y => w y * deriv ψ y) x) =
        ∫ x in a..b, k x * ψ x) :
    (∫ x in a..b, u x * k x - v x * g x) =
      (u b * (w b * derivWithin v (Icc a b) b) -
        v b * (w b * derivWithin u (Icc a b) b)) -
      (u a * (w a * derivWithin v (Icc a b) a) -
        v a * (w a * derivWithin u (Icc a b) a)) := by
  obtain ⟨hpu, hpac, hpd⟩ := weakPrincipal_withinFlux_regular hab hu hg hw hweakU
  obtain ⟨hqv, hqac, hqd⟩ := weakPrincipal_withinFlux_regular hab hv hk hw hweakV
  have hu' : ContDiffOn ℝ 1 u (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using hu
  have hv' : ContDiffOn ℝ 1 v (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using hv
  apply integral_green_of_absolutelyContinuous_flux
    hu'.absolutelyContinuousOnInterval hv'.absolutelyContinuousOnInterval hpac hqac
  · filter_upwards [derivWithin_Icc_ae_eq_deriv hab u] with x hx hxi
    rw [hx hxi]
  · filter_upwards [derivWithin_Icc_ae_eq_deriv hab v] with x hx hxi
    rw [hx hxi]
  · rw [restrict_Ioo_eq_restrict_Icc] at hpd
    simpa only [uIcc_of_le hab.le] using
      (ae_restrict_iff' measurableSet_Icc).mp hpd
  · rw [restrict_Ioo_eq_restrict_Icc] at hqd
    simpa only [uIcc_of_le hab.le] using
      (ae_restrict_iff' measurableSet_Icc).mp hqd

/-- Green's identity with a C1 weak solution and a C2 test on the same
closed interval. An arbitrary zeroth-order potential cancels algebraically.
All displayed endpoint derivatives are within-derivatives. -/
theorem integral_green_of_weak_principal_and_contDiffOn
    {a b : ℝ} (hab : a < b) {u φ g w Q : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Icc a b))
    (hφ : ContDiffOn ℝ 2 φ (Icc a b))
    (hg : IntervalIntegrable g volume a b)
    (hw : ContDiff ℝ ∞ w)
    (hweak : ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ x in a..b, u x * deriv (fun y => w y * deriv ψ y) x) =
        ∫ x in a..b, g x * ψ x) :
    (∫ x in a..b,
      u x * (deriv (fun y => w y * deriv φ y) x - Q x * φ x) -
        (g x - Q x * u x) * φ x) =
      (u b * (w b * derivWithin φ (Icc a b) b) -
        φ b * (w b * derivWithin u (Icc a b) b)) -
      (u a * (w a * derivWithin φ (Icc a b) a) -
        φ a * (w a * derivWithin u (Icc a b) a)) := by
  let p (x : ℝ) : ℝ := w x * derivWithin u (Icc a b) x
  let q (x : ℝ) : ℝ := w x * derivWithin φ (Icc a b) x
  obtain ⟨hpu, hpac, hpd⟩ := weakPrincipal_withinFlux_regular hab hu hg hw hweak
  have hφd : ContDiffOn ℝ 1 (derivWithin φ (Icc a b)) (Icc a b) :=
    hφ.derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hq : ContDiffOn ℝ 1 q (Icc a b) :=
    (hw.of_le (by simp)).contDiffOn.mul hφd
  have hu' : ContDiffOn ℝ 1 u (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using hu
  have hφ' : ContDiffOn ℝ 1 φ (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using
      (hφ.of_le (by norm_num) : ContDiffOn ℝ 1 φ (Icc a b))
  have hq' : ContDiffOn ℝ 1 q (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using hq
  have hpu' : ∀ᵐ x ∂volume, x ∈ uIcc a b → p x = w x * deriv u x := by
    filter_upwards [derivWithin_Icc_ae_eq_deriv hab u] with x hx hxi
    dsimp only [p]
    rw [hx hxi]
  have hqφ : ∀ᵐ x ∂volume, x ∈ uIcc a b → q x = w x * deriv φ x := by
    filter_upwards [derivWithin_Icc_ae_eq_deriv hab φ] with x hx hxi
    dsimp only [q]
    rw [hx hxi]
  have hpg : ∀ᵐ x ∂volume, x ∈ uIcc a b → deriv p x = g x := by
    rw [restrict_Ioo_eq_restrict_Icc] at hpd
    simpa only [uIcc_of_le hab.le] using
      (ae_restrict_iff' measurableSet_Icc).mp hpd
  have hqg : ∀ᵐ x ∂volume, x ∈ uIcc a b →
      deriv q x = deriv (fun y => w y * deriv φ y) x := by
    filter_upwards [weakInterval_ae_interior hab] with x hx hxi
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds (hx hxi)] with y hy
    dsimp only [q]
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
  have hi := integral_green_of_absolutelyContinuous_flux
    hu'.absolutelyContinuousOnInterval hφ'.absolutelyContinuousOnInterval
    hpac hq'.absolutelyContinuousOnInterval hpu' hqφ hpg hqg
  calc
    _ = ∫ x in a..b,
        u x * deriv (fun y => w y * deriv φ y) x - φ x * g x := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    _ = _ := hi

/-- The weak Green identity specialized to the actual radial Jacobi
expression, still with one-sided traces at the regular cuts. -/
theorem integral_radialJacobi_green_of_weak_principal
    {a b J : ℝ} (hab : a < b) {u φ g w : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Icc a b))
    (hφ : ContDiffOn ℝ 2 φ (Icc a b))
    (hg : IntervalIntegrable g volume a b)
    (hw : ContDiff ℝ ∞ w)
    (hweak : ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ x in a..b, u x * deriv (fun y => w y * deriv ψ y) x) =
        ∫ x in a..b, g x * ψ x) :
    (∫ x in a..b, u x * radialJacobi J w φ x -
      (g x - J * deriv w x / x * u x) * φ x) =
      (u b * (w b * derivWithin φ (Icc a b) b) -
        φ b * (w b * derivWithin u (Icc a b) b)) -
      (u a * (w a * derivWithin φ (Icc a b) a) -
        φ a * (w a * derivWithin u (Icc a b) a)) :=
  integral_green_of_weak_principal_and_contDiffOn
    (Q := fun x => J * deriv w x / x) hab hu hφ hg hw hweak

end ContinuousFlexibility.Radial
