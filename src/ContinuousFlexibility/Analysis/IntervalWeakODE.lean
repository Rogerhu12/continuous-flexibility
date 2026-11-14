module

public import ContinuousFlexibility.Analysis.IntervalL1Primitive
public import ContinuousFlexibility.Analysis.IntervalWeakDivergence
public import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Interior regularity of weak scalar divergence equations

An integrable weak solution of `(w u')' = f + q u` has a smooth representative
where the smooth leading coefficient does not vanish. The first step uses
two genuine integral primitives and the homogeneous weak-divergence
classification. The resulting continuous representative satisfies an actual
first-order system, to which the ordinary smooth ODE regularity theorem
applies.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Analysis

noncomputable section

/-- A weak scalar divergence equation with smooth coefficients has an actual
smooth representative in the open interval. No endpoint value, derivative,
or endpoint regularity of the solution is assumed. -/
theorem exists_contDiffOn_ae_eq_of_weak_divergence_Ioo {a b : ℝ} (hab : a < b)
    {w q f u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hwn : ∀ x ∈ Ioo a b, w x ≠ 0)
    (hq : ContDiffOn ℝ ∞ q (Ioo a b)) (hf : ContDiffOn ℝ ∞ f (Ioo a b))
    (hu : LocallyIntegrableOn u (Ioo a b) volume)
    (hg : IntegrableOn (fun x => f x + q x * u x) (Ioo a b))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x, u x * deriv (fun y => w y * deriv φ y) x) =
          ∫ x, (f x + q x * u x) * φ x) :
    ∃ U : ℝ → ℝ, ContDiffOn ℝ ∞ U (Ioo a b) ∧
      u =ᵐ[volume.restrict (Ioo a b)] U ∧
      ∀ x ∈ Ioo a b,
        deriv (fun y => w y * deriv U y) x = f x + q x * U x := by
  let g : ℝ → ℝ := fun x => f x + q x * u x
  let P : ℝ → ℝ := intervalL1Primitive a b g
  let x₀ : ℝ := (a + b) / 2
  have hx₀ : x₀ ∈ Ioo a b := by
    dsimp only [x₀]
    constructor <;> linarith
  have hPc : Continuous P := continuous_intervalL1Primitive hg
  let V : ℝ → ℝ := fun x => ∫ y in x₀..x, P y / w y
  have hquot : ContinuousOn (fun x => P x / w x) (Ioo a b) :=
    hPc.continuousOn.div hw.continuous.continuousOn hwn
  have hVd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt V (P x / w x) x := by
    have hsub : uIcc x₀ x ⊆ Ioo a b := by
      intro y hy
      exact ⟨(lt_min hx₀.1 hx.1).trans_le hy.1,
        hy.2.trans_lt (max_lt hx₀.2 hx.2)⟩
    have hi : IntervalIntegrable (fun y => P y / w y) volume x₀ x :=
      (hquot.mono hsub).intervalIntegrable
    have hm : AEStronglyMeasurable (fun y => P y / w y) volume :=
      (hPc.measurable.div hw.continuous.measurable).aestronglyMeasurable
    exact intervalIntegral.integral_hasDerivAt_right hi hm.stronglyMeasurableAtFilter
      (hPc.continuousAt.div hw.continuous.continuousAt (hwn x hx))
  have hVc : ContinuousOn V (Ioo a b) :=
    fun x hx => (hVd x hx).continuousAt.continuousWithinAt
  have hVi : LocallyIntegrableOn V (Ioo a b) volume :=
    hVc.locallyIntegrableOn measurableSet_Ioo
  have hVweak (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
      (hφs : tsupport φ ⊆ Ioo a b) :
      (∫ x, V x * deriv (fun y => w y * deriv φ y) x) =
        ∫ x, g x * φ x := by
    have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
    have hψ : ContDiff ℝ ∞ (fun y => w y * deriv φ y) := hw.mul hφd
    have hψc : HasCompactSupport (fun y => w y * deriv φ y) :=
      hφc.deriv.mul_left
    have hψs : tsupport (fun y => w y * deriv φ y) ⊆ Ioo a b :=
      tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hφs)
    have hip := integral_mul_deriv_eq_neg_of_hasDerivAt_Ioo hab hVd hquot hψ hψc hψs
    have hprod : (fun x => P x / w x * (w x * deriv φ x)) =
        (fun x => P x * deriv φ x) := by
      funext x
      by_cases hx : x ∈ Ioo a b
      · field_simp [hwn x hx] <;> ring
      · have hz : deriv φ x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hh => hx (hφs (tsupport_deriv_subset hh)))
        simp only [hz, mul_zero]
    have hPweak : (∫ x, P x * deriv φ x) = -(∫ x, g x * φ x) :=
      integral_intervalL1Primitive_mul_deriv_eq_neg hab hg hφ hφc hφs
    rw [hprod, hPweak] at hip
    simpa only [neg_neg] using hip
  have hhom : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x, (u x - V x) * deriv (fun y => w y * deriv φ y) x) = 0 := by
    intro φ hφ hφc hφs
    have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
    have hψ : ContDiff ℝ ∞ (deriv (fun y => w y * deriv φ y)) :=
      (contDiff_infty_iff_deriv.mp (hw.mul hφd)).2
    have hψc : HasCompactSupport (deriv (fun y => w y * deriv φ y)) :=
      (hφc.deriv.mul_left).deriv
    have hψs : tsupport (deriv (fun y => w y * deriv φ y)) ⊆ Ioo a b :=
      tsupport_deriv_subset.trans
        (tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hφs))
    have hui := integrable_mul_test_of_locallyIntegrableOn_Ioo hu hψ.continuous hψc hψs
    have hvi := integrable_mul_test_of_locallyIntegrableOn_Ioo hVi hψ.continuous hψc hψs
    simp_rw [sub_mul]
    rw [integral_sub hui hvi, hweak φ hφ hφc hφs, hVweak φ hφ hφc hφs]
    exact sub_self _
  obtain ⟨c, d, hcd⟩ :=
    exists_ae_eq_affine_reciprocalPrimitive_of_divergence_eq_zero_Ioo
      hab hw hwn (hu.sub hVi) x₀ hx₀ hhom
  let R : ℝ → ℝ := intervalReciprocalPrimitive w x₀
  let U : ℝ → ℝ := fun x => V x + c + d * R x
  let Q : ℝ → ℝ := fun x => P x + d
  have hRd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt R ((w x)⁻¹) x :=
    hasDerivAt_intervalReciprocalPrimitive hw hwn hx₀ hx
  have hUd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt U (Q x / w x) x := by
    have hd := ((hVd x hx).add_const c).add ((hRd x hx).const_mul d)
    convert hd using 1 <;> dsimp only [U, Q] <;> simp only [div_eq_mul_inv] <;> ring
  have hUc : ContinuousOn U (Ioo a b) :=
    fun x hx => (hUd x hx).continuousAt.continuousWithinAt
  have hUae : u =ᵐ[volume.restrict (Ioo a b)] U := by
    filter_upwards [hcd] with x hx
    change u x - V x = c + d * R x at hx
    dsimp only [U]
    linarith
  have hgU : g =ᵐ[volume.restrict (Ioo a b)] (fun x => f x + q x * U x) := by
    filter_upwards [hUae] with x hx
    dsimp only [g]
    rw [hx]
  have hPd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt P (f x + q x * U x) x :=
    hasDerivAt_intervalL1Primitive_of_ae_eq hg hgU
      (hf.continuousOn.add (hq.continuousOn.mul hUc)) hx
  have hQd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt Q (f x + q x * U x) x :=
    (hPd x hx).add_const d
  have hUs : ContDiffOn ℝ ∞ U (Ioo a b) := by
    intro x hx
    let l : ℝ := (a + x) / 2
    let r : ℝ := (x + b) / 2
    have hlx : l < x := by dsimp only [l]; linarith [hx.1]
    have hxr : x < r := by dsimp only [r]; linarith [hx.2]
    have hsub : Icc l r ⊆ Ioo a b := by
      intro y hy
      dsimp only [l, r] at hy
      constructor <;> linarith [hy.1, hy.2, hx.1, hx.2]
    let α : ℝ → ℝ × ℝ := fun t => (U t, Q t)
    let F : ℝ → (ℝ × ℝ) → (ℝ × ℝ) :=
      fun t z => (z.2 / w t, f t + q t * z.1)
    have htime : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => p.1)
        ((Icc l r) ×ˢ (univ : Set (ℝ × ℝ))) := contDiff_fst.contDiffOn
    have hfirst : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => p.2.1)
        ((Icc l r) ×ˢ (univ : Set (ℝ × ℝ))) :=
      (contDiff_fst.comp contDiff_snd).contDiffOn
    have hsecond : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => p.2.2)
        ((Icc l r) ×ˢ (univ : Set (ℝ × ℝ))) :=
      (contDiff_snd.comp contDiff_snd).contDiffOn
    have hmap : MapsTo (fun p : ℝ × (ℝ × ℝ) => p.1)
        ((Icc l r) ×ˢ (univ : Set (ℝ × ℝ))) (Ioo a b) :=
      fun p hp => hsub hp.1
    have hFs : ContDiffOn ℝ ∞ (Function.uncurry F)
        ((Icc l r) ×ˢ (univ : Set (ℝ × ℝ))) := by
      exact (hsecond.div (hw.comp_contDiffOn htime)
        (fun p hp => hwn p.1 (hsub hp.1))).prodMk
          ((hf.comp htime hmap).add ((hq.comp htime hmap).mul hfirst))
    have hαd : ∀ t ∈ Icc l r,
        HasDerivWithinAt α (F t (α t)) (Icc l r) t := by
      intro t ht
      exact ((hUd t (hsub ht)).prodMk (hQd t (hsub ht))).hasDerivWithinAt
    have hαs : ContDiffOn ℝ ∞ α (Icc l r) :=
      ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt hFs hαd (mapsTo_univ _ _)
    have hUI : ContDiffOn ℝ ∞ U (Icc l r) := contDiff_fst.comp_contDiffOn hαs
    exact (hUI.contDiffAt (Icc_mem_nhds hlx hxr)).contDiffWithinAt
  refine ⟨U, hUs, hUae, ?_⟩
  intro x hx
  have hflux : (fun y => w y * deriv U y) =ᶠ[𝓝 x] Q := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    rw [(hUd y hy).deriv]
    field_simp [hwn y hy] <;> ring
  exact hflux.deriv_eq.trans (hQd x hx).deriv

end

end ContinuousFlexibility.Analysis
