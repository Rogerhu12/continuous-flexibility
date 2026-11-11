import ContinuousFlexibility.Analysis.IntervalWeakIntegral

/-!
# Local regularity for a weak one-dimensional divergence equation

The locally integrable equation `(w * u')' = f` has an actual C¹ representative
when `w` is smooth and nonzero in the open interval. An explicit particular
solution is obtained by integrating `f`, dividing its primitive by `w`,
and integrating again. The remaining homogeneous solution is classified by
`IntervalWeakDivergence`.

The coefficient is allowed to vanish at the interval endpoints, and neither
the solution nor the forcing is assumed integrable up to those endpoints.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Analysis

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- A displayed continuous local derivative gives C¹ regularity on an open
real set. -/
theorem contDiffOn_one_of_hasDerivAt_of_continuousOn {s : Set ℝ} (hs : IsOpen s)
    {v d : ℝ → ℝ} (hder : ∀ x ∈ s, HasDerivAt v (d x) x)
    (hd : ContinuousOn d s) : ContDiffOn ℝ 1 v s := by
  apply (contDiffOn_one_iff_derivWithin hs.uniqueDiffOn).mpr
  refine ⟨fun x hx => (hder x hx).differentiableAt.differentiableWithinAt, ?_⟩
  apply hd.congr
  intro x hx
  exact (hder x hx).hasDerivWithinAt.derivWithin (hs.uniqueDiffOn x hx)

/-- Local C¹ regularity and the exact integrated conormal flux for an
arbitrary locally integrable weak divergence equation. -/
theorem exists_contDiffOn_one_rep_of_weak_divergence_Ioo {a b : ℝ}
    (hab : a < b) {w u f : ℝ → ℝ} (hw : ContDiffOn ℝ ∞ w (Ioo a b))
    (hwn : ∀ x ∈ Ioo a b, w x ≠ 0)
    (hu : LocallyIntegrableOn u (Ioo a b) volume)
    (hf : LocallyIntegrableOn f (Ioo a b) volume) (x₀ : ℝ) (hx₀ : x₀ ∈ Ioo a b)
    (heq : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x, u x * deriv (fun y => w y * deriv φ y) x) = ∫ x, f x * φ x) :
    ∃ v : ℝ → ℝ, ∃ q : ℝ,
      u =ᵐ[volume.restrict (Ioo a b)] v ∧ ContDiffOn ℝ 1 v (Ioo a b) ∧
        ∀ x ∈ Ioo a b, w x * deriv v x = intervalLocalPrimitive f x₀ x + q := by
  let H : ℝ → ℝ := intervalLocalPrimitive f x₀
  have hH : ContinuousOn H (Ioo a b) := continuousOn_intervalLocalPrimitive hab hf hx₀
  have hInv : ContinuousOn (fun x => (w x)⁻¹) (Ioo a b) :=
    (hw.inv hwn).continuousOn
  let g : ℝ → ℝ := fun x => H x / w x
  have hg : ContinuousOn g (Ioo a b) := by
    simpa only [g, div_eq_mul_inv, Pi.mul_apply] using hH.mul hInv
  let V : ℝ → ℝ := intervalLocalPrimitive g x₀
  have hVder (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt V (g x) x :=
    hasDerivAt_intervalLocalPrimitive_of_continuousOn hg hx₀ hx
  have hV : ContinuousOn V (Ioo a b) :=
    fun x hx => (hVder x hx).continuousAt.continuousWithinAt
  have hVi : LocallyIntegrableOn V (Ioo a b) volume :=
    hV.locallyIntegrableOn measurableSet_Ioo
  let P : ℝ → ℝ := intervalLocalPrimitive (fun x => (w x)⁻¹) x₀
  have hPder (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt P ((w x)⁻¹) x :=
    hasDerivAt_intervalLocalPrimitive_of_continuousOn hInv hx₀ hx
  have htest (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
      (hφs : tsupport φ ⊆ Ioo a b) :
      ContDiff ℝ ∞ (fun x => w x * deriv φ x) ∧
      HasCompactSupport (fun x => w x * deriv φ x) ∧
      tsupport (fun x => w x * deriv φ x) ⊆ Ioo a b := by
    have hφd := (contDiff_infty_iff_deriv.mp hφ).2
    have hts : tsupport (fun x => w x * deriv φ x) ⊆ Ioo a b :=
      tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hφs)
    exact ⟨contDiff_of_contDiffOn_of_tsupport_subset isOpen_Ioo
      (hw.mul hφd.contDiffOn) hts, hφc.deriv.mul_left, hts⟩
  have hVeq (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
      (hφs : tsupport φ ⊆ Ioo a b) :
      (∫ x, V x * deriv (fun y => w y * deriv φ y) x) = ∫ x, f x * φ x := by
    obtain ⟨hψ, hψc, hψs⟩ := htest φ hφ hφc hφs
    have hip :=
      integral_mul_deriv_eq_neg_of_hasDerivAt_Ioo hab hVder hg hψ hψc hψs
    have hinner : (fun x => g x * (w x * deriv φ x)) =
        (fun x => H x * deriv φ x) := by
      funext x
      by_cases hx : x ∈ Ioo a b
      · dsimp only [g]
        field_simp [hwn x hx]
      · have hdx : deriv φ x = 0 :=
          deriv_of_notMem_tsupport (fun hh => hx (hφs hh))
        simp only [hdx, mul_zero]
    rw [hinner] at hip
    change (∫ x, V x * deriv (fun y => w y * deriv φ y) x) =
      -(∫ x, intervalLocalPrimitive f x₀ x * deriv φ x) at hip
    rw [integral_intervalLocalPrimitive_mul_deriv_Ioo hab hf hx₀ hφ hφc hφs,
      neg_neg] at hip
    exact hip
  have hdiff : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x, (u x - V x) * deriv (fun y => w y * deriv φ y) x) = 0 := by
    intro φ hφ hφc hφs
    obtain ⟨hψ, hψc, hψs⟩ := htest φ hφ hφc hφs
    have hψd := (contDiff_infty_iff_deriv.mp hψ).2
    have hψds : tsupport (deriv (fun y => w y * deriv φ y)) ⊆ Ioo a b :=
      tsupport_deriv_subset.trans hψs
    have hui : Integrable (fun x => u x * deriv (fun y => w y * deriv φ y) x) :=
      integrable_mul_test_of_locallyIntegrableOn_Ioo hu hψd.continuous hψc.deriv hψds
    have hvi : Integrable (fun x => V x * deriv (fun y => w y * deriv φ y) x) :=
      integrable_mul_test_of_locallyIntegrableOn_Ioo hVi hψd.continuous hψc.deriv hψds
    simp_rw [sub_mul]
    rw [integral_sub hui hvi, heq φ hφ hφc hφs, hVeq φ hφ hφc hφs, sub_self]
  obtain ⟨c, q, hrepr⟩ :=
    exists_ae_eq_affine_primitive_of_divergence_eq_zero_Ioo hab hw hwn (hu.sub hVi)
      hPder hdiff
  let v : ℝ → ℝ := fun x => V x + c + q * P x
  let d : ℝ → ℝ := fun x => g x + q * (w x)⁻¹
  have hvder (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt v (d x) x :=
    ((hVder x hx).add_const c).add ((hPder x hx).const_mul q)
  have hd : ContinuousOn d (Ioo a b) := hg.add (continuousOn_const.mul hInv)
  refine ⟨v, q, ?_, contDiffOn_one_of_hasDerivAt_of_continuousOn isOpen_Ioo hvder hd, ?_⟩
  · filter_upwards [hrepr] with x hx
    change u x - V x = c + q * P x at hx
    change u x = V x + c + q * P x
    linarith
  · intro x hx
    rw [(hvder x hx).deriv]
    change w x * (H x / w x + q * (w x)⁻¹) = H x + q
    field_simp [hwn x hx]

end

end ContinuousFlexibility.Analysis
