module

public import ContinuousFlexibility.Radial.GeneralLiouvilleLocalConjugacy
public import ContinuousFlexibility.Radial.MorseCellMassTravel

/-!
# Liouville transport on a retained Morse cell

The inverse radius is taken on the retained interval. Its local smoothness
follows from the positive velocity there, even if the extended ODE solution
has a turning point outside the interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped ContDiff Topology

/-- The height obtained by pulling a model solution back to the actual radius. -/
def morseCellRadialHeight (r ψ : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  ψ ∘ morseCellModelCoordinate r a b

theorem morseCellModelCoordinate_contDiffAt {r : ℝ → ℝ} {a b x : ℝ}
    (hr : ContDiff ℝ ∞ r) (hv : ∀ y ∈ Icc a b, 0 < deriv r y)
    (hx : x ∈ Ioo a b) :
    ContDiffAt ℝ ∞ (morseCellModelCoordinate r a b) (r x) := by
  have hmono := morseCell_strictMonoOn hr hv
  have hnear : (fun y => morseCellModelCoordinate r a b (r y)) =ᶠ[𝓝 x] id := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact morseCellModelCoordinate_apply hmono (Ioo_subset_Icc_self hy)
  have h0 := (hv x (Ioo_subset_Icc_self hx)).ne'
  let h := (hr.hasStrictDerivAt (x := x) (by simp)).hasStrictFDerivAt_equiv h0
  let e := h.toOpenPartialHomeomorph r
  have he : e.symm (r x) = x := h.localInverse_apply_image
  have hD : HasDerivAt e (deriv r x) (e.symm (r x)) := by
    rw [he]
    exact (hr.differentiable (by simp) x).hasDerivAt
  have hC : ContDiffAt ℝ ∞ (e : ℝ → ℝ) (e.symm (r x)) := by
    rw [he]
    exact hr.contDiffAt
  have hi := e.contDiffAt_symm_deriv h0 h.image_mem_toOpenPartialHomeomorph_target hD hC
  exact hi.congr_of_eventuallyEq (h.localInverse_unique hnear)

theorem morseCellRadialHeight_contDiffOn {r ψ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hr : ContDiff ℝ ∞ r) (hψ : ContDiff ℝ ∞ ψ)
    (hv : ∀ y ∈ Icc a b, 0 < deriv r y) :
    ContDiffOn ℝ ∞ (morseCellRadialHeight r ψ a b) (Ioo (r a) (r b)) := by
  rw [← hr.continuous.continuousOn.image_Ioo_of_strictMonoOn hab
    (morseCell_strictMonoOn hr hv)]
  rintro _ ⟨x, hx, rfl⟩
  exact (hψ.contDiffAt.comp (r x)
    (morseCellModelCoordinate_contDiffAt hr hv hx)).contDiffWithinAt

/-- The exact differential factor for the actual Morse model, on the open
retained interval where the physical radius is a smooth coordinate. -/
theorem morseCell_radialJacobi {r ψ : ℝ → ℝ} {A B a b : ℝ}
    (hr : ContDiff ℝ ∞ r) (hψ : ContDiff ℝ ∞ ψ)
    (hpos : ∀ y ∈ Icc a b, 0 < r y ∧ 0 < deriv r y)
    (hEq : ∀ y ∈ Icc a b, deriv (deriv r) y = -morseRho A B y * r y)
    (scale j : ℝ) {x : ℝ} (hx : x ∈ Ioo a b) :
    radialJacobi (j ^ 2) (morseCellRadialProfile r a b scale)
        (morseCellRadialHeight r ψ a b) (r x) =
      -(scale / deriv r x) * morseSchrodingerExpression j A B ψ x := by
  let s : ℝ → ℝ := fun _ => 1
  let w := morseCellRadialProfile r a b scale
  let u := morseCellRadialHeight r ψ a b
  have hv (y : ℝ) (hy : y ∈ Icc a b) : 0 < deriv r y := (hpos y hy).2
  have hmono := morseCell_strictMonoOn hr hv
  have hri : ContDiff ℝ ∞ (deriv r) := (contDiff_infty_iff_deriv.mp hr).2
  have hu (y : ℝ) (hy : y ∈ Ioo a b) : ContDiffAt ℝ ∞ u (r y) :=
    hψ.contDiffAt.comp _ (morseCellModelCoordinate_contDiffAt hr hv hy)
  have hw : ContDiffAt ℝ ∞ w (r x) :=
    (contDiff_const.mul hri).contDiffAt.comp _ (morseCellModelCoordinate_contDiffAt hr hv hx)
  have hdu : DifferentiableAt ℝ (deriv u) (r x) :=
    ((hu x hx).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have hs : ContDiff ℝ ∞ s := contDiff_const
  have hsd : ContDiff ℝ ∞ (deriv s) := (contDiff_infty_iff_deriv.mp hs).2
  have hweight : (fun y => w (r y)) =ᶠ[𝓝 x]
      (fun y => scale * s y ^ 2 * deriv r y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    simpa only [s, one_pow, mul_one] using
      morseCellRadialProfile_apply scale hmono (Ioo_subset_Icc_self hy)
  have hheight : (fun y => u (r y)) =ᶠ[𝓝 x] (fun y => ψ y / s y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    simp only [u, morseCellRadialHeight, Function.comp_apply, s, div_one,
      morseCellModelCoordinate_apply hmono (Ioo_subset_Icc_self hy)]
  have hxs := Ioo_subset_Icc_self hx
  obtain ⟨hrx, hvx⟩ := hpos x hxs
  have hue : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u (r y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (hu y hy).differentiableAt (by simp)
  have hidentity := radialJacobi_liouville (a := j ^ 2) (c := scale)
    (Eventually.of_forall (hr.differentiable (by simp)))
    (Eventually.of_forall (hs.differentiable (by simp)))
    (Eventually.of_forall (hψ.differentiable (by simp)))
    hue
    (hri.differentiable (by simp) x) (hsd.differentiable (by simp) x)
    ((contDiff_infty_iff_deriv.mp hψ).2.differentiable (by simp) x)
    (hw.differentiableAt (by simp)) ((hw.differentiableAt (by simp)).mul hdu)
    hrx.ne' hvx.ne' (by simp [s]) hweight hheight
  have hρ : liouvilleRho r s x = morseRho A B x := by
    simp only [liouvilleRho, s, deriv_const, mul_zero, zero_div, zero_mul, add_zero,
      hEq x hxs, neg_mul, neg_neg]
    exact mul_div_cancel_right₀ _ hrx.ne'
  have hV : liouvilleV0 s x = 0 := by
    have hs' : deriv s = fun _ => 0 := funext fun y => by simp [s]
    simp only [liouvilleV0, hs', deriv_const, zero_div]
  simpa only [liouvilleSchrodinger, hV, zero_sub, zero_add, hρ, morseSchrodingerExpression,
    s, mul_one, sub_eq_add_neg, neg_mul]
    using hidentity

/-- An inhomogeneous radial equation on the same cell has the actual Morse
forcing multiplied by the signed velocity-to-amplitude ratio. -/
theorem morseCell_radialJacobi_forcing_iff {r ψ f : ℝ → ℝ} {A B a b scale : ℝ}
    (hr : ContDiff ℝ ∞ r) (hψ : ContDiff ℝ ∞ ψ)
    (hpos : ∀ y ∈ Icc a b, 0 < r y ∧ 0 < deriv r y)
    (hEq : ∀ y ∈ Icc a b, deriv (deriv r) y = -morseRho A B y * r y)
    (hscale : 0 < scale) (j : ℝ) {x : ℝ} (hx : x ∈ Ioo a b) :
    radialJacobi (j ^ 2) (morseCellRadialProfile r a b scale)
        (morseCellRadialHeight r ψ a b) (r x) = f (r x) ↔
      morseSchrodingerExpression j A B ψ x = -(deriv r x / scale) * f (r x) := by
  have hv := (hpos x (Ioo_subset_Icc_self hx)).2.ne'
  rw [morseCell_radialJacobi hr hψ hpos hEq scale j hx]
  constructor
  · intro h
    rw [← h]
    field_simp [hscale.ne', hv]
  · intro h
    rw [h]
    field_simp [hscale.ne', hv]

/-- The exact Morse differential conjugacy holds on an actual retained cell
with the initial data used in the chain construction. -/
theorem exists_morseRetainedCell_radialJacobi {A B : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hA₀ : A ≤ 1 / 1000)
    (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9) :
    let a := morseCellLeftCut
    let b := morseRightCapEnd A B (1 / 100)
    ∃ r : ℝ → ℝ, ContDiff ℝ ∞ r ∧ r (morseRightTurn A B) = 1 ∧
      deriv r (morseRightTurn A B) = (1 / 100 : ℝ) * A ^ 5 ∧
      (∀ x ∈ Icc a b, 0 < r x ∧ 0 < deriv r x) ∧
      ∀ (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ → ∀ scale j, ∀ x ∈ Ioo a b,
        radialJacobi (j ^ 2) (morseCellRadialProfile r a b scale)
            (morseCellRadialHeight r ψ a b) (r x) =
          -(scale / deriv r x) * morseSchrodingerExpression j A B ψ x := by
  dsimp only
  obtain ⟨r, hr, hr₀, hv₀, hEq, hb, _⟩ :=
    exists_morseRadius_retainedCell hB hAB hA₀ hBAlo hBAhi
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hpos (x : ℝ) (hx : x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100))) :
      0 < r x ∧ 0 < deriv r x :=
    ⟨(hb x hx).2.1, (mul_pos (by norm_num : (0 : ℝ) < 1 / 100)
      (pow_pos hA 5)).trans_le (hb x hx).2.2.2.1⟩
  exact ⟨r, hr, hr₀, hv₀, hpos,
    fun _ hψ scale j _ hx => morseCell_radialJacobi hr hψ hpos hEq scale j hx⟩

end ContinuousFlexibility.Radial
