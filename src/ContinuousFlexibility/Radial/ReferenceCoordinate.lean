import ContinuousFlexibility.Radial.ReferenceCompactSurgery
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Transport of the reference geometry by a smooth coordinate

The coordinate maps the new radius to the old radius.  Every cell and
localizer is pulled back, so pointwise overlap and local finiteness are
preserved.  Quantitative metric assumptions are ordinary two-sided
Lipschitz estimates, used below to transport the actual trace intervals
and Gaussian endpoint-distance scale.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Real Set
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- The complete reference data pulled back by an increasing coordinate. -/
def coordinateReference (D : ReferenceData) (e : ℝ ≃o ℝ) : ReferenceData where
  a := e.symm D.a
  b := e.symm D.b
  w := fun r => D.w (e r)
  phi := fun r => D.phi (e r)
  chi := fun r => D.chi (e r)
  chiLeft := fun r => D.chiLeft (e r)
  cells := fun m => e ⁻¹' D.cells m
  localizer := fun m r => D.localizer m (e r)
  cellIndex := D.cellIndex

@[simp] theorem coordinateReference_core_iff (D : ReferenceData) (e : ℝ ≃o ℝ)
    (r : ℝ) : r ∈ radialCore (coordinateReference D e) ↔ e r ∈ radialCore D := by
  change (e.symm D.a < r ∧ r < e.symm D.b) ↔ (D.a < e r ∧ e r < D.b)
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨by simpa using e.strictMono ha, by simpa using e.strictMono hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨by simpa using e.symm.strictMono ha, by simpa using e.symm.strictMono hb⟩

/-- Scalar changes of coordinate commute with the total derivative even
at points where the original function is not differentiable. -/
theorem deriv_scalar_coordinate (f : ℝ → ℝ) (c r : ℝ) :
    deriv (fun x => f (c * x)) r = c * deriv f (c * r) := by
  have h := congrArg (fun A : ℝ →L[ℝ] ℝ => A 1)
    (fderiv_comp_smul (f := f) (x := r) c)
  simpa only [smul_eq_mul, ContinuousLinearMap.smul_apply,
    fderiv_apply_one_eq_deriv] using h

/-- Exact all-order radius and height scaling, with no regularity
hypothesis.  This also applies to reciprocal profiles. -/
theorem radialJet_scalar_coordinate (s : ℕ) (f : ℝ → ℝ) (A c : ℝ) :
    radialJet s (fun x => A * f (c * x)) =
      fun x => A * c ^ s * radialJet s f (c * x) := by
  induction s with
  | zero =>
    funext x
    simp only [radialJet, pow_zero, mul_one]
  | succ s ih =>
    rw [radialJet, ih]
    funext x
    rw [deriv_const_mul_field, deriv_scalar_coordinate]
    simp only [radialJet, pow_succ]
    ring

theorem endpointFlat_coordinateReference {D : ReferenceData} {u : ℝ → ℝ}
    (e : ℝ ≃o ℝ) (he : ContDiff ℝ ∞ (fun r => e r)) (hu : EndpointFlat D u) :
    EndpointFlat (coordinateReference D e) (fun r => u (e r)) := by
  refine ⟨hu.1.comp he, ?_⟩
  intro r hr
  change r ≤ e.symm D.a ∨ e.symm D.b ≤ r at hr
  apply hu.2 (e r)
  rcases hr with hr | hr
  · exact Or.inl (by simpa using e.monotone hr)
  · exact Or.inr (by simpa using e.monotone hr)

/-- A smooth increasing coordinate with nonzero derivative preserves
the actual simple-critical-point condition. -/
theorem radialProfileGeometry_coordinateReference {D : ReferenceData}
    (e : ℝ ≃o ℝ) (he : ContDiff ℝ ∞ (fun r => e r))
    (he0 : 0 < e.symm D.a) (hne : ∀ r, deriv (fun x => e x) r ≠ 0)
    (hD : RadialProfileGeometry D) :
    RadialProfileGeometry (coordinateReference D e) := by
  rcases hD with ⟨ha, hab, hw, hp, hpos, hnonzero, hmorse⟩
  have hdw := (contDiff_infty_iff_deriv.mp hw.1).1
  have hdw' := (contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp hw.1).2).1
  have hde := (contDiff_infty_iff_deriv.mp he).1
  have hde' := (contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp he).2).1
  have hd : deriv (fun r => D.w (e r)) =
      fun r => deriv D.w (e r) * deriv (fun x => e x) r := by
    funext r
    exact ((hdw (e r)).hasDerivAt.comp r (hde r).hasDerivAt).deriv
  refine ⟨he0, e.symm.strictMono hab,
    endpointFlat_coordinateReference e he hw,
    endpointFlat_coordinateReference e he hp, ?_, ?_, ?_⟩
  · intro r hr
    exact hpos (e r) ((coordinateReference_core_iff D e r).mp hr)
  · obtain ⟨r, hr, hp⟩ := hnonzero
    refine ⟨e.symm r, ?_, ?_⟩
    · exact (coordinateReference_core_iff D e _).mpr (by simpa using hr)
    · simpa only [coordinateReference, e.apply_symm_apply] using hp
  · intro r hr hc
    change deriv (fun t => D.w (e t)) r = 0 at hc
    rw [hd] at hc
    have hc' : deriv D.w (e r) = 0 := (mul_eq_zero.mp hc).resolve_right (hne r)
    have hn := hmorse (e r) ((coordinateReference_core_iff D e r).mp hr) hc'
    change deriv (deriv (fun t => D.w (e t))) r ≠ 0
    rw [hd]
    have hh : deriv (fun t => deriv D.w (e t) * deriv (fun x => e x) t) r =
        deriv (deriv D.w) (e r) * deriv (fun x => e x) r * deriv (fun x => e x) r +
          deriv D.w (e r) * deriv (deriv (fun x => e x)) r :=
      (((hdw' (e r)).hasDerivAt.comp r (hde r).hasDerivAt).mul
        (hde' r).hasDerivAt).deriv
    rw [hh, hc', zero_mul, add_zero]
    exact mul_ne_zero (mul_ne_zero hn (hne r)) (hne r)

theorem radialPartition_coordinateReference {D : ReferenceData}
    (e : ℝ ≃o ℝ) (he : ContDiff ℝ ∞ (fun r => e r))
    (hD : RadialPartition D) :
    RadialPartition (coordinateReference D e) := by
  rcases hD with ⟨hsmooth, hnonneg, hsupp, hcore, hsum, B, hoverlap⟩
  refine ⟨fun m => (hsmooth m).comp he, fun m r => hnonneg m (e r),
    ?_, ?_, ?_, B, ?_⟩
  · intro m r hr
    exact hsupp m hr
  · intro m r hr
    exact (coordinateReference_core_iff D e r).mpr (hcore m hr)
  · intro r hr
    exact hsum (e r) ((coordinateReference_core_iff D e r).mp hr)
  · intro r
    exact hoverlap (e r)

/-- Local finiteness of the actual cells, not only of the localizers. -/
theorem coordinateReference_cells_locallyFinite {D : ReferenceData}
    (e : ℝ ≃o ℝ)
    (hD : ∀ K : Set ℝ, IsCompact K → K ⊆ radialCore D →
      Set.Finite {m | (D.cells m ∩ K).Nonempty}) :
    ∀ K : Set ℝ, IsCompact K → K ⊆ radialCore (coordinateReference D e) →
      Set.Finite {m | ((coordinateReference D e).cells m ∩ K).Nonempty} := by
  intro K hK hsub
  have him : e '' K ⊆ radialCore D := by
    rintro _ ⟨r, hr, rfl⟩
    exact (coordinateReference_core_iff D e r).mp (hsub hr)
  apply (hD (e '' K) (hK.image e.continuous) him).subset
  rintro m ⟨r, hr, hKr⟩
  exact ⟨e r, hr, ⟨r, hKr, rfl⟩⟩

private theorem coordinate_min_bound {a b c d L : ℝ}
    (hleft : a ≤ L * c) (hright : b ≤ L * d) :
    min a b ≤ L * min c d := by
  rcases le_total c d with h | h
  · rw [min_eq_left h]
    exact (min_le_left a b).trans hleft
  · rw [min_eq_right h]
    exact (min_le_right a b).trans hright

/-- Both endpoint distances obey the same metric constant. -/
theorem coordinateReference_endpoint_distances (D : ReferenceData) (e : ℝ ≃o ℝ)
    {L : ℝ}
    (hforward : ∀ x y : ℝ, |e x - e y| ≤ L * |x - y|)
    (hbackward : ∀ x y : ℝ, |x - y| ≤ L * |e x - e y|)
    {r : ℝ} (hr : r ∈ radialCore (coordinateReference D e)) :
    min (e r - D.a) (D.b - e r) ≤
        L * min (r - e.symm D.a) (e.symm D.b - r) ∧
      min (r - e.symm D.a) (e.symm D.b - r) ≤
        L * min (e r - D.a) (D.b - e r) := by
  have hold := (coordinateReference_core_iff D e r).mp hr
  change e.symm D.a < r ∧ r < e.symm D.b at hr
  have hfa := hforward r (e.symm D.a)
  have hfb := hforward (e.symm D.b) r
  have hba := hbackward r (e.symm D.a)
  have hbb := hbackward (e.symm D.b) r
  simp only [e.apply_symm_apply, abs_of_pos (sub_pos.mpr hold.1),
    abs_of_pos (sub_pos.mpr hold.2), abs_of_pos (sub_pos.mpr hr.1),
    abs_of_pos (sub_pos.mpr hr.2)] at hfa hfb hba hbb
  exact ⟨coordinate_min_bound hfa hfb, coordinate_min_bound hba hbb⟩

/-- Gaussian lower and upper distance bounds under the coordinate. -/
theorem coordinateReference_gaussian_distance (D : ReferenceData) (e : ℝ ≃o ℝ)
    {L C : ℝ} (hL : 0 < L)
    (hforward : ∀ x y : ℝ, |e x - e y| ≤ L * |x - y|)
    (hbackward : ∀ x y : ℝ, |x - y| ≤ L * |e x - e y|)
    (hCore : ∀ m, D.cells m ⊆ radialCore D)
    (hDist : ∀ m r, r ∈ D.cells m →
      C⁻¹ * exp (-((D.cellIndex m : ℝ) + 1) ^ 2) ≤ min (r - D.a) (D.b - r) ∧
      min (r - D.a) (D.b - r) ≤ C * exp (-(D.cellIndex m : ℝ) ^ 2)) :
    ∀ m r, r ∈ (coordinateReference D e).cells m →
      (L * C)⁻¹ * exp (-((D.cellIndex m : ℝ) + 1) ^ 2) ≤
          min (r - e.symm D.a) (e.symm D.b - r) ∧
      min (r - e.symm D.a) (e.symm D.b - r) ≤
          (L * C) * exp (-(D.cellIndex m : ℝ) ^ 2) := by
  intro m r hr
  have hdist := hDist m (e r) hr
  have hc := (coordinateReference_core_iff D e r).mpr (hCore m hr)
  have hd := coordinateReference_endpoint_distances D e hforward hbackward hc
  constructor
  · have hh := (div_le_iff₀ hL).mpr
      (by simpa only [mul_comm] using hdist.1.trans hd.1)
    calc
      _ = (C⁻¹ * exp (-((D.cellIndex m : ℝ) + 1) ^ 2)) / L := by
        simp only [mul_inv_rev, div_eq_mul_inv]
        ring
      _ ≤ _ := hh
  · exact hd.2.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdist.2 hL.le)

/-- The coordinate takes actual bounded cell hulls to bounded cell hulls. -/
theorem coordinateReference_cell_widths (D : ReferenceData) (e : ℝ ≃o ℝ)
    {L C : ℝ} (hL : 0 ≤ L)
    (hbackward : ∀ x y : ℝ, |x - y| ≤ L * |e x - e y|)
    (hNE : ∀ m, (D.cells m).Nonempty)
    (hWidth : ∀ m, ∃ l h : ℝ, D.cells m ⊆ Icc l h ∧
      h - l ≤ C * exp (-(D.cellIndex m : ℝ) ^ 2)) :
    ∀ m, ∃ l h : ℝ, (coordinateReference D e).cells m ⊆ Icc l h ∧
      h - l ≤ (L * C) * exp (-(D.cellIndex m : ℝ) ^ 2) := by
  intro m
  obtain ⟨l, h, hsub, hlen⟩ := hWidth m
  obtain ⟨x, hx⟩ := hNE m
  have hlh : l ≤ h := (hsub hx).1.trans (hsub hx).2
  have hlength := hbackward (e.symm h) (e.symm l)
  simp only [e.apply_symm_apply, abs_of_nonneg (sub_nonneg.mpr hlh),
    abs_of_nonneg (sub_nonneg.mpr (e.symm.monotone hlh))] at hlength
  refine ⟨e.symm l, e.symm h, ?_, ?_⟩
  · intro r hr
    obtain ⟨hl, hh⟩ := hsub hr
    exact ⟨by simpa using e.symm.monotone hl, by simpa using e.symm.monotone hh⟩
  · exact hlength.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlen hL)

end ContinuousFlexibility.Radial
