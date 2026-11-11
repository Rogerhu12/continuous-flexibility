import ContinuousFlexibility.Radial.MorseModel
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The finite Morse radius initial value problem

Clip the two state coordinates to obtain a bounded field on the whole time
interval. A two-sided Grönwall estimate then puts the solution inside the
region where clipping is the identity. Solving on a wider interval permits
a globally smooth extension that satisfies the original system on a
neighborhood of the retained closed interval.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

set_option backward.isDefEq.respectTransparency false

private abbrev RadiusState := ℝ × ℝ

private def radiusField (q : ℝ → ℝ) (t : ℝ) (z : RadiusState) : RadiusState :=
  (z.2, -q t * z.1)

private theorem radiusField_zero (q : ℝ → ℝ) (t : ℝ) : radiusField q t 0 = 0 := by
  ext <;> simp [radiusField]

private theorem radiusField_lipschitz {q : ℝ → ℝ} {t : ℝ} {K : ℝ≥0}
    (hK : 1 ≤ (K : ℝ)) (hq : ‖q t‖ ≤ (K : ℝ)) :
    LipschitzWith K (radiusField q t) := by
  apply LipschitzWith.of_dist_le_mul
  intro p z
  simp only [dist_eq_norm, radiusField, Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
  rw [← mul_sub, norm_mul, norm_neg]
  refine max_le ?_ (mul_le_mul hq (le_max_left _ _) (norm_nonneg _) K.2)
  exact (le_max_right _ _).trans (le_mul_of_one_le_left
    ((norm_nonneg _).trans (le_max_left _ _)) hK)

private theorem contDiff_radiusField {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (Function.uncurry (radiusField q)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × RadiusState => (p.2.2, -q p.1 * p.2.1))
  exact (contDiff_snd.comp contDiff_snd).prodMk
    ((hq.comp contDiff_fst).neg.mul (contDiff_fst.comp contDiff_snd))

private def clipRadiusCoordinate (R x : ℝ) : ℝ :=
  min (max x (-R)) R

private def clipRadiusState (R : ℝ) (z : RadiusState) : RadiusState :=
  (clipRadiusCoordinate R z.1, clipRadiusCoordinate R z.2)

private theorem clipRadiusCoordinate_lipschitz (R : ℝ) :
    LipschitzWith 1 (clipRadiusCoordinate R) :=
  (LipschitzWith.id.max_const (-R)).min_const R

private theorem clipRadiusState_lipschitz (R : ℝ) : LipschitzWith 1 (clipRadiusState R) := by
  have h := clipRadiusCoordinate_lipschitz R
  have h₁ := h.comp (LipschitzWith.prod_fst : LipschitzWith 1 (@Prod.fst ℝ ℝ))
  have h₂ := h.comp (LipschitzWith.prod_snd : LipschitzWith 1 (@Prod.snd ℝ ℝ))
  change LipschitzWith 1 (fun z : RadiusState => (clipRadiusCoordinate R z.1, clipRadiusCoordinate R z.2))
  simpa only [Function.comp_apply, one_mul, max_self] using h₁.prodMk h₂

private theorem clipRadiusCoordinate_norm_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    ‖clipRadiusCoordinate R x‖ ≤ R := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩

private theorem clipRadiusState_norm_le {R : ℝ} (hR : 0 ≤ R) (z : RadiusState) :
    ‖clipRadiusState R z‖ ≤ R := by
  rw [Prod.norm_def]
  exact max_le (clipRadiusCoordinate_norm_le hR z.1) (clipRadiusCoordinate_norm_le hR z.2)

private theorem clipRadiusCoordinate_eq {R x : ℝ} (hx : ‖x‖ ≤ R) :
    clipRadiusCoordinate R x = x := by
  rw [Real.norm_eq_abs, abs_le] at hx
  rw [clipRadiusCoordinate, max_eq_left hx.1, min_eq_left hx.2]

private theorem clipRadiusState_eq {R : ℝ} {z : RadiusState} (hz : ‖z‖ ≤ R) :
    clipRadiusState R z = z := by
  rw [Prod.norm_def, max_le_iff] at hz
  exact Prod.ext (clipRadiusCoordinate_eq hz.1) (clipRadiusCoordinate_eq hz.2)

private theorem clipRadiusState_zero {R : ℝ} (hR : 0 ≤ R) :
    clipRadiusState R 0 = 0 := by
  apply clipRadiusState_eq
  simpa only [norm_zero] using hR

private theorem radius_norm_bound_from_left {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b K : ℝ} {z dz : ℝ → E} {z₀ : E}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt z (dz x) (Icc a b) x)
    (hinit : z a = z₀) (hbd : ∀ x ∈ Icc a b, ‖dz x‖ ≤ K * ‖z x‖) :
    ∀ x ∈ Icc a b, ‖z x‖ ≤ ‖z₀‖ * exp (K * (x - a)) := by
  intro x hx
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := z) (f' := dz) (δ := ‖z₀‖) (K := K) (ε := 0)
    (HasDerivWithinAt.continuousOn hd)
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (le_of_eq (congrArg (fun y : E => ‖y‖) hinit))
    (fun t ht => by simpa only [add_zero] using hbd t (Ico_subset_Icc_self ht)) x hx
  simpa only [gronwallBound_ε0] using h

private theorem radius_norm_bound_from_right {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b K : ℝ} {z dz : ℝ → E} {z₀ : E}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt z (dz x) (Icc a b) x)
    (hinit : z b = z₀) (hbd : ∀ x ∈ Icc a b, ‖dz x‖ ≤ K * ‖z x‖) :
    ∀ x ∈ Icc a b, ‖z x‖ ≤ ‖z₀‖ * exp (K * (b - x)) := by
  let w : ℝ → E := fun t => z (-t)
  let dw : ℝ → E := fun t => -dz (-t)
  have hm : MapsTo (fun t : ℝ => -t) (Icc (-b) (-a)) (Icc a b) := by
    intro t ht
    exact ⟨by simpa only [neg_neg] using neg_le_neg ht.2,
      by simpa only [neg_neg] using neg_le_neg ht.1⟩
  have hdw : ∀ t ∈ Icc (-b) (-a), HasDerivWithinAt w (dw t) (Icc (-b) (-a)) t := by
    intro t ht
    have hn : HasDerivWithinAt (fun s : ℝ => -s) (-1) (Icc (-b) (-a)) t :=
      (hasDerivAt_neg t).hasDerivWithinAt
    have hh := (hd (-t) (hm ht)).scomp t hn hm
    change HasDerivWithinAt w ((-1 : ℝ) • dz (-t)) (Icc (-b) (-a)) t at hh
    simpa only [dw, neg_one_smul] using hh
  have hi : w (-b) = z₀ := by simpa only [w, neg_neg] using hinit
  have hbw : ∀ t ∈ Icc (-b) (-a), ‖dw t‖ ≤ K * ‖w t‖ := by
    intro t ht
    simpa only [dw, w, norm_neg] using hbd (-t) (hm ht)
  intro x hx
  have hx' : -x ∈ Icc (-b) (-a) := ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩
  have hh := radius_norm_bound_from_left hdw hi hbw (-x) hx'
  change ‖z (-(-x))‖ ≤ ‖z₀‖ * exp (K * (-x - -b)) at hh
  rwa [neg_neg, show -x - -b = b - x by ring] at hh

private theorem exists_radiusState_on_Icc {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (z₀ : RadiusState) :
    ∃ z : ℝ → RadiusState, z t₀ = z₀ ∧ ContDiffOn ℝ ∞ z (Icc a b) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt z (radiusField q t (z t)) (Icc a b) t := by
  obtain ⟨K₀, hK₀⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    hq.continuous.continuousOn
  let K : ℝ≥0 := ⟨max 1 K₀, zero_le_one.trans (le_max_left _ _)⟩
  have hK : 1 ≤ (K : ℝ) := le_max_left _ _
  have hfield (t : ℝ) (ht : t ∈ Icc a b) : LipschitzWith K (radiusField q t) :=
    radiusField_lipschitz hK ((hK₀ t ht).trans (le_max_right _ _))
  let R : ℝ := ‖z₀‖ * exp ((K : ℝ) * (b - a)) + 1
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  let L : ℝ≥0 := ⟨(K : ℝ) * R, mul_nonneg K.2 hR⟩
  let W : ℝ≥0 := ⟨(L : ℝ) * (b - a), mul_nonneg L.2 (sub_nonneg.mpr (ht₀.1.trans ht₀.2))⟩
  let tstart : Icc a b := ⟨t₀, ht₀⟩
  let f : ℝ → RadiusState → RadiusState := fun t z => radiusField q t (clipRadiusState R z)
  have hf (t : ℝ) (ht : t ∈ Icc a b) : LipschitzWith K (f t) := by
    change LipschitzWith K (radiusField q t ∘ clipRadiusState R)
    simpa only [mul_one] using (hfield t ht).comp (clipRadiusState_lipschitz R)
  have hfzero (t : ℝ) : f t 0 = 0 := by
    change radiusField q t (clipRadiusState R 0) = 0
    rw [clipRadiusState_zero hR, radiusField_zero]
  have hfgrowth (t : ℝ) (ht : t ∈ Icc a b) (z : RadiusState) : ‖f t z‖ ≤ (K : ℝ) * ‖z‖ := by
    simpa only [hfzero, dist_zero_right] using (hf t ht).dist_le_mul z 0
  have hfbound (t : ℝ) (ht : t ∈ Icc a b) (z : RadiusState) : ‖f t z‖ ≤ (L : ℝ) := by
    have hz : ‖f t z‖ ≤ (K : ℝ) * ‖clipRadiusState R z‖ := by
      simpa only [radiusField_zero, dist_zero_right] using
        (hfield t ht).dist_le_mul (clipRadiusState R z) 0
    exact hz.trans (mul_le_mul_of_nonneg_left (clipRadiusState_norm_le hR z) K.2)
  have hPL : IsPicardLindelof f tstart z₀ W 0 L K := by
    refine ⟨fun t ht => (hf t ht).lipschitzOnWith, ?_, fun t ht z _ => hfbound t ht z, ?_⟩
    · intro z _
      have hc : Continuous (fun t : ℝ =>
          ((clipRadiusState R z).2, -q t * (clipRadiusState R z).1)) :=
        continuous_const.prodMk (hq.continuous.neg.mul continuous_const)
      exact hc.continuousOn
    · change (L : ℝ) * max (b - t₀) (t₀ - a) ≤ (L : ℝ) * (b - a) - 0
      rw [sub_zero]
      exact mul_le_mul_of_nonneg_left
        (max_le (by linarith only [ht₀.1]) (by linarith only [ht₀.2])) L.2
  obtain ⟨z, hz₀, hz⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  change z t₀ = z₀ at hz₀
  have hleft : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
  have hright : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
  have hL := radius_norm_bound_from_right
    (fun t ht => (hz t (hleft ht)).mono hleft) hz₀ (fun t ht => hfgrowth t (hleft ht) (z t))
  have hR' := radius_norm_bound_from_left
    (fun t ht => (hz t (hright ht)).mono hright) hz₀ (fun t ht => hfgrowth t (hright ht) (z t))
  have hbound (d : ℝ) (hd : d ≤ b - a) : ‖z₀‖ * exp ((K : ℝ) * d) ≤ R :=
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd K.2))
      (norm_nonneg z₀)).trans (le_add_of_nonneg_right zero_le_one)
  have hinside (t : ℝ) (ht : t ∈ Icc a b) : ‖z t‖ ≤ R := by
    by_cases h : t ≤ t₀
    · exact (hL t ⟨ht.1, h⟩).trans (hbound _ (by linarith only [ht.1, ht₀.2]))
    · exact (hR' t ⟨le_of_lt (lt_of_not_ge h), ht.2⟩).trans
        (hbound _ (by linarith only [ht.2, ht₀.1]))
  have horig (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt z (radiusField q t (z t)) (Icc a b) t := by
    have hd := hz t ht
    change HasDerivWithinAt z (radiusField q t (clipRadiusState R (z t))) (Icc a b) t at hd
    rw [clipRadiusState_eq (hinside t ht)] at hd
    exact hd
  exact ⟨z, hz₀, ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
    (u := univ) (contDiff_radiusField hq).contDiffOn horig (mapsTo_univ _ _), horig⟩

private theorem smooth_radiusState_extension {a b : ℝ} (hab : a ≤ b)
    {z dz : ℝ → RadiusState}
    (hs : ContDiffOn ℝ ∞ z (Icc (a - 3) (b + 3)))
    (hd : ∀ x ∈ Icc (a - 3) (b + 3), HasDerivWithinAt z (dz x) (Icc (a - 3) (b + 3)) x) :
    ∃ u : ℝ → RadiusState, ContDiff ℝ ∞ u ∧
      ∀ x ∈ Ioo (a - 1) (b + 1), (u =ᶠ[𝓝 x] z) ∧ HasDerivAt u (dz x) x := by
  let m : ℝ := (a + b) / 2
  let d : ℝ := (b - a) / 2
  let χ : ContDiffBump m :=
    ⟨d + 1, d + 2, by dsimp only [d]; linarith, by linarith⟩
  let u : ℝ → RadiusState := fun x => χ x • z x
  have hsupp : tsupport (χ : ℝ → ℝ) ⊆ Ioo (a - 3) (b + 3) := by
    rw [χ.tsupport_eq, Real.closedBall_eq_Icc]
    intro x hx
    change m - (d + 2) ≤ x ∧ x ≤ m + (d + 2) at hx
    change a - 3 < x ∧ x < b + 3
    dsimp only [m, d] at hx
    exact ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  refine ⟨u, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ tsupport (χ : ℝ → ℝ)
    · have hx' := hsupp hx
      exact χ.contDiffAt.smul (hs.contDiffAt (Icc_mem_nhds hx'.1 hx'.2))
    · have hχ := notMem_tsupport_iff_eventuallyEq.mp hx
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : RadiusState)) x).congr_of_eventuallyEq
      filter_upwards [hχ] with y hy
      change χ y = 0 at hy
      change χ y • z y = 0
      rw [hy, zero_smul]
  · intro x hx
    have hi : x ∈ Metric.ball m χ.rIn := by
      rw [Real.ball_eq_Ioo]
      change m - (d + 1) < x ∧ x < m + (d + 1)
      dsimp only [m, d]
      exact ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
    have heq : u =ᶠ[𝓝 x] z := by
      filter_upwards [χ.eventuallyEq_one_of_mem_ball hi] with y hy
      change χ y = 1 at hy
      change χ y • z y = z y
      rw [hy, one_smul]
    have hw : Icc (a - 3) (b + 3) ∈ 𝓝 x :=
      Icc_mem_nhds (by linarith only [hx.1]) (by linarith only [hx.2])
    exact ⟨heq, ((hd x (mem_of_mem_nhds hw)).hasDerivAt hw).congr_of_eventuallyEq heq⟩

theorem contDiff_morseRho (A B : ℝ) : ContDiff ℝ ∞ (morseRho A B) := by
  unfold morseRho
  exact (contDiff_const.mul (contDiff_id.neg.exp.sub (contDiff_const.mul contDiff_id).exp)).sub
    contDiff_const

/-- Arbitrary initial data at a point of the retained interval give a smooth
radius and velocity satisfying the actual system on a neighborhood of it. -/
theorem exists_morseRadiusSystem (A B : ℝ) {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (r₀ v₀ : ℝ) :
    ∃ r v : ℝ → ℝ, ContDiff ℝ ∞ r ∧ ContDiff ℝ ∞ v ∧ r t₀ = r₀ ∧ v t₀ = v₀ ∧
      ∀ x ∈ Ioo (a - 1) (b + 1), HasDerivAt r (v x) x ∧
        HasDerivAt v (-morseRho A B x * r x) x := by
  have hstart : t₀ ∈ Icc (a - 3) (b + 3) :=
    ⟨by linarith only [ht₀.1], by linarith only [ht₀.2]⟩
  obtain ⟨z, hz₀, hzs, hzd⟩ := exists_radiusState_on_Icc (contDiff_morseRho A B) hstart (r₀, v₀)
  obtain ⟨u, hus, hu⟩ := smooth_radiusState_extension (ht₀.1.trans ht₀.2) hzs hzd
  have hstart' : t₀ ∈ Ioo (a - 1) (b + 1) :=
    ⟨by linarith only [ht₀.1], by linarith only [ht₀.2]⟩
  have hu₀ : u t₀ = (r₀, v₀) := (hu t₀ hstart').1.eq_of_nhds.trans hz₀
  refine ⟨fun x => (u x).1, fun x => (u x).2, contDiff_fst.comp hus, contDiff_snd.comp hus,
    congrArg Prod.fst hu₀, congrArg Prod.snd hu₀, ?_⟩
  intro x hx
  have h := (hu x hx).2
  rw [← (hu x hx).1.eq_of_nhds] at h
  exact ⟨(ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt x h,
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt x h⟩

/-- The same finite-interval radius solves the actual scalar second-order
equation, including at both endpoints of the retained interval. -/
theorem exists_morseRadius (A B : ℝ) {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (r₀ v₀ : ℝ) :
    ∃ r : ℝ → ℝ, ContDiff ℝ ∞ r ∧ r t₀ = r₀ ∧ deriv r t₀ = v₀ ∧
      ∀ x ∈ Icc a b, deriv (deriv r) x = -morseRho A B x * r x := by
  obtain ⟨r, v, hrs, _, hr₀, hv₀, hd⟩ := exists_morseRadiusSystem A B ht₀ r₀ v₀
  have hsub : Icc a b ⊆ Ioo (a - 1) (b + 1) := by
    intro x hx
    exact ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  refine ⟨r, hrs, hr₀, ((hd t₀ (hsub ht₀)).1.deriv).trans hv₀, ?_⟩
  intro x hx
  have he : deriv r =ᶠ[𝓝 x] v := by
    have hx' := hsub hx
    filter_upwards [Ioo_mem_nhds hx'.1 hx'.2] with y hy
    exact (hd y hy).1.deriv
  exact he.deriv_eq.trans (hd x (hsub hx)).2.deriv

/-- The radius and its initial derivative determine the solution on the
retained interval. -/
theorem morseRadius_eqOn {A B a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) {r s : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hrEq : ∀ x ∈ Icc a b, deriv (deriv r) x = -morseRho A B x * r x)
    (hsEq : ∀ x ∈ Icc a b, deriv (deriv s) x = -morseRho A B x * s x)
    (h₀ : r t₀ = s t₀) (h₁ : deriv r t₀ = deriv s t₀) : EqOn r s (Icc a b) := by
  let q : ℝ → ℝ := morseRho A B
  let p (u : ℝ → ℝ) : ℝ → RadiusState := fun x => (u x, deriv u x)
  have hp (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u)
      (hEq : ∀ x ∈ Icc a b, deriv (deriv u) x = -q x * u x) (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (p u) (radiusField q x (p u x)) x := by
    have hd := ((hu.differentiable (by simp) x).hasDerivAt).prodMk
      (((contDiff_infty_iff_deriv.mp hu).2.differentiable (by simp) x).hasDerivAt)
    rw [hEq x hx] at hd
    exact hd
  have hdr := hp r hr hrEq
  have hds := hp s hs hsEq
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    (contDiff_morseRho A B).continuous.continuousOn
  let K : ℝ≥0 := ⟨max 1 C, zero_le_one.trans (le_max_left _ _)⟩
  have hLip (x : ℝ) (hx : x ∈ Icc a b) : LipschitzWith K (radiusField q x) :=
    radiusField_lipschitz (le_max_left _ _) ((hC x hx).trans (le_max_right _ _))
  have hstart : p r t₀ = p s t₀ := Prod.ext h₀ h₁
  have hleft : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
  have hright : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
  have hL := ODE_solution_unique_of_mem_Icc_left
    (v := radiusField q) (s := fun _ => univ) (f := p r) (g := p s) (a := a) (b := t₀)
    (fun x hx => (hLip x (hleft (Ioc_subset_Icc_self hx))).lipschitzOnWith)
    ((HasDerivAt.continuousOn hdr).mono hleft)
    (fun x hx => (hdr x (hleft (Ioc_subset_Icc_self hx))).hasDerivWithinAt)
    (fun _ _ => mem_univ _)
    ((HasDerivAt.continuousOn hds).mono hleft)
    (fun x hx => (hds x (hleft (Ioc_subset_Icc_self hx))).hasDerivWithinAt)
    (fun _ _ => mem_univ _) hstart
  have hR := ODE_solution_unique_of_mem_Icc_right
    (v := radiusField q) (s := fun _ => univ) (f := p r) (g := p s) (a := t₀) (b := b)
    (fun x hx => (hLip x (hright (Ico_subset_Icc_self hx))).lipschitzOnWith)
    ((HasDerivAt.continuousOn hdr).mono hright)
    (fun x hx => (hdr x (hright (Ico_subset_Icc_self hx))).hasDerivWithinAt)
    (fun _ _ => mem_univ _)
    ((HasDerivAt.continuousOn hds).mono hright)
    (fun x hx => (hds x (hright (Ico_subset_Icc_self hx))).hasDerivWithinAt)
    (fun _ _ => mem_univ _) hstart
  intro x hx
  by_cases h : x ≤ t₀
  · exact congrArg Prod.fst (hL (show x ∈ Icc a t₀ from ⟨hx.1, h⟩))
  · exact congrArg Prod.fst (hR (show x ∈ Icc t₀ b from ⟨le_of_lt (lt_of_not_ge h), hx.2⟩))

/-- The signed velocity identity holds in either time direction. -/
theorem morseRadius_velocity_eq_integral {A B a b t₀ x : ℝ} {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) (ht₀ : t₀ ∈ Icc a b) (hx : x ∈ Icc a b)
    (hEq : ∀ y ∈ Icc a b, deriv (deriv r) y = -morseRho A B y * r y) :
    deriv r x = deriv r t₀ - ∫ y in t₀..x, morseRho A B y * r y := by
  have hp := (contDiff_infty_iff_deriv.mp hr).2
  have hpp := (contDiff_infty_iff_deriv.mp hp).2
  have hFTC : (∫ y in t₀..x, deriv (deriv r) y) = deriv r x - deriv r t₀ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => (hp.differentiable (by simp) y).hasDerivAt)
      (hpp.continuous.intervalIntegrable t₀ x)
  have hInt : (∫ y in t₀..x, deriv (deriv r) y) = -(∫ y in t₀..x, morseRho A B y * r y) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y hy
    change deriv (deriv r) y = -(morseRho A B y * r y)
    rw [hEq y (uIcc_subset_Icc ht₀ hx hy)]
    ring
  rw [hInt] at hFTC
  linarith only [hFTC]

/-- The radius satisfies the actual Volterra formula with an oriented
interval integral. -/
theorem morseRadius_eq_volterra {A B a b t₀ x : ℝ} {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) (ht₀ : t₀ ∈ Icc a b) (hx : x ∈ Icc a b)
    (hEq : ∀ y ∈ Icc a b, deriv (deriv r) y = -morseRho A B y * r y) :
    r x = r t₀ + deriv r t₀ * (x - t₀) -
      ∫ y in t₀..x, (x - y) * morseRho A B y * r y := by
  let g : ℝ → ℝ := fun y => r y + (x - y) * deriv r y
  have hp := (contDiff_infty_iff_deriv.mp hr).2
  have hpp := (contDiff_infty_iff_deriv.mp hp).2
  have hD (y : ℝ) : HasDerivAt g ((x - y) * deriv (deriv r) y) y := by
    have h := ((hr.differentiable (by simp) y).hasDerivAt).add
      (((hasDerivAt_const y x).sub (hasDerivAt_id y)).mul
        ((hp.differentiable (by simp) y).hasDerivAt))
    apply h.congr_deriv
    change deriv r y + ((0 - 1) * deriv r y + (x - y) * deriv (deriv r) y) =
      (x - y) * deriv (deriv r) y
    ring
  have hFTC : (∫ y in t₀..x, (x - y) * deriv (deriv r) y) =
      r x - (r t₀ + (x - t₀) * deriv r t₀) := by
    have hc : Continuous (fun y => (x - y) * deriv (deriv r) y) :=
      (continuous_const.sub continuous_id).mul hpp.continuous
    simpa only [g, sub_self, zero_mul, add_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hD y) (hc.intervalIntegrable t₀ x)
  have hInt : (∫ y in t₀..x, (x - y) * deriv (deriv r) y) =
      -(∫ y in t₀..x, (x - y) * morseRho A B y * r y) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y hy
    change (x - y) * deriv (deriv r) y = -((x - y) * morseRho A B y * r y)
    rw [hEq y (uIcc_subset_Icc ht₀ hx hy)]
    ring
  rw [hInt] at hFTC
  rw [mul_comm (deriv r t₀) (x - t₀)]
  linarith only [hFTC]

end ContinuousFlexibility.Radial
