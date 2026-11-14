module

public import ContinuousFlexibility.Radial.DeepTailEdgeComparison

/-!
# Uniform control of the actual tail flux

Cauchy's mean value theorem finds one point where the flux is the endpoint
increment divided by the total resistance. The differential equation then
controls its variation on the edge. No lower bound on the physical edge
length, and no derivative of the density, is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

theorem tail_abs_sub_le_of_derivative_bound {f f' : ℝ → ℝ} {a b C : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hb : ∀ x ∈ Ioo a b, |f' x| ≤ C)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f x - f y| ≤ C * |x - y| := by
  have hforward {l r : ℝ} (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) (hlt : l < r) :
      |f r - f l| ≤ C * (r - l) := by
    have hs : Icc l r ⊆ Icc a b := fun _ hz => ⟨hl.1.trans hz.1, hz.2.trans hr.2⟩
    have hi : Ioo l r ⊆ Ioo a b := fun _ hz =>
      ⟨hl.1.trans_lt hz.1, hz.2.trans_le hr.2⟩
    obtain ⟨z, hz, he⟩ := exists_hasDerivAt_eq_slope f f' hlt (hc.mono hs)
      (fun z hz => hd z (hi hz))
    have hh := hb z (hi hz)
    rw [he, abs_div, abs_of_pos (sub_pos.mpr hlt)] at hh
    exact (div_le_iff₀ (sub_pos.mpr hlt)).mp hh
  rcases lt_trichotomy x y with hlt | rfl | hlt
  · have h := hforward hx hy hlt
    calc
      _ = |f y - f x| := abs_sub_comm _ _
      _ ≤ C * (y - x) := h
      _ = _ := by rw [abs_of_neg (sub_neg.mpr hlt)]; ring
  · simp
  · simpa only [abs_of_pos (sub_pos.mpr hlt)] using hforward hy hx hlt

/-- A bound for the physical flux of any actual divergence-form solution. -/
theorem tail_flux_bound_of_height_bound {p u : ℝ → ℝ} {a b Λ P M : ℝ}
    (hab : a < b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (hΛ : 0 ≤ Λ)
    (hu : ContinuousOn u (Icc a b)) (hdu : ContinuousOn (deriv u) (Icc a b))
    (huD : ∀ x ∈ Ioo a b, HasDerivAt u (deriv u x) x)
    (hflux : ∀ x ∈ Ioo a b,
      HasDerivAt (fun y => p y * deriv u y) (-(Λ * p x * u x)) x)
    (hP : ∀ x ∈ Icc a b, p x ≤ P) (hM : ∀ x ∈ Icc a b, |u x| ≤ M)
    {x : ℝ} (hx : x ∈ Icc a b) :
    |p x * deriv u x| ≤ (|u a| + |u b|) / (∫ t in a..b, (p t)⁻¹) +
      Λ * P * M * (b - a) := by
  let S := tailResistanceChart (tailClampedDensity p a b hab.le) a
  have hSc : Continuous S := continuous_iff_continuousAt.mpr fun y =>
    (hasDerivAt_tailResistanceChart (tailClampedDensity_continuous hab.le hp)
      (tailClampedDensity_pos hab.le hpos) a y).continuousAt
  have hL : 0 < ∫ t in a..b, (p t)⁻¹ := by
    have hS := tailResistanceChart_strictMono (tailClampedDensity_continuous hab.le hp)
      (tailClampedDensity_pos hab.le hpos) a hab
    rw [← sub_pos] at hS
    rwa [tailClampedResistanceChart_sub hab.le hp hpos ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩] at hS
  obtain ⟨c, hc, he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope u (deriv u) hab hu huD
    S (fun y => (p y)⁻¹) hSc.continuousOn
    (fun y hy => hasDerivAt_tailClampedResistanceChart hab.le hp hpos (Ioo_subset_Icc_self hy))
  rw [tailClampedResistanceChart_sub hab.le hp hpos ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩] at he
  have hcflux : p c * deriv u c = (u b - u a) / (∫ t in a..b, (p t)⁻¹) := by
    apply (eq_div_iff hL.ne').mpr
    calc
      _ = (∫ t in a..b, (p t)⁻¹) * deriv u c * p c := by ring
      _ = (u b - u a) * (p c)⁻¹ * p c := by rw [he]
      _ = _ := by rw [mul_assoc, inv_mul_cancel₀ (hpos c (Ioo_subset_Icc_self hc)).ne', mul_one]
  have hP₀ : 0 ≤ P := (hpos a ⟨le_rfl, hab.le⟩).le.trans (hP a ⟨le_rfl, hab.le⟩)
  have hM₀ : 0 ≤ M := (abs_nonneg (u a)).trans (hM a ⟨le_rfl, hab.le⟩)
  have hbound (y : ℝ) (hy : y ∈ Ioo a b) : |-(Λ * p y * u y)| ≤ Λ * P * M := by
    have hy' := Ioo_subset_Icc_self hy
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hΛ, abs_of_pos (hpos y hy')]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hP y hy') hΛ)
      (hM y hy') (abs_nonneg _) (mul_nonneg hΛ hP₀)
  have hdiff := tail_abs_sub_le_of_derivative_bound (hp.mul hdu) hflux hbound
    hx (Ioo_subset_Icc_self hc)
  have hdist : |x - c| ≤ b - a := abs_le.mpr ⟨by linarith [hx.1, hc.2], by linarith [hx.2, hc.1]⟩
  have hdelta : |u b - u a| ≤ |u a| + |u b| := by
    simpa only [sub_eq_add_neg, abs_neg, add_comm] using abs_add_le (u b) (-(u a))
  calc
    _ = |p c * deriv u c + (p x * deriv u x - p c * deriv u c)| := by congr 1; ring
    _ ≤ |p c * deriv u c| + |p x * deriv u x - p c * deriv u c| := abs_add_le _ _
    _ ≤ |p c * deriv u c| + Λ * P * M * |x - c| := add_le_add le_rfl hdiff
    _ ≤ |p c * deriv u c| + Λ * P * M * (b - a) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hdist (mul_nonneg (mul_nonneg hΛ hP₀) hM₀))
    _ = |u b - u a| / (∫ t in a..b, (p t)⁻¹) + Λ * P * M * (b - a) := by
      rw [hcflux, abs_div, abs_of_pos hL]
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hdelta hL.le) le_rfl

theorem deepTail_mass_le_density_bound {T : DeepTailData} (hT : DeepTailHypotheses T)
    {P : ℝ} (hP₀ : 0 ≤ P) (hP : ∀ x ∈ Ico T.entrance T.endpoint, T.p x ≤ P)
    (n : ℕ) : tailMass T n ≤ P * (T.endpoint - T.entrance) := by
  have hab := deepTail_node_lt_massEnd hT n
  have hsub := deepTail_Icc_subset hT (deepTail_entrance_le_node hT n)
    (deepTail_massEnd_lt_endpoint hT n)
  have hp := (deepTail_contDiffOn hT).continuousOn.mono hsub
  calc
    _ ≤ ∫ x in T.node n..T.massEnd n, P :=
      intervalIntegral.integral_mono_on hab.le (hp.intervalIntegrable_of_Icc hab.le)
        (continuous_const.intervalIntegrable _ _) (fun x hx => hP x (hsub hx))
    _ = P * (T.massEnd n - T.node n) := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by linarith [deepTail_massEnd_lt_endpoint hT n, deepTail_entrance_le_node hT n]) hP₀

theorem deepTail_whole_resistance_ge {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) : tailResistance T n ≤
      ∫ x in T.node n..T.node (n + 1), (T.p x)⁻¹ := by
  have hsub := deepTail_Icc_subset hT (deepTail_entrance_le_node hT n)
    (deepTail_node_lt_endpoint hT (n + 1))
  have hi : ContinuousOn (fun x => (T.p x)⁻¹) (Icc (T.node n) (T.node (n + 1))) :=
    ((deepTail_contDiffOn hT).continuousOn.mono hsub).inv₀
      (fun x hx => (deepTail_pos hT x (hsub hx)).ne')
  have h₀ : IntervalIntegrable (fun x => (T.p x)⁻¹) volume (T.node n) (T.massEnd n) :=
    (hi.mono (fun x (hx : x ∈ Icc (T.node n) (T.massEnd n)) =>
      ⟨hx.1, hx.2.trans (deepTail_massEnd_lt_succ_node hT n).le⟩)).intervalIntegrable_of_Icc
        (deepTail_node_lt_massEnd hT n).le
  have h₁ : IntervalIntegrable (fun x => (T.p x)⁻¹) volume (T.massEnd n) (T.node (n + 1)) :=
    (hi.mono (fun x (hx : x ∈ Icc (T.massEnd n) (T.node (n + 1))) =>
      ⟨(deepTail_node_lt_massEnd hT n).le.trans hx.1, hx.2⟩)).intervalIntegrable_of_Icc
        (deepTail_massEnd_lt_succ_node hT n).le
  have heq : (∫ x in T.node n..T.node (n + 1), (T.p x)⁻¹) =
      tailInnerResistance T n + tailResistance T n :=
    (intervalIntegral.integral_add_adjacent_intervals h₀ h₁).symm
  rw [heq]
  exact le_add_of_nonneg_left (tailInnerResistance_pos hT n).le

/-- A global upper bound for the original density gives one flux constant
for every edge of a deep tail. -/
theorem tailNatural_flux_edge_bound {T : DeepTailData} {u : ℝ → ℝ}
    (hT : DeepTailHypotheses T) (hu : TailNaturalEquation T u)
    (hη : T.η ≤ 1 / 2) {P : ℝ} (hP₀ : 0 < P)
    (hP : ∀ x ∈ Ico T.entrance T.endpoint, T.p x ≤ P)
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
    |T.p x * deriv u x| ≤ 3 * T.Λ * P * (T.endpoint - T.entrance) *
      (|u (T.node n)| + |u (T.node (n + 1))|) := by
  have hΛ : 0 < T.Λ := hT.2.2.1
  have hab := deepTail_node_strictMono hT (Nat.lt_succ_self n)
  have hsub := deepTail_Icc_subset hT (deepTail_entrance_le_node hT n)
    (deepTail_node_lt_endpoint hT (n + 1))
  have hinterior : Ioo (T.node n) (T.node (n + 1)) ⊆ Ioo T.entrance T.endpoint :=
    fun _ hy => ⟨(deepTail_entrance_le_node hT n).trans_lt hy.1,
      hy.2.trans (deepTail_node_lt_endpoint hT (n + 1))⟩
  have hp := (deepTail_contDiffOn hT).continuousOn.mono hsub
  have hpos := fun y hy => deepTail_pos hT y (hsub hy)
  have huC : ContinuousOn u (Icc (T.node n) (T.node (n + 1))) :=
    fun y hy => (tailNatural_contDiffAt_Ico hu (hsub hy)).continuousAt.continuousWithinAt
  have hduC : ContinuousOn (deriv u) (Icc (T.node n) (T.node (n + 1))) :=
    fun y hy => ((tailNatural_contDiffAt_Ico hu (hsub hy)).derivWithin
      (m := 1) (by simp)).continuousAt.continuousWithinAt
  have hbound := tail_flux_bound_of_height_bound hab hp hpos hT.2.2.1.le huC hduC
    (fun y hy => ((tailNatural_contDiffAt_Ico hu
      (Ioo_subset_Ico_self (hinterior hy))).differentiableAt (by simp)).hasDerivAt)
    (fun _ hy => tailNatural_hasFluxDerivAt hT hu (hinterior hy))
    (fun y hy => hP y (hsub hy)) (fun _ hy => tailNatural_edge_bound hT hu hη n hy) hx
  have hres : 1 / (∫ t in T.node n..T.node (n + 1), (T.p t)⁻¹) ≤
      T.Λ * P * (T.endpoint - T.entrance) := by
    calc
      _ ≤ 1 / tailResistance T n := one_div_le_one_div_of_le
        (tailResistance_pos hT n) (deepTail_whole_resistance_ge hT n)
      _ ≤ T.Λ * tailMass T n / T.K := by
        simpa only [one_div] using deepTail_inverse_resistance_left hT n
      _ ≤ T.Λ * tailMass T n :=
        div_le_self (mul_nonneg hT.2.2.1.le (tailMass_pos hT n).le)
          hT.2.2.2.2.2.2.1.le
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (deepTail_mass_le_density_bound hT hP₀.le hP n) hT.2.2.1.le
  have hsum : 0 ≤ |u (T.node n)| + |u (T.node (n + 1))| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hspan : T.node (n + 1) - T.node n ≤ T.endpoint - T.entrance := by
    linarith [deepTail_node_lt_endpoint hT (n + 1), deepTail_entrance_le_node hT n]
  apply hbound.trans
  calc
    _ = (1 / (∫ t in T.node n..T.node (n + 1), (T.p t)⁻¹)) *
        (|u (T.node n)| + |u (T.node (n + 1))|) +
        T.Λ * P * (2 * (|u (T.node n)| + |u (T.node (n + 1))|)) *
          (T.node (n + 1) - T.node n) := by ring
    _ ≤ (T.Λ * P * (T.endpoint - T.entrance)) *
        (|u (T.node n)| + |u (T.node (n + 1))|) +
        T.Λ * P * (2 * (|u (T.node n)| + |u (T.node (n + 1))|)) *
          (T.endpoint - T.entrance) :=
      add_le_add (mul_le_mul_of_nonneg_right hres hsum)
        (mul_le_mul_of_nonneg_left hspan (by positivity))
    _ = _ := by ring

end ContinuousFlexibility.Radial
