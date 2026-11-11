import ContinuousFlexibility.Analysis.ReturnCorrectedFlow
import ContinuousFlexibility.Analysis.ReturnCorrectionCoefficients
import ContinuousFlexibility.Analysis.ReturnCorrectionCutoff

/-!
# Actual corrected coefficients on the disjoint negative components

The coefficient candidate uses the velocity of the actual corrected flow.
The unchanged radial coefficient and the reflected pair of slopes determine
the two remaining coefficients. The patch is active only where the cutoff
derivative is nonzero. It therefore agrees with the original coefficients
near every positive point and every simple turning point.

The final characteristic-speed identification needs positivity of the
reconstructed speed. The quantitative estimate giving that positivity on
one neighborhood for all components is deliberately not assumed to follow
from these qualitative patching arguments.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Isolation of a zero forces all middle-third cutoff derivatives to
vanish on one neighborhood of it, uniformly over the intervals. -/
theorem returnCorrectionCutoff_deriv_eventually_zero_at_isolated_root
    (l h : ℕ → ℝ) (f : ℝ → ℝ) (r₀ : ℝ)
    (hlh : ∀ m, l m < h m) (hroot : ∀ m, f (l m) = 0 ∧ f (h m) = 0)
    (hneg : ∀ m r, r ∈ Ioo (l m) (h m) → f r < 0) (hr₀ : f r₀ = 0)
    (hiso : ∀ᶠ r in 𝓝 r₀, f r = 0 → r = r₀) :
    ∀ᶠ r in 𝓝 r₀, ∀ m, deriv (returnCorrectionCutoff (l m) (h m)) r = 0 := by
  obtain ⟨δ, hδ, hisoδ⟩ := Metric.mem_nhds_iff.mp hiso
  filter_upwards [Metric.ball_mem_nhds r₀ (div_pos hδ (by norm_num : (0 : ℝ) < 4))]
    with r hr
  have hrabs : |r - r₀| < δ / 4 := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
  obtain ⟨hrlo, hrhi⟩ := abs_lt.mp hrabs
  intro m
  by_contra hderiv
  have hmid := returnCorrectionCutoff_deriv_support_subset (hlh m) hderiv
  have hside : r₀ ≤ l m ∨ h m ≤ r₀ := by
    by_cases hl : r₀ ≤ l m
    · exact Or.inl hl
    · right
      by_contra hh
      have hn := hneg m r₀ ⟨lt_of_not_ge hl, lt_of_not_ge hh⟩
      linarith
  rcases hside with hl | hh
  · have hhball : h m ∈ Metric.ball r₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hmid.1, hlh m]
    have heq := hisoδ hhball (hroot m).2
    linarith [hlh m]
  · have hlball : l m ∈ Metric.ball r₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hmid.2, hlh m]
    have heq := hisoδ hlball (hroot m).1
    linarith [hlh m]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

/-- The explicit interpolation cutoff on each component. -/
def returnCorrectionCutoffs {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (m : ℕ) : ℝ → ℝ := returnCorrectionCutoff (C.left m) (C.right m)

theorem returnCorrectionCutoffs_apply {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (m : ℕ) (r : ℝ) : returnCorrectionCutoffs C m r =
      returnCorrectionCutoff (C.left m) (C.right m) r := rfl

/-- Reconstruction from the actual corrected minus speed and its
reflected plus speed on one negative component. -/
def returnCorrectedComponentCoefficients (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) : SymmetricCoefficients :=
  returnCorrectionCoefficients (originalCoefficients D S C z).a
    (fun p => (-returnCorrectedMinusSpeed D S C χ z m (p.1, -p.2) +
      returnCorrectedMinusSpeed D S C χ z m p) / 2)
    (fun p => (-returnCorrectedMinusSpeed D S C χ z m (p.1, -p.2) -
      returnCorrectedMinusSpeed D S C χ z m p) / 2)

/-- Global patch of the actual corrected coefficients. The radial
coefficient is unchanged. Selection is restricted to the support of the
cutoff derivative inside a negative component. -/
def returnCorrectedCoefficients (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) : SymmetricCoefficients where
  a := (originalCoefficients D S C z).a
  b := fun p => if h : ∃ m, p.1 ∈ Ioo (C.left m) (C.right m) ∧ deriv (χ m) p.1 ≠ 0 then
    (returnCorrectedComponentCoefficients D S C χ z (Classical.choose h)).b p
    else (originalCoefficients D S C z).b p
  c := fun p => if h : ∃ m, p.1 ∈ Ioo (C.left m) (C.right m) ∧ deriv (χ m) p.1 ≠ 0 then
    (returnCorrectedComponentCoefficients D S C χ z (Classical.choose h)).c p
    else (originalCoefficients D S C z).c p

theorem returnCorrectedCoefficients_a (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) :
    (returnCorrectedCoefficients D S C χ z).a = (originalCoefficients D S C z).a := rfl

theorem returnCorrectedCoefficients_eq_original_at_of_inactive
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (p : PolarPoint)
    (hp : ¬∃ m, p.1 ∈ Ioo (C.left m) (C.right m) ∧ deriv (χ m) p.1 ≠ 0) :
    (returnCorrectedCoefficients D S C χ z).b p = (originalCoefficients D S C z).b p ∧
    (returnCorrectedCoefficients D S C χ z).c p = (originalCoefficients D S C z).c p := by
  simp only [returnCorrectedCoefficients, dif_neg hp, and_self]

theorem returnCorrectedCoefficients_eq_component_at
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hdisj : ∀ m n, m ≠ n → Disjoint (Ioo (C.left m) (C.right m))
      (Ioo (C.left n) (C.right n)))
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint)
    (hp : p.1 ∈ Ioo (C.left m) (C.right m)) (hχ : deriv (χ m) p.1 ≠ 0) :
    (returnCorrectedCoefficients D S C χ z).b p =
        (returnCorrectedComponentCoefficients D S C χ z m).b p ∧
    (returnCorrectedCoefficients D S C χ z).c p =
        (returnCorrectedComponentCoefficients D S C χ z m).c p := by
  have hex : ∃ n, p.1 ∈ Ioo (C.left n) (C.right n) ∧ deriv (χ n) p.1 ≠ 0 :=
    ⟨m, hp, hχ⟩
  have hm : Classical.choose hex = m := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj _ _ hne) (Classical.choose_spec hex).1 hp
  simp only [returnCorrectedCoefficients, dif_pos hex, hm, and_self]

theorem returnCorrectedCoefficients_eq_original_at_of_deriv_zero
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hdisj : ∀ m n, m ≠ n → Disjoint (Ioo (C.left m) (C.right m))
      (Ioo (C.left n) (C.right n)))
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint)
    (hp : p.1 ∈ Ioo (C.left m) (C.right m)) (hχ : deriv (χ m) p.1 = 0) :
    (returnCorrectedCoefficients D S C χ z).b p = (originalCoefficients D S C z).b p ∧
    (returnCorrectedCoefficients D S C χ z).c p = (originalCoefficients D S C z).c p := by
  apply returnCorrectedCoefficients_eq_original_at_of_inactive
  rintro ⟨n, hn, hχn⟩
  by_cases hnm : n = m
  · subst n
    exact hχn hχ
  · exact Set.disjoint_left.mp (hdisj _ _ hnm) hn hp

/-- Ordered actual corrected slopes give exactly the characteristic
speeds of the local reconstructed coefficient object. -/
theorem returnCorrectedComponentCoefficients_characteristicSpeeds
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint)
    (ha : 0 < (originalCoefficients D S C z).a p)
    (hv : returnCorrectedMinusSpeed D S C χ z m p ≤
      -returnCorrectedMinusSpeed D S C χ z m (p.1, -p.2)) :
    minusCharacteristicSpeed (returnCorrectedComponentCoefficients D S C χ z m) p =
        returnCorrectedMinusSpeed D S C χ z m p ∧
    plusCharacteristicSpeed (returnCorrectedComponentCoefficients D S C χ z m) p =
        -returnCorrectedMinusSpeed D S C χ z m (p.1, -p.2) := by
  exact returnCorrectionCoefficients_of_slopes (originalCoefficients D S C z).a
    (returnCorrectedMinusSpeed D S C χ z m)
    (fun q => -returnCorrectedMinusSpeed D S C χ z m (q.1, -q.2)) p ha hv

/-- The global coefficient candidate has the actual corrected minus
speed throughout every negative component, once that speed is positive
in the required reflected sense. -/
theorem returnCorrectedCoefficients_minusCharacteristicSpeed
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hdisj : ∀ m n, m ≠ n → Disjoint (Ioo (C.left m) (C.right m))
      (Ioo (C.left n) (C.right n)))
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint)
    (hp : p.1 ∈ Ioo (C.left m) (C.right m))
    (ha : 0 < (originalCoefficients D S C z).a p)
    (hv : returnCorrectedMinusSpeed D S C χ z m p ≤
      -returnCorrectedMinusSpeed D S C χ z m (p.1, -p.2)) :
    minusCharacteristicSpeed (returnCorrectedCoefficients D S C χ z) p =
      returnCorrectedMinusSpeed D S C χ z m p := by
  by_cases hχ : deriv (χ m) p.1 = 0
  · obtain ⟨hb, hc⟩ := returnCorrectedCoefficients_eq_original_at_of_deriv_zero
      hdisj χ z m p hp hχ
    simp only [returnCorrectedMinusSpeed, hχ, mul_zero, zero_mul, add_zero,
      minusCharacteristicSpeed, returnCorrectedCoefficients_a, hb, hc]
  · obtain ⟨hb, hc⟩ := returnCorrectedCoefficients_eq_component_at hdisj χ z m p hp hχ
    have hs := (returnCorrectedComponentCoefficients_characteristicSpeeds D S C χ z m p
      ha hv).1
    simpa only [minusCharacteristicSpeed, returnCorrectedCoefficients_a, hb, hc,
      returnCorrectedComponentCoefficients, returnCorrectionCoefficients_a] using hs

/-- Reflection of the actual symmetric coefficients reflects the two
characteristic families. -/
theorem minusCharacteristicSpeed_reflection (L : SymmetricCoefficients) (r θ : ℝ)
    (ha : L.a (r, -θ) = L.a (r, θ))
    (hb : L.b (r, -θ) = -L.b (r, θ))
    (hc : L.c (r, -θ) = L.c (r, θ)) :
    minusCharacteristicSpeed L (r, -θ) = -plusCharacteristicSpeed L (r, θ) := by
  simp only [minusCharacteristicSpeed, plusCharacteristicSpeed, ha, hb, hc, neg_sq, neg_div]
  ring

/-- The exact scalar bound needed for positivity of the actual corrected
speed. Supplying it uniformly in the state and component is the weighted
analytic step of N03. -/
theorem returnCorrectedComponentSpeed_positive_of_error_bound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (r θ : ℝ)
    (hreflection : minusCharacteristicSpeed (originalCoefficients D S C z) (r, -θ) =
      -plusCharacteristicSpeed (originalCoefficients D S C z) (r, θ))
    (hv : 0 < Real.sqrt ((originalCoefficients D S C z).b (r, θ) ^ 2 -
      (originalCoefficients D S C z).a (r, θ) * (originalCoefficients D S C z).c (r, θ)) /
        (originalCoefficients D S C z).a (r, θ))
    (hminus : |returnCorrectedMinusSpeed D S C χ z m (r, θ) -
      minusCharacteristicSpeed (originalCoefficients D S C z) (r, θ)| ≤
      (Real.sqrt ((originalCoefficients D S C z).b (r, θ) ^ 2 -
        (originalCoefficients D S C z).a (r, θ) * (originalCoefficients D S C z).c (r, θ)) /
          (originalCoefficients D S C z).a (r, θ)) / 2)
    (hreflected : |returnCorrectedMinusSpeed D S C χ z m (r, -θ) -
      minusCharacteristicSpeed (originalCoefficients D S C z) (r, -θ)| ≤
      (Real.sqrt ((originalCoefficients D S C z).b (r, θ) ^ 2 -
        (originalCoefficients D S C z).a (r, θ) * (originalCoefficients D S C z).c (r, θ)) /
          (originalCoefficients D S C z).a (r, θ)) / 2) :
    0 < (-returnCorrectedMinusSpeed D S C χ z m (r, -θ) -
      returnCorrectedMinusSpeed D S C χ z m (r, θ)) / 2 := by
  have hp := (returnCorrection_speed_positive hv hminus
    (show |-(returnCorrectedMinusSpeed D S C χ z m (r, -θ) -
      minusCharacteristicSpeed (originalCoefficients D S C z) (r, -θ))| ≤ _ by
        simpa only [abs_neg] using hreflected)).2
  rw [hreflection] at hp
  simp only [minusCharacteristicSpeed, plusCharacteristicSpeed] at hp
  linarith

theorem returnCorrectedComponentCoefficients_parity
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ)
    (ha : ∀ r θ, (originalCoefficients D S C z).a (r, -θ) =
      (originalCoefficients D S C z).a (r, θ)) (r θ : ℝ) :
    (returnCorrectedComponentCoefficients D S C χ z m).a (r, -θ) =
        (returnCorrectedComponentCoefficients D S C χ z m).a (r, θ) ∧
    (returnCorrectedComponentCoefficients D S C χ z m).b (r, -θ) =
        -(returnCorrectedComponentCoefficients D S C χ z m).b (r, θ) ∧
    (returnCorrectedComponentCoefficients D S C χ z m).c (r, -θ) =
        (returnCorrectedComponentCoefficients D S C χ z m).c (r, θ) := by
  apply returnCorrectionCoefficients_parity _ _ _ ha
  · intro s t
    simpa only using (returnCorrection_reflected_parity
      (fun q => returnCorrectedMinusSpeed D S C χ z m (s, q)) t).1
  · intro s t
    simpa only using (returnCorrection_reflected_parity
      (fun q => returnCorrectedMinusSpeed D S C χ z m (s, q)) t).2

theorem returnCorrectedCoefficients_parity
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (ha : ∀ r θ, (originalCoefficients D S C z).a (r, -θ) =
      (originalCoefficients D S C z).a (r, θ))
    (hb : ∀ r θ, (originalCoefficients D S C z).b (r, -θ) =
      -(originalCoefficients D S C z).b (r, θ))
    (hc : ∀ r θ, (originalCoefficients D S C z).c (r, -θ) =
      (originalCoefficients D S C z).c (r, θ)) (r θ : ℝ) :
    (returnCorrectedCoefficients D S C χ z).a (r, -θ) =
        (returnCorrectedCoefficients D S C χ z).a (r, θ) ∧
    (returnCorrectedCoefficients D S C χ z).b (r, -θ) =
        -(returnCorrectedCoefficients D S C χ z).b (r, θ) ∧
    (returnCorrectedCoefficients D S C χ z).c (r, -θ) =
        (returnCorrectedCoefficients D S C χ z).c (r, θ) := by
  refine ⟨ha r θ, ?_⟩
  by_cases hex : ∃ m, r ∈ Ioo (C.left m) (C.right m) ∧ deriv (χ m) r ≠ 0
  · simpa only [returnCorrectedCoefficients, dif_pos hex] using
      (returnCorrectedComponentCoefficients_parity D S C χ z (Classical.choose hex) ha r θ).2
  · simpa only [returnCorrectedCoefficients, dif_neg hex] using ⟨hb r θ, hc r θ⟩

theorem returnCorrectedCoefficients_eventuallyEq_of_deriv_eventually_zero
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (p : PolarPoint)
    (hχ : ∀ᶠ r in 𝓝 p.1, ∀ m, deriv (χ m) r = 0) :
    (returnCorrectedCoefficients D S C χ z).b =ᶠ[𝓝 p] (originalCoefficients D S C z).b ∧
    (returnCorrectedCoefficients D S C χ z).c =ᶠ[𝓝 p] (originalCoefficients D S C z).c := by
  have hp : ∀ᶠ q : PolarPoint in 𝓝 p, ∀ m, deriv (χ m) q.1 = 0 :=
    continuous_fst.continuousAt.preimage_mem_nhds hχ
  have heq : ∀ᶠ q : PolarPoint in 𝓝 p,
      (returnCorrectedCoefficients D S C χ z).b q = (originalCoefficients D S C z).b q ∧
      (returnCorrectedCoefficients D S C χ z).c q = (originalCoefficients D S C z).c q := by
    filter_upwards [hp] with q hq
    apply returnCorrectedCoefficients_eq_original_at_of_inactive
    rintro ⟨m, _, hm⟩
    exact hm (hq m)
  exact ⟨heq.mono fun _ h => h.1, heq.mono fun _ h => h.2⟩

/-- The actual global patch is unchanged on a neighborhood of every
positive point. No state-dependent neighborhood is needed here. -/
theorem N01Properties.returnCorrectedCoefficients_eventuallyEq_at_positive
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) (p : PolarPoint) (hp : 0 < deriv D.w p.1) :
    (returnCorrectedCoefficients D S C (returnCorrectionCutoffs C) z).b
        =ᶠ[𝓝 p] (originalCoefficients D S C z).b ∧
    (returnCorrectedCoefficients D S C (returnCorrectionCutoffs C) z).c
        =ᶠ[𝓝 p] (originalCoefficients D S C z).c := by
  obtain ⟨bounds, hbounds⟩ := hN01.1.1
  have hw : ContDiff ℝ ∞ D.w := hbounds.1.2.2.1.1
  have hc := (hw.continuous_deriv (by norm_num)).continuousAt
  have hpos : ∀ᶠ r in 𝓝 p.1, 0 < deriv D.w r :=
    hc.preimage_mem_nhds (Ioi_mem_nhds hp)
  rcases hN01 with ⟨_, _, _, hcontrol, _⟩
  apply returnCorrectedCoefficients_eventuallyEq_of_deriv_eventually_zero
  filter_upwards [hpos] with r hr
  intro m
  by_contra hne
  have hm := returnCorrectionCutoff_deriv_support_subset_component
    (hcontrol.1 m).2.1 hne
  have hn := hcontrol.2.2.2.1 m r hm
  linarith

/-- At every simple turning point all patching terms vanish on one
neighborhood, simultaneously for every negative component. -/
theorem N01Properties.returnCorrectedCoefficients_eventuallyEq_at_root
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) (p : PolarPoint) (hp : p ∈ annularOpen D)
    (hroot : deriv D.w p.1 = 0) :
    (returnCorrectedCoefficients D S C (returnCorrectionCutoffs C) z).b
        =ᶠ[𝓝 p] (originalCoefficients D S C z).b ∧
    (returnCorrectedCoefficients D S C (returnCorrectionCutoffs C) z).c
        =ᶠ[𝓝 p] (originalCoefficients D S C z).c := by
  obtain ⟨bounds, hbounds⟩ := hN01.1.1
  have hsimple : deriv (deriv D.w) p.1 ≠ 0 :=
    hbounds.1.2.2.2.2.2.2 p.1 hp.1 hroot
  have hne : ∀ᶠ r in 𝓝[≠] p.1, deriv D.w r ≠ 0 :=
    (differentiableAt_of_deriv_ne_zero hsimple).hasDerivAt.eventually_ne hsimple
  have hiso : ∀ᶠ r in 𝓝 p.1, deriv D.w r = 0 → r = p.1 := by
    filter_upwards [eventually_nhdsWithin_iff.mp hne] with r hr
    intro hzero
    by_contra hrne
    exact hr hrne hzero
  rcases hN01 with ⟨_, _, _, hcontrol, _⟩
  apply returnCorrectedCoefficients_eventuallyEq_of_deriv_eventually_zero
  exact returnCorrectionCutoff_deriv_eventually_zero_at_isolated_root
    C.left C.right (deriv D.w) p.1 (fun m => (hcontrol.1 m).2.1)
    (fun m => ⟨(hcontrol.2.1 m).1, (hcontrol.2.1 m).2.1⟩)
    hcontrol.2.2.2.1 hroot hiso

/-- The canonical actual cutoff and patched coefficients satisfy all
parts of the flow clause of N03 once joint interior regularity and the
positive characteristic gap have been established. -/
theorem N01Properties.returnCorrectedFlow_properties_with_coefficients
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ)
    (hΦ : ContDiffOn ℝ ∞ (fun p : PolarPoint => C.minusFlow z m p.1 p.2)
      (Ioo (C.left m) (C.right m) ×ˢ univ))
    (ha : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ,
      0 < (originalCoefficients D S C z).a (r, θ))
    (hv : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ,
      returnCorrectedMinusSpeed D S C (returnCorrectionCutoffs C) z m (r, θ) ≤
        -returnCorrectedMinusSpeed D S C (returnCorrectionCutoffs C) z m (r, -θ))
    (θ : ℝ) :
    returnCorrectedMinusFlow S C (returnCorrectionCutoffs C) z m (C.left m) θ = θ ∧
    ContinuousOn (fun r => returnCorrectedMinusFlow S C (returnCorrectionCutoffs C) z m r θ)
      (Icc (C.left m) (C.right m)) ∧
    (∀ r ∈ Ioo (C.left m) (C.right m), HasDerivAt
      (fun s => returnCorrectedMinusFlow S C (returnCorrectionCutoffs C) z m s θ)
      (minusCharacteristicSpeed (returnCorrectedCoefficients D S C (returnCorrectionCutoffs C) z)
        (r, returnCorrectedMinusFlow S C (returnCorrectionCutoffs C) z m r θ)) r) ∧
    rightChartCandidate S C z m
      (returnCorrectedMinusFlow S C (returnCorrectionCutoffs C) z m (C.right m) θ) =
        stateLeftChart S z.1 m θ - C.travel m ∧
    rightChartCandidate S C z m
      (-returnCorrectedMinusFlow S C (returnCorrectionCutoffs C) z m (C.right m) (-θ)) =
        stateLeftChart S z.1 m θ + C.travel m := by
  have hcontrol := hN01.2.2.2.1
  have hlh := (hcontrol.1 m).2.1
  have hf := hN01.returnCorrectedMinusFlow_properties (returnCorrectionCutoffs C) hz hsector m
    (returnCorrectionCutoff_contDiff _ _)
    (fun r _ => returnCorrectionCutoff_mem_Icc _ _ r)
    (returnCorrectionCutoff_eventually_zero_left hlh)
    (returnCorrectionCutoff_eventually_one_right hlh) hΦ θ
  refine ⟨hf.1, hf.2.1, ?_, hf.2.2.2.1, hf.2.2.2.2⟩
  intro r hr
  rw [returnCorrectedCoefficients_minusCharacteristicSpeed hcontrol.2.2.1
    (returnCorrectionCutoffs C) z m _ hr (ha r hr _) (hv r hr _)]
  exact hf.2.2.1 r hr

end ContinuousFlexibility.Statements
