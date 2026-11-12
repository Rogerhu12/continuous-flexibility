import ContinuousFlexibility.Statements.Radial
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Basic.Denumerable
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Encodable
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.DiscreteSubset

/-!
# The actual negative components of a radial reference

Two intervals with zero endpoint derivatives and strictly negative derivative
inside are either identical or disjoint. Simple critical points make this
family locally finite in the open radial annulus. Positivity of the profile,
flatness at the right endpoint, and the return-component coverage produce
components arbitrarily close to that endpoint. Thus the actual components
admit a bijective enumeration by the natural numbers.

This module makes no assertion relating that enumeration to a coefficient
weight or to the indexing of the reference partition.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

/-- One representation of a negative component, by its actual endpoint pair. -/
def N01aNegativeComponent (D : ReferenceData) : Type :=
  {p : ℝ × ℝ // NegativeRadialComponent D p.1 p.2}

namespace N01aNegativeComponent

variable {D : ReferenceData}

def left (J : N01aNegativeComponent D) : ℝ := J.val.1

def right (J : N01aNegativeComponent D) : ℝ := J.val.2

def interval (J : N01aNegativeComponent D) : Set ℝ := Ioo J.left J.right

theorem property (J : N01aNegativeComponent D) :
    NegativeRadialComponent D J.left J.right := J.prop

theorem left_mem_core (J : N01aNegativeComponent D) : J.left ∈ radialCore D :=
  ⟨J.property.1, J.property.2.1.trans J.property.2.2.1⟩

theorem right_mem_core (J : N01aNegativeComponent D) : J.right ∈ radialCore D :=
  ⟨J.property.1.trans J.property.2.1, J.property.2.2.1⟩

theorem left_lt_right (J : N01aNegativeComponent D) : J.left < J.right :=
  J.property.2.1

theorem left_zero (J : N01aNegativeComponent D) : deriv D.w J.left = 0 :=
  J.property.2.2.2.1

theorem right_zero (J : N01aNegativeComponent D) : deriv D.w J.right = 0 :=
  J.property.2.2.2.2.1

theorem negative (J : N01aNegativeComponent D) {r : ℝ} (hr : r ∈ J.interval) :
    deriv D.w r < 0 := J.property.2.2.2.2.2 r hr

theorem mem_core (J : N01aNegativeComponent D) {r : ℝ} (hr : r ∈ J.interval) :
    r ∈ radialCore D :=
  ⟨J.left_mem_core.1.trans hr.1, hr.2.trans J.right_mem_core.2⟩

/-- Overlapping negative intervals have the same two actual endpoints. -/
theorem eq_of_mem {J K : N01aNegativeComponent D} {r : ℝ}
    (hJ : r ∈ J.interval) (hK : r ∈ K.interval) : J = K := by
  have hl : J.left = K.left := by
    apply le_antisymm
    · by_contra h
      have hh : deriv D.w J.left < 0 :=
        K.negative ⟨lt_of_not_ge h, hJ.1.trans hK.2⟩
      rw [J.left_zero] at hh
      exact (lt_irrefl (0 : ℝ)) hh
    · by_contra h
      have hh : deriv D.w K.left < 0 :=
        J.negative ⟨lt_of_not_ge h, hK.1.trans hJ.2⟩
      rw [K.left_zero] at hh
      exact (lt_irrefl (0 : ℝ)) hh
  have hr : J.right = K.right := by
    apply le_antisymm
    · by_contra h
      have hh : deriv D.w K.right < 0 :=
        J.negative ⟨hJ.1.trans hK.2, lt_of_not_ge h⟩
      rw [K.right_zero] at hh
      exact (lt_irrefl (0 : ℝ)) hh
    · by_contra h
      have hh : deriv D.w J.right < 0 :=
        K.negative ⟨hK.1.trans hJ.2, lt_of_not_ge h⟩
      rw [J.right_zero] at hh
      exact (lt_irrefl (0 : ℝ)) hh
  apply Subtype.ext
  exact Prod.ext hl hr

theorem pairwise_disjoint :
    Pairwise (fun J K : N01aNegativeComponent D => Disjoint J.interval K.interval) := by
  intro J K hne
  exact Set.disjoint_left.mpr fun _ hJ hK => hne (eq_of_mem hJ hK)

theorem left_injective : Function.Injective (left (D := D)) := by
  intro J K h
  have hm : J.left < min J.right K.right :=
    lt_min J.left_lt_right (h.symm ▸ K.left_lt_right)
  obtain ⟨r, hl, hr⟩ := exists_between hm
  exact eq_of_mem ⟨hl, hr.trans_le (min_le_left _ _)⟩
    ⟨h ▸ hl, hr.trans_le (min_le_right _ _)⟩

theorem simple_endpoints (hD : RadialProfileGeometry D) (J : N01aNegativeComponent D) :
    deriv (deriv D.w) J.left ≠ 0 ∧ deriv (deriv D.w) J.right ≠ 0 :=
  ⟨hD.2.2.2.2.2.2 J.left J.left_mem_core J.left_zero,
    hD.2.2.2.2.2.2 J.right J.right_mem_core J.right_zero⟩

private def marker (J : N01aNegativeComponent D) : ℚ :=
  Classical.choose (exists_rat_btwn J.left_lt_right)

private theorem marker_mem (J : N01aNegativeComponent D) :
    (marker J : ℝ) ∈ J.interval :=
  Classical.choose_spec (exists_rat_btwn J.left_lt_right)

private theorem marker_injective : Function.Injective (marker (D := D)) := by
  intro J K h
  apply eq_of_mem (marker_mem J)
  rw [h]
  exact marker_mem K

instance : Countable (N01aNegativeComponent D) := marker_injective.countable

end N01aNegativeComponent

/-- Every stationary point in the open annulus is isolated among stationary points. -/
theorem n01a_stationary_point_isolated {D : ReferenceData}
    (hD : RadialProfileGeometry D) {r : ℝ} (hr : r ∈ radialCore D)
    (hz : deriv D.w r = 0) :
    ∀ᶠ x in 𝓝 r, deriv D.w x = 0 → x = r := by
  have hd : ContDiff ℝ ∞ (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hD.2.2.1.1).2
  have hn := hD.2.2.2.2.2.2 r hr hz
  have he : ∀ᶠ x in 𝓝[≠] r, deriv D.w x ≠ 0 :=
    (hd.differentiable (by simp) r).hasDerivAt.eventually_ne hn
  filter_upwards [eventually_nhdsWithin_iff.mp he] with x hx hzero
  by_contra hne
  exact hx (by simpa only [mem_compl_iff, mem_singleton_iff] using hne) hzero

/-- Only finitely many stationary points occur in a compact subset of the annulus. -/
theorem n01a_stationary_points_finite_on_compact {D : ReferenceData}
    (hD : RadialProfileGeometry D) {K : Set ℝ} (hK : IsCompact K)
    (hcore : K ⊆ radialCore D) : {r ∈ K | deriv D.w r = 0}.Finite := by
  have hd : Continuous (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hD.2.2.1.1).2.continuous
  have hc : IsCompact {r ∈ K | deriv D.w r = 0} :=
    hK.inter_right (isClosed_eq hd continuous_const)
  apply hc.finite
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro r hr
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp
    (n01a_stationary_point_isolated hD (hcore hr.1) hr.2)
  refine ⟨Metric.ball r δ, Metric.isOpen_ball, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hroot⟩
    exact Set.mem_singleton_iff.mpr (hb hx hroot.2)
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact ⟨Metric.mem_ball_self hδ, hr⟩

namespace N01aNegativeComponent

variable {D : ReferenceData}

/-- A compact radial interval inside the annulus meets only finitely many components. -/
theorem finite_inter_Icc (hD : RadialProfileGeometry D) {a b : ℝ}
    (ha : a ∈ radialCore D) (hb : b ∈ radialCore D) :
    {J : N01aNegativeComponent D | (J.interval ∩ Icc a b).Nonempty}.Finite := by
  have hroots := n01a_stationary_points_finite_on_compact hD isCompact_Icc
    (fun _ hr => ⟨ha.1.trans_le hr.1, hr.2.trans_lt hb.2⟩)
  have hleft : {J : N01aNegativeComponent D | J.left ∈ Icc a b}.Finite :=
    (hroots.preimage left_injective.injOn).subset
      (fun J hJ => ⟨hJ, J.left_zero⟩)
  have hpoint : {J : N01aNegativeComponent D | a ∈ J.interval}.Subsingleton :=
    fun _ hJ _ hK => eq_of_mem hJ hK
  apply (hleft.union hpoint.finite).subset
  rintro J ⟨r, hr, hI⟩
  by_cases h : a ≤ J.left
  · exact Or.inl ⟨h, hr.1.le.trans hI.2⟩
  · exact Or.inr ⟨lt_of_not_ge h, hI.1.trans_lt hr.2⟩

/-- The actual negative intervals are locally finite in the open annulus. -/
theorem locallyFinite (hD : RadialProfileGeometry D) :
    LocallyFinite (fun J : N01aNegativeComponent D =>
      {r : radialCore D | (r : ℝ) ∈ J.interval}) := by
  intro x
  let a : ℝ := (D.a + x.val) / 2
  let b : ℝ := (x.val + D.b) / 2
  have hax : a < x.val := by dsimp only [a]; linarith only [x.property.1]
  have hxb : x.val < b := by dsimp only [b]; linarith only [x.property.2]
  have ha : a ∈ radialCore D := by
    change D.a < a ∧ a < D.b
    dsimp only [a]
    constructor <;> linarith only [x.property.1, x.property.2]
  have hb : b ∈ radialCore D := by
    change D.a < b ∧ b < D.b
    dsimp only [b]
    constructor <;> linarith only [x.property.1, x.property.2]
  refine ⟨{r : radialCore D | (r : ℝ) ∈ Ioo a b},
    continuous_subtype_val.continuousAt.preimage_mem_nhds (Ioo_mem_nhds hax hxb), ?_⟩
  apply (finite_inter_Icc hD ha hb).subset
  rintro J ⟨r, hrJ, hrI⟩
  exact ⟨r.val, hrJ, Ioo_subset_Icc_self hrI⟩

/-- Compact subsets of the actual open annulus meet only finitely many components. -/
theorem finite_inter_compact (hD : RadialProfileGeometry D) {K : Set ℝ}
    (hK : IsCompact K) (hcore : K ⊆ radialCore D) :
    {J : N01aNegativeComponent D | (J.interval ∩ K).Nonempty}.Finite := by
  let K' : Set (radialCore D) := {r | (r : ℝ) ∈ K}
  have himage : Subtype.val '' K' = K := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hr
      exact ⟨⟨r, hcore hr⟩, hr, rfl⟩
  have hK' : IsCompact K' := by
    apply Subtype.isCompact_iff.mpr
    rw [himage]
    exact hK
  apply ((locallyFinite hD).finite_nonempty_inter_compact hK').subset
  rintro J ⟨r, hrJ, hrK⟩
  exact ⟨⟨r, hcore hrK⟩, hrJ, hrK⟩

/-- There are components with right endpoint beyond any prescribed interior radius. -/
theorem exists_right_gt (hD : RadialProfileGeometry D) (hR : RadialReturnMargins D)
    {c : ℝ} (hc : c < D.b) :
    ∃ J : N01aNegativeComponent D, c < J.right := by
  let d : ℝ := max c ((D.a + D.b) / 2)
  have hmid : (D.a + D.b) / 2 < D.b := by linarith only [hD.2.1]
  have hdb : d < D.b := max_lt hc hmid
  have had : D.a < d :=
    (show D.a < (D.a + D.b) / 2 by linarith only [hD.2.1]).trans_le (le_max_right _ _)
  have hw : ContDiff ℝ ∞ D.w := hD.2.2.1.1
  obtain ⟨r, hr, hslope⟩ := exists_deriv_eq_slope D.w hdb hw.continuous.continuousOn
    (hw.differentiable (by simp)).differentiableOn
  have hwb : D.w D.b = 0 := hD.2.2.1.2 D.b (Or.inr le_rfl)
  have hwd : 0 < D.w d := hD.2.2.2.2.1 d ⟨had, hdb⟩
  have hneg : deriv D.w r < 0 := by
    rw [hslope, hwb, zero_sub]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hwd) (sub_pos.mpr hdb)
  obtain ⟨l, h, hJ, hrJ⟩ := hR.1 r ⟨had.trans hr.1, hr.2⟩ hneg
  exact ⟨⟨(l, h), hJ⟩, (le_max_left _ _).trans_lt (hr.1.trans hrJ.2)⟩

/-- Entire negative components occur arbitrarily far toward the right endpoint. -/
theorem exists_left_gt (hD : RadialProfileGeometry D) (hR : RadialReturnMargins D)
    {c : ℝ} (hc : c < D.b) :
    ∃ J : N01aNegativeComponent D, c < J.left := by
  obtain ⟨J, hJ⟩ := exists_right_gt hD hR hc
  obtain ⟨K, hK⟩ := exists_right_gt hD hR J.right_mem_core.2
  have hleft : J.right ≤ K.left := by
    by_contra h
    have hh := K.negative ⟨lt_of_not_ge h, hK⟩
    rw [J.right_zero] at hh
    exact (lt_irrefl (0 : ℝ)) hh
  exact ⟨K, hJ.trans_le hleft⟩

theorem infinite (hD : RadialProfileGeometry D) (hR : RadialReturnMargins D) :
    Infinite (N01aNegativeComponent D) := by
  classical
  refine ⟨fun hfinite => ?_⟩
  letI : Finite (N01aNegativeComponent D) := hfinite
  letI : Fintype (N01aNegativeComponent D) := Fintype.ofFinite _
  obtain ⟨J₀, _⟩ := exists_right_gt hD hR hD.2.1
  letI : Nonempty (N01aNegativeComponent D) := ⟨J₀⟩
  obtain ⟨J, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (right (D := D)) Finset.univ_nonempty
  obtain ⟨K, hK⟩ := exists_right_gt hD hR J.right_mem_core.2
  exact (not_lt_of_ge (hmax K (Finset.mem_univ K))) hK

end N01aNegativeComponent

/-- A bijective enumeration of all actual negative components. No coefficient
comparison is included in this qualitative choice. -/
def n01aNegativeComponentEnumeration {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hR : RadialReturnMargins D) :
    ℕ ≃ N01aNegativeComponent D := by
  letI := N01aNegativeComponent.infinite hD hR
  exact Classical.choice inferInstance

theorem n01aNegativeComponentEnumeration_covers {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hR : RadialReturnMargins D)
    {r : ℝ} (hr : r ∈ radialCore D) (hneg : deriv D.w r < 0) :
    ∃ m : ℕ, r ∈ (n01aNegativeComponentEnumeration hD hR m).interval := by
  obtain ⟨l, h, hJ, hrJ⟩ := hR.1 r hr hneg
  let J : N01aNegativeComponent D := ⟨(l, h), hJ⟩
  refine ⟨(n01aNegativeComponentEnumeration hD hR).symm J, ?_⟩
  rw [Equiv.apply_symm_apply]
  exact hrJ

theorem n01aNegativeComponentEnumeration_mem_iff {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hR : RadialReturnMargins D) (r : ℝ) :
    (∃ m : ℕ, r ∈ (n01aNegativeComponentEnumeration hD hR m).interval) ↔
      r ∈ radialCore D ∧ deriv D.w r < 0 := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨(n01aNegativeComponentEnumeration hD hR m).mem_core hm,
      (n01aNegativeComponentEnumeration hD hR m).negative hm⟩
  · rintro ⟨hr, hneg⟩
    exact n01aNegativeComponentEnumeration_covers hD hR hr hneg

/-- Any family supported in these enumerated intervals is locally finite. -/
theorem n01aNegativeComponent_supports_locallyFinite {D : ReferenceData}
    (hD : RadialProfileGeometry D) (e : ℕ ≃ N01aNegativeComponent D)
    (χ : ℕ → ℝ → ℝ) (hsupp : ∀ m, Function.support (χ m) ⊆ (e m).interval) :
    LocallyFinite (fun m => {r : radialCore D | (r : ℝ) ∈ Function.support (χ m)}) := by
  have hf : LocallyFinite (fun m => {r : radialCore D | (r : ℝ) ∈ (e m).interval}) := by
    simpa only [Function.comp_def] using (N01aNegativeComponent.locallyFinite hD).comp_injective
      e.injective
  exact hf.subset fun m _ hr => hsupp m hr

end ContinuousFlexibility.Statements
