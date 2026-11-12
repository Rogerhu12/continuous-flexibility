import ContinuousFlexibility.Analysis.SmoothDirectionsAffine
import ContinuousFlexibility.Analysis.N01NeighborhoodRestriction

/-!
# Local directional towers and local tame estimates glue

Actual projective derivatives are unique on open overlaps. This permits
estimates on bounded low-seminorm neighborhoods while retaining one
genuine tower on the entire open domain. No global growth assumption is
imposed on a nonlinear or bilinear map.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology BigOperators

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [T2Space F]
  {U V : Set E} {f : E → F}

theorem SmoothDirections.eq_on_overlap (J : SmoothDirections U f)
    (K : SmoothDirections V f) (n : ℕ) {x : E} (hx : x ∈ U ∩ V) :
    J.D n x = K.D n x :=
  (J.restrict (J.open_domain.inter K.open_domain) inter_subset_left).unique
    (K.restrict (J.open_domain.inter K.open_domain) inter_subset_right) n x hx

theorem exists_smoothDirections_of_open_cover {ι : Type*}
    (hU : IsOpen U) (V : ι → Set E) (J : ∀ i, SmoothDirections (V i) f)
    (hsub : ∀ i, V i ⊆ U) (hcover : ∀ x ∈ U, ∃ i, x ∈ V i) :
    ∃ K : SmoothDirections U f, ∀ i n x, x ∈ V i → K.D n x = (J i).D n x := by
  classical
  let L : ∀ n : ℕ, E → E [×n]→L[ℝ] F := fun n x =>
    if hx : x ∈ U then (J (hcover x hx).choose).D n x else 0
  have heq : ∀ i n x, x ∈ V i → L n x = (J i).D n x := by
    intro i n x hx
    have hxU : x ∈ U := hsub i hx
    dsimp only [L]
    rw [dif_pos hxU]
    exact (J (hcover x hxU).choose).eq_on_overlap (J i) n
      ⟨(hcover x hxU).choose_spec, hx⟩
  have hzero : ∀ x ∈ U, L 0 x Fin.elim0 = f x := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    rw [heq i 0 x hi]
    exact (J i).zero x hi
  have hcont (n : ℕ) :
      ContinuousOn (fun z : E × (Fin n → E) => L n z.1 z.2) (U ×ˢ univ) := by
    rintro ⟨x, v⟩ hx
    obtain ⟨i, hi⟩ := hcover x hx.1
    have hlocal : ContinuousAt (fun z : E × (Fin n → E) => (J i).D n z.1 z.2) (x, v) :=
      ((J i).continuous n).continuousAt
        (((J i).open_domain.prod isOpen_univ).mem_nhds ⟨hi, mem_univ v⟩)
    have hmem : ∀ᶠ z : E × (Fin n → E) in 𝓝[U ×ˢ univ] (x, v), z.1 ∈ V i :=
      (continuous_fst.continuousAt.eventually ((J i).open_domain.mem_nhds hi)).filter_mono
        nhdsWithin_le_nhds
    change Tendsto (fun z : E × (Fin n → E) => L n z.1 z.2)
      (𝓝[U ×ˢ univ] (x, v)) (𝓝 (L n x v))
    rw [heq i n x hi]
    exact (hlocal.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (hmem.mono fun z hz => (congrArg (fun M => M z.2) (heq i n z.1 hz)).symm)
  have hderiv : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => L n y v) (L (n + 1) x (Fin.cons w v)) x w := by
    intro n x hx v w
    obtain ⟨i, hi⟩ := hcover x hx
    rw [heq i (n + 1) x hi]
    apply ((J i).derivative n x hi v w).congr_germ
    filter_upwards [(J i).open_domain.mem_nhds hi] with y hy
    exact congrArg (fun M => M v) (heq i n y hy)
  let K : SmoothDirections U f :=
    { open_domain := hU, D := L, zero := hzero, continuous := hcont, derivative := hderiv }
  exact ⟨K, heq⟩

/-- A local tame map on a cover of low-seminorm neighborhoods has the
same frozen SmoothTameOn property on the full open set. Increasing
the base seminorm combines neighborhood conditions without increasing
the derivative loss with the output order. -/
theorem smoothTameOn_of_local_neighborhoods
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (hp : Monotone p)
    (hU : IsOpen U)
    (hlocal : ∀ x₀ ∈ U, ∃ b : ℕ, ∃ δ : ℝ, ∃ V : Set E,
      0 < δ ∧ IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧
        (∀ x ∈ U, p b (x - x₀) < δ → x ∈ V) ∧ SmoothTameOn p q V f) :
    SmoothTameOn p q U f := by
  classical
  choose b δ V hδ hV hcenter hsub hball htame using hlocal
  let W : U → Set E := fun i => V i.val i.property
  have hWsub (i : U) : W i ⊆ U := hsub i.val i.property
  have hWcover : ∀ x ∈ U, ∃ i : U, x ∈ W i := by
    intro x hx
    exact ⟨⟨x, hx⟩, hcenter x hx⟩
  have hlocalTame : ∀ i : U, SmoothTameOn p q (W i) f :=
    fun i => htame i.val i.property
  choose J hJ using hlocalTame
  obtain ⟨K, hK⟩ := exists_smoothDirections_of_open_cover hU W J hWsub hWcover
  refine ⟨K, ?_⟩
  intro k x₀ hx₀
  let i : U := ⟨x₀, hx₀⟩
  obtain ⟨loss, low, rad, hrad, hb⟩ := hJ i k x₀ (hcenter x₀ hx₀)
  let base := max (b x₀ hx₀) low
  refine ⟨loss, base, min (δ x₀ hx₀) rad, lt_min (hδ x₀ hx₀) hrad, ?_⟩
  intro s hs
  obtain ⟨C, hC, hCs⟩ := hb s ((le_max_right _ _).trans hs)
  refine ⟨C, hC, ?_⟩
  intro x hx hnear v
  have hlocalMem : x ∈ W i := hball x₀ hx₀ x hx
    ((hp (le_max_left _ _) (x - x₀)).trans_lt
      (hnear.trans_le (min_le_left _ _)))
  have hnearLow : p low (x - x₀) < rad :=
    (hp (le_max_right _ _) (x - x₀)).trans_lt (hnear.trans_le (min_le_right _ _))
  rw [hK i k x hlocalMem]
  change q s ((J i).D k x v) ≤ C * oneHighVariationWeight p base (s + loss) x v
  exact (hCs x hlocalMem hnearLow v).trans (mul_le_mul_of_nonneg_left
    (oneHighVariationWeight_mono hp (le_max_right _ _) le_rfl x v) hC)

end ContinuousFlexibility.Statements
