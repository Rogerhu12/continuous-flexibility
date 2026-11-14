module

public import ContinuousFlexibility.Analysis.N07aLocalizedWeakJets
public import ContinuousFlexibility.Analysis.N07aAngularCutoff
public import ContinuousFlexibility.Analysis.CircleSmoothReconstruction

/-!
# Smooth reconstruction on a whole canonical piece

Compact radial cutoffs produce genuine global smooth representatives.
Their products agree pointwise on the overlap, by periodic continuity
and the original canonical measure. Choosing a cutoff equal to one near
each radial point therefore glues a smooth representative on the entire
open piece, without assuming traces at the endpoints.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonical_periodic_eqOn_of_ae_eq {f g : PolarPoint → ℝ}
    (hf : ContinuousOn f (canonicalOpen S K m))
    (hg : ContinuousOn g (canonicalOpen S K m))
    (hfp : Function.Periodic f (0, Real.pi)) (hgp : Function.Periodic g (0, Real.pi))
    (hae : f =ᵐ[canonicalMeasure S K m] g) : EqOn f g (canonicalOpen S K m) := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  rw [canonicalMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict] at hae
  have hrows := Measure.ae_ae_of_ae_prod hae
  have hmem : ∀ᵐ r ∂(volume.restrict (Ioo (K.left m) (K.right m))),
      r ∈ Ioo (K.left m) (K.right m) := ae_restrict_mem measurableSet_Ioo
  intro p hp
  have hpoint : ∀ᵐ r ∂(volume.restrict (Ioo (K.left m) (K.right m))),
      f (r, p.2) = g (r, p.2) := by
    filter_upwards [hrows, hmem] with r hr hri
    have hfr : Continuous (fun θ => f (r, θ)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun _ => ⟨hri, mem_univ _⟩)
    have hgr : Continuous (fun θ => g (r, θ)) :=
      hg.comp_continuous (continuous_const.prodMk continuous_id)
        (fun _ => ⟨hri, mem_univ _⟩)
    have hfp' : Function.Periodic (fun θ => f (r, θ)) Real.pi := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hfp (r, θ)
    have hgp' : Function.Periodic (fun θ => g (r, θ)) Real.pi := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hgp (r, θ)
    exact congrFun (angle_periodic_eq_of_ae_eq hfr hgr hfp' hgp' hr) p.2
  exact Measure.eqOn_open_of_ae_eq hpoint isOpen_Ioo
    (hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => ⟨hr, mem_univ _⟩))
    (hg.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => ⟨hr, mem_univ _⟩)) hp.1

def n07aCanonicalCutoff (hm : K.left m < K.right m) (n : ℕ) (p : PolarPoint) : ℝ :=
  n07aAngularIntervalCutoff (K.left m) (K.right m) hm n p.1

theorem n07aCanonicalCutoff_test (hm : K.left m < K.right m) (n : ℕ) :
    CanonicalTest S K m (n07aCanonicalCutoff hm n) := by
  refine ⟨(n07aAngularIntervalCutoff_contDiff _ _ hm n).comp contDiff_fst, ?_,
    tsupport (n07aAngularIntervalCutoff _ _ hm n),
    n07aAngularIntervalCutoff_compact _ _ hm n,
    n07aAngularIntervalCutoff_tsupport _ _ hm n, ?_⟩
  · intro p
    simp only [n07aCanonicalCutoff, Prod.fst_add, add_zero]
  · intro r hr θ
    change n07aAngularIntervalCutoff _ _ hm n r = 0
    exact image_eq_zero_of_notMem_tsupport hr

/-- All genuine canonical weak mixed jets produce a smooth periodic
representative on the complete open piece. -/
theorem n07a_exists_smooth_canonicalRepresentative (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (hu : ∀ n, N07aCanonicalNormalRegular S K m u n) :
    ∃ v : PolarPoint → ℝ, ContDiffOn ℝ ∞ v (canonicalOpen S K m) ∧
      Function.Periodic v (0, Real.pi) ∧ v =ᵐ[canonicalMeasure S K m] u ∧
      ∀ p, p ∉ canonicalOpen S K m → v p = 0 := by
  classical
  let χ : ℕ → PolarPoint → ℝ := n07aCanonicalCutoff hm
  have hχ (n : ℕ) : CanonicalTest S K m (χ n) := n07aCanonicalCutoff_test hm n
  choose v hv hvp hve using fun n => n07a_exists_smooth_localizedCanonical (hχ n) u hu
  have hcross (i j : ℕ) : EqOn (fun p => χ i p * v j p)
      (fun p => χ j p * v i p) (canonicalOpen S K m) := by
    apply n07a_canonical_periodic_eqOn_of_ae_eq
      ((hχ i).1.continuous.mul (hv j).continuous).continuousOn
      ((hχ j).1.continuous.mul (hv i).continuous).continuousOn
      ((hχ i).2.1.mul (hvp j)) ((hχ j).2.1.mul (hvp i))
    filter_upwards [hve i, hve j] with p hi hj
    simp only [Pi.mul_apply]
    rw [hi, hj]
    ring
  have hex (r : ℝ) (hr : r ∈ Ioo (K.left m) (K.right m)) :
      ∃ n : ℕ, ∀ᶠ t in 𝓝 r, n07aAngularIntervalCutoff _ _ hm n t = 1 :=
    n07aAngularIntervalCutoff_exists_one_nhds _ _ hm hr
  let index (r : ℝ) : ℕ := if hr : r ∈ Ioo (K.left m) (K.right m)
    then (hex r hr).choose else 0
  have hindex (r : ℝ) (hr : r ∈ Ioo (K.left m) (K.right m)) :
      ∀ᶠ t in 𝓝 r, n07aAngularIntervalCutoff _ _ hm (index r) t = 1 := by
    simp only [index, dite_eq_left hr]
    exact (hex r hr).choose_spec
  let w : PolarPoint → ℝ := fun p =>
    if p.1 ∈ Ioo (K.left m) (K.right m) then v (index p.1) p else 0
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hloc : w =ᶠ[𝓝 p] v (index p.1) := by
      have hone : ∀ᶠ q : PolarPoint in 𝓝 p,
          n07aAngularIntervalCutoff _ _ hm (index p.1) q.1 = 1 :=
        continuous_fst.continuousAt.eventually (hindex p.1 hp.1)
      have hopen : canonicalOpen S K m ∈ 𝓝 p :=
        (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
      filter_upwards [hone, hopen] with q hq hqo
      have hself := (hindex q.1 hqo.1).self_of_nhds
      have hc := hcross (index p.1) (index q.1) hqo
      dsimp only at hc
      change χ (index p.1) q = 1 at hq
      change χ (index q.1) q = 1 at hself
      rw [hq, hself, one_mul, one_mul] at hc
      exact (ite_eq_left hqo.1).trans hc
    exact ((hv (index p.1)).contDiffAt.congr_of_eventuallyEq hloc).contDiffWithinAt
  · intro p
    dsimp only [w, Prod.fst_add, Prod.snd_add]
    simp only [add_zero, hvp (index p.1) p]
  · have hall : ∀ᵐ p ∂canonicalMeasure S K m, ∀ n, v n p = χ n p * u p :=
      ae_all_iff.mpr hve
    have hmem : ∀ᵐ p ∂canonicalMeasure S K m,
        p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
    filter_upwards [hall, hmem] with p he hp
    have hone := (hindex p.1 hp.1).self_of_nhds
    change χ (index p.1) p = 1 at hone
    dsimp only [w]
    rw [ite_eq_left hp.1, he, hone, one_mul]
  · intro p hp
    have hr : p.1 ∉ Ioo (K.left m) (K.right m) :=
      fun hr => hp ⟨hr, mem_univ _⟩
    exact ite_eq_right hr

end ContinuousFlexibility.Analysis
