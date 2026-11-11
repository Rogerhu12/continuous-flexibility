import ContinuousFlexibility.Geometry.SphereCapGluing
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Actual fixed disks on the standard sphere

The northern graph disk and the complementary southern cap are closed
hemispheres in the standard sphere.  The fixed inner disk is the inverse image
of the physical Cartesian disk of radius `a` under the scaled northern chart.
All disk homeomorphisms below are constructed from the actual stereographic
coordinates; no disk-topology hypothesis is used.  Cartesian disks use the
Euclidean radius, not the max norm of `PolarPoint`.

This supplies the fixed-region topology in `thm:geometric-closure`, including
the relative complement and regular-closed properties on the standard sphere.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Function
open scoped ContDiff Manifold Topology

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}

set_option backward.isDefEq.respectTransparency false

def sphereGraphDisk : Set SpherePoint := {x | 0 ≤ (x : E3) 2}

def sphereComplementaryCap : Set SpherePoint := {x | (x : E3) 2 ≤ 0}

def sphereNorthClosedDisk (r : ℝ) : Set SpherePoint :=
  sphereNorthSource ∩ sphereNorthChart ⁻¹' {u : PolarPoint | cartesianRadius u ≤ r}

/-- `a` is a physical radius in the same Cartesian graph disk of radius `R`. -/
def sphereInnerDisk (R a : ℝ) : Set SpherePoint :=
  {x | x ∈ sphereNorthSource ∧ cartesianRadius (R • sphereNorthChart x) ≤ a}

theorem sphereNorthClosedDisk_eq_image (r : ℝ) :
    sphereNorthClosedDisk r =
      sphereNorthInverse '' {u : PolarPoint | cartesianRadius u ≤ r} := by
  ext x
  constructor
  · rintro ⟨hx, hr⟩
    exact ⟨sphereNorthChart x, hr, sphereNorthInverse_chart x hx⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨sphereNorthInverse_source u, ?_⟩
    change cartesianRadius (sphereNorthChart (sphereNorthInverse u)) ≤ r
    rw [sphereNorthChart_inverse]
    exact hu

/-- A genuine restriction of the northern stereographic homeomorphism. -/
def sphereNorthClosedDiskHomeomorph (r : ℝ) :
    ↥(sphereNorthClosedDisk r) ≃ₜ {u : PolarPoint // cartesianRadius u ≤ r} :=
  sphereNorthCoordinates.homeomorphOfImageSubsetSource (fun _ hx => hx.1) (by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hu
      exact ⟨sphereNorthInverse u,
        ⟨sphereNorthInverse_source u, by
          change cartesianRadius (sphereNorthChart (sphereNorthInverse u)) ≤ r
          rw [sphereNorthChart_inverse]
          exact hu⟩,
        sphereNorthChart_inverse u⟩)

/-- Scaling identifies every positive-radius Cartesian disk with the unit disk. -/
def closedCartesianDiskScaleHomeomorph {r : ℝ} (hr : 0 < r) :
    {u : PolarPoint // cartesianRadius u ≤ 1} ≃ₜ
      {u : PolarPoint // cartesianRadius u ≤ r} where
  toFun u := ⟨r • u.1, by
    rw [capDisk_radius_smul, abs_of_pos hr]
    nlinarith [u.property]⟩
  invFun u := ⟨r⁻¹ • u.1, by
    rw [capDisk_radius_smul, abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_iff₀ hr).mpr (by simpa using u.property)⟩
  left_inv u := by
    apply Subtype.ext
    simp [smul_smul, hr.ne']
  right_inv u := by
    apply Subtype.ext
    simp [smul_smul, hr.ne']
  continuous_toFun := (continuous_subtype_val.const_smul r).subtype_mk _
  continuous_invFun := (continuous_subtype_val.const_smul r⁻¹).subtype_mk _

theorem sphereGraphDisk_eq_northClosedDisk : sphereGraphDisk = sphereNorthClosedDisk 1 := by
  ext x
  constructor
  · intro hx
    have hn : x ∈ sphereNorthSource := by change (x : E3) 2 ≠ -1; have := hx; change 0 ≤ (x : E3) 2 at this; linarith
    exact ⟨hn, (sphereNorthChart_radius_le_one_iff x hn).mpr hx⟩
  · rintro ⟨hx, hr⟩
    exact (sphereNorthChart_radius_le_one_iff x hx).mp hr

def sphereGraphDiskHomeomorph :
    ↥sphereGraphDisk ≃ₜ {u : PolarPoint // cartesianRadius u ≤ 1} :=
  (Homeomorph.setCongr sphereGraphDisk_eq_northClosedDisk).trans
    (sphereNorthClosedDiskHomeomorph 1)

def sphereGraphDiskPhysicalHomeomorph {R : ℝ} (hR : 0 < R) :
    ↥sphereGraphDisk ≃ₜ {u : PolarPoint // cartesianRadius u ≤ R} :=
  sphereGraphDiskHomeomorph.trans (closedCartesianDiskScaleHomeomorph hR)

def sphereComplementaryCapHomeomorph :
    ↥sphereComplementaryCap ≃ₜ {u : PolarPoint // cartesianRadius u ≤ 1} :=
  sphereSouthCoordinates.homeomorphOfImageSubsetSource
    (by intro x hx; change (x : E3) 2 ≠ 1; change (x : E3) 2 ≤ 0 at hx; linarith)
    (by
      ext u
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hs : x ∈ sphereSouthSource := by change (x : E3) 2 ≠ 1; change (x : E3) 2 ≤ 0 at hx; linarith
        exact (sphereSouthChart_radius_le_one_iff x hs).mpr hx
      · intro hu
        refine ⟨sphereSouthInverse u, ?_, sphereSouthChart_inverse u⟩
        apply (sphereSouthChart_radius_le_one_iff _ (sphereSouthInverse_source u)).mp
        rw [sphereSouthChart_inverse]
        exact hu)

theorem sphereInnerDisk_eq_northClosedDisk {R : ℝ} (hR : 0 < R) (a : ℝ) :
    sphereInnerDisk R a = sphereNorthClosedDisk (a / R) := by
  ext x
  simp only [sphereInnerDisk, sphereNorthClosedDisk, mem_ofPred_eq, mem_inter_iff,
    mem_preimage, capDisk_radius_smul, abs_of_pos hR]
  rw [le_div_iff₀ hR, mul_comm]

def sphereInnerDiskHomeomorph {R a : ℝ} (hR : 0 < R) (ha : 0 < a) :
    ↥(sphereInnerDisk R a) ≃ₜ {u : PolarPoint // cartesianRadius u ≤ 1} :=
  ((Homeomorph.setCongr (sphereInnerDisk_eq_northClosedDisk hR a)).trans
    (sphereNorthClosedDiskHomeomorph (a / R))).trans
    (closedCartesianDiskScaleHomeomorph (div_pos ha hR)).symm

/-- The homeomorphism uses precisely the physical graph coordinate `R • chart`. -/
def sphereInnerDiskPhysicalHomeomorph {R : ℝ} (hR : 0 < R) (a : ℝ) :
    ↥(sphereInnerDisk R a) ≃ₜ {u : PolarPoint // cartesianRadius u ≤ a} where
  toFun x := ⟨R • sphereNorthChart x.1, x.property.2⟩
  invFun u := ⟨sphereNorthInverse (R⁻¹ • u.1),
    sphereNorthInverse_source _, by
      simpa only [sphereNorthChart_inverse, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
        using u.property⟩
  left_inv x := by
    apply Subtype.ext
    simp only [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
    exact sphereNorthInverse_chart x.1 x.property.1
  right_inv u := by
    apply Subtype.ext
    simp only [sphereNorthChart_inverse, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun x : ↥(sphereInnerDisk R a) => sphereNorthChart x.1) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      exact (contMDiffAt_sphereNorthChart x.1 x.property.1).continuousAt.comp
        continuous_subtype_val.continuousAt
    exact hc.const_smul R
  continuous_invFun :=
    (contMDiff_sphereNorthInverse.continuous.comp
      (continuous_subtype_val.const_smul R⁻¹)).subtype_mk _

/-- Explicitly identify the circular Cartesian disk with the standard
Euclidean closed ball; the max-norm square is never used. -/
def closedCartesianDiskEuclideanHomeomorph (r : ℝ) :
    {u : PolarPoint // cartesianRadius u ≤ r} ≃ₜ
      ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r) := by
  let e : PolarPoint ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.trans
      Complex.orthonormalBasisOneI.repr.toHomeomorph
  have hn (u : PolarPoint) : ‖e u‖ = cartesianRadius u :=
    Complex.orthonormalBasisOneI.repr.norm_map _
  refine (e.image {u : PolarPoint | cartesianRadius u ≤ r}).trans (Homeomorph.setCongr ?_)
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    change cartesianRadius u ≤ r at hu
    simpa only [Metric.mem_closedBall, dist_zero_right, hn] using hu
  · intro hv
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    change cartesianRadius (e.symm v) ≤ r
    rw [← hn, e.apply_symm_apply]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hv

def sphereGraphDiskStandardHomeomorph :
    ↥sphereGraphDisk ≃ₜ ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  sphereGraphDiskHomeomorph.trans (closedCartesianDiskEuclideanHomeomorph 1)

def sphereComplementaryCapStandardHomeomorph :
    ↥sphereComplementaryCap ≃ₜ ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  sphereComplementaryCapHomeomorph.trans (closedCartesianDiskEuclideanHomeomorph 1)

def sphereInnerDiskStandardHomeomorph {R a : ℝ} (hR : 0 < R) (ha : 0 < a) :
    ↥(sphereInnerDisk R a) ≃ₜ ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  (sphereInnerDiskHomeomorph hR ha).trans (closedCartesianDiskEuclideanHomeomorph 1)

theorem isCompact_sphereNorthClosedDisk (r : ℝ) : IsCompact (sphereNorthClosedDisk r) := by
  rw [sphereNorthClosedDisk_eq_image]
  exact (isCompact_closedCartesianDisk r).image contMDiff_sphereNorthInverse.continuous

theorem isClosed_sphereGraphDisk : IsClosed sphereGraphDisk := by
  rw [sphereGraphDisk_eq_northClosedDisk]
  exact (isCompact_sphereNorthClosedDisk 1).isClosed

theorem isClosed_sphereComplementaryCap : IsClosed sphereComplementaryCap :=
  isClosed_le ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp
    continuous_subtype_val) continuous_const

theorem isCompact_sphereInnerDisk {R : ℝ} (hR : 0 < R) (a : ℝ) :
    IsCompact (sphereInnerDisk R a) := by
  rw [sphereInnerDisk_eq_northClosedDisk hR a]
  exact isCompact_sphereNorthClosedDisk _

theorem isClosed_sphereInnerDisk {R : ℝ} (hR : 0 < R) (a : ℝ) :
    IsClosed (sphereInnerDisk R a) := (isCompact_sphereInnerDisk hR a).isClosed

theorem interior_closedCartesianDisk (r : ℝ) :
    interior {u : PolarPoint | cartesianRadius u ≤ r} =
      {u : PolarPoint | cartesianRadius u < r} := by
  let e : PolarPoint ≃ₜ ℂ := Complex.equivRealProdCLM.symm.toHomeomorph
  have he : {u : PolarPoint | cartesianRadius u ≤ r} =
      e ⁻¹' Metric.closedBall (0 : ℂ) r := by
    ext u
    simp [e, cartesianRadius]
  rw [he, ← e.preimage_interior, interior_closedBall' (0 : ℂ) r]
  ext u
  simp [e, cartesianRadius]

theorem interior_sphereNorthClosedDisk (r : ℝ) :
    interior (sphereNorthClosedDisk r) =
      sphereNorthSource ∩ sphereNorthChart ⁻¹' {u : PolarPoint | cartesianRadius u < r} := by
  change interior (sphereNorthCoordinates.source ∩ sphereNorthCoordinates ⁻¹'
    {u : PolarPoint | cartesianRadius u ≤ r}) = _
  rw [interior_inter, sphereNorthCoordinates.open_source.interior_eq,
    ← sphereNorthCoordinates.preimage_interior, interior_closedCartesianDisk]
  rfl

theorem closure_openCartesianDisk {r : ℝ} (hr : 0 < r) :
    closure {u : PolarPoint | cartesianRadius u < r} =
      {u : PolarPoint | cartesianRadius u ≤ r} := by
  let e : PolarPoint ≃ₜ ℂ := Complex.equivRealProdCLM.symm.toHomeomorph
  have he : {u : PolarPoint | cartesianRadius u < r} = e ⁻¹' Metric.ball (0 : ℂ) r := by
    ext u
    simp [e, cartesianRadius]
  rw [he, ← e.preimage_closure, closure_ball (0 : ℂ) hr.ne']
  ext u
  simp [e, cartesianRadius]

theorem sphereNorthClosedDisk_interior_nonempty {r : ℝ} (hr : 0 < r) :
    (interior (sphereNorthClosedDisk r)).Nonempty := by
  rw [interior_sphereNorthClosedDisk]
  refine ⟨sphereNorthInverse 0, sphereNorthInverse_source 0, ?_⟩
  change cartesianRadius (sphereNorthChart (sphereNorthInverse 0)) < r
  simpa [sphereNorthChart_inverse, cartesianRadius] using hr

theorem closure_interior_sphereNorthClosedDisk {r : ℝ} (hr : 0 < r) :
    closure (interior (sphereNorthClosedDisk r)) = sphereNorthClosedDisk r := by
  apply le_antisymm (closure_minimal interior_subset (isCompact_sphereNorthClosedDisk r).isClosed)
  have himage : sphereNorthInverse '' {u : PolarPoint | cartesianRadius u ≤ r} ⊆
      closure (sphereNorthInverse '' {u : PolarPoint | cartesianRadius u < r}) := by
    rw [← closure_openCartesianDisk hr]
    exact image_closure_subset_closure_image contMDiff_sphereNorthInverse.continuous
  have hopen : sphereNorthInverse '' {u : PolarPoint | cartesianRadius u < r} ⊆
      interior (sphereNorthClosedDisk r) := by
    rintro x ⟨u, hu, rfl⟩
    rw [interior_sphereNorthClosedDisk]
    refine ⟨sphereNorthInverse_source u, ?_⟩
    change cartesianRadius (sphereNorthChart (sphereNorthInverse u)) < r
    rw [sphereNorthChart_inverse]
    exact hu
  calc
    sphereNorthClosedDisk r =
        sphereNorthInverse '' {u : PolarPoint | cartesianRadius u ≤ r} := sphereNorthClosedDisk_eq_image r
    _ ⊆ closure (sphereNorthInverse '' {u : PolarPoint | cartesianRadius u < r}) := himage
    _ ⊆ closure (interior (sphereNorthClosedDisk r)) := closure_mono hopen

theorem sphereGraphDisk_interior_nonempty : (interior sphereGraphDisk).Nonempty := by
  rw [sphereGraphDisk_eq_northClosedDisk]
  exact sphereNorthClosedDisk_interior_nonempty (by norm_num)

theorem closure_interior_sphereGraphDisk : closure (interior sphereGraphDisk) = sphereGraphDisk := by
  rw [sphereGraphDisk_eq_northClosedDisk]
  exact closure_interior_sphereNorthClosedDisk (by norm_num)

theorem closure_interior_sphereInnerDisk {R a : ℝ} (hR : 0 < R) (ha : 0 < a) :
    closure (interior (sphereInnerDisk R a)) = sphereInnerDisk R a := by
  rw [sphereInnerDisk_eq_northClosedDisk hR a]
  exact closure_interior_sphereNorthClosedDisk (div_pos ha hR)

theorem sphereNorthChart_radius_lt_one_iff (x : SpherePoint) (hx : x ∈ sphereNorthSource) :
    cartesianRadius (sphereNorthChart x) < 1 ↔ 0 < (x : E3) 2 := by
  have hden : 0 < 1 + (x : E3) 2 := by
    have hb := (spherePoint_vertical_bounds x).1
    change (x : E3) 2 ≠ -1 at hx
    rcases eq_or_lt_of_le hb with he | he
    · exact (hx he.symm).elim
    · linarith
  have hs := sphereNorthChart_energy x hx
  rw [spherePlaneEnergy_eq_radius_sq] at hs
  have hr : 0 ≤ cartesianRadius (sphereNorthChart x) := norm_nonneg _
  constructor
  · intro h
    have hsq : cartesianRadius (sphereNorthChart x) ^ 2 < 1 := by nlinarith
    rw [hs] at hsq
    have he := (div_lt_one hden).mp hsq
    linarith
  · intro h
    have he : (1 - (x : E3) 2) / (1 + (x : E3) 2) < 1 :=
      (div_lt_one hden).mpr (by linarith)
    rw [← hs] at he
    nlinarith

/-- Interior is relative to the actual standard sphere. -/
theorem interior_sphereGraphDisk :
    interior sphereGraphDisk = {x : SpherePoint | 0 < (x : E3) 2} := by
  rw [sphereGraphDisk_eq_northClosedDisk, interior_sphereNorthClosedDisk]
  ext x
  constructor
  · rintro ⟨hx, hr⟩
    exact (sphereNorthChart_radius_lt_one_iff x hx).mp hr
  · intro hx
    have hn : x ∈ sphereNorthSource := by change (x : E3) 2 ≠ -1; change 0 < (x : E3) 2 at hx; linarith
    exact ⟨hn, (sphereNorthChart_radius_lt_one_iff x hn).mpr hx⟩

theorem sphereComplementaryCap_eq_compl_interior :
    sphereComplementaryCap = (interior sphereGraphDisk)ᶜ := by
  rw [interior_sphereGraphDisk]
  ext x
  simp [sphereComplementaryCap]

theorem sphereComplementaryCap_eq_diff_interior :
    sphereComplementaryCap = Set.univ \ interior sphereGraphDisk := by
  simpa only [compl_eq_univ_sdiff] using sphereComplementaryCap_eq_compl_interior

theorem closure_interior_sphereComplementaryCap :
    closure (interior sphereComplementaryCap) = sphereComplementaryCap := by
  rw [sphereComplementaryCap_eq_compl_interior, interior_compl,
    closure_interior_sphereGraphDisk, closure_compl]

theorem sphereGraphDisk_union_complementaryCap :
    sphereGraphDisk ∪ sphereComplementaryCap = Set.univ := by
  ext x
  simp only [sphereGraphDisk, sphereComplementaryCap, mem_union, mem_ofPred_eq, mem_univ, iff_true]
  exact le_total 0 ((x : E3) 2)

theorem sphereGraphDisk_inter_complementaryCap :
    sphereGraphDisk ∩ sphereComplementaryCap = {x : SpherePoint | (x : E3) 2 = 0} := by
  ext x
  simp only [sphereGraphDisk, sphereComplementaryCap, mem_inter_iff, mem_ofPred_eq]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => by simp [h]⟩

theorem sphereInnerDisk_subset_interior_graphDisk {R a : ℝ}
    (hR : 0 < R) (haR : a < R) : sphereInnerDisk R a ⊆ interior sphereGraphDisk := by
  rw [sphereInnerDisk_eq_northClosedDisk hR a, interior_sphereGraphDisk]
  intro x hx
  apply (sphereNorthChart_radius_lt_one_iff x hx.1).mp
  exact hx.2.trans_lt ((div_lt_one hR).mpr haR)

theorem sphereInnerDisk_interior_nonempty {R a : ℝ} (hR : 0 < R) (ha : 0 < a) :
    (interior (sphereInnerDisk R a)).Nonempty := by
  rw [sphereInnerDisk_eq_northClosedDisk hR a, interior_sphereNorthClosedDisk]
  refine ⟨sphereNorthInverse 0, sphereNorthInverse_source 0, ?_⟩
  change cartesianRadius (sphereNorthChart (sphereNorthInverse 0)) < a / R
  simpa [sphereNorthChart_inverse, cartesianRadius] using div_pos ha hR

theorem sphereComplementaryCap_interior_nonempty :
    (interior sphereComplementaryCap).Nonempty := by
  let U : Set SpherePoint := {x | (x : E3) 2 < 0}
  have hU : IsOpen U := isOpen_lt
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp continuous_subtype_val)
    continuous_const
  have hsub : U ⊆ sphereComplementaryCap := by
    intro x hx
    change (x : E3) 2 ≤ 0
    change (x : E3) 2 < 0 at hx
    exact le_of_lt hx
  refine ⟨sphereSouthInverse 0, hU.subset_interior_iff.mpr hsub ?_⟩
  change (sphereSouthInvVector 0) 2 < 0
  simp [sphereSouthInvVector, graphMap_two, spherePlaneEnergy, sphereStereoDenom]

theorem disjoint_sphereInnerDisk_complementaryCap {R a : ℝ}
    (hR : 0 < R) (haR : a < R) : Disjoint (sphereInnerDisk R a) sphereComplementaryCap := by
  rw [sphereComplementaryCap_eq_compl_interior]
  exact Set.disjoint_compl_right_iff_subset.mpr
    (sphereInnerDisk_subset_interior_graphDisk hR haR)

@[simp] theorem sphereGraphDiskPhysicalHomeomorph_apply {R : ℝ} (hR : 0 < R)
    (x : ↥sphereGraphDisk) :
    (sphereGraphDiskPhysicalHomeomorph hR x : PolarPoint) = R • sphereNorthChart x.1 := rfl

@[simp] theorem sphereComplementaryCapHomeomorph_apply (x : ↥sphereComplementaryCap) :
    (sphereComplementaryCapHomeomorph x : PolarPoint) = sphereSouthChart x.1 := rfl

theorem sphereGraphCapFamily_image_graphDisk {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (C : PolarPoint → E3) {R : ℝ}
    (hR : 0 < R) (L t : ℝ) :
    (fun x : SpherePoint => sphereGraphCapFamily D C R L (x, t)) '' sphereGraphDisk =
      graphPhaseDiskImage D R t := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    change sphereGraphCapFamily D C R L (x, t) ∈ graphPhaseDiskImage D R t
    rw [sphereGraphCapFamily_north D C R L t x hx]
    exact ⟨R • sphereNorthChart x, (sphereGraphDiskPhysicalHomeomorph hR ⟨x, hx⟩).property, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨x, hx⟩ := (sphereGraphDiskPhysicalHomeomorph hR).surjective ⟨u, hu⟩
    refine ⟨x.1, x.property, ?_⟩
    change sphereGraphCapFamily D C R L (x.1, t) = D.rotationFamily t u
    rw [sphereGraphCapFamily_north D C R L t x.1 x.property]
    exact congrArg (D.rotationFamily t) (congrArg Subtype.val hx)

theorem sphereGraphCapFamily_image_complementaryCap {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {C : PolarPoint → E3} {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L)
    (hcollar : ∀ y : PolarPoint, cartesianRadius y = 1 →
      (C ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
        fun z => graphMap id (fun _ => A.cRight) ((R / cartesianRadius z ^ 2) • z)) (t : ℝ) :
    (fun x : SpherePoint => sphereGraphCapFamily D C R L (x, t)) '' sphereComplementaryCap =
      C '' {u : PolarPoint | cartesianRadius u ≤ 1} := by
  have ha := capSphereRatio_mem (A.b_pos.trans hR) hL
  have hp := capSphereRadialMap_bijOn_disk ha.1 ha.2
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    change sphereGraphCapFamily D C R L (x, t) ∈ C '' {u : PolarPoint | cartesianRadius u ≤ 1}
    rw [sphereGraphCapFamily_south D hR hcollar x hx t]
    exact ⟨capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x),
      hp.mapsTo (sphereComplementaryCapHomeomorph ⟨x, hx⟩).property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, hu, heu⟩ := hp.surjOn hy
    obtain ⟨x, hx⟩ := sphereComplementaryCapHomeomorph.surjective ⟨u, hu⟩
    refine ⟨x.1, x.property, ?_⟩
    change sphereGraphCapFamily D C R L (x.1, t) = C y
    rw [sphereGraphCapFamily_south D hR hcollar x.1 x.property t]
    change C (capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x.1)) = C y
    rw [← sphereComplementaryCapHomeomorph_apply x, congrArg Subtype.val hx, heu]

theorem sphereGraphCapFamily_fixed_innerDisk {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (C : PolarPoint → E3) {R : ℝ}
    (hR : A.b < R) (L t : ℝ) {x : SpherePoint} (hx : x ∈ sphereInnerDisk R A.a) :
    sphereGraphCapFamily D C R L (x, t) = sphereGraphCapFamily D C R L (x, 0) := by
  have hn := sphereInnerDisk_subset_interior_graphDisk (A.b_pos.trans hR) (A.a_lt_b.trans hR) hx
  rw [interior_sphereGraphDisk] at hn
  exact sphereGraphCapFamily_fixed_inner D C R L t x (le_of_lt hn) hx.2

theorem sphereGraphCapFamily_image_innerDisk {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (C : PolarPoint → E3) {R : ℝ}
    (hR : A.b < R) (L t : ℝ) :
    (fun x : SpherePoint => sphereGraphCapFamily D C R L (x, t)) '' sphereInnerDisk R A.a =
      D.map '' {u : PolarPoint | cartesianRadius u ≤ A.a} := by
  have heq (x : SpherePoint) (hx : x ∈ sphereInnerDisk R A.a) :
      sphereGraphCapFamily D C R L (x, t) = D.map (R • sphereNorthChart x) := by
    have hn := sphereInnerDisk_subset_interior_graphDisk
      (A.b_pos.trans hR) (A.a_lt_b.trans hR) hx
    rw [interior_sphereGraphDisk] at hn
    rw [sphereGraphCapFamily_north D C R L t x (le_of_lt hn),
      D.rotationFamily_fixed_inside t hx.2]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨R • sphereNorthChart x, hx.2, (heq x hx).symm⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨x, hx⟩ := (sphereInnerDiskPhysicalHomeomorph (A.b_pos.trans hR) A.a).surjective ⟨u, hu⟩
    refine ⟨x.1, x.property, ?_⟩
    change sphereGraphCapFamily D C R L (x.1, t) = D.map u
    rw [heq x.1 x.property]
    exact congrArg D.map (congrArg Subtype.val hx)

/-- The actual closed inner disk and the entire complementary cap are fixed
for the same sphere family and the same physical radius `R`. -/
theorem IsometricGraphDevelopment.markedSphereFamily_fixed_disks {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) :
    (interior (sphereInnerDisk R A.a)).Nonempty ∧
    (interior sphereComplementaryCap).Nonempty ∧
    sphereInnerDisk R A.a ⊆ interior sphereGraphDisk ∧
    sphereComplementaryCap = Set.univ \ interior sphereGraphDisk ∧
    ∀ x ∈ sphereInnerDisk R A.a ∪ sphereComplementaryCap, ∀ t : ℝ,
      sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t) =
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, 0) := by
  refine ⟨sphereInnerDisk_interior_nonempty (A.b_pos.trans hR) A.a_pos,
    sphereComplementaryCap_interior_nonempty,
    sphereInnerDisk_subset_interior_graphDisk (A.b_pos.trans hR) (A.a_lt_b.trans hR),
    sphereComplementaryCap_eq_diff_interior, ?_⟩
  intro x hx t
  rcases hx with hx | hx
  · exact sphereGraphCapFamily_fixed_innerDisk D _ hR L t hx
  · exact sphereGraphCapFamily_fixed_closed_south D hR
      (fun y hy => markedCapMap_capSphereRadialMap_rim_germ
        (A.b_pos.trans hR) hL hρ hsmall A.cRight hy) x hx t

end ContinuousFlexibility
