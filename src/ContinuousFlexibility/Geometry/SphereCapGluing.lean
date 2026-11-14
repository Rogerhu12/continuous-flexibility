module

public import ContinuousFlexibility.Geometry.SphereCoordinates
public import ContinuousFlexibility.Geometry.CapSphereProfile
public import ContinuousFlexibility.Geometry.GraphCapAttachment
public import ContinuousFlexibility.Geometry.MarkedCapDisk

/-!
# Gluing the actual graph family to a cap on the standard sphere

The two hemispheres use nondegenerate normalized stereographic coordinates.
The cap profile supplies equality on an entire neighborhood of each equatorial
point. The generic collar statement below is instantiated with both constructed
caps, rather than being an unproved existence input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped ContDiff Manifold Topology

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}
local notation "SphereTimeModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

set_option backward.isDefEq.respectTransparency false

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

def sphereNorthFamily {A : FlatAnnularCore} (D : IsometricGraphDevelopment A)
    (R : ℝ) (q : SpherePoint × ℝ) : E3 :=
  D.rotationFamily q.2 (R • sphereNorthChart q.1)

def sphereSouthCap (C : PolarPoint → E3) (R L : ℝ) (x : SpherePoint) : E3 :=
  C (capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x))

def sphereGraphCapFamily {A : FlatAnnularCore} (D : IsometricGraphDevelopment A)
    (C : PolarPoint → E3) (R L : ℝ) (q : SpherePoint × ℝ) : E3 :=
  if 0 ≤ (q.1 : E3) 2 then sphereNorthFamily D R q else sphereSouthCap C R L q.1

theorem contMDiffAt_sphereNorthFamily {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R : ℝ) (q : SpherePoint × ℝ)
    (hq : q.1 ∈ sphereNorthSource) :
    ContMDiffAt SphereTimeModel 𝓘(ℝ, E3) ∞ (sphereNorthFamily D R) q := by
  change ContMDiffAt SphereTimeModel 𝓘(ℝ, E3) ∞
    (fun p : SpherePoint × ℝ => D.rotationFamily p.2 (R • sphereNorthChart p.1)) q
  have hfst : ContMDiffAt SphereTimeModel (𝓡 2) ∞ Prod.fst q := contMDiffAt_fst
  have hc : ContMDiffAt SphereTimeModel 𝓘(ℝ, PolarPoint) ∞
      (fun p : SpherePoint × ℝ => sphereNorthChart p.1) q :=
    (contMDiffAt_sphereNorthChart q.1 hq).comp q hfst
  have ht : ContMDiffAt SphereTimeModel 𝓘(ℝ, ℝ) ∞ Prod.snd q := contMDiffAt_snd
  have hpair : ContMDiffAt SphereTimeModel 𝓘(ℝ, PolarPoint × ℝ) ∞
      (fun p : SpherePoint × ℝ => (sphereNorthChart p.1, p.2)) q := hc.prodMk_space ht
  have hRconst : ContDiff ℝ ∞ (fun _ : PolarPoint × ℝ => R) := contDiff_const
  have hspace : ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => p.1) := contDiff_fst
  have hs : ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => R • p.1) :=
    hRconst.smul hspace
  have ht' : ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => p.2) := contDiff_snd
  have hinput : ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => (p.2, R • p.1)) :=
    ht'.prodMk hs
  have hf : ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => D.rotationFamily p.2 (R • p.1)) :=
    by simpa only [Function.comp_def] using D.rotationFamily_joint_smooth.comp hinput
  have hFat : ContMDiffAt 𝓘(ℝ, PolarPoint × ℝ) 𝓘(ℝ, E3) ∞
      (fun p : PolarPoint × ℝ => D.rotationFamily p.2 (R • p.1))
      (sphereNorthChart q.1, q.2) := hf.contDiffAt.contMDiffAt
  simpa only [Function.comp_def] using hFat.comp q hpair

theorem contMDiffAt_sphereSouthCap {C : PolarPoint → E3}
    (hC : ContDiff ℝ ∞ C) (R L : ℝ) (x : SpherePoint) (hx : x ∈ sphereSouthSource) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, E3) ∞ (sphereSouthCap C R L) x := by
  exact hC.contMDiff.contMDiffAt.comp x
    ((contDiff_capSphereRadialMap (capSphereRatio R L)).contMDiff.contMDiffAt.comp x
      (contMDiffAt_sphereSouthChart x hx))

theorem sphere_equator_sources {x : SpherePoint} (hx : (x : E3) 2 = 0) :
    x ∈ sphereNorthSource ∧ x ∈ sphereSouthSource := by
  constructor
  · change (x : E3) 2 ≠ -1
    rw [hx]
    norm_num
  · change (x : E3) 2 ≠ 1
    rw [hx]
    norm_num

theorem sphere_equator_chart_radii {x : SpherePoint} (hx : (x : E3) 2 = 0) :
    cartesianRadius (sphereNorthChart x) = 1 ∧
      cartesianRadius (sphereSouthChart x) = 1 := by
  obtain ⟨hn, hs⟩ := sphere_equator_sources hx
  have hen := sphereNorthChart_energy x hn
  have hes := sphereSouthChart_energy x hs
  rw [spherePlaneEnergy_eq_radius_sq, hx] at hen hes
  norm_num only [sub_zero, add_zero, div_one] at hen hes
  have hrn : 0 ≤ cartesianRadius (sphereNorthChart x) := norm_nonneg _
  have hrs : 0 ≤ cartesianRadius (sphereSouthChart x) := norm_nonneg _
  constructor <;> nlinarith

theorem sphere_chart_physical_inversion (R : ℝ) (x : SpherePoint)
    (hn : x ∈ sphereNorthSource) (hs : x ∈ sphereSouthSource) :
    (R / cartesianRadius (sphereSouthChart x) ^ 2) • sphereSouthChart x =
      R • sphereNorthChart x := by
  rw [sphereNorthChart_eq_inversion_south x hn hs, spherePlaneEnergy_eq_radius_sq, smul_smul]
  simp only [div_eq_mul_inv]

theorem markedCapMap_capSphereRadialMap_rim_germ {R L ρ k : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ)
    {y : PolarPoint} (hy : cartesianRadius y = 1) :
    (markedCapMap R h L k ρ ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
      fun z : PolarPoint => graphMap id (fun _ => h) ((R / cartesianRadius z ^ 2) • z) := by
  have hb : cartesianRadius
      (capDiskBase R L (capSphereRadialMap (capSphereRatio R L) y)) = R := by
    rw [capSphereRadialMap_boundary _ hy, capDiskBase_radius hR hL hy.le]
    simp [capDiskParameter, hy, capMeridianRadius]
  have hc : Continuous (fun z : PolarPoint => cartesianRadius
      (capDiskBase R L (capSphereRadialMap (capSphereRatio R L) z))) :=
    continuous_cartesianRadius.comp ((markedCap_contDiff_base hR hL).continuous.comp
      (contDiff_capSphereRadialMap (capSphereRatio R L)).continuous)
  have hn : ∀ᶠ z in 𝓝 y, cartesianRadius
      (capDiskBase R L (capSphereRadialMap (capSphereRatio R L) z)) < R + L / 16 :=
    hc.continuousAt.eventually_lt continuousAt_const (by rw [hb]; linarith)
  filter_upwards [hn, capDiskMap_capSphereRadialMap_rim_germ hR hL h hy] with z hz he
  change markedCapMap R h L k ρ (capSphereRadialMap (capSphereRatio R L) z) = _
  rw [markedCapMap_eq_capDiskMap_of_inner hR hL hρ hsmall h hz.le]
  exact he

/-- The actual open equatorial overlap, uniform in the real phase. -/
theorem sphereGraphCap_equator_germ {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {C : PolarPoint → E3} {R L : ℝ}
    (hR : A.b < R)
    (hcollar : ∀ y : PolarPoint, cartesianRadius y = 1 →
      (C ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
        fun z => graphMap id (fun _ => A.cRight) ((R / cartesianRadius z ^ 2) • z))
    (q : SpherePoint × ℝ) (hq : (q.1 : E3) 2 = 0) :
    (fun p : SpherePoint × ℝ => sphereSouthCap C R L p.1) =ᶠ[𝓝 q]
      sphereNorthFamily D R := by
  obtain ⟨hn, hs⟩ := sphere_equator_sources hq
  obtain ⟨hrn, hrs⟩ := sphere_equator_chart_radii hq
  have hnc := (contMDiffAt_sphereNorthChart q.1 hn).continuousAt.comp continuousAt_fst
  have hsc := (contMDiffAt_sphereSouthChart q.1 hs).continuousAt.comp continuousAt_fst
  have hcap := (hcollar _ hrs).comp_tendsto hsc.tendsto
  have hphysical : ContinuousAt
      (fun p : SpherePoint × ℝ => cartesianRadius (R • sphereNorthChart p.1)) q :=
    continuous_cartesianRadius.continuousAt.comp
      ((continuousAt_const : ContinuousAt (fun _ : SpherePoint × ℝ => R) q).smul hnc)
  have hrad : A.b < cartesianRadius (R • sphereNorthChart q.1) := by
    rw [capDisk_radius_smul, abs_of_pos (A.b_pos.trans hR), hrn, mul_one]
    exact hR
  have hnear := continuousAt_const.eventually_lt hphysical hrad
  have hsrcn : ∀ᶠ p : SpherePoint × ℝ in 𝓝 q, p.1 ∈ sphereNorthSource :=
    continuousAt_fst.preimage_mem_nhds (isOpen_sphereNorthSource.mem_nhds hn)
  have hsrcs : ∀ᶠ p : SpherePoint × ℝ in 𝓝 q, p.1 ∈ sphereSouthSource :=
    continuousAt_fst.preimage_mem_nhds (isOpen_sphereSouthSource.mem_nhds hs)
  filter_upwards [hcap, hnear, hsrcn, hsrcs] with p hp hpr hpn hps
  change C (capSphereRadialMap (capSphereRatio R L) (sphereSouthChart p.1)) =
    D.rotationFamily p.2 (R • sphereNorthChart p.1)
  rw [D.phase_flat_outside p.2 hpr]
  exact hp.trans (congrArg (graphMap id (fun _ => A.cRight))
    (sphere_chart_physical_inversion R p.1 hpn hps))

theorem contMDiff_sphereGraphCapFamily {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {C : PolarPoint → E3} {R L : ℝ}
    (hR : A.b < R) (hC : ContDiff ℝ ∞ C)
    (hcollar : ∀ y : PolarPoint, cartesianRadius y = 1 →
      (C ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
        fun z => graphMap id (fun _ => A.cRight) ((R / cartesianRadius z ^ 2) • z)) :
    ContMDiff SphereTimeModel 𝓘(ℝ, E3) ∞ (sphereGraphCapFamily D C R L) := by
  intro q
  have hcoord : Continuous (fun p : SpherePoint × ℝ => (p.1 : E3) 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp
      (continuous_subtype_val.comp continuous_fst)
  by_cases hp : 0 < (q.1 : E3) 2
  · have hn : q.1 ∈ sphereNorthSource := by
      change (q.1 : E3) 2 ≠ -1
      linarith
    apply (contMDiffAt_sphereNorthFamily D R q hn).congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt hcoord.continuousAt hp] with p hpp
    simp only [sphereGraphCapFamily, hpp.le, ↓reduceIte]
  by_cases hm : (q.1 : E3) 2 < 0
  · have hs : q.1 ∈ sphereSouthSource := by
      change (q.1 : E3) 2 ≠ 1
      linarith
    have hsm : ContMDiffAt SphereTimeModel 𝓘(ℝ, E3) ∞
        (fun p : SpherePoint × ℝ => sphereSouthCap C R L p.1) q :=
      (contMDiffAt_sphereSouthCap hC R L q.1 hs).comp q contMDiffAt_fst
    apply hsm.congr_of_eventuallyEq
    filter_upwards [hcoord.continuousAt.eventually_lt continuousAt_const hm] with p hpm
    simp only [sphereGraphCapFamily, not_le.mpr hpm, ↓reduceIte]
  · have hz : (q.1 : E3) 2 = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hm)
    have hn := (sphere_equator_sources hz).1
    apply (contMDiffAt_sphereNorthFamily D R q hn).congr_of_eventuallyEq
    filter_upwards [sphereGraphCap_equator_germ D hR hcollar q hz] with p he
    change (if 0 ≤ (p.1 : E3) 2 then _ else _) = _
    split_ifs
    · rfl
    · exact he

/-- The unmarked constructed cap gives a genuinely smooth standard-sphere family. -/
theorem IsometricGraphDevelopment.contMDiff_unmarkedSphereFamily {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L : ℝ} (hR : A.b < R) (hL : 0 < L) :
    ContMDiff SphereTimeModel 𝓘(ℝ, E3) ∞
      (sphereGraphCapFamily D (capDiskMap R A.cRight L) R L) :=
  contMDiff_sphereGraphCapFamily D hR (contDiff_capDiskMap (A.b_pos.trans hR) hL A.cRight)
    (fun _ hy => capDiskMap_capSphereRadialMap_rim_germ (A.b_pos.trans hR) hL A.cRight hy)

/-- The same bridge is instantiated with the actual inserted-marker cap. -/
theorem IsometricGraphDevelopment.contMDiff_markedSphereFamily {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) :
    ContMDiff SphereTimeModel 𝓘(ℝ, E3) ∞
      (sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L) :=
  contMDiff_sphereGraphCapFamily D hR
    (contDiff_markedCapMap (A.b_pos.trans hR) hL A.cRight k ρ)
    (fun _ hy => markedCapMap_capSphereRadialMap_rim_germ
      (A.b_pos.trans hR) hL hρ hsmall A.cRight hy)

theorem sphereGraphCapFamily_periodic {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (C : PolarPoint → E3) (R L : ℝ) (x : SpherePoint) :
    Function.Periodic (fun t => sphereGraphCapFamily D C R L (x, t)) 1 := by
  intro t
  simp only [sphereGraphCapFamily, sphereNorthFamily]
  split_ifs
  · exact congrFun (D.rotationFamily_periodic t) _
  · rfl

theorem sphereGraphCapFamily_fixed_south {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (C : PolarPoint → E3) (R L t : ℝ)
    (x : SpherePoint) (hx : (x : E3) 2 < 0) :
    sphereGraphCapFamily D C R L (x, t) = sphereGraphCapFamily D C R L (x, 0) := by
  simp only [sphereGraphCapFamily, not_le.mpr hx, ↓reduceIte]

theorem sphereGraphCapFamily_fixed_inner {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (C : PolarPoint → E3) (R L t : ℝ)
    (x : SpherePoint) (hx : 0 ≤ (x : E3) 2)
    (hinner : cartesianRadius (R • sphereNorthChart x) ≤ A.a) :
    sphereGraphCapFamily D C R L (x, t) = sphereGraphCapFamily D C R L (x, 0) := by
  simp only [sphereGraphCapFamily, hx, ↓reduceIte, sphereNorthFamily]
  rw [D.rotationFamily_fixed_inside t hinner, D.rotationFamily_zero]

theorem sphereGraphCapFamily_north {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (C : PolarPoint → E3) (R L t : ℝ)
    (x : SpherePoint) (hx : 0 ≤ (x : E3) 2) :
    sphereGraphCapFamily D C R L (x, t) = D.rotationFamily t (R • sphereNorthChart x) := by
  simp only [sphereGraphCapFamily, hx, ↓reduceIte, sphereNorthFamily]

theorem sphereGraphCapFamily_south {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {C : PolarPoint → E3} {R L : ℝ}
    (hR : A.b < R)
    (hcollar : ∀ y : PolarPoint, cartesianRadius y = 1 →
      (C ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
        fun z => graphMap id (fun _ => A.cRight) ((R / cartesianRadius z ^ 2) • z))
    (x : SpherePoint) (hx : (x : E3) 2 ≤ 0) (t : ℝ) :
    sphereGraphCapFamily D C R L (x, t) = sphereSouthCap C R L x := by
  by_cases hn : 0 ≤ (x : E3) 2
  · have hz : (x : E3) 2 = 0 := le_antisymm hx hn
    have he := (sphereGraphCap_equator_germ D hR hcollar (x, t) hz).eq_of_nhds
    simp only [sphereGraphCapFamily, hn, ↓reduceIte]
    exact he.symm
  · simp only [sphereGraphCapFamily, hn, ↓reduceIte]

theorem sphereGraphCapFamily_fixed_closed_south {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {C : PolarPoint → E3} {R L : ℝ}
    (hR : A.b < R)
    (hcollar : ∀ y : PolarPoint, cartesianRadius y = 1 →
      (C ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
        fun z => graphMap id (fun _ => A.cRight) ((R / cartesianRadius z ^ 2) • z))
    (x : SpherePoint) (hx : (x : E3) 2 ≤ 0) (t : ℝ) :
    sphereGraphCapFamily D C R L (x, t) = sphereGraphCapFamily D C R L (x, 0) := by
  rw [sphereGraphCapFamily_south D hR hcollar x hx,
    sphereGraphCapFamily_south D hR hcollar x hx]

/-- The image is the same actual graph disk and the same actual cap disk. -/
theorem sphereGraphCapFamily_range {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {C : PolarPoint → E3} {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L)
    (hcollar : ∀ y : PolarPoint, cartesianRadius y = 1 →
      (C ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
        fun z => graphMap id (fun _ => A.cRight) ((R / cartesianRadius z ^ 2) • z)) (t : ℝ) :
    Set.range (fun x : SpherePoint => sphereGraphCapFamily D C R L (x, t)) =
      graphPhaseDiskImage D R t ∪ C '' {y : PolarPoint | cartesianRadius y ≤ 1} := by
  have hRp : 0 < R := A.b_pos.trans hR
  have ha := capSphereRatio_mem hRp hL
  have hphi := capSphereRadialMap_bijOn_disk ha.1 ha.2
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : 0 ≤ (x : E3) 2
    · left
      change sphereGraphCapFamily D C R L (x, t) ∈ graphPhaseDiskImage D R t
      rw [sphereGraphCapFamily_north D C R L t x hx]
      refine ⟨R • sphereNorthChart x, ?_, rfl⟩
      have hn : x ∈ sphereNorthSource := by change (x : E3) 2 ≠ -1; linarith
      have hr := (sphereNorthChart_radius_le_one_iff x hn).mpr hx
      change cartesianRadius (R • sphereNorthChart x) ≤ R
      rw [capDisk_radius_smul, abs_of_pos hRp]
      nlinarith
    · right
      change sphereGraphCapFamily D C R L (x, t) ∈ C '' {y : PolarPoint | cartesianRadius y ≤ 1}
      rw [sphereGraphCapFamily_south D hR hcollar x (le_of_not_ge hx)]
      refine ⟨capSphereRadialMap (capSphereRatio R L) (sphereSouthChart x), ?_, rfl⟩
      have hs : x ∈ sphereSouthSource := by change (x : E3) 2 ≠ 1; linarith
      exact hphi.mapsTo ((sphereSouthChart_radius_le_one_iff x hs).mpr (le_of_not_ge hx))
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · let u : PolarPoint := R⁻¹ • y
      have hu : cartesianRadius u ≤ 1 := by
        dsimp [u]
        rw [capDisk_radius_smul, abs_of_pos (inv_pos.mpr hRp)]
        exact (inv_mul_le_iff₀ hRp).mpr (by simpa using hy)
      have hx : 0 ≤ (sphereNorthInverse u : E3) 2 := by
        have hr := (sphereNorthChart_radius_le_one_iff
          (sphereNorthInverse u) (sphereNorthInverse_source u))
        rw [sphereNorthChart_inverse] at hr
        exact hr.mp hu
      refine ⟨sphereNorthInverse u, ?_⟩
      change sphereGraphCapFamily D C R L (sphereNorthInverse u, t) = _
      rw [sphereGraphCapFamily_north D C R L t _ hx, sphereNorthChart_inverse]
      simp only [u, smul_smul, mul_inv_cancel₀ hRp.ne', one_smul]
    · obtain ⟨u, hu, heu⟩ := hphi.surjOn hy
      have hx : (sphereSouthInverse u : E3) 2 ≤ 0 := by
        have hr := sphereSouthChart_radius_le_one_iff
          (sphereSouthInverse u) (sphereSouthInverse_source u)
        rw [sphereSouthChart_inverse] at hr
        exact hr.mp hu
      refine ⟨sphereSouthInverse u, ?_⟩
      change sphereGraphCapFamily D C R L (sphereSouthInverse u, t) = _
      rw [sphereGraphCapFamily_south D hR hcollar _ hx]
      simp only [sphereSouthCap, sphereSouthChart_inverse, heu]

theorem sphereNorthInverse_eq_southInverse_of_radius_one {u : PolarPoint}
    (hu : cartesianRadius u = 1) : sphereNorthInverse u = sphereSouthInverse u := by
  have he : spherePlaneEnergy u = 1 := by
    rw [spherePlaneEnergy_eq_radius_sq, hu]
    norm_num
  apply Subtype.ext
  apply e3_eq_of_base_height
  · simp only [sphereNorthInverse, sphereSouthInverse, sphereNorthInvVector,
      sphereSouthInvVector, graphBaseProjection_graphMap]
  · simp only [sphereNorthInverse, sphereSouthInverse, sphereNorthInvVector,
      sphereSouthInvVector, graphMap_two, he, sub_self, zero_div]

/-- Cross-hemisphere coincidences are forced to represent the same equator point. -/
theorem sphereGraphCap_cross_eq {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {C : PolarPoint → E3} {R L t : ℝ}
    (hR : A.b < R) (hL : 0 < L)
    (hCinj : Set.InjOn C {y : PolarPoint | cartesianRadius y ≤ 1})
    (hboundary : ∀ u : PolarPoint, cartesianRadius u = 1 →
      C u = graphMap id (fun _ => A.cRight) (R • u))
    (hmeet : graphPhaseDiskImage D R t ∩ (C '' {y : PolarPoint | cartesianRadius y ≤ 1}) ⊆
      capAttachingRim R A.cRight)
    {x y : SpherePoint} (hx : 0 ≤ (x : E3) 2) (hy : (y : E3) 2 ≤ 0)
    (he : D.rotationFamily t (R • sphereNorthChart x) = sphereSouthCap C R L y) : x = y := by
  have hRp := A.b_pos.trans hR
  have ha := capSphereRatio_mem hRp hL
  have hnx : x ∈ sphereNorthSource := by change (x : E3) 2 ≠ -1; linarith
  have hsy : y ∈ sphereSouthSource := by change (y : E3) 2 ≠ 1; linarith
  have hxr : cartesianRadius (R • sphereNorthChart x) ≤ R := by
    have hr := (sphereNorthChart_radius_le_one_iff x hnx).mpr hx
    rw [capDisk_radius_smul, abs_of_pos hRp]
    nlinarith
  have hyr : cartesianRadius
      (capSphereRadialMap (capSphereRatio R L) (sphereSouthChart y)) ≤ 1 :=
    (capSphereRadialMap_bijOn_disk ha.1 ha.2).mapsTo
      ((sphereSouthChart_radius_le_one_iff y hsy).mpr hy)
  obtain ⟨p, hp, hpv⟩ := hmeet ⟨⟨R • sphereNorthChart x, hxr, rfl⟩,
    ⟨capSphereRadialMap (capSphereRatio R L) (sphereSouthChart y), hyr, he.symm⟩⟩
  let u : PolarPoint := R⁻¹ • p
  have hu : cartesianRadius u = 1 := by
    dsimp [u]
    rw [capDisk_radius_smul, abs_of_pos (inv_pos.mpr hRp), hp, inv_mul_cancel₀ hRp.ne']
  have hRu : R • u = p := by simp only [u, smul_smul, mul_inv_cancel₀ hRp.ne', one_smul]
  have hxp : R • sphereNorthChart x = p :=
    (D.rotationFamily_embedding t).injective (hpv.symm.trans
      (D.phase_flat_outside t (by rw [hp]; exact hR)).symm)
  have hNu : sphereNorthChart x = u := by
    have hh := congrArg (fun v : PolarPoint => R⁻¹ • v) hxp
    simpa only [smul_smul, inv_mul_cancel₀ hRp.ne', one_smul, u] using hh
  have hCu : C u = D.rotationFamily t (R • sphereNorthChart x) := by
    rw [hboundary u hu, hRu]
    exact hpv
  have hpu : capSphereRadialMap (capSphereRatio R L) (sphereSouthChart y) = u :=
    hCinj hyr hu.le (he.symm.trans hCu.symm)
  have hSu : sphereSouthChart y = u :=
    capSphereRadialMap_injective ha.1 ha.2 (hpu.trans (capSphereRadialMap_boundary _ hu).symm)
  calc
    x = sphereNorthInverse (sphereNorthChart x) := (sphereNorthInverse_chart x hnx).symm
    _ = sphereNorthInverse u := congrArg sphereNorthInverse hNu
    _ = sphereSouthInverse u := sphereNorthInverse_eq_southInverse_of_radius_one hu
    _ = sphereSouthInverse (sphereSouthChart y) := congrArg sphereSouthInverse hSu.symm
    _ = y := sphereSouthInverse_chart y hsy

theorem sphereGraphCapFamily_injective {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {C : PolarPoint → E3} {R L t : ℝ}
    (hR : A.b < R) (hL : 0 < L)
    (hCinj : Set.InjOn C {y : PolarPoint | cartesianRadius y ≤ 1})
    (hboundary : ∀ u : PolarPoint, cartesianRadius u = 1 →
      C u = graphMap id (fun _ => A.cRight) (R • u))
    (hmeet : graphPhaseDiskImage D R t ∩ (C '' {y : PolarPoint | cartesianRadius y ≤ 1}) ⊆
      capAttachingRim R A.cRight) :
    Function.Injective (fun x : SpherePoint => sphereGraphCapFamily D C R L (x, t)) := by
  have hRp := A.b_pos.trans hR
  have ha := capSphereRatio_mem hRp hL
  intro x y hxy
  change sphereGraphCapFamily D C R L (x, t) = sphereGraphCapFamily D C R L (y, t) at hxy
  by_cases hx : 0 ≤ (x : E3) 2
  · by_cases hy : 0 ≤ (y : E3) 2
    · rw [sphereGraphCapFamily_north D C R L t x hx,
        sphereGraphCapFamily_north D C R L t y hy] at hxy
      have hN : sphereNorthChart x = sphereNorthChart y := by
        have hh := congrArg (fun v : PolarPoint => R⁻¹ • v)
          ((D.rotationFamily_embedding t).injective hxy)
        simpa only [smul_smul, inv_mul_cancel₀ hRp.ne', one_smul] using hh
      exact sphereNorthChart_injectiveOn (by change (x : E3) 2 ≠ -1; linarith)
        (by change (y : E3) 2 ≠ -1; linarith) hN
    · simp only [sphereGraphCapFamily, hx, hy, ↓reduceIte, sphereNorthFamily] at hxy
      exact sphereGraphCap_cross_eq D hR hL hCinj hboundary hmeet hx (le_of_not_ge hy) hxy
  · by_cases hy : 0 ≤ (y : E3) 2
    · simp only [sphereGraphCapFamily, hx, hy, ↓reduceIte, sphereNorthFamily] at hxy
      exact (sphereGraphCap_cross_eq D hR hL hCinj hboundary hmeet hy (le_of_not_ge hx)
        hxy.symm).symm
    · simp only [sphereGraphCapFamily, hx, hy, ↓reduceIte, sphereSouthCap] at hxy
      have hsx : x ∈ sphereSouthSource := by change (x : E3) 2 ≠ 1; linarith
      have hsy : y ∈ sphereSouthSource := by change (y : E3) 2 ≠ 1; linarith
      have hxd := (capSphereRadialMap_bijOn_disk ha.1 ha.2).mapsTo
        ((sphereSouthChart_radius_le_one_iff x hsx).mpr (le_of_not_ge hx))
      have hyd := (capSphereRadialMap_bijOn_disk ha.1 ha.2).mapsTo
        ((sphereSouthChart_radius_le_one_iff y hsy).mpr (le_of_not_ge hy))
      exact sphereSouthChart_injectiveOn hsx hsy
        (capSphereRadialMap_injective ha.1 ha.2 (hCinj hxd hyd hxy))

theorem isEmbedding_sphereGraphCapFamily {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {C : PolarPoint → E3} {R L t : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hC : ContDiff ℝ ∞ C)
    (hcollar : ∀ y : PolarPoint, cartesianRadius y = 1 →
      (C ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
        fun z => graphMap id (fun _ => A.cRight) ((R / cartesianRadius z ^ 2) • z))
    (hCinj : Set.InjOn C {y : PolarPoint | cartesianRadius y ≤ 1})
    (hboundary : ∀ u : PolarPoint, cartesianRadius u = 1 →
      C u = graphMap id (fun _ => A.cRight) (R • u))
    (hmeet : graphPhaseDiskImage D R t ∩ (C '' {y : PolarPoint | cartesianRadius y ≤ 1}) ⊆
      capAttachingRim R A.cRight) :
    Topology.IsEmbedding (fun x : SpherePoint => sphereGraphCapFamily D C R L (x, t)) := by
  have hc : Continuous (fun x : SpherePoint => sphereGraphCapFamily D C R L (x, t)) :=
    (contMDiff_sphereGraphCapFamily D hR hC hcollar).continuous.comp
      (continuous_id.prodMk continuous_const)
  exact (hc.isClosedEmbedding
    (sphereGraphCapFamily_injective D hR hL hCinj hboundary hmeet)).isEmbedding

theorem markedCap_boundary {R L ρ k : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ)
    {y : PolarPoint} (hy : cartesianRadius y = 1) :
    markedCapMap R h L k ρ y = graphMap id (fun _ => h) (R • y) := by
  have hb : cartesianRadius (capDiskBase R L y) = R := by
    rw [capDiskBase_radius hR hL hy.le]
    simp [capDiskParameter, hy, capMeridianRadius]
  rw [markedCapMap_eq_capDiskMap_of_inner hR hL hρ hsmall h (by rw [hb]; linarith)]
  exact capDisk_boundary R h L hy

theorem IsometricGraphDevelopment.marked_cap_meeting_subset {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L ρ k t : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hold : graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) :
    graphPhaseDiskImage D R t ∩
      (markedCapMap R A.cRight L k ρ '' {y : PolarPoint | cartesianRadius y ≤ 1}) ⊆
        capAttachingRim R A.cRight := by
  rintro v ⟨⟨x, hx, hxv⟩, ⟨y, hy, hyv⟩⟩
  have he : markedCapMap R A.cRight L k ρ y = D.rotationFamily t x := hyv.trans hxv.symm
  have hb := congrArg graphBaseProjection he
  simp only [markedCapMap_base] at hb
  have hrad : cartesianRadius (capDiskBase R L y) ≤ R := by
    rw [hb]
    exact D.phase_disk_projection_bound t hR.le hx
  have hsame := markedCapMap_eq_capDiskMap_of_inner (A.b_pos.trans hR) hL hρ hsmall
    A.cRight (k := k) (by linarith : cartesianRadius (capDiskBase R L y) ≤ R + L / 16)
  have hv : v ∈ graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L :=
    ⟨⟨x, hx, hxv⟩, ⟨⟨y, hy⟩, hsame.symm.trans hyv⟩⟩
  rwa [hold] at hv

/-- One actual cap length supplies smooth, topologically embedded marked spheres.
The differential assertion is proved below; the metric is a separate obligation. -/
theorem IsometricGraphDevelopment.exists_markedSphereFamily {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b < R) :
    ∃ L : ℝ, 0 < L ∧ ∀ k ρ : ℝ, 0 ≤ k → 0 < ρ → ρ < L / 64 →
      ContMDiff SphereTimeModel 𝓘(ℝ, E3) ∞
        (sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L) ∧
      ∀ t : ℝ, Topology.IsEmbedding (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t)) := by
  obtain ⟨L, hL, hmeet, _⟩ := D.exists_fixed_cap_attachment hR
  refine ⟨L, hL, ?_⟩
  intro k ρ hk hρ hsmall
  refine ⟨D.contMDiff_markedSphereFamily hR hL hρ hsmall, ?_⟩
  intro t
  exact isEmbedding_sphereGraphCapFamily D hR hL
    (contDiff_markedCapMap (A.b_pos.trans hR) hL A.cRight k ρ)
    (fun _ hy => markedCapMap_capSphereRadialMap_rim_germ
      (A.b_pos.trans hR) hL hρ hsmall A.cRight hy)
    (markedCapMap_injOn (A.b_pos.trans hR) hL hk hρ hsmall A.cRight)
    (fun _ hy => markedCap_boundary (A.b_pos.trans hR) hL hρ hsmall A.cRight hy)
    (D.marked_cap_meeting_subset hR hL hρ hsmall (hmeet t))

theorem sphereGraphCapFamily_north_germ {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {C : PolarPoint → E3} {R L : ℝ}
    (hR : A.b < R)
    (hcollar : ∀ y : PolarPoint, cartesianRadius y = 1 →
      (C ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
        fun z => graphMap id (fun _ => A.cRight) ((R / cartesianRadius z ^ 2) • z))
    (q : SpherePoint × ℝ) (hq : 0 ≤ (q.1 : E3) 2) :
    sphereGraphCapFamily D C R L =ᶠ[𝓝 q] sphereNorthFamily D R := by
  by_cases hp : 0 < (q.1 : E3) 2
  · have hc : Continuous (fun p : SpherePoint × ℝ => (p.1 : E3) 2) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp
        (continuous_subtype_val.comp continuous_fst)
    filter_upwards [continuousAt_const.eventually_lt hc.continuousAt hp] with p hpp
    simp only [sphereGraphCapFamily, hpp.le, ↓reduceIte]
  · have hz : (q.1 : E3) 2 = 0 := le_antisymm (le_of_not_gt hp) hq
    filter_upwards [sphereGraphCap_equator_germ D hR hcollar q hz] with p he
    change (if 0 ≤ (p.1 : E3) 2 then _ else _) = _
    split_ifs
    · rfl
    · exact he

theorem sphereGraphCapFamily_south_germ {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (C : PolarPoint → E3) (R L : ℝ)
    (q : SpherePoint × ℝ) (hq : (q.1 : E3) 2 < 0) :
    sphereGraphCapFamily D C R L =ᶠ[𝓝 q]
      fun p : SpherePoint × ℝ => sphereSouthCap C R L p.1 := by
  have hc : Continuous (fun p : SpherePoint × ℝ => (p.1 : E3) 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp
      (continuous_subtype_val.comp continuous_fst)
  filter_upwards [hc.continuousAt.eventually_lt continuousAt_const hq] with p hp
  simp only [sphereGraphCapFamily, not_le.mpr hp, ↓reduceIte]

theorem mdifferentiable_sphereNorthCoordinates :
    sphereNorthCoordinates.MDifferentiable (𝓡 2) 𝓘(ℝ, PolarPoint) := by
  constructor
  · intro x hx
    exact ((contMDiffAt_sphereNorthChart x hx).mdifferentiableAt (by simp)).mdifferentiableWithinAt
  · intro u _
    exact ((contMDiff_sphereNorthInverse u).mdifferentiableAt (by simp)).mdifferentiableWithinAt

theorem mdifferentiable_sphereSouthCoordinates :
    sphereSouthCoordinates.MDifferentiable (𝓡 2) 𝓘(ℝ, PolarPoint) := by
  constructor
  · intro x hx
    exact ((contMDiffAt_sphereSouthChart x hx).mdifferentiableAt (by simp)).mdifferentiableWithinAt
  · intro u _
    exact ((contMDiff_sphereSouthInverse u).mdifferentiableAt (by simp)).mdifferentiableWithinAt

theorem mfderiv_sphereNorthChart_bijective (x : SpherePoint) (hx : x ∈ sphereNorthSource) :
    Function.Bijective (mfderiv (𝓡 2) 𝓘(ℝ, PolarPoint) sphereNorthChart x) :=
  mdifferentiable_sphereNorthCoordinates.mfderiv_bijective hx

theorem mfderiv_sphereSouthChart_bijective (x : SpherePoint) (hx : x ∈ sphereSouthSource) :
    Function.Bijective (mfderiv (𝓡 2) 𝓘(ℝ, PolarPoint) sphereSouthChart x) :=
  mdifferentiable_sphereSouthCoordinates.mfderiv_bijective hx

private theorem sphere_comp_mfderiv_injective {φ : SpherePoint → PolarPoint}
    {F : PolarPoint → E3} (x : SpherePoint)
    (hφ : MDifferentiableAt (𝓡 2) 𝓘(ℝ, PolarPoint) φ x)
    (hφi : Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, PolarPoint) φ x))
    (hF : DifferentiableAt ℝ F (φ x))
    (hFi : Function.Injective (fderiv ℝ F (φ x))) :
    Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) (F ∘ φ) x) := by
  rw [mfderiv_comp x hF.mdifferentiableAt hφ, mfderiv_eq_fderiv]
  exact ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (F (φ x))).symm.injective.comp
    (hFi.comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) (φ x)).injective)).comp hφi

/-- Actual injectivity of the manifold differential, including at the equator.
This is not an assertion of the stronger library normal-form `IsImmersion`. -/
theorem sphereGraphCapFamily_mfderiv_injective {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {C : PolarPoint → E3} {R L : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hC : ContDiff ℝ ∞ C)
    (hCi : ∀ y : PolarPoint, cartesianRadius y ≤ 1 → Function.Injective (fderiv ℝ C y))
    (hcollar : ∀ y : PolarPoint, cartesianRadius y = 1 →
      (C ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
        fun z => graphMap id (fun _ => A.cRight) ((R / cartesianRadius z ^ 2) • z))
    (t : ℝ) (x : SpherePoint) :
    Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3)
      (fun y : SpherePoint => sphereGraphCapFamily D C R L (y, t)) x) := by
  have hRp := A.b_pos.trans hR
  have ha := capSphereRatio_mem hRp hL
  have hslice : Tendsto (fun y : SpherePoint => (y, t)) (𝓝 x) (𝓝 (x, t)) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  by_cases hx : 0 ≤ (x : E3) 2
  · have hnx : x ∈ sphereNorthSource := by change (x : E3) 2 ≠ -1; linarith
    let F : PolarPoint → E3 := fun u => D.rotationFamily t (R • u)
    have hs (u : PolarPoint) : HasFDerivAt (fun v : PolarPoint => R • v)
        (R • ContinuousLinearMap.id ℝ PolarPoint) u := (hasFDerivAt_id u).const_smul R
    have hFD (u : PolarPoint) :=
      ((D.rotationFamily_smooth t).differentiable (by simp) (R • u)).hasFDerivAt.comp u (hs u)
    have hFi : Function.Injective (fderiv ℝ F (sphereNorthChart x)) := by
      change Function.Injective (fderiv ℝ
        (D.rotationFamily t ∘ (fun u : PolarPoint => R • u)) (sphereNorthChart x))
      rw [(hFD (sphereNorthChart x)).fderiv]
      apply (D.rotationFamily_immersion t _).comp
      intro u v huv
      change R • u = R • v at huv
      have hh := congrArg (fun z : PolarPoint => R⁻¹ • z) huv
      simpa only [smul_smul, inv_mul_cancel₀ hRp.ne', one_smul] using hh
    have hi := sphere_comp_mfderiv_injective x
      ((contMDiffAt_sphereNorthChart x hnx).mdifferentiableAt (by simp))
      (mfderiv_sphereNorthChart_bijective x hnx).injective
      (hFD (sphereNorthChart x)).differentiableAt hFi
    have he : (fun y : SpherePoint => sphereGraphCapFamily D C R L (y, t)) =ᶠ[𝓝 x]
        (F ∘ sphereNorthChart) := by
      simpa only [Function.comp_def, sphereNorthFamily, F] using
        (sphereGraphCapFamily_north_germ D hR hcollar (x, t) hx).comp_tendsto hslice
    rw [he.mfderiv_eq (I := 𝓡 2) (I' := 𝓘(ℝ, E3))]
    exact (tangentSpaceCast 𝓘(ℝ, E3) _ _).injective.comp hi
  · have hsx : x ∈ sphereSouthSource := by change (x : E3) 2 ≠ 1; linarith
    let P : PolarPoint → PolarPoint := capSphereRadialMap (capSphereRatio R L)
    let F : PolarPoint → E3 := C ∘ P
    have hp : DifferentiableAt ℝ P (sphereSouthChart x) :=
      (contDiff_capSphereRadialMap _).differentiable (by simp) _
    have hcp : DifferentiableAt ℝ C (P (sphereSouthChart x)) := hC.differentiable (by simp) _
    have hdom : cartesianRadius (P (sphereSouthChart x)) ≤ 1 :=
      (capSphereRadialMap_bijOn_disk ha.1 ha.2).mapsTo
        ((sphereSouthChart_radius_le_one_iff x hsx).mpr (le_of_not_ge hx))
    have hFi : Function.Injective (fderiv ℝ F (sphereSouthChart x)) := by
      rw [fderiv_comp _ hcp hp]
      exact (hCi _ hdom).comp (capSphereRadialMap_fderiv_injective ha.1 ha.2 _)
    have hi := sphere_comp_mfderiv_injective x
      ((contMDiffAt_sphereSouthChart x hsx).mdifferentiableAt (by simp))
      (mfderiv_sphereSouthChart_bijective x hsx).injective (hcp.comp _ hp) hFi
    have he : (fun y : SpherePoint => sphereGraphCapFamily D C R L (y, t)) =ᶠ[𝓝 x]
        (F ∘ sphereSouthChart) := by
      simpa only [Function.comp_def, sphereSouthCap, F, P] using
        (sphereGraphCapFamily_south_germ D C R L (x, t) (lt_of_not_ge hx)).comp_tendsto hslice
    rw [he.mfderiv_eq (I := 𝓡 2) (I' := 𝓘(ℝ, E3))]
    exact (tangentSpaceCast 𝓘(ℝ, E3) _ _).injective.comp hi

theorem IsometricGraphDevelopment.markedSphereFamily_mfderiv_injective {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) (x : SpherePoint) :
    Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) (fun y : SpherePoint =>
      sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (y, t)) x) :=
  sphereGraphCapFamily_mfderiv_injective D hR hL
    (contDiff_markedCapMap (A.b_pos.trans hR) hL A.cRight k ρ)
    (fun _ hy => markedCapMap_fderiv_injective (A.b_pos.trans hR) hL hk hρ hsmall A.cRight hy)
    (fun _ hy => markedCapMap_capSphereRadialMap_rim_germ
      (A.b_pos.trans hR) hL hρ hsmall A.cRight hy) t x

theorem IsometricGraphDevelopment.exists_markedSphereFamily_regular {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b < R) :
    ∃ L : ℝ, 0 < L ∧ ∀ k ρ : ℝ, 0 ≤ k → 0 < ρ → ρ < L / 64 →
      ContMDiff SphereTimeModel 𝓘(ℝ, E3) ∞
        (sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L) ∧
      ∀ t : ℝ, Topology.IsEmbedding (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t)) ∧
        ∀ x : SpherePoint, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3)
          (fun y : SpherePoint => sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ)
            R L (y, t)) x) := by
  obtain ⟨L, hL, hfamily⟩ := D.exists_markedSphereFamily hR
  refine ⟨L, hL, ?_⟩
  intro k ρ hk hρ hsmall
  obtain ⟨hsm, hem⟩ := hfamily k ρ hk hρ hsmall
  exact ⟨hsm, fun t => ⟨hem t, D.markedSphereFamily_mfderiv_injective hR hL hk hρ hsmall t⟩⟩

end ContinuousFlexibility
