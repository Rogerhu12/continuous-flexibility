import ContinuousFlexibility.Geometry.GraphEmbedding
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Explicit Cartesian stereographic coordinates on the standard sphere

The domain is the existing mathlib unit sphere in actual Euclidean E3.
These charts use half the library's stereographic scale, so the equator
has planar radius one. Their manifold compatibility is proved separately
from the coordinate algebra; no replacement smooth sphere is introduced.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Metric
open scoped ContDiff Manifold

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}

set_option backward.isDefEq.respectTransparency false

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

def spherePlaneEnergy (u : PolarPoint) : ℝ := u.1 ^ 2 + u.2 ^ 2

def sphereStereoDenom (u : PolarPoint) : ℝ := 1 + spherePlaneEnergy u

theorem sphereStereoDenom_pos (u : PolarPoint) : 0 < sphereStereoDenom u := by
  unfold sphereStereoDenom spherePlaneEnergy
  positivity

theorem e3_mem_unit_sphere_iff (v : E3) :
    v ∈ Metric.sphere (0 : E3) 1 ↔ v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  constructor
  · intro hn
    have hi : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
    rw [e3_inner_coordinates] at hi
    simpa only [pow_two] using hi
  · intro hc
    have hs : ‖v‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, e3_inner_coordinates]
      simpa only [pow_two] using hc
    nlinarith [norm_nonneg v]

theorem spherePoint_coordinate_sq (x : SpherePoint) :
    (x : E3) 0 ^ 2 + (x : E3) 1 ^ 2 + (x : E3) 2 ^ 2 = 1 :=
  (e3_mem_unit_sphere_iff (x : E3)).mp x.property

theorem spherePoint_vertical_bounds (x : SpherePoint) :
    -1 ≤ (x : E3) 2 ∧ (x : E3) 2 ≤ 1 := by
  have hc := spherePoint_coordinate_sq x
  constructor <;> nlinarith [sq_nonneg ((x : E3) 0), sq_nonneg ((x : E3) 1)]

theorem spherePlaneEnergy_eq_radius_sq (u : PolarPoint) :
    spherePlaneEnergy u = cartesianRadius u ^ 2 := by
  simp [spherePlaneEnergy, cartesianRadius, Complex.sq_norm, Complex.normSq_apply,
    Complex.equivRealProdCLM_symm_apply]
  ring

def sphereNorthChart (x : SpherePoint) : PolarPoint :=
  ((x : E3) 0 / (1 + (x : E3) 2), (x : E3) 1 / (1 + (x : E3) 2))

def sphereSouthChart (x : SpherePoint) : PolarPoint :=
  ((x : E3) 0 / (1 - (x : E3) 2), (x : E3) 1 / (1 - (x : E3) 2))

def sphereNorthSource : Set SpherePoint := {x | (x : E3) 2 ≠ -1}

def sphereSouthSource : Set SpherePoint := {x | (x : E3) 2 ≠ 1}

theorem sphere_chart_sources_cover : sphereNorthSource ∪ sphereSouthSource = Set.univ := by
  ext x
  simp only [sphereNorthSource, sphereSouthSource, mem_union, mem_ofPred_eq, mem_univ, iff_true]
  by_cases hn : (x : E3) 2 = -1
  · right
    rw [hn]
    norm_num
  · exact Or.inl hn

def sphereNorthInvVector (u : PolarPoint) : E3 :=
  graphMap (fun v => (2 * v.1 / sphereStereoDenom v, 2 * v.2 / sphereStereoDenom v))
    (fun v => (1 - spherePlaneEnergy v) / sphereStereoDenom v) u

def sphereSouthInvVector (u : PolarPoint) : E3 :=
  graphMap (fun v => (2 * v.1 / sphereStereoDenom v, 2 * v.2 / sphereStereoDenom v))
    (fun v => (spherePlaneEnergy v - 1) / sphereStereoDenom v) u

theorem sphereNorthInvVector_mem (u : PolarPoint) :
    sphereNorthInvVector u ∈ Metric.sphere (0 : E3) 1 := by
  apply (e3_mem_unit_sphere_iff _).mpr
  simp only [sphereNorthInvVector, graphMap_zero, graphMap_one, graphMap_two]
  field_simp [(sphereStereoDenom_pos u).ne']
  dsimp [sphereStereoDenom, spherePlaneEnergy]
  ring

theorem sphereSouthInvVector_mem (u : PolarPoint) :
    sphereSouthInvVector u ∈ Metric.sphere (0 : E3) 1 := by
  apply (e3_mem_unit_sphere_iff _).mpr
  simp only [sphereSouthInvVector, graphMap_zero, graphMap_one, graphMap_two]
  field_simp [(sphereStereoDenom_pos u).ne']
  dsimp [sphereStereoDenom, spherePlaneEnergy]
  ring

def sphereNorthInverse (u : PolarPoint) : SpherePoint :=
  ⟨sphereNorthInvVector u, sphereNorthInvVector_mem u⟩

def sphereSouthInverse (u : PolarPoint) : SpherePoint :=
  ⟨sphereSouthInvVector u, sphereSouthInvVector_mem u⟩

theorem sphereNorthChart_energy (x : SpherePoint) (hx : x ∈ sphereNorthSource) :
    spherePlaneEnergy (sphereNorthChart x) = (1 - (x : E3) 2) / (1 + (x : E3) 2) := by
  have hd : 1 + (x : E3) 2 ≠ 0 := by
    change (x : E3) 2 ≠ -1 at hx
    intro h
    exact hx (by linarith)
  have hc := spherePoint_coordinate_sq x
  unfold spherePlaneEnergy sphereNorthChart
  dsimp only
  field_simp [hd]
  nlinarith

theorem sphereSouthChart_energy (x : SpherePoint) (hx : x ∈ sphereSouthSource) :
    spherePlaneEnergy (sphereSouthChart x) = (1 + (x : E3) 2) / (1 - (x : E3) 2) := by
  have hd : 1 - (x : E3) 2 ≠ 0 := by
    change (x : E3) 2 ≠ 1 at hx
    intro h
    exact hx (by linarith)
  have hc := spherePoint_coordinate_sq x
  unfold spherePlaneEnergy sphereSouthChart
  dsimp only
  field_simp [hd]
  nlinarith

theorem sphereNorthChart_inverse (u : PolarPoint) :
    sphereNorthChart (sphereNorthInverse u) = u := by
  have hd := (sphereStereoDenom_pos u).ne'
  apply Prod.ext
  all_goals
    simp only [sphereNorthChart, sphereNorthInverse, sphereNorthInvVector,
      graphMap_zero, graphMap_one, graphMap_two]
    field_simp [hd]
    dsimp [sphereStereoDenom, spherePlaneEnergy]
    ring

theorem sphereSouthChart_inverse (u : PolarPoint) :
    sphereSouthChart (sphereSouthInverse u) = u := by
  have hd := (sphereStereoDenom_pos u).ne'
  apply Prod.ext
  all_goals
    simp only [sphereSouthChart, sphereSouthInverse, sphereSouthInvVector,
      graphMap_zero, graphMap_one, graphMap_two]
    field_simp [hd]
    dsimp [sphereStereoDenom, spherePlaneEnergy]
    ring

theorem sphereNorthInverse_source (u : PolarPoint) :
    sphereNorthInverse u ∈ sphereNorthSource := by
  simp only [sphereNorthSource, mem_ofPred_eq, sphereNorthInverse,
    sphereNorthInvVector, graphMap_two]
  intro he
  have he' := (div_eq_iff (sphereStereoDenom_pos u).ne').mp he
  dsimp [sphereStereoDenom] at he'
  linarith

theorem sphereSouthInverse_source (u : PolarPoint) :
    sphereSouthInverse u ∈ sphereSouthSource := by
  simp only [sphereSouthSource, mem_ofPred_eq, sphereSouthInverse,
    sphereSouthInvVector, graphMap_two]
  intro he
  have he' := (div_eq_iff (sphereStereoDenom_pos u).ne').mp he
  dsimp [sphereStereoDenom] at he'
  linarith

theorem sphereNorthInverse_chart (x : SpherePoint) (hx : x ∈ sphereNorthSource) :
    sphereNorthInverse (sphereNorthChart x) = x := by
  have hd : 1 + (x : E3) 2 ≠ 0 := by
    change (x : E3) 2 ≠ -1 at hx
    intro h
    exact hx (by linarith)
  have he := sphereNorthChart_energy x hx
  have hden : sphereStereoDenom (sphereNorthChart x) = 2 / (1 + (x : E3) 2) := by
    rw [sphereStereoDenom, he]
    field_simp
    ring
  apply Subtype.ext
  ext i
  fin_cases i
  · change sphereNorthInvVector (sphereNorthChart x) 0 = (x : E3) 0
    simp only [sphereNorthInvVector, graphMap_zero]
    rw [hden]
    simp only [sphereNorthChart]
    field_simp
  · change sphereNorthInvVector (sphereNorthChart x) 1 = (x : E3) 1
    simp only [sphereNorthInvVector, graphMap_one]
    rw [hden]
    simp only [sphereNorthChart]
    field_simp
  · change sphereNorthInvVector (sphereNorthChart x) 2 = (x : E3) 2
    simp only [sphereNorthInvVector, graphMap_two, hden, he]
    field_simp
    ring

theorem sphereSouthInverse_chart (x : SpherePoint) (hx : x ∈ sphereSouthSource) :
    sphereSouthInverse (sphereSouthChart x) = x := by
  have hd : 1 - (x : E3) 2 ≠ 0 := by
    change (x : E3) 2 ≠ 1 at hx
    intro h
    exact hx (by linarith)
  have he := sphereSouthChart_energy x hx
  have hden : sphereStereoDenom (sphereSouthChart x) = 2 / (1 - (x : E3) 2) := by
    rw [sphereStereoDenom, he]
    field_simp
    ring
  apply Subtype.ext
  ext i
  fin_cases i
  · change sphereSouthInvVector (sphereSouthChart x) 0 = (x : E3) 0
    simp only [sphereSouthInvVector, graphMap_zero]
    rw [hden]
    simp only [sphereSouthChart]
    field_simp
  · change sphereSouthInvVector (sphereSouthChart x) 1 = (x : E3) 1
    simp only [sphereSouthInvVector, graphMap_one]
    rw [hden]
    simp only [sphereSouthChart]
    field_simp
  · change sphereSouthInvVector (sphereSouthChart x) 2 = (x : E3) 2
    simp only [sphereSouthInvVector, graphMap_two, hden, he]
    field_simp
    ring

theorem sphereNorthChart_injectiveOn : Set.InjOn sphereNorthChart sphereNorthSource := by
  intro x hx y hy hxy
  rw [← sphereNorthInverse_chart x hx, ← sphereNorthInverse_chart y hy, hxy]

theorem sphereSouthChart_injectiveOn : Set.InjOn sphereSouthChart sphereSouthSource := by
  intro x hx y hy hxy
  rw [← sphereSouthInverse_chart x hx, ← sphereSouthInverse_chart y hy, hxy]

private theorem sphere_coordinate_contMDiff (i : Fin 3) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x : SpherePoint => (x : E3) i) := by
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contMDiff.comp
    (contMDiff_coe_sphere (E := E3) (n := 2) (m := ∞))

theorem contMDiffAt_sphereNorthChart (x : SpherePoint) (hx : x ∈ sphereNorthSource) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, PolarPoint) ∞ sphereNorthChart x := by
  have hd : ContDiffAt ℝ ∞ (fun z : E3 => 1 + z 2) (x : E3) :=
    contDiffAt_const.add (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff.contDiffAt
  have hn : 1 + (x : E3) 2 ≠ 0 := by
    change (x : E3) 2 ≠ -1 at hx
    intro h
    exact hx (by linarith)
  have hf := ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff.contDiffAt.div hd hn).prodMk
    ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff.contDiffAt.div hd hn)
  exact hf.contMDiffAt.comp x (contMDiff_coe_sphere (E := E3) (n := 2) (m := ∞) x)

theorem contMDiffAt_sphereSouthChart (x : SpherePoint) (hx : x ∈ sphereSouthSource) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, PolarPoint) ∞ sphereSouthChart x := by
  have hd : ContDiffAt ℝ ∞ (fun z : E3 => 1 - z 2) (x : E3) :=
    contDiffAt_const.sub (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff.contDiffAt
  have hn : 1 - (x : E3) 2 ≠ 0 := by
    change (x : E3) 2 ≠ 1 at hx
    intro h
    exact hx (by linarith)
  have hf := ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff.contDiffAt.div hd hn).prodMk
    ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff.contDiffAt.div hd hn)
  exact hf.contMDiffAt.comp x (contMDiff_coe_sphere (E := E3) (n := 2) (m := ∞) x)

theorem isOpen_sphereNorthSource : IsOpen sphereNorthSource :=
  isOpen_ne_fun (sphere_coordinate_contMDiff 2).continuous continuous_const

theorem isOpen_sphereSouthSource : IsOpen sphereSouthSource :=
  isOpen_ne_fun (sphere_coordinate_contMDiff 2).continuous continuous_const

theorem contDiff_spherePlaneEnergy : ContDiff ℝ ∞ spherePlaneEnergy :=
  (contDiff_fst.pow 2).add (contDiff_snd.pow 2)

theorem contDiff_sphereStereoDenom : ContDiff ℝ ∞ sphereStereoDenom :=
  contDiff_const.add contDiff_spherePlaneEnergy

theorem contDiff_sphereNorthInvVector : ContDiff ℝ ∞ sphereNorthInvVector := by
  apply contDiff_graphMap
  · exact ((contDiff_const.mul contDiff_fst).div contDiff_sphereStereoDenom
      (fun u => (sphereStereoDenom_pos u).ne')).prodMk
        ((contDiff_const.mul contDiff_snd).div contDiff_sphereStereoDenom
          (fun u => (sphereStereoDenom_pos u).ne'))
  · exact (contDiff_const.sub contDiff_spherePlaneEnergy).div contDiff_sphereStereoDenom
      (fun u => (sphereStereoDenom_pos u).ne')

theorem contDiff_sphereSouthInvVector : ContDiff ℝ ∞ sphereSouthInvVector := by
  apply contDiff_graphMap
  · exact ((contDiff_const.mul contDiff_fst).div contDiff_sphereStereoDenom
      (fun u => (sphereStereoDenom_pos u).ne')).prodMk
        ((contDiff_const.mul contDiff_snd).div contDiff_sphereStereoDenom
          (fun u => (sphereStereoDenom_pos u).ne'))
  · exact (contDiff_spherePlaneEnergy.sub contDiff_const).div contDiff_sphereStereoDenom
      (fun u => (sphereStereoDenom_pos u).ne')

theorem contMDiff_sphereNorthInverse :
    ContMDiff 𝓘(ℝ, PolarPoint) (𝓡 2) ∞ sphereNorthInverse := by
  exact contDiff_sphereNorthInvVector.contMDiff.codRestrict_sphere
    (n := 2) sphereNorthInvVector_mem

theorem contMDiff_sphereSouthInverse :
    ContMDiff 𝓘(ℝ, PolarPoint) (𝓡 2) ∞ sphereSouthInverse := by
  exact contDiff_sphereSouthInvVector.contMDiff.codRestrict_sphere
    (n := 2) sphereSouthInvVector_mem

/-- The actual overlap transition, with equatorial planar radius one. -/
theorem sphereSouthChart_eq_inversion_north (x : SpherePoint)
    (hn : x ∈ sphereNorthSource) (hs : x ∈ sphereSouthSource) :
    sphereSouthChart x = (spherePlaneEnergy (sphereNorthChart x))⁻¹ • sphereNorthChart x := by
  have hdn : 1 + (x : E3) 2 ≠ 0 := by
    change (x : E3) 2 ≠ -1 at hn
    intro h
    exact hn (by linarith)
  have hds : 1 - (x : E3) 2 ≠ 0 := by
    change (x : E3) 2 ≠ 1 at hs
    intro h
    exact hs (by linarith)
  rw [sphereNorthChart_energy x hn]
  apply Prod.ext
  all_goals
    simp only [sphereSouthChart, sphereNorthChart, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp

theorem sphereNorthChart_eq_inversion_south (x : SpherePoint)
    (hn : x ∈ sphereNorthSource) (hs : x ∈ sphereSouthSource) :
    sphereNorthChart x = (spherePlaneEnergy (sphereSouthChart x))⁻¹ • sphereSouthChart x := by
  have hdn : 1 + (x : E3) 2 ≠ 0 := by
    change (x : E3) 2 ≠ -1 at hn
    intro h
    exact hn (by linarith)
  have hds : 1 - (x : E3) 2 ≠ 0 := by
    change (x : E3) 2 ≠ 1 at hs
    intro h
    exact hs (by linarith)
  rw [sphereSouthChart_energy x hs]
  apply Prod.ext
  all_goals
    simp only [sphereSouthChart, sphereNorthChart, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp

/-- A genuine open partial homeomorphism on the standard smooth unit sphere. -/
def sphereNorthCoordinates : OpenPartialHomeomorph SpherePoint PolarPoint where
  toFun := sphereNorthChart
  invFun := sphereNorthInverse
  source := sphereNorthSource
  target := Set.univ
  map_source' := fun _ _ => Set.mem_univ _
  map_target' := fun u _ => sphereNorthInverse_source u
  left_inv' := fun x hx => sphereNorthInverse_chart x hx
  right_inv' := fun u _ => sphereNorthChart_inverse u
  open_source := isOpen_sphereNorthSource
  open_target := isOpen_univ
  continuousOn_toFun := fun x hx =>
    (contMDiffAt_sphereNorthChart x hx).continuousAt.continuousWithinAt
  continuousOn_invFun := contMDiff_sphereNorthInverse.continuous.continuousOn

def sphereSouthCoordinates : OpenPartialHomeomorph SpherePoint PolarPoint where
  toFun := sphereSouthChart
  invFun := sphereSouthInverse
  source := sphereSouthSource
  target := Set.univ
  map_source' := fun _ _ => Set.mem_univ _
  map_target' := fun u _ => sphereSouthInverse_source u
  left_inv' := fun x hx => sphereSouthInverse_chart x hx
  right_inv' := fun u _ => sphereSouthChart_inverse u
  open_source := isOpen_sphereSouthSource
  open_target := isOpen_univ
  continuousOn_toFun := fun x hx =>
    (contMDiffAt_sphereSouthChart x hx).continuousAt.continuousWithinAt
  continuousOn_invFun := contMDiff_sphereSouthInverse.continuous.continuousOn

theorem sphereNorthChart_radius_le_one_iff (x : SpherePoint) (hx : x ∈ sphereNorthSource) :
    cartesianRadius (sphereNorthChart x) ≤ 1 ↔ 0 ≤ (x : E3) 2 := by
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
    have hsq : cartesianRadius (sphereNorthChart x) ^ 2 ≤ 1 := by nlinarith
    rw [hs] at hsq
    have he := (div_le_iff₀ hden).mp hsq
    linarith
  · intro h
    have he : (1 - (x : E3) 2) / (1 + (x : E3) 2) ≤ 1 :=
      (div_le_iff₀ hden).mpr (by linarith)
    rw [← hs] at he
    nlinarith

theorem sphereSouthChart_radius_le_one_iff (x : SpherePoint) (hx : x ∈ sphereSouthSource) :
    cartesianRadius (sphereSouthChart x) ≤ 1 ↔ (x : E3) 2 ≤ 0 := by
  have hden : 0 < 1 - (x : E3) 2 := by
    have hb := (spherePoint_vertical_bounds x).2
    change (x : E3) 2 ≠ 1 at hx
    have hs := lt_of_le_of_ne hb hx
    linarith
  have hs := sphereSouthChart_energy x hx
  rw [spherePlaneEnergy_eq_radius_sq] at hs
  have hr : 0 ≤ cartesianRadius (sphereSouthChart x) := norm_nonneg _
  constructor
  · intro h
    have hsq : cartesianRadius (sphereSouthChart x) ^ 2 ≤ 1 := by nlinarith
    rw [hs] at hsq
    have he := (div_le_iff₀ hden).mp hsq
    linarith
  · intro h
    have he : (1 + (x : E3) 2) / (1 - (x : E3) 2) ≤ 1 :=
      (div_le_iff₀ hden).mpr (by linarith)
    rw [← hs] at he
    nlinarith

end ContinuousFlexibility
