import ContinuousFlexibility.Analysis.N06CurrentTestTraces
import ContinuousFlexibility.Analysis.N06CanonicalTestTransport
import ContinuousFlexibility.Analysis.N06WeakCylinderPDE

/-!
# True traces of transported compact canonical tests

A compact canonical test is transported by the actual current chart and
height. Its transformed value and first radial jet agree with the original
canonical test throughout the closed measured rectangle, by continuity
from the open rectangle. Thus both true endpoint traces vanish, without
using the totalized inverse chart at a boundary.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- The radial-coefficient expression depends only on the true input
germ, including both derivatives in its weighted radial flux. -/
theorem n06UnitReferenceTestOperator_input_congr_germ
    (a c V : ℝ → ℝ) {f g : PolarPoint → ℝ} {p : PolarPoint}
    (hfg : f =ᶠ[𝓝 p] g) :
    n06UnitReferenceTestOperator a c V f p =
      n06UnitReferenceTestOperator a c V g p := by
  have hr : radialPartial f =ᶠ[𝓝 p] radialPartial g := by
    filter_upwards [hfg.fderiv (𝕜 := ℝ)] with q hq
    exact congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0)) hq
  have ht : angularPartial f =ᶠ[𝓝 p] angularPartial g := by
    filter_upwards [hfg.fderiv (𝕜 := ℝ)] with q hq
    exact congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1)) hq
  have hflux : (fun q => a q.1 * radialPartial f q) =ᶠ[𝓝 p]
      (fun q => a q.1 * radialPartial g q) := by
    filter_upwards [hr] with q hq
    rw [hq]
  have hrr : radialPartial (fun q => a q.1 * radialPartial f q) p =
      radialPartial (fun q => a q.1 * radialPartial g q) p :=
    congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0)) (hflux.fderiv_eq (𝕜 := ℝ))
  have htt : angularPartial (angularPartial f) p = angularPartial (angularPartial g) p :=
    congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1)) (ht.fderiv_eq (𝕜 := ℝ))
  simp only [n06UnitReferenceTestOperator, hrr, htt, hfg.eq_of_nhds]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss m : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {φ : PolarPoint → ℝ}

/-- Compact support strictly inside the radial interval kills the true
value and first radial derivative at every point outside that interval. -/
theorem CanonicalTest.n06_value_radial_zero_of_not_mem
    (hφ : CanonicalTest S K m φ) {r : ℝ}
    (hr : r ∉ Ioo (K.left m) (K.right m)) (θ : ℝ) :
    φ (r, θ) = 0 ∧ radialPartial φ (r, θ) = 0 := by
  obtain ⟨J, hJ, hJK, hzero⟩ := hφ.2.2
  have hrJ : r ∉ J := fun h => hr (hJK h)
  have hg : φ =ᶠ[𝓝 (r, θ)] (fun _ => (0 : ℝ)) := by
    filter_upwards [(continuous_fst.tendsto (r, θ)).eventually
      (hJ.isClosed.isOpen_compl.mem_nhds hrJ)] with q hq
    exact hzero q.1 hq q.2
  refine ⟨hzero r hrJ θ, ?_⟩
  have hd := congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0))
    (hg.fderiv_eq (𝕜 := ℝ))
  exact hd.trans (radialPartial_const 0)

/-- The inverse is used only in the open domain; the height transform
of the true compact pullback has the original test germ there. -/
theorem n06CanonicalTestPullback_height_germ
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalHeight S K z m (n06CanonicalTestPullback S K z m φ) =ᶠ[𝓝 p] φ := by
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
  exact n06CanonicalTestPullback_canonicalHeight (n06_N04_qualitative_parts h04).1 hz hs hq

/-- Both true continuous trace functions of a transported compact test
agree with the corresponding original canonical functions on the closed
rectangle. No endpoint inverse value is evaluated. -/
theorem N06CurrentHeightTestTraces.compactPullback_closed
    (Q : N06CurrentHeightTestTraces S K z m (n06CanonicalTestPullback S K z m φ))
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) :
    EqOn Q.value φ (Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi) ∧
      EqOn Q.radial (radialPartial φ)
        (Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi) := by
  let O : Set PolarPoint := Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi
  let F : Set PolarPoint := Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi
  have hsub : O ⊆ F := fun _ hp => ⟨mem_Icc_of_Ioo hp.1, hp.2.1.le, hp.2.2⟩
  have hcl : F ⊆ closure O := by
    simpa only [O, F, closure_prod_eq, closure_Ioo (h04.1.referenceBounds m).2.1.ne,
      closure_Ioc Real.pi_pos.ne] using (Subset.rfl : F ⊆ F)
  have hval : EqOn Q.value φ O := by
    intro p hp
    exact (Q.value_eq hp).trans
      (n06CanonicalTestPullback_height_germ h04 hz hs ⟨hp.1, mem_univ _⟩).eq_of_nhds
  have hrad : EqOn Q.radial (radialPartial φ) O := by
    intro p hp
    refine (Q.radial_eq hp).trans ?_
    exact congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0))
      ((n06CanonicalTestPullback_height_germ h04 hz hs
        ⟨hp.1, mem_univ _⟩).fderiv_eq (𝕜 := ℝ))
  exact ⟨hval.of_subset_closure Q.value_lipschitz.continuous.continuousOn
      hφ.1.continuous.continuousOn hsub hcl,
    hrad.of_subset_closure Q.radial_lipschitz.continuous.continuousOn
      (contDiff_cylinder_radialPartial hφ.1).continuous.continuousOn hsub hcl⟩

end ContinuousFlexibility.Statements
