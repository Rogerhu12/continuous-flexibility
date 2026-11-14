module

public import ContinuousFlexibility.Analysis.N06CanonicalTestTransport
public import ContinuousFlexibility.Analysis.N05ReferenceTests
public import ContinuousFlexibility.Radial.MatchingCutoffTests

/-!
# Compact realizations of the actual canonical height germ

A cutoff in the canonical radial coordinate has a genuine smooth physical
zero extension on the moving physical piece. Its compact support and
symmetries put it in the original physical height model. One such field
agrees with the actual height near every point of the selected canonical
radial fiber, including its periodic translates and reflections.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- One original HeightPair realizes the actual height simultaneously on
a canonical radial fiber. The physical piece need not be a radial strip. -/
theorem n06_exists_heightPair_canonicalHeight_germ
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hA : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K z m) :
    ∃ η : HeightPair S, ∀ q ∈ physicalPieceOpen S K z m,
      (K.chart z m q).1 = (K.chart z m p).1 →
      heightPairField S η =ᶠ[𝓝 q] K.height z m := by
  have hcharts := hA.charts z hz hs m
  have hFp := hcharts.1 hp
  obtain ⟨χ, hχ, hcompact, hsupport, hone⟩ :=
    Radial.exists_matching_cutoff hFp.1.1 hFp.1.2
  let φ : PolarPoint → ℝ := fun q => χ q.1
  have hφ : CanonicalTest S K m φ := by
    refine ⟨hχ.comp contDiff_fst, ?_, tsupport χ, hcompact, hsupport, ?_⟩
    · intro q
      simp only [φ, Prod.fst_add, add_zero]
    · intro r hr θ
      change χ r = 0
      exact image_eq_zero_of_notMem_tsupport hr
  have hφeven : ∀ r θ, φ (r, -θ) = φ (r, θ) := fun _ _ => rfl
  have hcompactPhysical :
      HasCompactRadialSupport D (n06CanonicalTestPullback S K z m φ) :=
    n06CanonicalTestPullback_radialSupport hA hz hs hφ
  obtain ⟨η, hη⟩ := n05_exists_heightPair_of_compact_test hT hS
    (n06CanonicalTestPullback_contDiff hA hz hs hφ)
    (n06CanonicalTestPullback_even hA hz hs hφeven)
    (n06CanonicalTestPullback_periodic hA hz hs hφ) hcompactPhysical
  refine ⟨η, ?_⟩
  intro q hq hradial
  have honeq : χ =ᶠ[𝓝 (K.chart z m q).1] fun _ => (1 : ℝ) := by
    rw [hradial]
    exact hone
  have hFq : ContinuousAt (fun x : PolarPoint => (K.chart z m x).1) q :=
    (hcharts.2.2.2.2.1.contDiffAt ((hA.domains z hz hs m).1.mem_nhds hq)).continuousAt.fst
  rw [hη]
  filter_upwards [n06CanonicalTestPullback_eventuallyEq_of_mem (φ := φ) hA hz hs hq,
    hFq.tendsto.eventually honeq] with x hx honeX
  change χ (K.chart z m x).1 = 1 at honeX
  change n06CanonicalTestPullback S K z m φ x = K.height z m x
  rw [hx]
  change K.height z m x * χ (K.chart z m x).1 = K.height z m x
  rw [honeX, mul_one]

end ContinuousFlexibility.Statements
