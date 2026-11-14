module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Analysis.FlatExtension

/-!
# Regularity of the actual controlled profile

Each interior neighborhood sees a finite set of control supports. The
pointwise infinite sum in the profile agrees there with a smooth finite
sum. At the two ends, flatness of the control sum supplies the remaining
regularity needed to form the smooth profile.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology BigOperators

def stateControlSum {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (x : AnnularState S) (r : ℝ) : ℝ :=
  ∑' m, stateKappa S x m * C.control m r

theorem contDiffOn_stateControlSum {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hC : controlGeometryConditions D S C)
    (x : AnnularState S) : ContDiffOn ℝ ∞ (stateControlSum C x) (Ioo D.a D.b) := by
  classical
  obtain ⟨_, _, _, _, _, hcontrol, hfinite, _⟩ := hC
  intro r hr
  have hs : IsOpen (Ioo D.a D.b) := isOpen_Ioo
  obtain ⟨t, ht, htf⟩ := hfinite ⟨r, hr⟩
  let indices := htf.toFinset
  have hn : (Subtype.val : Ioo D.a D.b → ℝ) '' t ∈ 𝓝 r :=
    hs.isOpenMap_subtype_val.image_mem_nhds ht
  have heq : stateControlSum C x =ᶠ[𝓝 r]
      (fun y => ∑ m ∈ indices, stateKappa S x m * C.control m y) := by
    filter_upwards [hn] with y hy
    obtain ⟨z, hzt, rfl⟩ := hy
    unfold stateControlSum
    apply tsum_eq_sum
    intro m hm
    have hz : C.control m z = 0 := by
      by_contra hne
      exact hm (htf.mem_toFinset.mpr ⟨z, hne, hzt⟩)
    rw [hz, mul_zero]
  have hsmooth : ContDiffAt ℝ ∞
      (fun y => ∑ m ∈ indices, stateKappa S x m * C.control m y) r :=
    ContDiffAt.sum fun m _ => contDiffAt_const.mul (hcontrol m).1.contDiffAt
  exact (hsmooth.congr_of_eventuallyEq heq).contDiffWithinAt

theorem stateControlSum_zero_off_core {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hC : controlGeometryConditions D S C)
    (x : AnnularState S) {r : ℝ} (hr : r ∉ Ioo D.a D.b) : stateControlSum C x r = 0 := by
  obtain ⟨hInterval, _, _, _, _, hcontrol, _⟩ := hC
  have hzero (m : ℕ) : C.control m r = 0 := by
    by_contra hne
    have hh := (hcontrol m).2.2 (subset_tsupport (C.control m) hne)
    exact hr ⟨(hInterval m).1.trans hh.1, hh.2.trans (hInterval m).2.2⟩
  simp only [stateControlSum, hzero, mul_zero, tsum_zero]

theorem contDiffOn_stateProfile {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hC : controlGeometryConditions D S C)
    (x : AnnularState S) : ContDiffOn ℝ ∞ (stateProfile D S C x) (Ioo D.a D.b) := by
  have hW := hD.2.2.1.1.contDiffOn (s := Ioo D.a D.b)
  have hν : ContDiff ℝ ∞ (fun _ : ℝ => x.2.1) := contDiff_const
  have he := ((hν.mul hχ).contDiffOn (s := Ioo D.a D.b)).add
    (contDiffOn_stateControlSum hC x)
  exact hW.mul he.exp

/-- The flat endpoint limits concern the actual control sum for this same
state. With those limits the nonlinear profile itself is smooth on all of
the real line. -/
theorem contDiff_stateProfile_of_flat_control_sum {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hC : controlGeometryConditions D S C) (x : AnnularState S)
    (hleft : ∀ n : ℕ, Tendsto (iteratedDeriv n (stateControlSum C x)) (𝓝[>] D.a) (𝓝 0))
    (hright : ∀ n : ℕ, Tendsto (iteratedDeriv n (stateControlSum C x)) (𝓝[<] D.b) (𝓝 0)) :
    ContDiff ℝ ∞ (stateProfile D S C x) := by
  have h := Analysis.contDiff_extendZeroOutside hD.2.1
    (contDiffOn_stateControlSum hC x) hleft hright
  have heq : Analysis.extendZeroOutside D.a D.b (stateControlSum C x) = stateControlSum C x := by
    funext r
    by_cases hr : r ∈ Ioo D.a D.b
    · exact Analysis.extendZeroOutside_of_mem hr
    · exact (Analysis.extendZeroOutside_of_notMem hr).trans
        (stateControlSum_zero_off_core hC x hr).symm
  rw [heq] at h
  have hν : ContDiff ℝ ∞ (fun _ : ℝ => x.2.1) := contDiff_const
  exact hD.2.2.1.1.mul (((hν.mul hχ).add h).exp)

end ContinuousFlexibility.Statements
