module

public import ContinuousFlexibility.Analysis.N01ActualRootGeometry
public import ContinuousFlexibility.Analysis.N01RootFieldLocalization

/-!
# Actual root strips with a cell and a state-independent positive speed

The common profile germ and the N01 numerical bounds discharge every
condition in the coefficient strip used by the fixed-loss estimates.
The selected material cell and collar precede the state. The same
positive lower bound survives the fixed radial localization everywhere.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem n01_exists_actual_root_coefficient_strip
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {r σ : ℝ} (hr : r ∈ Ioo D.a D.b) (hzero : deriv D.w r = 0)
    (hsign : σ * deriv (deriv D.w) r < 0) (hσ : σ = 1 ∨ σ = -1) :
    ∃ g : ℝ → ℝ, ∃ R : ℝ, ∃ hR : 0 < R, ∃ κ : ℝ,
      ContDiff ℝ ∞ g ∧ 0 < g 0 ∧ 0 < κ ∧
      (∀ t : ℝ, -deriv D.w (r + σ * t) = t * g t) ∧
      Ioo ((r - R) - R) ((r + R) + R) ⊆ Ioo D.a D.b ∧
      (∃ j : ℕ, Ioo (r - R) (r + R) ⊆ D.cells j) ∧
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ R) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ∀ q : PolarPoint, κ ≤ localizedRootSpeed D S C g r σ hR z q := by
  obtain ⟨_, hD⟩ := hN.1.1
  have hP : RadialPartition D := hD.2.1
  have ha : 0 < D.a := hD.1.1
  have hwpos : ∀ s ∈ Ioo D.a D.b, 0 < D.w s := hD.1.2.2.2.2.1
  obtain ⟨g, δ, hg, hg0, hδ, hdivide, hdata, hfields⟩ :=
    n01_exists_common_characteristic_root_strip hS hT hN hr hzero hsign
  obtain ⟨j, ρ, hρ, hcellρ⟩ := exists_radialCell_collar_of_partition hP hr
  let R : ℝ := min (δ / 4) (ρ / 4)
  have hR : 0 < R := lt_min (div_pos hδ (by norm_num)) (div_pos hρ (by norm_num))
  have hRδ : R ≤ δ / 4 := min_le_left _ _
  have hRρ : R ≤ ρ / 4 := min_le_right _ _
  have hphysical : Ioo ((r - R) - R) ((r + R) + R) ⊆ Ioo D.a D.b := by
    intro y hy
    apply hP.2.2.2.1 j
    apply hcellρ
    constructor <;> linarith [hy.1, hy.2]
  have hcell : Ioo (r - R) (r + R) ⊆ D.cells j := by
    intro y hy
    apply hcellρ
    constructor <;> linarith [hy.1, hy.2]
  have hprofile (x : AnnularState S) :
      EqOn (stateProfile D S C x) D.w (Ioo (r - δ) (r + δ)) := by
    intro y hy
    rcases hσ with hσ | hσ
    · have ht : y - r ∈ Ioo (-δ) δ := by
        constructor <;> linarith [hy.1, hy.2]
      have he : r + σ * (y - r) = y := by rw [hσ]; ring
      simpa only [he] using (hdata (y - r) ht).2.2 x
    · have ht : r - y ∈ Ioo (-δ) δ := by
        constructor <;> linarith [hy.1, hy.2]
      have he : r + σ * (r - y) = y := by rw [hσ]; ring
      simpa only [he] using (hdata (r - y) ht).2.2 x
  have hstrip (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
      (hsector : stateSector S z.1) :
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ R := by
    intro p hp
    have hpδ : p.1 ∈ Ioo (-δ) δ := by
      constructor <;> linarith [hp.1.1, hp.1.2]
    have hpoint := hdata p.1 hpδ
    have hmem : rootProfileShift r σ p ∈ annularOpen D := ⟨hpoint.1, mem_univ _⟩
    have hrp : 0 < (rootProfileShift r σ p).1 := ha.trans hpoint.1.1
    have hwp : 0 < D.w (rootProfileShift r σ p).1 := hwpos _ hpoint.1
    have hweq : stateProfile D S C z.1 (rootProfileShift r σ p).1 =
        D.w (rootProfileShift r σ p).1 := hpoint.2.2 z.1
    have hwstate : 0 < stateProfile D S C z.1 (rootProfileShift r σ p).1 := by
      rw [hweq]
      exact hwp
    have hlow :=
      (hN.2.2.2.2.2.2.2.2.2.1 z hz hsector (rootProfileShift r σ p) hmem).2.2
    have hDp : 0 < polarDiscriminant (stateProfile D S C z.1)
        (stateHeight D S C z) (rootProfileShift r σ p) :=
      (by norm_num : (0 : ℝ) < 1 / 2).trans_le hlow.2.2.1
    have hQp : 0 < heightQ (profileEnergy (stateProfile D S C z.1) (rootProfileShift r σ p))
        (heightRadial (stateHeight D S C z) (rootProfileShift r σ p))
        (angularPartial (heightAngular (stateHeight D S C z)) (rootProfileShift r σ p)) :=
      (mul_pos (by norm_num : (0 : ℝ) < 7 / 8) hwstate).trans_le
        ((le_div_iff₀ hwstate).mp hlow.1)
    have hnear : (rootProfileShift r σ p).1 ∈ Ioo (r - δ) (r + δ) := by
      rcases hσ with hσ | hσ <;>
        simp only [rootProfileShift, hσ, one_mul, neg_one_mul] <;>
        constructor <;> linarith [hpδ.1, hpδ.2]
    have heq : stateProfile D S C z.1 =ᶠ[𝓝 (rootProfileShift r σ p).1] D.w :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hnear) (fun y hy => hprofile z.1 hy)
    refine ⟨hrp, hwp, hpoint.2.1, hDp, hQp, hweq, ?_⟩
    rw [heq.deriv_eq]
    exact hdivide p.1
  have hr0 : 0 < r + σ * 0 := by simpa only [mul_zero, add_zero] using ha.trans hr.1
  have hw0 : 0 < D.w (r + σ * 0) := by simpa only [mul_zero, add_zero] using hwpos r hr
  let κ := referenceRootSpeedFactor D.w g r σ 0 / 4
  have hκ : 0 < κ := div_pos (referenceRootSpeedFactor_pos hr0 hw0 hg0) (by norm_num)
  refine ⟨g, R, hR, κ, hg, hg0, hκ, hdivide, hphysical, ⟨j, hcell⟩, hstrip, ?_⟩
  intro z hz hsector q
  let t := circleFlowSmoothTimeClamp (-(R / 2)) (R / 2) (R / 2)
    (neg_le_self (half_pos hR).le) (half_pos hR) q.1
  have ht := circleFlowSmoothTimeClamp_mem
    (neg_le_self (half_pos hR).le) (half_pos hR) q.1
  have htδ : t ∈ Ioo (-δ) δ := by
    change -(R / 2) - R / 2 < t ∧ t < R / 2 + R / 2 at ht
    constructor <;> linarith [ht.1, ht.2]
  change κ ≤ factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ (t, q.2)
  exact ((hfields z hz hsector).2.2 (t, q.2) ⟨htδ, mem_univ _⟩).2.1

end ContinuousFlexibility.Analysis
