import ContinuousFlexibility.Analysis.N01LocalizedCoefficientBounds
import ContinuousFlexibility.Analysis.N01ActualRootGeometry
import ContinuousFlexibility.Analysis.PointwiseAffineMaterialJets
import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# Actual radial coefficient jets at every interior root

A genuine material-cell neighborhood is selected from the fixed radial
partition. The existing N01 coefficient estimate on that neighborhood
then bounds all ordinary jets of the actual radial coefficient, with
the original N01 loss and constants before the state and angle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem norm_jet_le_of_germ_mixed_bound
    {f g : PolarPoint → ℝ} {U : Set PolarPoint} {q : PolarPoint}
    (hU : IsOpen U) (hf : ContDiff ℝ ∞ f) (hq : q ∈ U)
    (he : f =ᶠ[𝓝 q] g) (n : ℕ) {A w : ℝ} (hA : 0 ≤ A) (hw : 0 ≤ w)
    (hb : ∀ a b : ℕ, a + b = n → |mixedDerivative a b f q| ≤ A * (1 + w)) :
    ‖iteratedFDeriv ℝ n g q‖ ≤ ((2 : ℝ) ^ n * A) * (1 + w) := by
  have hn : ‖iteratedFDeriv ℝ n f q‖ ≤ (2 : ℝ) ^ n * (A * (1 + w)) := by
    apply norm_iteratedFDeriv_le_of_mixedDerivative hU hf.contDiffOn n hq
      (mul_nonneg hA (add_nonneg zero_le_one hw))
    intro a b hab
    simpa only [Real.norm_eq_abs] using hb a b hab
  rw [(he.iteratedFDeriv ℝ n).self_of_nhds] at hn
  exact hn.trans_eq (by ring)

def N01RadialCoefficientRootJetBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε r : ℝ) (A : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ θ : ℝ,
    ContDiffAt ℝ ∞ (originalCoefficients D S C z).a (r, θ) ∧
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) loss A
        (z - (C.referenceState, 0)) (originalCoefficients D S C z).a (r, θ)

private theorem n01_radialCoefficient_root_bound_of_localized_family
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε r R : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hr : r ∈ Ioo D.a D.b)
    (hR : 0 < R) (hlu : r - R ≤ r + R)
    (hphysical : Ioo ((r - R) - R) ((r + R) + R) ⊆ Ioo D.a D.b)
    (A : ℕ → ℝ) (hA : ∀ n, 1 ≤ A n)
    (hbound : ∀ n, LocalizedOriginalCoefficientBoundAtOrder D S C base loss ε hlu hR n (A n)) :
    N01RadialCoefficientRootJetBound D S C base loss ε r (fun n => (2 : ℝ) ^ n * A n) := by
  intro z hz hs θ
  have hq : (r, θ) ∈ Ioo (r - R) (r + R) ×ˢ (univ : Set ℝ) :=
    ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
  have hk := contDiff_localizedOriginalCoefficient hS hT hN hlu hR hphysical hz hs 0
  have he : localizedOriginalCoefficient D S C hlu hR z 0 =ᶠ[𝓝 (r, θ)]
      (originalCoefficients D S C z).a :=
    Filter.eventually_of_mem ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq)
      (fun q hq => localizedOriginalCoefficient_eqOn D S C hlu hR z 0 hq)
  have hactual : ContDiffAt ℝ ∞ (originalCoefficients D S C z).a (r, θ) :=
    (contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz hs 0).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr, mem_univ θ⟩)
  refine ⟨hactual, ?_⟩
  intro n
  exact norm_jet_le_of_germ_mixed_bound (isOpen_Ioo.prod isOpen_univ) hk hq he n
    (zero_le_one.trans (hA n)) (apply_nonneg _ _)
    (fun a b hab => hbound n z hz hs 0 a b (le_of_eq hab) (r, θ) hq)

theorem n01_radialCoefficient_root_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε r : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hr : r ∈ Ioo D.a D.b) :
    ∃ A : ℕ → ℝ, (∀ n, 0 < A n) ∧ N01RadialCoefficientRootJetBound D S C base loss ε r A := by
  obtain ⟨_, hD⟩ := hN.1.1
  have hP : RadialPartition D := hD.2.1
  obtain ⟨j, ρ, hρ, hcellρ⟩ := exists_radialCell_collar_of_partition hP hr
  let R := ρ / 4
  have hR : 0 < R := div_pos hρ (by norm_num)
  have hlu : r - R ≤ r + R := by linarith
  have hphysical : Ioo ((r - R) - R) ((r + R) + R) ⊆ Ioo D.a D.b := by
    intro y hy
    apply hP.2.2.2.1 j
    apply hcellρ
    dsimp only [R] at hy
    constructor <;> linarith [hy.1, hy.2]
  have hcell : Ioo (r - R) (r + R) ⊆ D.cells j := by
    intro y hy
    apply hcellρ
    dsimp only [R] at hy
    constructor <;> linarith [hy.1, hy.2]
  choose A hA hb using fun n => localizedOriginalCoefficient_fixed_loss_bound_of_n01
    hS hT hN hlu hR hphysical j hcell n
  refine ⟨fun n => (2 : ℝ) ^ n * A n,
    fun n => mul_pos (pow_pos (by norm_num) n) (zero_lt_one.trans_le (hA n)), ?_⟩
  exact n01_radialCoefficient_root_bound_of_localized_family hS hT hN hr hR hlu
    hphysical A hA hb

end ContinuousFlexibility.Analysis
