module

public import ContinuousFlexibility.Analysis.RootCircleSampleMaterialJets
public import ContinuousFlexibility.Analysis.TransportedLabelMaterialJets
public import ContinuousFlexibility.Analysis.OneSidedOrdinaryJets

/-!
# Actual material jets of a transported root-section label

The root label is a fixed angular sample of the same controlled root
input. Its transport uses the actual interior inverse flow. Equality
on an open set therefore gives both genuine smoothness and all ordinary
jets of the original first integral, with one common low order and loss.
The first integral is not assumed to have any higher derivative bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem interiorRootLabel_fixed_loss_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (rootLoss flowLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A D : ℕ → ℝ,
      (∀ n, 0 < A n) → (∀ n, 0 < D n) →
      ∀ a b : ℝ, a < b →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p low z ≤ 1 →
      ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G →
        (∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi) →
        (∀ s : ℕ, CSBound s
          (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G
            (A s * (1 + p (s + rootLoss) z))) →
      ∀ Λ : ℝ, ∀ Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
        N04FlowJetBounds p flowLoss D z 1 Λ Ψ →
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ ζ ∈ Icc (-1 : ℝ) 1,
      ∀ U : PolarPoint → ℝ, ∀ V : Set PolarPoint, IsOpen V →
        (∀ q ∈ V, q.1 ∈ Icc a b) →
        EqOn U (fun q => rootCircleSample G x ζ
          (interiorEndpointPullback Ψ a b q)) V →
      ∀ q ∈ V, ContDiffAt ℝ ∞ U q ∧
        PointwiseMaterialJetBound p outLoss B z (fun y => U y - y.2) q := by
  let inputLoss := max rootLoss flowLoss
  obtain ⟨low, outLoss, hcompose⟩ :=
    transportedLabel_displacement_fixed_loss hp hI inputLoss
  refine ⟨low, outLoss, ?_⟩
  intro A D hA hD a b hab
  obtain ⟨R, hR, hroot⟩ :=
    exists_rootCircleSample_displacement_jet_constants p rootLoss A hA
  obtain ⟨F, hF, hflow⟩ :=
    exists_interiorEndpoint_displacement_jet_constants p flowLoss D hD hab
  let C : ℕ → ℝ := fun n => R n + F n
  have hC (n : ℕ) : 0 < C n := add_pos (hR n) (hF n)
  obtain ⟨B, hB, hbound⟩ := hcompose C hC
  refine ⟨B, hB, ?_⟩
  intro z hz G hG hperiod hjets Λ Ψ hΨ x hx ζ hζ U V hV hradial he q hq
  let u : ℝ → ℝ := rootCircleSample G x ζ
  let g : PolarPoint → ℝ := interiorEndpointPullback Ψ a b
  have hu : ContDiff ℝ ∞ u := contDiff_rootCircleSample hG x ζ
  have hg : ContDiff ℝ ∞ g :=
    contDiff_interiorEndpointPullback (hΨ 1 ⟨zero_le_one, le_rfl⟩).1 a b
  have hU : ContDiffAt ℝ ∞ U q := by
    have he' : U =ᶠ[𝓝 q] (u ∘ g) :=
      Filter.eventually_of_mem (hV.mem_nhds hq) (fun y hy => he hy)
    exact (hu.comp hg).contDiffAt.congr_of_eventuallyEq he'
  have huj : PointwiseMaterialJetBound p inputLoss C z
      (fun θ => u θ - θ) (g q) :=
    PointwiseMaterialJetBound.mono hp (le_max_left rootLoss flowLoss)
      (fun n => (hR n).le) (fun n => le_add_of_nonneg_right (hF n).le)
      (hroot z G hG hperiod hjets x hx ζ hζ (g q))
  have hgj : PointwiseMaterialJetBound p inputLoss C z
      (fun y => g y - y.2) q :=
    PointwiseMaterialJetBound.mono hp (le_max_right rootLoss flowLoss)
      (fun n => (hF n).le) (fun n => le_add_of_nonneg_left (hR n).le)
      (hflow z Λ Ψ hΨ q (hradial q hq))
  have hj := hbound z hz u g hu hg q huj hgj
  refine ⟨hU, ?_⟩
  have he' : EqOn (fun y => U y - y.2) (fun y => u (g y) - y.2) V := by
    intro y hy
    exact congrArg (fun t : ℝ => t - y.2) (he hy)
  intro n
  rw [iteratedFDeriv_eqOn_of_isOpen hV he' n hq]
  exact hj n

end ContinuousFlexibility.Analysis
