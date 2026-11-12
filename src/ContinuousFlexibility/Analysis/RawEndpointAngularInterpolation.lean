import ContinuousFlexibility.Analysis.EndpointAngularInterpolation
import ContinuousFlexibility.Analysis.OneSidedBoundaryTaylorRepresentative
import ContinuousFlexibility.Analysis.BoundaryRadialFrechetJets
import ContinuousFlexibility.Analysis.CylinderMixedJetNorms

/-!
# Angular interpolation from finite jets of the actual endpoint fields

The zero order lift is never bounded. Only positive ordinary jets of
the supplied endpoint fields produce the finite coefficient estimates.
Radial matching then identifies their full ordinary boundary jets.
This is reconstructed source, with an explicitly displayed family width.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def rawEndpointAngularData (l r : ℝ) (ψ : Bool → PolarPoint → ℝ)
    (side : Bool) : ℕ → ℝ → ℝ :=
  radialBoundaryJet (ψ side) (if side then r else l)

theorem rawEndpointAngularInterpolation_family
    {ι : Type*} (n : ℕ) {ψ : ι → Bool → PolarPoint → ℝ}
    {l r c d κ M : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκ : 0 < κ) (hκone : κ ≤ 1) (hM : 0 ≤ M)
    (hψ : ∀ i side, ContDiff ℝ ∞ (ψ i side))
    (hangle : ∀ i side θ, κ ≤ angularPartial (ψ i side) (if side then r else l, θ))
    (hjets : ∀ i side k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
      ‖iteratedFDeriv ℝ k (ψ i side) (if side then r else l, θ)‖ ≤ M)
    (hlift : ∀ i side x θ, ψ i side (x, θ + Real.pi) = ψ i side (x, θ) + Real.pi)
    (hodd : ∀ i side x θ, ψ i side (x, -θ) = -ψ i side (x, θ)) :
    let δ := endpointAngularWidth n l r c d κ M
    0 < δ ∧ δ ≤ 1 ∧ 2 * δ < r - l ∧ δ < c - l ∧ δ < r - d ∧
      ∀ i, let φ := (positiveAngularTaylorInterpolation n l r δ
        (rawEndpointAngularData l r (ψ i)))
      ContDiff ℝ ∞ φ ∧
      (∀ x θ, κ / 2 ≤ deriv (fun η => φ (x, η)) θ) ∧
      (∀ side k, k ≤ n → ∀ θ,
        radialBoundaryJet φ (if side then r else l) k θ =
          radialBoundaryJet (ψ i side) (if side then r else l) k θ) ∧
      (∀ side k, k ≤ n → ∀ θ,
        iteratedFDeriv ℝ k φ (if side then r else l, θ) =
          iteratedFDeriv ℝ k (ψ i side) (if side then r else l, θ)) ∧
      (∀ x θ, φ (x, θ + Real.pi) = φ (x, θ) + Real.pi) ∧
      (∀ x θ, φ (x, -θ) = -φ (x, θ)) ∧
      ∀ x ∈ Icc c d, ∀ θ, φ =ᶠ[𝓝 (x, θ)] (Prod.snd : PolarPoint → ℝ) := by
  let A : ι → Bool → ℕ → ℝ → ℝ := fun i => rawEndpointAngularData l r (ψ i)
  let e : Bool → ℝ := fun side => if side then r else l
  have hA (i : ι) (side : Bool) (j : ℕ) (_ : j ≤ n) :
      ContDiff ℝ ∞ (A i side j) :=
    contDiff_radialBoundaryJet (hψ i side) (e side) j
  have hzero (i : ι) (side : Bool) (θ : ℝ) :
      κ ≤ deriv (A i side 0) θ := by
    change κ ≤ deriv (fun η => ψ i side (e side, η)) θ
    rw [deriv_cylinder_angular_slice ((hψ i side).differentiable (by simp))]
    exact hangle i side θ
  have hbound (i : ι) (side : Bool) (j : ℕ) (hj : 0 < j) (hjn : j ≤ n) (θ : ℝ) :
      |deriv (A i side j) θ| ≤ M := by
    have he : deriv (A i side j) θ = mixedDerivative j 1 (ψ i side) (e side, θ) := by
      simpa only [iteratedDeriv_one] using
        iteratedDeriv_radialBoundaryJet_eq_mixedDerivative isOpen_univ
          (hψ i side).contDiffOn (e side) (fun _ => mem_univ _) j 1 θ
    rw [he]
    exact (abs_mixedDerivative_le_norm_iteratedFDeriv isOpen_univ
      (hψ i side).contDiffOn j 1 (mem_univ (e side, θ))).trans
      (hjets i side (j + 1) (by omega) (by omega) θ)
  have haffine (i : ι) (side : Bool) (α β : ℝ) (τ : ℝ → ℝ)
      (hτ : ContDiff ℝ ∞ τ)
      (he : ∀ x θ, ψ i side (x, τ θ) = β + α * ψ i side (x, θ))
      (j : ℕ) (θ : ℝ) :
      A i side j (τ θ) = (if j = 0 then β else 0) + α * A i side j θ := by
    exact radialBoundaryJet_angleAffine_on_closedStrip
      (a := e side - 1) (b := e side + 1)
      (by linarith) (by constructor <;> linarith)
      (fun _ => (hψ i side).contDiffAt) hτ (fun x _ η => he x η) j θ
  have hAlift (i : ι) (side : Bool) (θ : ℝ) :
      A i side 0 (θ + Real.pi) = A i side 0 θ + Real.pi := by
    simpa only [A, rawEndpointAngularData, radialBoundaryJet, iteratedDeriv_zero]
      using hlift i side (e side) θ
  have hAperiod (i : ι) (side : Bool) (j : ℕ) (hj : 0 < j) (_ : j ≤ n) :
      Function.Periodic (A i side j) Real.pi := by
    intro θ
    simpa only [if_neg (Nat.ne_of_gt hj), one_mul, zero_add] using
      haffine i side 1 Real.pi (fun η => η + Real.pi) (contDiff_id.add contDiff_const)
        (fun x η => by simpa only [one_mul, add_comm] using hlift i side x η) j θ
  have hAodd (i : ι) (side : Bool) (j : ℕ) (_ : j ≤ n) (θ : ℝ) :
      A i side j (-θ) = -A i side j θ := by
    simpa only [ite_self, zero_add, neg_one_mul] using
      haffine i side (-1) 0 (fun η => -η) contDiff_neg
        (fun x η => by simpa only [zero_add, neg_one_mul] using hodd i side x η) j θ
  have hout := endpointAngularInterpolation_family hlc hcd hdr hκ hκone hM
    hA hzero hbound hAlift hAperiod hAodd
  dsimp only at hout ⊢
  rcases hout with ⟨hδ, hδone, hgap, hδL, hδR, hout⟩
  refine ⟨hδ, hδone, hgap, hδL, hδR, ?_⟩
  intro i
  rcases hout i with ⟨hφ, hlower, hradial, hperiod, hreflect, hmiddle⟩
  refine ⟨hφ, hlower, hradial, ?_, hperiod, hreflect, hmiddle⟩
  intro side k hk θ
  exact iteratedFDeriv_eq_of_radialBoundaryJets_eq isOpen_univ hφ.contDiffOn
    (hψ i side).contDiffOn (e side) (fun _ => mem_univ _)
    (n := n) (hradial side) hk θ

end ContinuousFlexibility.Analysis
