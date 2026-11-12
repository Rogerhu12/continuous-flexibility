import ContinuousFlexibility.Analysis.N06RootPhysicalWeightedSmallness
import ContinuousFlexibility.Analysis.SolveStateSpaces

/-!
# All finite jets of the actual physical root difference

The input order n+7 is fixed before the state. Every derivative through
order n retains the same H^(3/4) M |q| factor. The field is the genuine
physical drift and speed ratio minus its reference value.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n06PhysicalRootDifference (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) (p : PolarPoint) : PolarPoint :=
  n06PhysicalRootFields D S C z p - (0, 1)

theorem n06_physicalRootFields_contDiffAt_root
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r : ℝ} (hr : r ∈ radialCore D)
    (hroot : deriv D.w r = 0) (θ : ℝ) :
    ContDiffAt ℝ ∞ (n06PhysicalRootFields D S C z) (r, θ) := by
  have hb := n06_actualRootNormalized_denominators_lower hT hS hN01 hz hs hr hroot θ
  have houter := n06RootNormalizedFields_contDiffAt
    (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hb.1))
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb.2)
  have hinner := n06_actualRootNormalizedCoordinates_contDiff hN01.1.1 hT hS z
  exact (houter.comp (r, θ) hinner.contDiffAt).congr_of_eventuallyEq
    (n06_physicalRootFields_germ_eq_normalized hT hS hN01 hz hr hroot θ)

theorem n06_physicalRootDifference_contDiffAt_root
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r : ℝ} (hr : r ∈ radialCore D)
    (hroot : deriv D.w r = 0) (θ : ℝ) :
    ContDiffAt ℝ ∞ (n06PhysicalRootDifference D S C z) (r, θ) :=
  (n06_physicalRootFields_contDiffAt_root hT hS hN01 hz hs hr hroot θ).sub contDiffAt_const

def N06PhysicalRootFiniteJetsSmall (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (base n : ℕ) (ε Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (n + 7) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∀ r ∈ radialCore D, deriv D.w r = 0 → ∀ θ : ℝ, ∀ k, k ≤ n →
      ‖iteratedFDeriv ℝ k (n06PhysicalRootDifference D S C z) (r, θ)‖ ≤
        Q * n06RootJetWeight T (r, θ) * |z.2|

theorem n06_physicalRootFields_finite_weighted_jets
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06PhysicalRootFiniteJetsSmall D T S C base n ε Q := by
  classical
  have hchoices (i : Fin (n + 1)) := n06_physicalRootFields_state_weighted_small hT hS hN01 i.val
  choose q hq hb using hchoices
  let Q : ℝ := ∑ i : Fin (n + 1), q i
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => hq i)
  refine ⟨Q, hQ, ?_⟩
  intro z hz hs hsmall r hr hroot θ k hk
  let i : Fin (n + 1) := ⟨k, by omega⟩
  have hgrade : stateGrading S (k + 7) (z.1 - C.referenceState) ≤
      stateGrading S (n + 7) (z.1 - C.referenceState) :=
    solve_stateGrading_monotone S (by omega) _
  have hsmallk : stateGrading S (k + 7) (z.1 - C.referenceState) + |z.2| ≤ 1 :=
    (add_le_add hgrade (le_refl |z.2|)).trans hsmall
  have h := hb i z hz hs hsmallk r hr hroot θ
  have hi : q i ≤ Q := Finset.single_le_sum (fun j _ => hq j) (Finset.mem_univ i)
  have hW : 0 ≤ n06RootJetWeight T (r, θ) :=
    n06_rootJetWeight_nonneg hT ⟨hr, mem_univ θ⟩
  have hf := n06_physicalRootFields_contDiffAt_root hT hS hN01 hz hs hr hroot θ
  have he := iteratedFDeriv_sub_apply (x := (r, θ)) (i := k)
    (hf.of_le (by simp : (k : ℕ∞ω) ≤ ∞))
    (contDiffAt_const : ContDiffAt ℝ (k : ℕ∞ω)
      (fun _ : PolarPoint => ((0, 1) : PolarPoint)) (r, θ))
  simp only [Pi.sub_def] at he
  change ‖iteratedFDeriv ℝ k (fun p => n06PhysicalRootFields D S C z p - (0, 1)) (r, θ)‖ ≤ _
  rw [he]
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hi hW) (abs_nonneg _))

end ContinuousFlexibility.Statements
