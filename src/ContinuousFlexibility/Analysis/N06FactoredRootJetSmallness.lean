module

public import ContinuousFlexibility.Analysis.N06RootJetTransportCalculus
public import ContinuousFlexibility.Analysis.N06RootPhysicalFiniteJets

/-!
# The actual oriented and factored root coefficient differences

This applies the weighted physical estimate to the very drift and speed
passed to the characteristic-root equation. Radial reorientation is
isometric. Multiplication by the true fixed reference root factor has
the displayed finite reference-jet cost. No uniform material estimate
for that reference cost is silently assumed here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n06_rootProfileShift_boundary (r σ θ : ℝ) :
    rootProfileShift r σ (0, θ) = (r, θ) := by
  simp only [rootProfileShift, mul_zero, add_zero]

theorem n06_rootShift_contDiffAt
    {f : PolarPoint → PolarPoint} {r σ θ : ℝ}
    (hf : ContDiffAt ℝ ∞ f (r, θ)) :
    ContDiffAt ℝ ∞ (f ∘ rootProfileShift r σ) (0, θ) := by
  have hf' : ContDiffAt ℝ ∞ f (rootProfileShift r σ (0, θ)) := by
    rw [n06_rootProfileShift_boundary]
    exact hf
  exact hf'.comp (0, θ) (n06_rootProfileShift_contDiff r σ).contDiffAt

theorem n06_orientedFst_jet_le
    {f : PolarPoint → PolarPoint} {r σ θ : ℝ}
    (hf : ContDiffAt ℝ ∞ f (r, θ)) (hσ : σ = 1 ∨ σ = -1) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun p => σ * (f (rootProfileShift r σ p)).1) (0, θ)‖ ≤
      ‖iteratedFDeriv ℝ n f (r, θ)‖ := by
  have hs := n06_rootShift_contDiffAt (σ := σ) hf
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  change ‖iteratedFDeriv ℝ n
    (fun p => σ * ((f ∘ rootProfileShift r σ) p).1) (0, θ)‖ ≤
      ‖iteratedFDeriv ℝ n f (r, θ)‖
  rw [n06_norm_iteratedFDeriv_real_mul_at hs.fst, hσabs, one_mul]
  have h := n06_norm_iteratedFDeriv_fst_le hs n
  have he := n06_norm_iteratedFDeriv_rootProfileShift f r σ hσ n (0, θ)
  rw [n06_rootProfileShift_boundary] at he
  exact h.trans_eq he

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n06_orientedCharacteristicDrift_eq_rootDifference
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (r σ : ℝ) :
    orientedCharacteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) r σ =
      fun p => σ * (n06PhysicalRootDifference D S C z (rootProfileShift r σ p)).1 := by
  funext p
  simp only [n06PhysicalRootDifference, Prod.fst_sub, sub_zero]
  rfl

theorem n06_factoredCharacteristicSpeed_difference_germ
    (hD : IsAccumulatingProfile D) (z : AnnularState S × ℝ)
    (g : ℝ → ℝ) {r : ℝ} (hr : r ∈ radialCore D) (σ θ : ℝ) :
    (fun p => factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ p - referenceRootSpeedFactor D.w g r σ p.1) =ᶠ[𝓝 (0, θ)]
      fun p => referenceRootSpeedFactor D.w g r σ p.1 *
        (n06PhysicalRootDifference D S C z (rootProfileShift r σ p)).2 := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hp : rootProfileShift r σ (0, θ) ∈ annularOpen D := by
    rw [n06_rootProfileShift_boundary]
    exact ⟨hr, mem_univ θ⟩
  have hnear : ∀ᶠ p in 𝓝 ((0, θ) : PolarPoint), rootProfileShift r σ p ∈ annularOpen D :=
    (hU.preimage (n06_rootProfileShift_contDiff r σ).continuous).mem_nhds hp
  filter_upwards [hnear] with p hp
  have hw : D.w (rootProfileShift r σ p).1 ≠ 0 :=
    (hD.choose_spec.1.2.2.2.2.1 _ hp.1).ne'
  have he := (n06_factoredRootFields_eq_physical D S C z g r σ p hw).2
  change factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ p - referenceRootSpeedFactor D.w g r σ p.1 =
    referenceRootSpeedFactor D.w g r σ p.1 *
      ((n06PhysicalRootFields D S C z (rootProfileShift r σ p)).2 - 1)
  rw [he]
  ring

def N06FactoredRootFiniteJetsSmall (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (base n : ℕ) (ε Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (n + 7) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∀ r ∈ radialCore D, deriv D.w r = 0 → ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
    ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → 0 < g 0 → ∀ θ : ℝ, ∀ k, k ≤ n →
      ‖iteratedFDeriv ℝ k
        (orientedCharacteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) r σ)
          (0, θ)‖ ≤ Q * n06RootJetWeight T (r, θ) * |z.2| ∧
      ‖iteratedFDeriv ℝ k (fun p =>
        factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ p - referenceRootSpeedFactor D.w g r σ p.1)
        (0, θ)‖ ≤
          ((2 : ℝ) ^ n * n06RootRadialFactorJetCost (referenceRootSpeedFactor D.w g r σ) n * Q) *
            n06RootJetWeight T (r, θ) * |z.2|

private theorem n06_factoredRootFiniteJets_of_physical
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) (n : ℕ)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hphysical : N06PhysicalRootFiniteJetsSmall D T S C base n ε Q) :
    N06FactoredRootFiniteJetsSmall D T S C base n ε Q := by
  intro z hz hs hsmall r hr hroot σ hσ g hg hg0 θ k hk
  have hf := n06_physicalRootDifference_contDiffAt_root hT hS hN01 hz hs hr hroot θ
  have hfield := hphysical z hz hs hsmall r hr hroot θ
  constructor
  · rw [n06_orientedCharacteristicDrift_eq_rootDifference]
    exact (n06_orientedFst_jet_le hf hσ k).trans (hfield k hk)
  · let a : ℝ → ℝ := referenceRootSpeedFactor D.w g r σ
    let f : PolarPoint → PolarPoint := n06PhysicalRootDifference D S C z ∘ rootProfileShift r σ
    let A : ℝ := n06RootRadialFactorJetCost a n
    let B : ℝ := Q * n06RootJetWeight T (r, θ) * |z.2|
    have hA : 0 ≤ A := n06RootRadialFactorJetCost_nonneg a n
    have hB : 0 ≤ B := mul_nonneg
      (mul_nonneg hQ (n06_rootJetWeight_nonneg hT ⟨hr, mem_univ θ⟩)) (abs_nonneg _)
    have hfs : ContDiffAt ℝ ∞ f (0, θ) := n06_rootShift_contDiffAt (σ := σ) hf
    have hrpos : 0 < r := hN01.1.1.choose_spec.1.1.trans hr.1
    have hwpos : 0 < D.w r := hN01.1.1.choose_spec.1.2.2.2.2.1 r hr
    have ha : ContDiffAt ℝ ∞ a 0 :=
      contDiffAt_referenceRootSpeedFactor hN01.1.1.choose_spec.1.2.2.1.1 hg
        (by simpa only [mul_zero, add_zero] using hrpos)
        (by simpa only [mul_zero, add_zero] using hwpos) hg0
    have halift : ContDiffAt ℝ ∞ (fun p : PolarPoint => a p.1) (0, θ) :=
      ha.comp (0, θ) contDiffAt_fst
    have hfB (j : ℕ) (hj : j ≤ k) : ‖iteratedFDeriv ℝ j (fun p => (f p).2) (0, θ)‖ ≤ B := by
      have he := n06_norm_iteratedFDeriv_rootProfileShift
        (n06PhysicalRootDifference D S C z) r σ hσ j (0, θ)
      rw [n06_rootProfileShift_boundary] at he
      exact ((n06_norm_iteratedFDeriv_snd_le hfs j).trans_eq he).trans
        (hfield j (hj.trans hk))
    have hp := n06_norm_iteratedFDeriv_mul_at_le halift hfs.snd k hA hB
      (fun j hj => n06_radialFactor_jet_bound a n j (hj.trans hk) θ) hfB
    have hscale : (2 : ℝ) ^ k * A * B ≤ (2 : ℝ) ^ n * A * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hA) hB
    have he := ((n06_factoredCharacteristicSpeed_difference_germ
      (C := C) hN01.1.1 z g hr σ θ).iteratedFDeriv ℝ k).eq_of_nhds
    exact ((congrArg norm he).trans_le (hp.trans hscale)).trans_eq (by dsimp only [A, B, a]; ring)

/-- Genuine current drift and speed coefficients have all required
root jets with a linear small factor and explicit fixed reference cost. -/
theorem n06_factoredRootFields_finite_weighted_jets
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06FactoredRootFiniteJetsSmall D T S C base n ε Q := by
  obtain ⟨Q, hQ, hp⟩ := n06_physicalRootFields_finite_weighted_jets hT hS hN01 n
  exact ⟨Q, hQ, n06_factoredRootFiniteJets_of_physical hT hS hN01 n hQ hp⟩

end ContinuousFlexibility.Statements
