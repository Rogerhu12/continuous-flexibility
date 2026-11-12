import ContinuousFlexibility.Analysis.N06RootAbsorbedPacket
import ContinuousFlexibility.Analysis.N06RootPhysicalSmallness

/-!
# Actual root coefficient jets with their material decay

The parameter is absorbed into the four genuine weighted height entries.
Consequently the difference of the finite packets from q=0 carries
H^(3/4) M. The original N01 root germ and its denominator inequalities
identify the resulting finite formula with the actual physical root
coefficients. No state regularity of a chosen root-coordinate witness is
assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n06_actualRootAbsorbedCoordinates_parameter_affine
    (D : ReferenceData) (S : PhysicalSpacesData) (z : AnnularState S × ℝ)
    (t : ℝ) (p : PolarPoint) :
    n06ActualRootAbsorbedCoordinates D S (z.1, t * z.2) p =
      n06ActualRootAbsorbedCoordinates D S (z.1, 0) p +
        t • (n06ActualRootAbsorbedCoordinates D S z p -
          n06ActualRootAbsorbedCoordinates D S (z.1, 0) p) :=
  n06RootAbsorbedPacket_parameter_affine
    (fun q => D.w q.1) (n06RootNormalizedHeightFields D S z.1.1 0)
    (n06RootNormalizedHeightFields D S z.1.1 1)
    (n06RootNormalizedHeightFields D S z.1.1 2)
    (n06RootNormalizedHeightFields D S z.1.1 3) z.2 t p

theorem n06_actualRootAbsorbed_denominators
    (D : ReferenceData) (S : PhysicalSpacesData) (z : AnnularState S × ℝ)
    (p : PolarPoint) :
    n06RootNormalizedQ (n06ActualRootAbsorbedCoordinates D S z p) =
      n06RootNormalizedQ (n06ActualRootNormalizedCoordinates D S z p) ∧
      n06RootNormalizedDiscriminant (n06ActualRootAbsorbedCoordinates D S z p) =
        n06RootNormalizedDiscriminant (n06ActualRootNormalizedCoordinates D S z p) :=
  n06_absorbRoot_denominators (n06ActualRootNormalizedCoordinates D S z p)

theorem n06_actualRootAbsorbed_denominators_segment_lower
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r : ℝ} (hr : r ∈ radialCore D)
    (hroot : deriv D.w r = 0) (θ : ℝ) :
    ∀ v ∈ segment ℝ (n06ActualRootAbsorbedCoordinates D S (z.1, 0) (r, θ))
      (n06ActualRootAbsorbedCoordinates D S z (r, θ)),
      (7 / 8 : ℝ) ≤ n06RootNormalizedQ v ∧
        (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant v := by
  intro v hv
  rw [segment_eq_image'] at hv
  obtain ⟨t, ht, rfl⟩ := hv
  dsimp only
  rw [← n06_actualRootAbsorbedCoordinates_parameter_affine D S z t (r, θ)]
  have hb := n06_actualRootNormalized_denominators_lower hT hS hN01
    (n06_root_parameter_scale_mem hz ht) hs hr hroot θ
  have he := n06_actualRootAbsorbed_denominators D S (z.1, t * z.2) (r, θ)
  exact ⟨hb.1.trans_eq he.1.symm, hb.2.trans_eq he.2.symm⟩

theorem n06_physicalRootFields_germ_eq_absorbed
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {r : ℝ} (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0) (θ : ℝ) :
    n06PhysicalRootFields D S C z =ᶠ[𝓝 (r, θ)]
      n06RootNormalizedFields ∘ n06ActualRootAbsorbedCoordinates D S z := by
  filter_upwards [n06_physicalRootFields_germ_eq_normalized hT hS hN01 hz hr hroot θ]
    with p hp
  exact hp.trans (n06_absorbRoot_fields
    (n06ActualRootNormalizedCoordinates D S z p)).symm

theorem n06_rootAbsorbedFields_zero_parameter
    (D : ReferenceData) (S : PhysicalSpacesData) (x : AnnularState S) :
    n06RootNormalizedFields ∘ n06ActualRootAbsorbedCoordinates D S (x, 0) =
      fun _ : PolarPoint => ((0, 1) : PolarPoint) := by
  funext p
  exact (n06_absorbRoot_fields
    (n06ActualRootNormalizedCoordinates D S (x, 0) p)).trans
      (n06RootNormalizedFields_parameter_zero rfl)

private theorem n06_weightedRoot_seminorm_center_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) {x x₀ : E} (h : p (x - x₀) ≤ 1) : p x ≤ p x₀ + 1 := by
  calc
    p x = p ((x - x₀) + x₀) := congrArg p (sub_add_cancel x x₀).symm
    _ ≤ p (x - x₀) + p x₀ := map_add_le_add p _ _
    _ ≤ 1 + p x₀ := add_le_add h le_rfl
    _ = p x₀ + 1 := add_comm _ _

def N06PhysicalRootFieldsWeightedSmall (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (base n : ℕ) (ε Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (n + 7) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∀ r ∈ radialCore D, deriv D.w r = 0 → ∀ θ : ℝ,
      ‖iteratedFDeriv ℝ n (n06PhysicalRootFields D S C z) (r, θ) -
        iteratedFDeriv ℝ n (fun _ : PolarPoint => ((0, 1) : PolarPoint)) (r, θ)‖ ≤
          Q * n06RootJetWeight T (r, θ) * |z.2|

private theorem n06_physicalRootFields_weighted_small_of_packet_bounds
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) (n : ℕ)
    {R M A Q : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hcenter : stateGrading S (n + 7) C.referenceState + 1 ≤ R)
    (hpacket : N06RootAbsorbedSpatialBound D S n R M)
    (hdifference : N06RootAbsorbedWeightedDifferenceBound D T S n A)
    (hcomposition : ∀ (u v : PolarPoint → N06RootNormalizedCoordinates)
      (x : PolarPoint) (δ : ℝ),
      ContDiffAt ℝ ∞ u x → ContDiffAt ℝ ∞ v x → 0 ≤ δ →
      (∀ k, k ≤ n → ‖iteratedFDeriv ℝ k u x‖ ≤ M) →
      (∀ k, k ≤ n → ‖iteratedFDeriv ℝ k v x‖ ≤ M) →
      (∀ k, k ≤ n → ‖iteratedFDeriv ℝ k u x - iteratedFDeriv ℝ k v x‖ ≤ δ) →
      (∀ w ∈ segment ℝ (v x) (u x),
        (7 / 8 : ℝ) ≤ n06RootNormalizedQ w ∧
          (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant w) →
      ‖iteratedFDeriv ℝ n (n06RootNormalizedFields ∘ u) x -
        iteratedFDeriv ℝ n (n06RootNormalizedFields ∘ v) x‖ ≤ Q * δ) :
    N06PhysicalRootFieldsWeightedSmall D T S C base n ε (Q * A * R) := by
  intro z hz hs hsmall r hr hroot θ
  have hstate : stateGrading S (n + 7) z.1 ≤ R :=
    (n06_weightedRoot_seminorm_center_bound (stateGrading S (n + 7))
      ((le_add_of_nonneg_right (abs_nonneg z.2)).trans hsmall)).trans hcenter
  have hq : |z.2| ≤ 1 := (le_add_of_nonneg_left
    (apply_nonneg (stateGrading S (n + 7)) (z.1 - C.referenceState))).trans hsmall
  have hp : (r, θ) ∈ annularOpen D := ⟨hr, mem_univ θ⟩
  have hW : 0 ≤ n06RootJetWeight T (r, θ) := n06_rootJetWeight_nonneg hT hp
  have hu := n06_actualRootAbsorbedCoordinates_contDiff hN01.1.1 hT hS z
  have hv := n06_actualRootAbsorbedCoordinates_contDiff hN01.1.1 hT hS (z.1, 0)
  have hdiff (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k (n06ActualRootAbsorbedCoordinates D S z) (r, θ) -
        iteratedFDeriv ℝ k (n06ActualRootAbsorbedCoordinates D S (z.1, 0)) (r, θ)‖ ≤
          A * n06RootJetWeight T (r, θ) * R * |z.2| :=
    (hdifference z k hk (r, θ) hp).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hstate (mul_nonneg hA hW)) (abs_nonneg _))
  have hbound := hcomposition
    (n06ActualRootAbsorbedCoordinates D S z)
    (n06ActualRootAbsorbedCoordinates D S (z.1, 0)) (r, θ)
    (A * n06RootJetWeight T (r, θ) * R * |z.2|)
    hu.contDiffAt hv.contDiffAt
    (mul_nonneg (mul_nonneg (mul_nonneg hA hW) hR) (abs_nonneg _))
    (fun k hk => hpacket z hstate hq k hk (r, θ) hp)
    (fun k hk => hpacket (z.1, 0) hstate (by norm_num) k hk (r, θ) hp)
    hdiff (n06_actualRootAbsorbed_denominators_segment_lower hT hS hN01 hz hs hr hroot θ)
  have hgerm := n06_physicalRootFields_germ_eq_absorbed hT hS hN01 hz hr hroot θ
  have he := (hgerm.iteratedFDeriv ℝ n).eq_of_nhds
  rw [n06_rootAbsorbedFields_zero_parameter] at hbound
  exact ((congrArg (fun B => ‖B - iteratedFDeriv ℝ n
    (fun _ : PolarPoint => ((0, 1) : PolarPoint)) (r, θ)‖) he).trans_le hbound).trans_eq
      (by ring)

/-- At every true turning root, the actual physical drift and normalized
speed have state-linear jets with the original H^(3/4) M decay. The
constant is chosen before the state, root, and angle. -/
theorem n06_physicalRootFields_state_weighted_small
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06PhysicalRootFieldsWeightedSmall D T S C base n ε Q := by
  let R : ℝ := stateGrading S (n + 7) C.referenceState + 1
  have hR : 0 ≤ R := add_nonneg (apply_nonneg _ _) zero_le_one
  obtain ⟨M, hM, hpacket⟩ := n06_actualRootAbsorbedCoordinates_spatial_bound
    hN01.1.1 hT hS n hR
  obtain ⟨A, hA, hdifference⟩ := n06_actualRootAbsorbedCoordinates_weighted_difference_bound
    hN01.1.1 hT hS n
  obtain ⟨Q, hQ, hcomposition⟩ :=
    n06RootNormalizedFields_composition_difference_bound (E := PolarPoint) n hM
  exact ⟨Q * A * R, mul_nonneg (mul_nonneg hQ hA) hR,
    n06_physicalRootFields_weighted_small_of_packet_bounds hT hS hN01 n hR hA
      le_rfl hpacket hdifference hcomposition⟩

end ContinuousFlexibility.Statements
