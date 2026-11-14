module

public import ContinuousFlexibility.Analysis.N06RootNormalizedPacket

/-!
# State-linear spatial jets of the actual physical root coefficients

The original N01 neighborhood contains the line obtained by scaling only
q. On every true reference turning root, N01 fixes the whole profile germ
and gives Q/w >= 7/8 and discriminant >= 1/2 along this line. The actual
normalized root formula is constant (0,1) at q=0, for every height pair.
Its spatial derivatives therefore differ from the reference by O(|q|),
uniformly over all roots and angles, on a fixed original state seminorm ball.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n06_root_parameter_scale_mem
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (z.1, t * z.2) ∈ stateNeighborhood S C base ε := by
  refine ⟨hz.1, ?_⟩
  have hs : |t * z.2| ≤ |z.2| := by
    rw [abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg z.2)).trans_eq (one_mul _)
  exact hs.trans_lt hz.2

theorem n06_actualRootNormalizedCoordinates_parameter_affine
    (D : ReferenceData) (S : PhysicalSpacesData) (z : AnnularState S × ℝ)
    (t : ℝ) (p : PolarPoint) :
    n06ActualRootNormalizedCoordinates D S (z.1, t * z.2) p =
      n06ActualRootNormalizedCoordinates D S (z.1, 0) p +
        t • (n06ActualRootNormalizedCoordinates D S z p -
          n06ActualRootNormalizedCoordinates D S (z.1, 0) p) :=
  n06RootNormalizedPacket_parameter_affine
    (fun q => D.w q.1) (n06RootNormalizedHeightFields D S z.1.1 0)
    (n06RootNormalizedHeightFields D S z.1.1 1)
    (n06RootNormalizedHeightFields D S z.1.1 2)
    (n06RootNormalizedHeightFields D S z.1.1 3) z.2 t p

theorem n06_actualRootNormalized_denominators_lower
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r : ℝ} (hr : r ∈ radialCore D)
    (hroot : deriv D.w r = 0) (θ : ℝ) :
    (7 / 8 : ℝ) ≤ n06RootNormalizedQ (n06ActualRootNormalizedCoordinates D S z (r, θ)) ∧
      (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant
        (n06ActualRootNormalizedCoordinates D S z (r, θ)) := by
  have hrpos : 0 < r := hN01.1.1.choose_spec.1.1.trans hr.1
  have hw : D.w r ≠ 0 := (hN01.1.1.choose_spec.1.2.2.2.2.1 r hr).ne'
  have hprofile : stateProfile D S C z.1 r = D.w r :=
    (hN01.2.2.2.2.2.2.2.2.2.2.1 z hz r hr hroot).eq_of_nhds
  have hraw := n06_rootFinite_denominators_eq hT hS hN01 z
    (p := (r, θ)) hrpos.ne' hprofile
  have hnorm := n06_normalizeRoot_denominators
    (v := n06ActualNuJetCoordinates D S z (r, θ)) hw
  have hQ : n06RootNormalizedQ (n06ActualRootNormalizedCoordinates D S z (r, θ)) =
      heightQ (profileEnergy (stateProfile D S C z.1) (r, θ))
        (heightRadial (stateHeight D S C z) (r, θ))
        (angularPartial (heightAngular (stateHeight D S C z)) (r, θ)) /
          stateProfile D S C z.1 r :=
    hnorm.1.trans (congrArg₂ (fun a b : ℝ => a / b) hraw.1 hprofile.symm)
  have hD : n06RootNormalizedDiscriminant
      (n06ActualRootNormalizedCoordinates D S z (r, θ)) =
        polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) (r, θ) :=
    hnorm.2.trans hraw.2
  have hb := hN01.2.2.2.2.2.2.2.2.2.1 z hz hs (r, θ) ⟨hr, mem_univ θ⟩
  exact ⟨hb.2.2.1.trans_eq hQ.symm, hb.2.2.2.2.1.trans_eq hD.symm⟩

theorem n06_actualRootNormalized_denominators_segment_lower
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r : ℝ} (hr : r ∈ radialCore D)
    (hroot : deriv D.w r = 0) (θ : ℝ) :
    ∀ v ∈ segment ℝ (n06ActualRootNormalizedCoordinates D S (z.1, 0) (r, θ))
      (n06ActualRootNormalizedCoordinates D S z (r, θ)),
      (7 / 8 : ℝ) ≤ n06RootNormalizedQ v ∧
        (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant v := by
  intro v hv
  rw [segment_eq_image'] at hv
  obtain ⟨t, ht, rfl⟩ := hv
  dsimp only
  rw [← n06_actualRootNormalizedCoordinates_parameter_affine D S z t (r, θ)]
  exact n06_actualRootNormalized_denominators_lower hT hS hN01
    (n06_root_parameter_scale_mem hz ht) hs hr hroot θ

theorem n06_physicalRootFields_germ_eq_normalized
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {r : ℝ} (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0) (θ : ℝ) :
    n06PhysicalRootFields D S C z =ᶠ[𝓝 (r, θ)]
      n06RootNormalizedFields ∘ n06ActualRootNormalizedCoordinates D S z := by
  have hraw := n06_physicalRootFields_germ_eq_finite hT hS hN01 hz hr hroot θ
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hp : (r, θ) ∈ annularOpen D := ⟨hr, mem_univ θ⟩
  filter_upwards [hraw, hU.mem_nhds hp] with p he hp
  have hw : D.w p.1 ≠ 0 := (hN01.1.1.choose_spec.1.2.2.2.2.1 p.1 hp.1).ne'
  exact he.trans (n06_normalizeRoot_fields
    (v := n06ActualNuJetCoordinates D S z p) hw).symm

theorem n06_rootNormalizedFields_zero_parameter
    (D : ReferenceData) (S : PhysicalSpacesData) (x : AnnularState S) :
    n06RootNormalizedFields ∘ n06ActualRootNormalizedCoordinates D S (x, 0) =
      fun _ : PolarPoint => ((0, 1) : PolarPoint) := by
  funext p
  exact n06RootNormalizedFields_parameter_zero
    (v := n06ActualRootNormalizedCoordinates D S (x, 0) p) rfl

private theorem n06_root_seminorm_center_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) {x x₀ : E} (h : p (x - x₀) ≤ 1) : p x ≤ p x₀ + 1 := by
  calc
    p x = p ((x - x₀) + x₀) := congrArg p (sub_add_cancel x x₀).symm
    _ ≤ p (x - x₀) + p x₀ := map_add_le_add p _ _
    _ ≤ 1 + p x₀ := add_le_add h le_rfl
    _ = p x₀ + 1 := add_comm _ _

def N06PhysicalRootFieldsSmall (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base n : ℕ) (ε Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (n + 7) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∀ r ∈ radialCore D, deriv D.w r = 0 → ∀ θ : ℝ,
      ‖iteratedFDeriv ℝ n (n06PhysicalRootFields D S C z) (r, θ) -
        iteratedFDeriv ℝ n (fun _ : PolarPoint => ((0, 1) : PolarPoint)) (r, θ)‖ ≤ Q * |z.2|

/-- The coefficient jets are the actual physical root jets, and the
constant is chosen before the state, root, and angle. The only state size
condition uses the original fixed seminorm of order n+7. -/
theorem n06_physicalRootFields_state_small
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06PhysicalRootFieldsSmall D S C base n ε Q := by
  let R : ℝ := stateGrading S (n + 7) C.referenceState + 1
  have hR : 0 ≤ R := add_nonneg (apply_nonneg _ _) zero_le_one
  obtain ⟨M, hM, hpacket⟩ := n06_actualRootNormalizedCoordinates_spatial_bound
    hN01.1.1 hT hS n hR
  obtain ⟨Q, hQ, hcomposition⟩ :=
    n06RootNormalizedFields_composition_difference_bound (E := PolarPoint) n hM
  refine ⟨Q, hQ, ?_⟩
  intro z hz hs hsmall r hr hroot θ
  have hstate : stateGrading S (n + 7) z.1 ≤ R :=
    n06_root_seminorm_center_bound (stateGrading S (n + 7))
      ((le_add_of_nonneg_right (abs_nonneg z.2)).trans hsmall)
  have hq : |z.2| ≤ 1 := (le_add_of_nonneg_left
    (apply_nonneg (stateGrading S (n + 7)) (z.1 - C.referenceState))).trans hsmall
  have hp : (r, θ) ∈ annularOpen D := ⟨hr, mem_univ θ⟩
  have hu := n06_actualRootNormalizedCoordinates_contDiff hN01.1.1 hT hS z
  have hv := n06_actualRootNormalizedCoordinates_contDiff hN01.1.1 hT hS (z.1, 0)
  have hbound := hcomposition
    (n06ActualRootNormalizedCoordinates D S z)
    (n06ActualRootNormalizedCoordinates D S (z.1, 0)) (r, θ) |z.2|
    hu.contDiffAt hv.contDiffAt (abs_nonneg _)
    (fun k hk => hpacket z hstate hq k hk (r, θ) hp)
    (fun k hk => hpacket (z.1, 0) hstate (by norm_num) k hk (r, θ) hp)
    (fun k _ => n06_actualRootNormalizedCoordinates_parameter_jet_difference
      hN01.1.1 hT hS z k (r, θ))
    (n06_actualRootNormalized_denominators_segment_lower hT hS hN01 hz hs hr hroot θ)
  have hgerm := n06_physicalRootFields_germ_eq_normalized hT hS hN01 hz hr hroot θ
  have he := (hgerm.iteratedFDeriv ℝ n).eq_of_nhds
  rw [n06_rootNormalizedFields_zero_parameter] at hbound
  exact (congrArg (fun A => ‖A - iteratedFDeriv ℝ n
    (fun _ : PolarPoint => ((0, 1) : PolarPoint)) (r, θ)‖) he).trans_le hbound

end ContinuousFlexibility.Statements
