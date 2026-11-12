import ContinuousFlexibility.Analysis.N06NuCoordinateCompact
import ContinuousFlexibility.Analysis.N06NuFiniteDifference

/-!
# Fixed-seminorm smallness of the actual nu-column jets

The actual frozen nuColumnField has a fixed compact physical support. On
that support its finite formula is smooth along the genuine original
state segment, with N01's discriminant bound. Thus each fixed angular jet
of the actual current-reference difference is linearly small in one
original state seminorm and the real q parameter.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n06_nuColumn_angular_eq_finite_composition
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {r : ℝ} (hr : r ∈ radialCore D) :
    (fun θ => nuColumnField D S C z (r, θ)) =
      n06NuFiniteJetMap ∘ (fun θ => n06ActualNuJetCoordinates D S z (r, θ)) := by
  funext θ
  exact n06_nuColumn_eq_finiteJetMap hT hS hN01 z ⟨hr, mem_univ _⟩

theorem n06_nuColumn_angular_contDiffAt
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r : ℝ} (hr : r ∈ radialCore D)
    (hborder : r ∈ tsupport D.chi) (θ : ℝ) :
    ContDiffAt ℝ ∞ (fun t => nuColumnField D S C z (r, t)) θ := by
  have hrne : r ≠ 0 := (hN01.1.1.choose_spec.1.1.trans hr.1).ne'
  have hpos : 0 < n06NuFiniteDiscriminant (n06ActualNuJetCoordinates D S z (r, θ)) :=
    lt_of_lt_of_le (by norm_num)
      (n06_actualNuJetDiscriminant_lower hT hS hN01 hz hs ⟨hr, mem_univ _⟩ hborder)
  rw [n06_nuColumn_angular_eq_finite_composition hT hS hN01 z hr]
  exact (n06NuFiniteJetMap_contDiffAt hpos).comp θ
    (n06_actualNuJetCoordinates_angular_contDiff hT hS z hrne).contDiffAt

theorem n06_nuColumn_angularDifference_eq_finite_composition
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (n : ℕ) {p : PolarPoint}
    (hp : p ∈ annularOpen D) (hborder : p.1 ∈ tsupport D.chi) :
    |mixedDerivative 0 n (fun q => nuColumnField D S C z q -
        nuColumnField D S C (C.referenceState, 0) q) p| =
      ‖iteratedDeriv n
          (n06NuFiniteJetMap ∘ (fun θ => n06ActualNuJetCoordinates D S z (p.1, θ))) p.2 -
        iteratedDeriv n
          (n06NuFiniteJetMap ∘ (fun θ =>
            n06ActualNuJetCoordinates D S (C.referenceState, 0) (p.1, θ))) p.2‖ := by
  have hzSmooth := n06_nuColumn_angular_contDiffAt hT hS hN01 hz hs hp.1 hborder p.2
  have hrSmooth := n06_nuColumn_angular_contDiffAt hT hS hN01
    (n05_referenceState_mem hN01.2.1) (n05_referenceState_sector hN01.2.2.1)
    hp.1 hborder p.2
  change |iteratedDeriv n (fun θ => nuColumnField D S C z (p.1, θ) -
    nuColumnField D S C (C.referenceState, 0) (p.1, θ)) p.2| = _
  rw [iteratedDeriv_fun_sub (hzSmooth.of_le (by simp)) (hrSmooth.of_le (by simp)),
    n06_nuColumn_angular_eq_finite_composition hT hS hN01 z hp.1,
    n06_nuColumn_angular_eq_finite_composition hT hS hN01 (C.referenceState, 0) hp.1,
    Real.norm_eq_abs]

def N06NuAngularDifferenceBound (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) (n : ℕ) (Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ,
      z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
      stateGrading S (n + 4) (z.1 - C.referenceState) + |z.2| ≤ 1 →
      ∀ p ∈ annularOpen D,
        |mixedDerivative 0 n (fun q => nuColumnField D S C z q -
          nuColumnField D S C (C.referenceState, 0) q) p| ≤
            Q * (stateGrading S (n + 4) (z.1 - C.referenceState) + |z.2|)

/-- The fixed order is explicit: n+4 in the original state grading.
The radius-one condition only fixes a bounded packet of input jets; the
linear difference factor is retained in the conclusion. -/
theorem n06_nuColumn_angularDifference_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06NuAngularDifferenceBound D S C base ε n Q := by
  have hpacket : ∃ L M : ℝ, 1 ≤ L ∧ 0 ≤ M ∧
      N06NuCoordinatesNearFixedState D S C.referenceState n L M :=
    n06_actualNuJetCoordinates_near_fixed_state (D := D) (T := T) (S := S)
      hN01.1.1 hT hS hN01.1.2.2.2.1.1 C.referenceState n
  obtain ⟨L, M, hL, hM, hcoords⟩ := hpacket
  obtain ⟨Q, hQ, hfinite⟩ := n06NuFiniteJetMap_composition_difference_bound n hM
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  refine ⟨Q * L, mul_nonneg hQ hL₀, ?_⟩
  intro z hz hs hsmall p hp
  let P : ℝ := stateGrading S (n + 4) (z.1 - C.referenceState) + |z.2|
  have hP : 0 ≤ P := add_nonneg (apply_nonneg _ _) (abs_nonneg _)
  by_cases hborder : p.1 ∈ tsupport D.chi
  · let u : ℝ → N06NuJetCoordinates := fun θ => n06ActualNuJetCoordinates D S z (p.1, θ)
    let v : ℝ → N06NuJetCoordinates := fun θ =>
      n06ActualNuJetCoordinates D S (C.referenceState, 0) (p.1, θ)
    have hrne : p.1 ≠ 0 := (hN01.1.1.choose_spec.1.1.trans hp.1.1).ne'
    have hu : ContDiffAt ℝ ∞ u p.2 :=
      (n06_actualNuJetCoordinates_angular_contDiff hT hS z hrne).contDiffAt
    have hv : ContDiffAt ℝ ∞ v p.2 :=
      (n06_actualNuJetCoordinates_angular_contDiff hT hS (C.referenceState, 0) hrne).contDiffAt
    have hU (k : ℕ) (hk : k ≤ n) : ‖iteratedDeriv k u p.2‖ ≤ M :=
      (hcoords z hsmall k hk p.1 hp.1 p.2).1
    have hV (k : ℕ) (hk : k ≤ n) : ‖iteratedDeriv k v p.2‖ ≤ M :=
      (hcoords z hsmall k hk p.1 hp.1 p.2).2.1
    have hUV (k : ℕ) (hk : k ≤ n) :
        ‖iteratedDeriv k u p.2 - iteratedDeriv k v p.2‖ ≤ L * P :=
      (hcoords z hsmall k hk p.1 hp.1 p.2).2.2
    have hdisc : ∀ w ∈ segment ℝ (v p.2) (u p.2),
        (1 / 2 : ℝ) ≤ n06NuFiniteDiscriminant w :=
      n06_actualNuJetDiscriminant_segment_lower hT hS hN01 hz hs hp hborder
    have h := hfinite u v p.2 (L * P) hu hv (mul_nonneg hL₀ hP) hU hV hUV hdisc
    exact (n06_nuColumn_angularDifference_eq_finite_composition hT hS hN01 hz hs n hp hborder).trans_le
      (h.trans_eq (mul_assoc Q L P).symm)
  · have hzero : (fun θ => nuColumnField D S C z (p.1, θ) -
        nuColumnField D S C (C.referenceState, 0) (p.1, θ)) = (fun _ : ℝ => 0) := by
      funext θ
      rw [n06_nuColumn_zero_off_tsupport hT hS hN01 z (p := (p.1, θ)) hborder,
        n06_nuColumn_zero_off_tsupport hT hS hN01 (C.referenceState, 0)
          (p := (p.1, θ)) hborder, sub_self]
    change |iteratedDeriv n (fun θ => nuColumnField D S C z (p.1, θ) -
      nuColumnField D S C (C.referenceState, 0) (p.1, θ)) p.2| ≤ _
    have he := congrArg (fun f : ℝ → ℝ => |iteratedDeriv n f p.2|) hzero
    have hzjet : |iteratedDeriv n (fun θ => nuColumnField D S C z (p.1, θ) -
        nuColumnField D S C (C.referenceState, 0) (p.1, θ)) p.2| = 0 :=
      he.trans (by simp only [iteratedDeriv_fun_const_zero, abs_zero])
    exact hzjet.trans_le (mul_nonneg (mul_nonneg hQ hL₀) hP)

end ContinuousFlexibility.Statements
