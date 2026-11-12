import ContinuousFlexibility.Analysis.N06NormalizerCompatibility
import ContinuousFlexibility.Analysis.N06CurrentCompactSources

/-!
# The old inverse supplies the actual normalizer-change direction

The difference of the two normalized physical sources is compact and
smooth. Its canonical source is realized in every original weight and
angular level, all with the same L2 sequence. The old inverse's lambda
coordinate is zero by the physical compatibility identity.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}

theorem n06_height_sub_compact_support
    {u v : (S.height (3 / 4 : ℝ)).Space}
    (hu : HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode u))
    (hv : HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode v)) :
    HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode (u - v)) := by
  obtain ⟨I, hI, hID, hIzero⟩ := hu
  obtain ⟨J, hJ, hJD, hJzero⟩ := hv
  refine ⟨I ∪ J, hI.union hJ, union_subset hID hJD, ?_⟩
  intro r hr θ
  have hrI : r ∉ I := fun h => hr (Or.inl h)
  have hrJ : r ∉ J := fun h => hr (Or.inr h)
  simp only [map_sub, Pi.sub_apply, hIzero r hrI θ, hJzero r hrJ θ, sub_self]

theorem n06Volume_exists_compact_height_source
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hV : IsVolumeModel T S K V)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (u : (S.height (3 / 4 : ℝ)).Space)
    (hcompact : HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode u))
    (γ t : ℝ) (s : ℕ) :
    ∃ F : V.level γ t s,
      ∀ m, (V.forget γ t s F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m ((S.height (3 / 4 : ℝ)).decode u) := by
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hu := (hS.1 (3 / 4 : ℝ)).2.2.2.1 u
  exact n06Volume_exists_current_compact_source h01.1.1 h01.2.2.2.1
    hT hV h04 hcoordinates href hsector
    γ t s (physical_height_contDiff_and_flatJets hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) u).1 hu.2.2.1 (fun p => hu.2.1 p.1 p.2) hcompact

/-- One and the same canonical L2 sequence lies in every source level;
this is stronger than independently selecting unrelated representatives. -/
theorem n06Volume_compact_height_source_all_levels
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hV : IsVolumeModel T S K V)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (u : (S.height (3 / 4 : ℝ)).Space)
    (hcompact : HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode u))
    {F : CanonicalSequence S K}
    (hF : ∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K (C.referenceState, 0) m ((S.height (3 / 4 : ℝ)).decode u))
    (γ t : ℝ) (s : ℕ) : VolumeMember S K V γ t s F := by
  obtain ⟨G, hG⟩ := n06Volume_exists_compact_height_source
    hT hS hV h01 h04 hcoordinates u hcompact γ t s
  refine ⟨G, funext (fun m => ?_)⟩
  exact Lp.ext ((hG m).trans (hF m).symm)

/-- The correction source is constructed from the actual two normalizers.
Its old-inverse direction has zero compatibility coordinate and retains
all source weights and angular orders needed for N05 transport. -/
theorem n06_exists_normalizer_change_source
    {b : ℕ} {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (h05 : N05Properties D T S C K V b B)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (ψ : (S.height (3 / 4 : ℝ)).Space)
    (hcompact : HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode ψ))
    (hunit : S.Q ψ = 1) :
    ∃ d : V.level (3 / 4 : ℝ) 0 b,
      (∀ m, (V.forget (3 / 4 : ℝ) 0 b d m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
          ((S.height (3 / 4 : ℝ)).decode (S.psi - ψ))) ∧
      (B.inverse d).val.1.2.2.2 = 0 ∧
      ∀ γ t : ℝ, ∀ s : ℕ,
        VolumeMember S K V γ t s (V.forget (3 / 4 : ℝ) 0 b d) := by
  have hV : IsVolumeModel T S K V := h05.2.1
  have hc := n06_height_sub_compact_support hS.2.2.2.2.2.2.2.2.1 hcompact
  obtain ⟨d, hd⟩ := n06Volume_exists_compact_height_source
    hT hS hV h01 h04 hcoordinates (S.psi - ψ) hc (3 / 4 : ℝ) 0 b
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hlambda := n06N05_inverse_lambda_eq_Q h01.1.1.choose_spec.1.2.1.le
    hT hS h04 h05 href hsector d (S.psi - ψ) hd
  have hQ : S.Q (S.psi - ψ) = 0 := by
    rw [map_sub, hS.2.2.2.2.2.2.2.2.2.1, hunit, sub_self]
  exact ⟨d, hd, hlambda.trans hQ, fun γ t s =>
    n06Volume_compact_height_source_all_levels hT hS hV h01 h04 hcoordinates
      (S.psi - ψ) hc hd γ t s⟩

end ContinuousFlexibility.Statements
