import ContinuousFlexibility.Analysis.SpacesCircleRetraction
import ContinuousFlexibility.Analysis.SpacesCircleParity
import ContinuousFlexibility.Analysis.SpacesPhysicalProduct
import ContinuousFlexibility.Analysis.SpacesTameStructure
import ContinuousFlexibility.Analysis.SpacesTraceExtensionModels
import ContinuousFlexibility.Analysis.SpacesSources
import ContinuousFlexibility.Analysis.SpacesReciprocal

/-!
# Assembly of the exact weighted spaces

The canonical weak-jet models carry all the prescribed decoded operations.
This assembly keeps the two analytic inputs, physical shell retraction and
smooth scalar composition, explicit until their concrete constructions are
supplied. All other clauses are the exact clauses of `IsPhysicalSpaces`.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem spaces_sample_weight_bounds {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    (∀ m, 1 ≤ T.M (T.sample m)) ∧ (∀ m, 0 < T.H (T.sample m)) := by
  obtain ⟨_, hD⟩ := hD
  have hcells : ∀ m, D.cells m ⊆ radialCore D := hD.2.1.2.2.2.1
  rcases hT with ⟨_, hpos, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _, _⟩
  have hsample (m : ℕ) : T.sample m ∈ Ioo D.a D.b := hcells m (hs m)
  exact ⟨fun m => (hpos _ (hsample m)).2.2.2, fun m => (hpos _ (hsample m)).2.1⟩

theorem spaces_canonicalCircle_tame_structure (hH01 : H01Statement)
    (T : MaterialData) (hM0 : ∀ m, 0 < T.M (T.sample m))
    (hM1 : ∀ m, 1 ≤ T.M (T.sample m)) (γ : ℝ) :
    TameRetraction (canonicalCircleModelData T hM0 γ).grading modelGrading ∧
      HasSmoothing (canonicalCircleModelData T hM0 γ).grading ∧
      HasInterpolation (canonicalCircleModelData T hM0 γ).grading := by
  have hR := canonicalCircleModel_tameRetraction T hM0 hM1 γ
  exact ⟨hR, spaces_tameStructure_of_retraction hH01
    (fun s => ↥(circleJetClosedSubmodule T s)) (circleJetBond T hM0) hR⟩

theorem spaces_circle_parity_clause {T : MaterialData} {γ : ℝ} {C : CircleModelData}
    (hC : IsCircleModel T γ C) :
    ∃ even odd : C.Space →L[ℝ] C.Space,
      (∀ u m θ, C.decode (even u) m θ = (C.decode u m θ + C.decode u m (-θ)) / 2) ∧
      (∀ u m θ, C.decode (odd u) m θ = (C.decode u m θ - C.decode u m (-θ)) / 2) ∧
      (∀ u, even (even u) = even u ∧ odd (odd u) = odd u) ∧
      (∃ loss base, Analysis.IsTameLinear C.grading C.grading even.toLinearMap loss base) ∧
      (∃ loss base, Analysis.IsTameLinear C.grading C.grading odd.toLinearMap loss base) := by
  refine ⟨circleModelEvenProjection hC, circleModelOddProjection hC,
    circleModelEvenProjection_decode hC, circleModelOddProjection_decode hC, ?_,
    ⟨0, 0, circleModelEvenProjection_isTame hC⟩,
    ⟨0, 0, circleModelOddProjection_isTame hC⟩⟩
  intro u
  exact ⟨circleModelEvenProjection_idempotent hC u, circleModelOddProjection_idempotent hC u⟩

/-- Assemble the exact W02 witness from the concrete physical analytic inputs. -/
theorem spaces_exists_physical_spaces_of_composition {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hH01 : H01Statement)
    (hR : TameRetraction (spacesPhysicalGrading hT) modelGrading)
    (hcomp : HasInterpolation (spacesPhysicalGrading hT) →
      ∀ γ : ℝ, 0 < γ → ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → F 0 = 0 →
        ∃ base : ℕ, ∃ ε : ℝ, 0 < ε ∧
          ∃ comp : PhysicalJetProjectiveLimit hT → PhysicalJetProjectiveLimit hT,
            (∀ u, spacesPhysicalGrading hT base u < ε → ∀ p,
              spacesPhysicalDecoded hT γ (comp u) p = F (spacesPhysicalDecoded hT γ u p)) ∧
            SmoothTameOn (spacesPhysicalGrading hT) (spacesPhysicalGrading hT)
              {u | spacesPhysicalGrading hT base u < ε} comp) :
    ∃ S : PhysicalSpacesData, IsPhysicalSpaces D T S := by
  obtain ⟨hM1, hHsample⟩ := spaces_sample_weight_bounds hD hT
  let hM0 : ∀ m, 0 < T.M (T.sample m) := fun m => zero_lt_one.trans_le (hM1 m)
  let H : ℝ → SobolevModelData := canonicalSobolevModelData hT
  let C : ℝ → CircleModelData := canonicalCircleModelData T hM0
  have hH (γ : ℝ) : IsSobolevModel D T γ (H γ) :=
    isSobolevModel_canonicalSobolevModelData hT γ
  have hC (γ : ℝ) : IsCircleModel T γ (C γ) :=
    isCircleModel_canonicalCircleModelData hM0 hHsample γ
  have hSI := spaces_tameStructure_of_retraction hH01
    (fun s => ↥(physicalJetClosedSubmodule hT s)) (physicalJetBond hT) hR
  have hI : HasInterpolation (spacesPhysicalGrading hT) := hSI.2
  obtain ⟨χ, hχ⟩ := spaces_exists_cutoff_of_accumulating hD
  obtain ⟨ψ, hψ, hQψ⟩ := spaces_source_normalizer hT (hH (3 / 4)) hD
  let S : PhysicalSpacesData :=
    { height := H
      circle := C
      chiLeft := χ
      Q := spacesSourceFunctional hT (hH (3 / 4))
      psi := ψ }
  refine ⟨S, hH, hC, hχ, ?_, ?_, ?_, ?_, ?_, hψ, hQψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro γ
    exact ⟨hR, hSI⟩
  · intro γ
    exact spaces_canonicalCircle_tame_structure hH01 T hM0 hM1 γ
  · intro γ δ
    refine ⟨fun z => spacesPhysicalMultiply hT γ δ z.1 z.2, ?_, ?_⟩
    · intro u v p
      exact congrFun (spacesPhysicalMultiply_decode hT γ δ u v) p
    · exact spacesPhysicalMultiply_smoothTame hT hH01 hI γ δ
  · intro γ
    exact spaces_trace_split_tame (S := S) hD hT (hH γ) (hC γ)
  · intro f
    exact spacesSourceFunctional_apply hT (hH (3 / 4)) f
  · exact ⟨0, 2, spacesSourceLinear_isTame hT (hH (3 / 4))⟩
  · obtain ⟨P, hP, hPQ, hPid, htame⟩ := spaces_source_projection hT (hH (3 / 4)) ψ hQψ
    exact ⟨P, hP, hPQ, hPid, 0, 2, htame⟩
  · intro γ hγ
    exact spaces_reciprocal_of_composition hT hγ (hH γ) (hcomp hI γ hγ)
  · intro γ hγ F hF hF0
    exact hcomp hI γ hγ F hF hF0
  · intro γ
    exact spaces_circle_parity_clause (hC γ)

end ContinuousFlexibility.Statements
