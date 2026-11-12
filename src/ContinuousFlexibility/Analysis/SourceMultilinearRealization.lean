import ContinuousFlexibility.Analysis.PhysicalTopology
import ContinuousFlexibility.Analysis.CircleMultilinearRealization

/-!
# Continuous multilinear realization in the physical source kernel

Every scalar jet is realized in the supplied height model and its actual
compatibility kernel. The physical norm identity and a product seminorm
bound prove continuity in each coordinate of the given projective limit.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Filter ContinuousFlexibility.Analysis
open scoped Topology BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {n : ℕ}

def liftSourceMultilinear (hS : IsPhysicalSpaces D T S)
    (A : MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hA : ∀ v, HeightMember D T (3 / 4 : ℝ) (A v))
    (hcompat : ∀ v, physicalSourceIntegral D (A v) = 0) :
    MultilinearMap ℝ (fun _ : Fin n => E) S.Source where
  toFun v := physicalSourceRealize hS (A v) (hA v) (hcompat v)
  map_update_add' v i x y := by
    apply physicalSourceDecode_injective hS
    simp only [map_add, physicalSourceRealize_decode, A.map_update_add]
  map_update_smul' v i c x := by
    apply physicalSourceDecode_injective hS
    simp only [map_smul, physicalSourceRealize_decode, A.map_update_smul]

theorem liftSourceMultilinear_decode (hS : IsPhysicalSpaces D T S)
    (A : MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hA : ∀ v, HeightMember D T (3 / 4 : ℝ) (A v))
    (hcompat : ∀ v, physicalSourceIntegral D (A v) = 0) (v : Fin n → E) :
    physicalSourceDecode S (liftSourceMultilinear hS A hA hcompat v) = A v :=
  physicalSourceRealize_decode hS (A v) (hA v) (hcompat v)

theorem liftSourceMultilinear_continuous
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hS : IsPhysicalSpaces D T S)
    (A : MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hA : ∀ v, HeightMember D T (3 / 4 : ℝ) (A v))
    (hcompat : ∀ v, physicalSourceIntegral D (A v) = 0)
    (hbound : ∀ s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧
      ∀ v : Fin n → E, physicalNorm T (3 / 4 : ℝ) s (A v) ≤ B * ∏ i, p (v i)) :
    Continuous (liftSourceMultilinear hS A hA hcompat) := by
  let M := liftSourceMultilinear hS A hA hcompat
  have hn : ∀ u : (S.height (3 / 4 : ℝ)).Space, ∀ s,
      ‖u.val s‖ = physicalNorm T (3 / 4 : ℝ) s ((S.height (3 / 4 : ℝ)).decode u) :=
    (hS.1 (3 / 4 : ℝ)).2.2.2.2.2.2.2
  have hcoordinate (s : ℕ) : Continuous (fun v => (M v).val.val s) := by
    obtain ⟨p, B, hp, hb⟩ := hbound s
    let Q := (projectiveCoordinate (fun j => (S.height (3 / 4 : ℝ)).level j)
      (S.height (3 / 4 : ℝ)).bond s).comp S.Q.toLinearMap.ker.subtypeL
    let L := Q.toLinearMap.compMultilinearMap M
    apply continuous_multilinear_of_seminorm_bound L p hp B
    intro v
    change ‖(M v).val.val s‖ ≤ _
    rw [hn]
    change physicalNorm T (3 / 4 : ℝ) s (physicalSourceDecode S (M v)) ≤ _
    rw [liftSourceMultilinear_decode]
    exact hb v
  apply continuous_iff_continuousAt.mpr
  intro v
  rw [ContinuousAt, tendsto_subtype_rng, tendsto_projectiveLimit_iff]
  exact fun s => (hcoordinate s).tendsto v

def liftSourceContinuousMultilinear
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hS : IsPhysicalSpaces D T S)
    (A : MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hA : ∀ v, HeightMember D T (3 / 4 : ℝ) (A v))
    (hcompat : ∀ v, physicalSourceIntegral D (A v) = 0)
    (hbound : ∀ s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧
      ∀ v : Fin n → E, physicalNorm T (3 / 4 : ℝ) s (A v) ≤ B * ∏ i, p (v i)) :
    E [×n]→L[ℝ] S.Source :=
  { liftSourceMultilinear hS A hA hcompat with
    cont := liftSourceMultilinear_continuous hS A hA hcompat hbound }

theorem liftSourceContinuousMultilinear_decode
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hS : IsPhysicalSpaces D T S)
    (A : MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hA : ∀ v, HeightMember D T (3 / 4 : ℝ) (A v))
    (hcompat : ∀ v, physicalSourceIntegral D (A v) = 0)
    (hbound : ∀ s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧
      ∀ v : Fin n → E, physicalNorm T (3 / 4 : ℝ) s (A v) ≤ B * ∏ i, p (v i))
    (v : Fin n → E) :
    physicalSourceDecode S (liftSourceContinuousMultilinear hS A hA hcompat hbound v) = A v :=
  liftSourceMultilinear_decode hS A hA hcompat v

end ContinuousFlexibility.Statements
