import ContinuousFlexibility.Analysis.PhysicalTopology
import ContinuousFlexibility.Analysis.TameMultilinearNormalization

/-!
# Homogeneous normalization in the actual physical height model

A scalar multilinear field whose values belong to the given physical
model lifts algebraically through its injective decoder. Every actual
physical norm is the norm of one coordinate of that lift. Unit-ball
growth therefore yields the exact one-high-factor estimate before any
continuity of the multilinear map is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {D : ReferenceData} {T : MaterialData} {H : SobolevModelData} {γ : ℝ} {k : ℕ}

def liftHeightMultilinear
    (hH : IsSobolevModel D T γ H)
    (A : MultilinearMap ℝ (fun _ : Fin k => E) (PolarPoint → ℝ))
    (hA : ∀ v, HeightMember D T γ (A v)) :
    MultilinearMap ℝ (fun _ : Fin k => E) H.Space where
  toFun v := heightRealize hH (A v) (hA v)
  map_update_add' v i x y := by
    apply hH.2.2.2.2.2.1
    simp only [map_add, heightRealize_decode, A.map_update_add]
  map_update_smul' v i c x := by
    apply hH.2.2.2.2.2.1
    simp only [map_smul, heightRealize_decode, A.map_update_smul]

theorem liftHeightMultilinear_decode
    (hH : IsSobolevModel D T γ H)
    (A : MultilinearMap ℝ (fun _ : Fin k => E) (PolarPoint → ℝ))
    (hA : ∀ v, HeightMember D T γ (A v)) (v : Fin k → E) :
    H.decode (liftHeightMultilinear hH A hA v) = A v :=
  heightRealize_decode hH (A v) (hA v)

theorem physicalNorm_multilinear_bound_of_unitBall
    (hH : IsSobolevModel D T γ H)
    (A : MultilinearMap ℝ (fun _ : Fin k => E) (PolarPoint → ℝ))
    (hA : ∀ v, HeightMember D T γ (A v)) (s : ℕ)
    (low high : Seminorm ℝ E) {C a : ℝ} (hC : 0 ≤ C)
    (hlocal : ∀ v : Fin k → E, (∀ i, low (v i) < 1) →
      physicalNorm T γ s (A v) ≤ C * (a + ∑ i, high (v i))) :
    ∀ v : Fin k → E, physicalNorm T γ s (A v) ≤
      C * multilinearTameSize low high k a v := by
  let L := liftHeightMultilinear hH A hA
  let q : Seminorm ℝ H.Space := (normSeminorm ℝ (H.level s)).comp
    (projectiveCoordinate (fun j => H.level j) H.bond s).toLinearMap
  have hq (v : Fin k → E) : q (L v) = physicalNorm T γ s (A v) := by
    change ‖(L v).val s‖ = physicalNorm T γ s (A v)
    exact (hH.2.2.2.2.2.2.2 (L v) s).trans
      (congrArg (physicalNorm T γ s) (liftHeightMultilinear_decode hH A hA v))
  have hb := multilinearMap_bound_of_unitBall L q low high hC
    (fun v hv => (hq v).trans_le (hlocal v hv))
  intro v
  exact (hq v).symm.trans_le (hb v)

end ContinuousFlexibility.Statements
