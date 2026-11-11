import ContinuousFlexibility.Analysis.ReturnDivergenceBilinear
import ContinuousFlexibility.Analysis.LinearFiberJetExpansion
import ContinuousFlexibility.Analysis.PhysicalJetCompatibility

/-!
# Actual multilinear jets of the independent-residual source

The coefficient tower is combined with the original height pair through
the actual symmetric divergence. The height dependence is linear, so
every positive jet is the sum of one term with the base height and one
term for each height direction. The scalar derivative recurrence is
proved for every weighted spatial jet, including the height product rule.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- Restrict actual coefficient jets to their proved smooth subspace.
The value outside the parameter domain has no effect on derivatives
inside its open domain. -/
def smoothCoefficientJetRestriction
    (U : Set E)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ × ℝ))
    (hA : ∀ n x, x ∈ U → ∀ v,
      ContDiffOn ℝ ∞ (A n x v) (annularOpen D))
    (n : ℕ) (x : E) :
    MultilinearMap ℝ (fun _ : Fin n => E) (annularSmoothCoefficientSpace D) := by
  classical
  exact if hx : x ∈ U then
    (A n x).codRestrict (annularSmoothCoefficientSpace D) (hA n x hx)
    else 0

theorem smoothCoefficientJetRestriction_apply
    (U : Set E)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ × ℝ))
    (hA : ∀ n x, x ∈ U → ∀ v,
      ContDiffOn ℝ ∞ (A n x v) (annularOpen D))
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    (smoothCoefficientJetRestriction U A hA n x v).val = A n x v := by
  classical
  simp only [smoothCoefficientJetRestriction, dif_pos hx]
  rfl

def symmetricSourceJetData
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D)) (x : E) :
    LinearFiberJetData E (HeightPair S) (annularSmoothFieldSpace D) :=
  fun n => (symmetricDivergenceSmoothBilinear hS hT).compMultilinearMap (A n x)

theorem symmetricSourceJetData_apply
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D)) (x : E) (n : ℕ)
    (v : Fin n → E) (η : HeightPair S) :
    (symmetricSourceJetData hS hT A x n v η).val =
      symmetricDivergenceBilinear hS hT (A n x v) η :=
  symmetricDivergenceSmoothBilinear_apply hS hT (A n x v) η

def symmetricSourceSmoothJets
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    (n : ℕ) (z : E × HeightPair S) :
    MultilinearMap ℝ (fun _ : Fin n => E × HeightPair S) (annularSmoothFieldSpace D) :=
  linearFiberJet n (symmetricSourceJetData hS hT A z.1) z.2

def symmetricSourceScalarJets
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    (n : ℕ) (z : E × HeightPair S) :
    MultilinearMap ℝ (fun _ : Fin n => E × HeightPair S) (PolarPoint → ℝ) :=
  (annularSmoothFieldSpace D).subtype.compMultilinearMap
    (symmetricSourceSmoothJets hS hT A n z)

theorem symmetricSourceScalarJets_apply
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    (n : ℕ) (z : E × HeightPair S) (v : Fin n → E × HeightPair S) :
    symmetricSourceScalarJets hS hT A n z v =
      (linearFiberJet n (symmetricSourceJetData hS hT A z.1) z.2 v).val := rfl

theorem symmetricSourceScalarJets_zero
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D)) (z : E × HeightPair S) :
    symmetricSourceScalarJets hS hT A 0 z Fin.elim0 =
      symmetricDivergenceBilinear hS hT (A 0 z.1 Fin.elim0) z.2 := by
  rw [symmetricSourceScalarJets_apply, linearFiberJet_zero_apply,
    symmetricSourceJetData_apply]

theorem symmetricSourceScalarJets_zero_apply
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D)) (z : E × HeightPair S)
    (v : Fin 0 → E × HeightPair S) :
    symmetricSourceScalarJets hS hT A 0 z v =
      symmetricDivergenceBilinear hS hT (A 0 z.1 (fun i => (v i).1)) z.2 := by
  rw [symmetricSourceScalarJets_apply, linearFiberJet_zero_apply,
    symmetricSourceJetData_apply]
  exact congrArg (fun vs : Fin 0 → E => symmetricDivergenceBilinear hS hT (A 0 z.1 vs) z.2)
    (Subsingleton.elim _ _)

theorem symmetricSourceScalarJets_contDiffOn
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    (n : ℕ) (z : E × HeightPair S) (v : Fin n → E × HeightPair S) :
    ContDiffOn ℝ ∞ (symmetricSourceScalarJets hS hT A n z v) (annularOpen D) :=
  (symmetricSourceSmoothJets hS hT A n z v).property

/-- The finite expansion is an equality of actual fields, rather than
an equality of only their formal coefficient expressions. -/
theorem symmetricSourceScalarJets_eq_sum
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    (n : ℕ) (z : E × HeightPair S) (v : Fin (n + 1) → E × HeightPair S) :
    symmetricSourceScalarJets hS hT A (n + 1) z v =
      symmetricDivergenceBilinear hS hT (A (n + 1) z.1 (fun i => (v i).1)) z.2 +
        ∑ i : Fin (n + 1), symmetricDivergenceBilinear hS hT
          (A n z.1 (fun j => (v (i.succAbove j)).1)) (v i).2 := by
  have heq := congrArg ((annularSmoothFieldSpace D).subtype)
    (linearFiberJet_eq_sum n (symmetricSourceJetData hS hT A z.1) z.2 v)
  simpa only [symmetricSourceScalarJets_apply, map_add, map_sum,
    Submodule.subtype_apply, symmetricSourceJetData_apply] using heq

theorem symmetricSourceScalarJets_heightMember
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D)) (x : E)
    (hmember : ∀ n (v : Fin n → E) (η : HeightPair S),
      HeightMember D T (3 / 4 : ℝ) (symmetricDivergenceBilinear hS hT (A n x v) η))
    (n : ℕ) (η : HeightPair S) (v : Fin n → E × HeightPair S) :
    HeightMember D T (3 / 4 : ℝ) (symmetricSourceScalarJets hS hT A n (x, η) v) := by
  let H := S.height (3 / 4 : ℝ)
  let V : Submodule ℝ (annularSmoothFieldSpace D) :=
    H.decode.range.comap (annularSmoothFieldSpace D).subtype
  have hdata : ∀ k (vs : Fin k → E) (ζ : HeightPair S),
      symmetricSourceJetData hS hT A x k vs ζ ∈ V := by
    intro k vs ζ
    change ∃ u : H.Space, H.decode u =
      (symmetricSourceJetData hS hT A x k vs ζ).val
    rw [symmetricSourceJetData_apply]
    exact (hS.1 (3 / 4 : ℝ)).2.2.2.2.1 _ (hmember k vs ζ)
  have hv := linearFiberJet_mem V n (symmetricSourceJetData hS hT A x) hdata η v
  change ∃ u : H.Space, H.decode u =
    (linearFiberJet n (symmetricSourceJetData hS hT A x) η v).val at hv
  obtain ⟨u, hu⟩ := hv
  rw [symmetricSourceScalarJets_apply, ← hu]
  exact (hS.1 (3 / 4 : ℝ)).2.2.2.1 u

section ParameterDerivatives

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The sole coefficient derivative hypothesis concerns its actual
unweighted material pullback. The source derivative is obtained through
spatial calculus and the proved linear-fiber product rule. -/
theorem symmetricSourceScalarJets_hasDerivAt_line
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {U : Set E}
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    (hderiv : ∀ n (x w : E) (v : Fin n → E) (t : ℝ), x + t • w ∈ U →
      MixedJetHasDerivAt
        (fun s p => ((A n (x + s • w) v).val (T.radius p.1, p.2)).1)
        (fun p => ((A (n + 1) (x + t • w) (Fin.cons w v)).val
          (T.radius p.1, p.2)).1) t ∧
      MixedJetHasDerivAt
        (fun s p => ((A n (x + s • w) v).val (T.radius p.1, p.2)).2)
        (fun p => ((A (n + 1) (x + t • w) (Fin.cons w v)).val
          (T.radius p.1, p.2)).2) t)
    (n : ℕ) (z w : E × HeightPair S) (v : Fin n → E × HeightPair S)
    (t : ℝ) (ht : z + t • w ∈ U ×ˢ (univ : Set (HeightPair S)))
    (a b c : ℕ) (p : PolarPoint) :
    HasDerivAt (fun s => weightedPhysicalJet T (3 / 4 : ℝ) a b c
      (symmetricSourceScalarJets hS hT A n (z + s • w) v) p)
      (weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (symmetricSourceScalarJets hS hT A (n + 1) (z + t • w) (Fin.cons w v)) p) t := by
  let Q : annularSmoothFieldSpace D →ₗ[ℝ] ℝ :=
    (LinearMap.proj p).comp (annularWeightedJetLinear hT (3 / 4 : ℝ) a b c)
  let F (s : ℝ) := symmetricSourceJetData hS hT A (z.1 + s • w.1)
  have hF : ∀ k (vs : Fin k → E) (η : HeightPair S),
      HasDerivAt (fun s => Q (F s k vs η))
        (Q (linearFiberHead (F t) w k vs η)) t := by
    intro k vs η
    have hc := hderiv k z.1 w.1 vs t ht.1
    have hd := symmetricDivergenceBilinear_physicalJetHasDerivAt
      (γ := (3 / 4 : ℝ)) hS hT
      (fun s => A k (z.1 + s • w.1) vs)
      (A (k + 1) (z.1 + t • w.1) (Fin.cons w.1 vs)) η hc.1 hc.2
    have heq (s : ℝ) : Q (F s k vs η) =
        weightedPhysicalJet T (3 / 4 : ℝ) a b c
          (symmetricDivergenceBilinear hS hT (A k (z.1 + s • w.1) vs) η) p := by
      change weightedPhysicalJet T (3 / 4 : ℝ) a b c (F s k vs η).val p = _
      rw [symmetricSourceJetData_apply]
    have hnext : Q (linearFiberHead (F t) w k vs η) =
        weightedPhysicalJet T (3 / 4 : ℝ) a b c
          (symmetricDivergenceBilinear hS hT
            (A (k + 1) (z.1 + t • w.1) (Fin.cons w.1 vs)) η) p := by
      rw [linearFiberHead_apply]
      change weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (F t (k + 1) (Fin.cons w.1 vs) η).val p = _
      rw [symmetricSourceJetData_apply]
    simpa only [heq, hnext] using hd.weighted a b c p
  have hd := hasDerivAt_linearFiberJet_affine Q n F z.2 w hF v
  change HasDerivAt
    (fun s => Q (linearFiberJet n (F s) (z.2 + s • w.2) v))
    (Q (linearFiberJet (n + 1) (F t) (z.2 + t • w.2) (Fin.cons w v))) t
  exact hd

/-- Smooth codomain restriction preserves the real material parameter
derivatives on the original open set. -/
theorem smoothCoefficientJetRestriction_hasDerivAt_line
    {U : Set E} (hU : IsOpen U)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ × ℝ))
    (hA : ∀ n x, x ∈ U → ∀ v,
      ContDiffOn ℝ ∞ (A n x v) (annularOpen D))
    (hderiv : ∀ n (x w : E) (v : Fin n → E) (t : ℝ), x + t • w ∈ U →
      MixedJetHasDerivAt
        (fun s p => (A n (x + s • w) v (T.radius p.1, p.2)).1)
        (fun p => (A (n + 1) (x + t • w) (Fin.cons w v) (T.radius p.1, p.2)).1) t ∧
      MixedJetHasDerivAt
        (fun s p => (A n (x + s • w) v (T.radius p.1, p.2)).2)
        (fun p => (A (n + 1) (x + t • w) (Fin.cons w v) (T.radius p.1, p.2)).2) t)
    (n : ℕ) (x w : E) (v : Fin n → E) (t : ℝ) (ht : x + t • w ∈ U) :
    MixedJetHasDerivAt
      (fun s p => ((smoothCoefficientJetRestriction U A hA n (x + s • w) v).val
        (T.radius p.1, p.2)).1)
      (fun p => ((smoothCoefficientJetRestriction U A hA (n + 1) (x + t • w)
        (Fin.cons w v)).val (T.radius p.1, p.2)).1) t ∧
    MixedJetHasDerivAt
      (fun s p => ((smoothCoefficientJetRestriction U A hA n (x + s • w) v).val
        (T.radius p.1, p.2)).2)
      (fun p => ((smoothCoefficientJetRestriction U A hA (n + 1) (x + t • w)
        (Fin.cons w v)).val (T.radius p.1, p.2)).2) t := by
  have hnear : ∀ᶠ s in 𝓝 t, x + s • w ∈ U :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
      (hU.mem_nhds ht)
  have hd := hderiv n x w v t ht
  constructor
  · apply hd.1.congr
    · filter_upwards [hnear] with s hs
      rw [smoothCoefficientJetRestriction_apply U A hA n _ hs v]
    · rw [smoothCoefficientJetRestriction_apply U A hA (n + 1) _ ht (Fin.cons w v)]
  · apply hd.2.congr
    · filter_upwards [hnear] with s hs
      rw [smoothCoefficientJetRestriction_apply U A hA n _ hs v]
    · rw [smoothCoefficientJetRestriction_apply U A hA (n + 1) _ ht (Fin.cons w v)]

end ParameterDerivatives

end ContinuousFlexibility.Statements
