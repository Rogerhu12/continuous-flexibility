module

public import ContinuousFlexibility.Analysis.SourceMultilinearRealization
public import ContinuousFlexibility.Analysis.PhysicalTaylorDifferentiation
public import ContinuousFlexibility.Analysis.ProjectiveJetContinuity

/-!
# Actual source-valued smooth towers from weighted scalar jets

The weighted second variations dominate the full projective difference
quotient. Coordinate mean value estimates then give joint continuity in
the base point and all directions, inside the original source kernel.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {U : Set E}

def SourceJetNormBounds
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ)) : Prop :=
  ∀ n s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
    ∀ x ∈ U, ∀ v : Fin n → E,
      physicalNorm T (3 / 4 : ℝ) s (A n x v) ≤ B * (1 + p x) * ∏ i, p (v i)

def sourceJetLift (hS : IsPhysicalSpaces D T S)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, HeightMember D T (3 / 4 : ℝ) (A n x v))
    (hcompat : ∀ n x, x ∈ U → ∀ v, physicalSourceIntegral D (A n x v) = 0)
    (hbound : SourceJetNormBounds (T := T) (U := U) A)
    (n : ℕ) (x : E) : E [×n]→L[ℝ] S.Source := by
  classical
  exact if hx : x ∈ U then
    liftSourceContinuousMultilinear hS (A n x) (hmember n x hx) (hcompat n x hx) (by
      intro s
      obtain ⟨p, B, hp, hB, hb⟩ := hbound n s
      exact ⟨p, B * (1 + p x), hp, hb x hx⟩)
    else 0

theorem sourceJetLift_decode (hS : IsPhysicalSpaces D T S)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, HeightMember D T (3 / 4 : ℝ) (A n x v))
    (hcompat : ∀ n x, x ∈ U → ∀ v, physicalSourceIntegral D (A n x v) = 0)
    (hbound : SourceJetNormBounds (T := T) (U := U) A)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    physicalSourceDecode S (sourceJetLift hS A hmember hcompat hbound n x v) = A n x v := by
  classical
  simp only [sourceJetLift, dif_pos hx]
  exact liftSourceContinuousMultilinear_decode hS (A n x)
    (hmember n x hx) (hcompat n x hx) _ v

theorem sourceJetLift_coordinate_bound (hS : IsPhysicalSpaces D T S)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, HeightMember D T (3 / 4 : ℝ) (A n x v))
    (hcompat : ∀ n x, x ∈ U → ∀ v, physicalSourceIntegral D (A n x v) = 0)
    (hbound : SourceJetNormBounds (T := T) (U := U) A) :
    ∀ n s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
      ∀ x ∈ U, ∀ v : Fin n → E,
        ‖(sourceJetLift hS A hmember hcompat hbound n x v).val.val s‖ ≤
          B * (1 + p x) * ∏ i, p (v i) := by
  have hn : ∀ u : (S.height (3 / 4 : ℝ)).Space, ∀ s,
      ‖u.val s‖ = physicalNorm T (3 / 4 : ℝ) s ((S.height (3 / 4 : ℝ)).decode u) :=
    (hS.1 (3 / 4 : ℝ)).2.2.2.2.2.2.2
  intro n s
  obtain ⟨p, B, hp, hB, hb⟩ := hbound n s
  refine ⟨p, B, hp, hB, ?_⟩
  intro x hx v
  rw [hn]
  change physicalNorm T (3 / 4 : ℝ) s
    (physicalSourceDecode S (sourceJetLift hS A hmember hcompat hbound n x v)) ≤ _
  rw [sourceJetLift_decode hS A hmember hcompat hbound n x hx v]
  exact hb x hx v

def SourceJetSecondEnvelopes
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ)) : Prop :=
  ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
    ∃ δ : ℝ, 0 < δ ∧ (∀ t : ℝ, |t| < δ → x + t • w ∈ U) ∧
      ∀ a b c, ∃ G : PolarPoint → ℝ,
        MemLp G 2 materialCylinderMeasure ∧ (∀ p, 0 ≤ G p) ∧
          ∀ t : ℝ, |t| < δ → ∀ p,
            |weightedPhysicalJet T (3 / 4 : ℝ) a b c
              (A (n + 2) (x + t • w) (Fin.cons w (Fin.cons w v))) p| ≤ G p

theorem sourceJetLift_hasProjectiveLineDerivAt
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hU : IsOpen U)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, HeightMember D T (3 / 4 : ℝ) (A n x v))
    (hcompat : ∀ n x, x ∈ U → ∀ v, physicalSourceIntegral D (A n x v) = 0)
    (hbound : SourceJetNormBounds (T := T) (U := U) A)
    (hscalar : ∀ n (x w : E) (v : Fin n → E) (t : ℝ), x + t • w ∈ U → ∀ a b c p,
      HasDerivAt (fun u => weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (A n (x + u • w) v) p)
        (weightedPhysicalJet T (3 / 4 : ℝ) a b c
          (A (n + 1) (x + t • w) (Fin.cons w v)) p) t)
    (henergy : SourceJetSecondEnvelopes (T := T) (U := U) A)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) (w : E) :
    HasProjectiveLineDerivAt
      (fun y => sourceJetLift hS A hmember hcompat hbound n y v)
      (sourceJetLift hS A hmember hcompat hbound (n + 1) x (Fin.cons w v)) x w := by
  let L := sourceJetLift hS A hmember hcompat hbound
  obtain ⟨δ, hδ, hmem, hb⟩ := henergy n x hx v w
  let J₁ : ℝ → ℕ → ℕ → ℕ → PolarPoint → ℝ := fun t a b c p =>
    weightedPhysicalJet T (3 / 4 : ℝ) a b c (A (n + 1) (x + t • w) (Fin.cons w v)) p
  let J₂ : ℝ → ℕ → ℕ → ℕ → PolarPoint → ℝ := fun t a b c p =>
    weightedPhysicalJet T (3 / 4 : ℝ) a b c
      (A (n + 2) (x + t • w) (Fin.cons w (Fin.cons w v))) p
  have hlineCont : Continuous (fun t : ℝ => x + t • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hfirst (t : ℝ) (ht : |t| < δ) (a b c : ℕ) (p : PolarPoint) :
      HasDerivAt (fun u => weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (physicalSourceDecode S (L n (x + u • w) v)) p) (J₁ t a b c p) t := by
    apply (hscalar n x w v t (hmem t ht) a b c p).congr_of_eventuallyEq
    have hu : ∀ᶠ u in 𝓝 t, x + u • w ∈ U :=
      hlineCont.continuousAt.eventually (hU.mem_nhds (hmem t ht))
    filter_upwards [hu] with u hux
    rw [show physicalSourceDecode S (L n (x + u • w) v) = A n (x + u • w) v from
      sourceJetLift_decode hS A hmember hcompat hbound n _ hux v]
  have hsecond (t : ℝ) (ht : |t| < δ) (a b c : ℕ) (p : PolarPoint) :
      HasDerivAt (fun u => J₁ u a b c p) (J₂ t a b c p) t :=
    hscalar (n + 1) x w (Fin.cons w v) t (hmem t ht) a b c p
  have hvalue (a b c : ℕ) (p : PolarPoint) :
      J₁ 0 a b c p = weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (physicalSourceDecode S (L (n + 1) x (Fin.cons w v))) p := by
    rw [show physicalSourceDecode S (L (n + 1) x (Fin.cons w v)) =
        A (n + 1) x (Fin.cons w v) from
      sourceJetLift_decode hS A hmember hcompat hbound (n + 1) x hx (Fin.cons w v)]
    simp only [J₁, zero_smul, add_zero]
  exact source_hasProjectiveCurveDerivAt_of_second_jet_envelopes hS hT
    (fun t : ℝ => L n (x + t • w) v) (L (n + 1) x (Fin.cons w v))
    J₁ J₂ hδ hfirst hsecond hvalue hb

theorem exists_source_smoothDirections_of_scalar_jets
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hU : IsOpen U) (hc : Convex ℝ U) (f : E → S.Source)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, HeightMember D T (3 / 4 : ℝ) (A n x v))
    (hcompat : ∀ n x, x ∈ U → ∀ v, physicalSourceIntegral D (A n x v) = 0)
    (hbound : SourceJetNormBounds (T := T) (U := U) A)
    (hzero : ∀ x ∈ U, A 0 x Fin.elim0 = physicalSourceDecode S (f x))
    (hscalar : ∀ n (x w : E) (v : Fin n → E) (t : ℝ), x + t • w ∈ U → ∀ a b c p,
      HasDerivAt (fun u => weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (A n (x + u • w) v) p)
        (weightedPhysicalJet T (3 / 4 : ℝ) a b c
          (A (n + 1) (x + t • w) (Fin.cons w v)) p) t)
    (henergy : SourceJetSecondEnvelopes (T := T) (U := U) A) :
    ∃ J : SmoothDirections U f, ∀ n x, x ∈ U → ∀ v : Fin n → E,
      physicalSourceDecode S (J.D n x v) = A n x v := by
  let L := sourceJetLift hS A hmember hcompat hbound
  have hzeroL : ∀ x ∈ U, L 0 x Fin.elim0 = f x := by
    intro x hx
    apply physicalSourceDecode_injective hS
    exact (sourceJetLift_decode hS A hmember hcompat hbound 0 x hx Fin.elim0).trans
      (hzero x hx)
  have hline : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => L n y v) (L (n + 1) x (Fin.cons w v)) x w :=
    sourceJetLift_hasProjectiveLineDerivAt hS hT hU A hmember hcompat hbound hscalar henergy
  let H : ∀ n : ℕ, E → E [×n]→L[ℝ] (S.height (3 / 4 : ℝ)).Space := fun n x =>
    S.Q.toLinearMap.ker.subtypeL.compContinuousMultilinearMap (L n x)
  have hheightLine : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => H n y v) (H (n + 1) x (Fin.cons w v)) x w := by
    intro n x hx v w
    exact (hline n x hx v w).clm_comp S.Q.toLinearMap.ker.subtypeL
  have hheightCont := continuousOn_projectiveJets_of_seminorm_bounds H hU hc hheightLine
    (sourceJetLift_coordinate_bound hS A hmember hcompat hbound)
  have hcont (n : ℕ) :
      ContinuousOn (fun z : E × (Fin n → E) => L n z.1 z.2) (U ×ˢ univ) := by
    intro z hz
    change Tendsto (fun q : E × (Fin n → E) => L n q.1 q.2)
      (𝓝[U ×ˢ univ] z) (𝓝 (L n z.1 z.2))
    exact tendsto_subtype_rng.mpr (hheightCont n z hz)
  let J : SmoothDirections U f :=
    { open_domain := hU, D := L, zero := hzeroL, continuous := hcont, derivative := hline }
  refine ⟨J, ?_⟩
  intro n x hx v
  exact sourceJetLift_decode hS A hmember hcompat hbound n x hx v

end ContinuousFlexibility.Statements
