import ContinuousFlexibility.Analysis.ReturnCorrectionSourceUnitGrowth
import ContinuousFlexibility.Analysis.PhysicalMultilinearNormalization

/-!
# Local one-high estimates for the actual source jets

Coefficient bounds first give physical membership. On each fixed low
ball, the complementary-order interpolation estimate controls unit
directions. Algebraic multilinear normalization then restores every
direction with the exact one-high expression. The derivative loss and
low order are fixed before the output order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {U : Set E}

theorem LocalCoefficientMaterialTameBounds.divergence_heightMember
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {p : ℕ → Seminorm ℝ E}
    {A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D)}
    (h : LocalCoefficientMaterialTameBounds (T := T) (U := U) p A)
    (hsym : ∀ n x, x ∈ U → ∀ v,
      SymmetricErrorCoefficientSymmetry (A n x v).val)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) (η : HeightPair S) :
    HeightMember D T (3 / 4 : ℝ) (symmetricDivergenceBilinear hS hT (A n x v) η) := by
  obtain ⟨base, loss, d, δ, hδ, hb⟩ := h n x hx
  have hx' : x ∈ U ∩ {y | p base (y - x) < δ} :=
    ⟨hx, by simpa only [sub_self, map_zero] using hδ⟩
  apply symmetricDivergenceBilinear_heightMember hS hT (A n x v) (hsym n x hx v) d
  intro a b
  obtain ⟨C, hC, hCbound⟩ := hb (a + b)
  have hw : 0 ≤ oneHighVariationWeight p base (a + b + loss) x v :=
    multilinearTameSize_nonneg _ _ _ (add_nonneg zero_le_one (apply_nonneg _ _)) v
  exact ⟨C * oneHighVariationWeight p base (a + b + loss) x v,
    mul_nonneg hC hw, fun r => hCbound x hx' v a b le_rfl r⟩

theorem LocalCoefficientMaterialTameBounds.sourceJets_heightMember
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {p : ℕ → Seminorm ℝ E}
    {A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D)}
    (h : LocalCoefficientMaterialTameBounds (T := T) (U := U) p A)
    (hsym : ∀ n x, x ∈ U → ∀ v,
      SymmetricErrorCoefficientSymmetry (A n x v).val)
    (n : ℕ) (z : E × HeightPair S) (hz : z ∈ U ×ˢ (univ : Set (HeightPair S)))
    (v : Fin n → E × HeightPair S) :
    HeightMember D T (3 / 4 : ℝ) (symmetricSourceScalarJets hS hT A n z v) :=
  symmetricSourceScalarJets_heightMember hS hT A z.1
    (fun k vs η => h.divergence_heightMember hS hT hsym k z.1 hz.1 vs η) n z.2 v

/-- A single local unit-direction estimate suffices; there is no
continuity assumption on the multilinear scalar field. -/
private theorem local_oneHigh_of_unit_growth
    (hS : IsPhysicalSpaces D T S)
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ (HeightPair S))
    (hp : Monotone p) (k : ℕ)
    (F : E × HeightPair S → MultilinearMap ℝ
      (fun _ : Fin k => E × HeightPair S) (PolarPoint → ℝ))
    (hmember : ∀ z ∈ U ×ˢ (univ : Set (HeightPair S)), ∀ v,
      HeightMember D T (3 / 4 : ℝ) (F z v))
    (z₀ : E × HeightPair S) (oldBase B L : ℕ) (hbase : oldBase ≤ B)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hunit : ∀ Kp Kq : ℝ, 0 ≤ Kp → 0 ≤ Kq →
      ∀ s : ℕ, B ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : E × HeightPair S,
        z.1 ∈ U ∩ {x | p oldBase (x - z₀.1) < δ₀} →
        ∀ v : Fin k → E × HeightPair S,
        p B z.1 ≤ Kp → q B z.2 ≤ Kq → (∀ i, pairGrading p q B (v i) ≤ 1) →
        physicalNorm T (3 / 4 : ℝ) s (F z v) ≤
          C * (1 + pairGrading p q (s + L) z +
            ∑ i : Fin k, pairGrading p q (s + L) (v i))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℕ, B ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ U ×ˢ (univ : Set (HeightPair S)),
        pairGrading p q B (z - z₀) < δ → ∀ v : Fin k → E × HeightPair S,
        physicalNorm T (3 / 4 : ℝ) s (F z v) ≤
          C * oneHighVariationWeight (pairGrading p q) B (s + L) z v := by
  let δ : ℝ := min δ₀ 1
  have hδ : 0 < δ := lt_min hδ₀ zero_lt_one
  refine ⟨δ, hδ, fun s hs => ?_⟩
  obtain ⟨C, hC, hb⟩ := hunit (p B z₀.1 + 1) (q B z₀.2 + 1)
    (add_nonneg (apply_nonneg _ _) zero_le_one)
    (add_nonneg (apply_nonneg _ _) zero_le_one) s hs
  refine ⟨C, hC, fun z hz hnear => ?_⟩
  have hpdiff : p B (z.1 - z₀.1) ≤ pairGrading p q B (z - z₀) :=
    le_add_of_nonneg_right (apply_nonneg (q B) (z.2 - z₀.2))
  have hqdiff : q B (z.2 - z₀.2) ≤ pairGrading p q B (z - z₀) :=
    le_add_of_nonneg_left (apply_nonneg (p B) (z.1 - z₀.1))
  have hx : z.1 ∈ U ∩ {x | p oldBase (x - z₀.1) < δ₀} :=
    ⟨hz.1, ((hp hbase _).trans hpdiff).trans_lt (hnear.trans_le (min_le_left _ _))⟩
  have hpx : p B z.1 ≤ p B z₀.1 + 1 := by
    calc
      p B z.1 = p B ((z.1 - z₀.1) + z₀.1) := by rw [sub_add_cancel]
      _ ≤ p B (z.1 - z₀.1) + p B z₀.1 := (p B).add_le _ _
      _ ≤ 1 + p B z₀.1 := add_le_add_right
        ((hpdiff.trans_lt hnear).le.trans (min_le_right _ _)) _
      _ = _ := add_comm _ _
  have hqη : q B z.2 ≤ q B z₀.2 + 1 := by
    calc
      q B z.2 = q B ((z.2 - z₀.2) + z₀.2) := by rw [sub_add_cancel]
      _ ≤ q B (z.2 - z₀.2) + q B z₀.2 := (q B).add_le _ _
      _ ≤ 1 + q B z₀.2 := add_le_add_right
        ((hqdiff.trans_lt hnear).le.trans (min_le_right _ _)) _
      _ = _ := add_comm _ _
  exact physicalNorm_multilinear_bound_of_unitBall (hS.1 (3 / 4 : ℝ)) (F z)
    (hmember z hz) s (pairGrading p q B) (pairGrading p q (s + L)) hC
    (fun v hv => hb z hx v hpx hqη (fun i => (hv i).le))

theorem symmetricSourceScalarJets_local_oneHigh_norm_bound
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ (HeightPair S))
    (hp : Monotone p) (hq : Monotone q)
    (hIp : HasInterpolation p) (hIq : HasInterpolation q)
    (hheight : ∀ s η, physicalNorm T (3 / 4 : ℝ) s
      ((S.height (3 / 4 : ℝ)).decode η.1) ≤ q s η)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    (hcoeff : LocalCoefficientMaterialTameBounds (T := T) (U := U) p A)
    (hsym : ∀ n x, x ∈ U → ∀ v,
      SymmetricErrorCoefficientSymmetry (A n x v).val) :
    ∀ k z₀, z₀ ∈ U ×ˢ (univ : Set (HeightPair S)) →
      ∃ loss base : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ U ×ˢ (univ : Set (HeightPair S)),
        pairGrading p q base (z - z₀) < δ → ∀ v : Fin k → E × HeightPair S,
        physicalNorm T (3 / 4 : ℝ) s (symmetricSourceScalarJets hS hT A k z v) ≤
          C * oneHighVariationWeight (pairGrading p q) base (s + loss) z v := by
  have hmember := hcoeff.sourceJets_heightMember hS hT hsym
  intro k z₀ hz₀
  cases k with
  | zero =>
      obtain ⟨b, l, d, δ₀, hδ₀, hb⟩ := hcoeff 0 z₀.1 hz₀.1
      obtain ⟨B, L, hB, hgrowth⟩ := exists_symmetricDivergence_unit_growth
        hS hT p q hp hq hIp hIq hheight b l d b
      let V : Set E := U ∩ {x | p b (x - z₀.1) < δ₀}
      have hunit : ∀ Kp Kq : ℝ, 0 ≤ Kp → 0 ≤ Kq →
          ∀ s : ℕ, B ≤ s → ∃ C : ℝ, 0 ≤ C ∧
          ∀ z : E × HeightPair S, z.1 ∈ V →
            ∀ v : Fin 0 → E × HeightPair S,
            p B z.1 ≤ Kp → q B z.2 ≤ Kq → (∀ i, pairGrading p q B (v i) ≤ 1) →
            physicalNorm T (3 / 4 : ℝ) s (symmetricSourceScalarJets hS hT A 0 z v) ≤
              C * (1 + pairGrading p q (s + L) z +
                ∑ i : Fin 0, pairGrading p q (s + L) (v i)) := by
        intro Kp Kq hKp hKq s hs
        obtain ⟨C, hC, hc⟩ := hgrowth 0 A V hb Kp Kq hKp hKq s hs
        refine ⟨C, hC, fun z hz v hpx hqη hv => ?_⟩
        rw [symmetricSourceScalarJets_zero_apply]
        exact hc z.1 hz z.2 v hpx hqη hv
      obtain ⟨δ, hδ, hbound⟩ := local_oneHigh_of_unit_growth hS p q hp 0
        (symmetricSourceScalarJets hS hT A 0) (hmember 0) z₀ b B L
        ((le_max_left b b).trans hB) δ₀ hδ₀ hunit
      exact ⟨L, B, δ, hδ, hbound⟩
  | succ n =>
      obtain ⟨b, l, d, δ₀, hδ₀, hlow, hhigh⟩ := hcoeff.adjacent hT hp n z₀.1 hz₀.1
      obtain ⟨B, L, hB, hgrowth⟩ := exists_symmetricSourceScalarJets_unit_growth
        hS hT p q hp hq hIp hIq hheight b l d b
      let V : Set E := U ∩ {x | p b (x - z₀.1) < δ₀}
      have hunit := hgrowth n A V hlow hhigh
        (fun x hx k vs η => hcoeff.divergence_heightMember hS hT hsym k x hx.1 vs η)
      obtain ⟨δ, hδ, hbound⟩ := local_oneHigh_of_unit_growth hS p q hp (n + 1)
        (symmetricSourceScalarJets hS hT A (n + 1)) (hmember (n + 1)) z₀ b B L
        ((le_max_left b b).trans hB) δ₀ hδ₀ hunit
      exact ⟨L, B, δ, hδ, hbound⟩

end ContinuousFlexibility.Statements
