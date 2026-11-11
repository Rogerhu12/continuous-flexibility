import ContinuousFlexibility.Analysis.PhysicalJetCompatibility
import ContinuousFlexibility.Analysis.ProjectiveJetLocalContinuity
import ContinuousFlexibility.Analysis.SourceLocalSmoothTameBounds
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine

/-!
# Source towers with order-dependent local norm bounds

Every jet is first realized at its own base point. Its directional
continuity follows from its own product bound. Joint continuity at a
point and target level uses only the next derivative on one open convex
neighborhood. No common neighborhood for infinitely many orders is
assumed or selected.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {U : Set E}

def SourcePointJetNormBounds
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ)) : Prop :=
  ∀ n x, x ∈ U → ∀ s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧
    ∀ v, physicalNorm T (3 / 4 : ℝ) s (A n x v) ≤ B * ∏ i, p (v i)

def SourceLocalJetNormBounds
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ)) : Prop :=
  ∀ n s x, x ∈ U →
    ∃ V : Set E, IsOpen V ∧ Convex ℝ V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
        ∀ y ∈ V, ∀ v : Fin n → E,
          physicalNorm T (3 / 4 : ℝ) s (A n y v) ≤ B * (1 + p y) * ∏ i, p (v i)

theorem SourceLocalJetNormBounds.point
    {A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ)}
    (h : SourceLocalJetNormBounds (T := T) (U := U) A) :
    SourcePointJetNormBounds (T := T) (U := U) A := by
  intro n x hx s
  obtain ⟨V, _, _, hVx, _, p, B, hp, _, hb⟩ := h n s x hx
  exact ⟨p, B * (1 + p x), hp, hb x hVx⟩

theorem sourceLocalJetNormBounds_of_local_oneHigh
    (hT : IsMaterialData D T) (hU : IsOpen U) (hc : Convex ℝ U)
    (p : ℕ → Seminorm ℝ E) (hp : ∀ s, Continuous (p s)) (hmono : Monotone p)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, HeightMember D T (3 / 4 : ℝ) (A n x v))
    (hbound : ∀ k x₀, x₀ ∈ U → ∃ loss base : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U,
        p base (x - x₀) < δ → ∀ v : Fin k → E,
        physicalNorm T (3 / 4 : ℝ) s (A k x v) ≤
          C * oneHighVariationWeight p base (s + loss) x v) :
    SourceLocalJetNormBounds (T := T) (U := U) A := by
  intro n s x₀ hx₀
  obtain ⟨loss, base, δ, hδ, hb⟩ := hbound n x₀ hx₀
  let V : Set E := U ∩ {x | p base (x - x₀) < δ}
  have hVo : IsOpen V := hU.inter
    (isOpen_lt ((hp base).comp (continuous_id.sub continuous_const)) continuous_const)
  have hVc : Convex ℝ V := by
    apply hc.inter
    exact (p base).convex_ball x₀ δ
  have hVx : x₀ ∈ V :=
    ⟨hx₀, by simpa only [Set.mem_setOf_eq, sub_self, map_zero] using hδ⟩
  let t : ℕ := max base s
  let q : Seminorm ℝ E := p (t + loss)
  obtain ⟨C, hC, hbC⟩ := hb t (le_max_left _ _)
  refine ⟨V, hVo, hVc, hVx, inter_subset_left, q, C * ((n : ℝ) + 1), hp _,
    mul_nonneg hC (add_nonneg (Nat.cast_nonneg _) zero_le_one), ?_⟩
  intro x hx v
  have hnorm := physicalNorm_monotone_of_memLp (hmember n x hx.1 v).2.2.2.2
    (le_max_right base s)
  have hw := oneHighVariationWeight_le_seminorm_product p q base (t + loss)
    (hmono (by dsimp only [t]; omega)) le_rfl x v
  exact (hnorm.trans (hbC x hx.1 hx.2 v)).trans
    ((mul_le_mul_of_nonneg_left hw hC).trans_eq (by ring))

def sourcePointJetLift (hS : IsPhysicalSpaces D T S)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, HeightMember D T (3 / 4 : ℝ) (A n x v))
    (hcompat : ∀ n x, x ∈ U → ∀ v, physicalSourceIntegral D (A n x v) = 0)
    (hbound : SourcePointJetNormBounds (T := T) (U := U) A)
    (n : ℕ) (x : E) : E [×n]→L[ℝ] S.Source := by
  classical
  exact if hx : x ∈ U then
    liftSourceContinuousMultilinear hS (A n x) (hmember n x hx) (hcompat n x hx)
      (hbound n x hx)
    else 0

theorem sourcePointJetLift_decode (hS : IsPhysicalSpaces D T S)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, HeightMember D T (3 / 4 : ℝ) (A n x v))
    (hcompat : ∀ n x, x ∈ U → ∀ v, physicalSourceIntegral D (A n x v) = 0)
    (hbound : SourcePointJetNormBounds (T := T) (U := U) A)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    physicalSourceDecode S (sourcePointJetLift hS A hmember hcompat hbound n x v) = A n x v := by
  classical
  simp only [sourcePointJetLift, dif_pos hx]
  exact liftSourceContinuousMultilinear_decode hS (A n x)
    (hmember n x hx) (hcompat n x hx) (hbound n x hx) v

/-- Weighted second envelopes prove the actual source derivative for
any realized jet family with the prescribed decoder. -/
theorem sourceJetFamily_hasProjectiveLineDerivAt
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hU : IsOpen U)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (L : ∀ n : ℕ, E → E [×n]→L[ℝ] S.Source)
    (hdecode : ∀ n x, x ∈ U → ∀ v, physicalSourceDecode S (L n x v) = A n x v)
    (hscalar : ∀ n (x w : E) (v : Fin n → E) (t : ℝ), x + t • w ∈ U → ∀ a b c p,
      HasDerivAt (fun u => weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (A n (x + u • w) v) p)
        (weightedPhysicalJet T (3 / 4 : ℝ) a b c
          (A (n + 1) (x + t • w) (Fin.cons w v)) p) t)
    (henergy : SourceJetSecondEnvelopes (T := T) (U := U) A)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) (w : E) :
    HasProjectiveLineDerivAt (fun y => L n y v) (L (n + 1) x (Fin.cons w v)) x w := by
  obtain ⟨δ, hδ, hmem, hb⟩ := henergy n x hx v w
  let J₁ (t : ℝ) (a b c : ℕ) (p : PolarPoint) :=
    weightedPhysicalJet T (3 / 4 : ℝ) a b c (A (n + 1) (x + t • w) (Fin.cons w v)) p
  let J₂ (t : ℝ) (a b c : ℕ) (p : PolarPoint) :=
    weightedPhysicalJet T (3 / 4 : ℝ) a b c
      (A (n + 2) (x + t • w) (Fin.cons w (Fin.cons w v))) p
  have hfirst (t : ℝ) (ht : |t| < δ) (a b c : ℕ) (p : PolarPoint) :
      HasDerivAt (fun u => weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (physicalSourceDecode S (L n (x + u • w) v)) p) (J₁ t a b c p) t := by
    apply (hscalar n x w v t (hmem t ht) a b c p).congr_of_eventuallyEq
    have hnear : ∀ᶠ u : ℝ in 𝓝 t, x + u • w ∈ U :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
        (hU.mem_nhds (hmem t ht))
    filter_upwards [hnear] with u hu
    rw [hdecode n _ hu v]
  have hsecond (t : ℝ) (ht : |t| < δ) (a b c : ℕ) (p : PolarPoint) :
      HasDerivAt (fun u => J₁ u a b c p) (J₂ t a b c p) t :=
    hscalar (n + 1) x w (Fin.cons w v) t (hmem t ht) a b c p
  have hvalue (a b c : ℕ) (p : PolarPoint) :
      J₁ 0 a b c p = weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (physicalSourceDecode S (L (n + 1) x (Fin.cons w v))) p := by
    rw [hdecode (n + 1) x hx (Fin.cons w v)]
    simp only [J₁, zero_smul, add_zero]
  exact source_hasProjectiveCurveDerivAt_of_second_jet_envelopes hS hT
    (fun t : ℝ => L n (x + t • w) v) (L (n + 1) x (Fin.cons w v))
    J₁ J₂ hδ hfirst hsecond hvalue hb

theorem exists_source_smoothDirections_of_local_scalar_jets
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hU : IsOpen U)
    (f : E → S.Source)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, HeightMember D T (3 / 4 : ℝ) (A n x v))
    (hbound : SourceLocalJetNormBounds (T := T) (U := U) A)
    (hzero : ∀ x ∈ U, A 0 x Fin.elim0 = physicalSourceDecode S (f x))
    (hscalar : ∀ n (x w : E) (v : Fin n → E) (t : ℝ), x + t • w ∈ U → ∀ a b c p,
      HasDerivAt (fun u => weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (A n (x + u • w) v) p)
        (weightedPhysicalJet T (3 / 4 : ℝ) a b c
          (A (n + 1) (x + t • w) (Fin.cons w v)) p) t)
    (henergy : SourceJetSecondEnvelopes (T := T) (U := U) A) :
    ∃ J : SmoothDirections U f, ∀ n x, x ∈ U → ∀ v,
      physicalSourceDecode S (J.D n x v) = A n x v := by
  have hzeroQ (x : E) (hx : x ∈ U) : physicalSourceIntegral D (A 0 x Fin.elim0) = 0 :=
    (congrArg (physicalSourceIntegral D) (hzero x hx)).trans
      (physicalSourceIntegral_decode_source_eq_zero hS (f x))
  have hcompat := sourceJet_compatibility_of_zero_jet hS hT hU A
    hmember hscalar henergy hzeroQ
  let L := sourcePointJetLift hS A hmember hcompat hbound.point
  have hdecode := sourcePointJetLift_decode hS A hmember hcompat hbound.point
  have hzeroL (x : E) (hx : x ∈ U) : L 0 x Fin.elim0 = f x := by
    apply physicalSourceDecode_injective hS
    exact (hdecode 0 x hx Fin.elim0).trans (hzero x hx)
  have hline := sourceJetFamily_hasProjectiveLineDerivAt hS hT hU A L hdecode hscalar henergy
  let H : ∀ n : ℕ, E → E [×n]→L[ℝ] (S.height (3 / 4 : ℝ)).Space := fun n x =>
    S.Q.toLinearMap.ker.subtypeL.compContinuousMultilinearMap (L n x)
  have hheightLine : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => H n y v) (H (n + 1) x (Fin.cons w v)) x w := by
    intro n x hx v w
    exact (hline n x hx v w).clm_comp S.Q.toLinearMap.ker.subtypeL
  have hn : ∀ u : (S.height (3 / 4 : ℝ)).Space, ∀ s,
      ‖u.val s‖ = physicalNorm T (3 / 4 : ℝ) s ((S.height (3 / 4 : ℝ)).decode u) :=
    (hS.1 (3 / 4 : ℝ)).2.2.2.2.2.2.2
  have hlocal : ∀ n s x, x ∈ U →
      ∃ V : Set E, IsOpen V ∧ Convex ℝ V ∧ x ∈ V ∧ V ⊆ U ∧
        ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
          ∀ y ∈ V, ∀ v : Fin (n + 1) → E,
            ‖(H (n + 1) y v).val s‖ ≤ B * (1 + p y) * ∏ i, p (v i) := by
    intro n s x hx
    obtain ⟨V, hVo, hVc, hVx, hVU, p, B, hp, hB, hb⟩ := hbound (n + 1) s x hx
    refine ⟨V, hVo, hVc, hVx, hVU, p, B, hp, hB, fun y hy v => ?_⟩
    rw [hn]
    change physicalNorm T (3 / 4 : ℝ) s (physicalSourceDecode S (L (n + 1) y v)) ≤ _
    rw [hdecode (n + 1) y (hVU hy) v]
    exact hb y hy v
  have hheightCont := continuousOn_projectiveJets_of_local_seminorm_bounds H hheightLine hlocal
  have hcont (n : ℕ) :
      ContinuousOn (fun z : E × (Fin n → E) => L n z.1 z.2) (U ×ˢ univ) := by
    intro z hz
    change Tendsto (fun q : E × (Fin n → E) => L n q.1 q.2)
      (𝓝[U ×ˢ univ] z) (𝓝 (L n z.1 z.2))
    exact tendsto_subtype_rng.mpr (hheightCont n z hz)
  let J : SmoothDirections U f :=
    { open_domain := hU, D := L, zero := hzeroL, continuous := hcont, derivative := hline }
  exact ⟨J, hdecode⟩

/-- Local physical bounds and real weighted scalar derivatives produce
the exact source-valued smooth tame map, with the original fixed loss. -/
theorem smoothTameOn_source_of_local_scalar_jets
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hU : IsOpen U) (hc : Convex ℝ U)
    (p : ℕ → Seminorm ℝ E) (hp : ∀ s, Continuous (p s)) (hmono : Monotone p)
    (f : E → S.Source)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, HeightMember D T (3 / 4 : ℝ) (A n x v))
    (hzero : ∀ x ∈ U, A 0 x Fin.elim0 = physicalSourceDecode S (f x))
    (hscalar : ∀ n (x w : E) (v : Fin n → E) (t : ℝ), x + t • w ∈ U → ∀ a b c q,
      HasDerivAt (fun u => weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (A n (x + u • w) v) q)
        (weightedPhysicalJet T (3 / 4 : ℝ) a b c
          (A (n + 1) (x + t • w) (Fin.cons w v)) q) t)
    (henergy : SourceJetSecondEnvelopes (T := T) (U := U) A)
    (hbound : ∀ k x₀, x₀ ∈ U → ∃ loss base : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U,
        p base (x - x₀) < δ → ∀ v : Fin k → E,
        physicalNorm T (3 / 4 : ℝ) s (A k x v) ≤
          C * oneHighVariationWeight p base (s + loss) x v) :
    SmoothTameOn p S.sourceGrading U f := by
  have hlocal := sourceLocalJetNormBounds_of_local_oneHigh hT hU hc p hp hmono A hmember hbound
  let data := exists_source_smoothDirections_of_local_scalar_jets
    hS hT hU f A hmember hlocal hzero hscalar henergy
  let J : SmoothDirections U f := data.choose
  have hJ : ∀ n x, x ∈ U → ∀ v,
      physicalSourceDecode S (J.D n x v) = A n x v := data.choose_spec
  apply smoothTameOn_source_of_local_oneHigh_norm_bounds hS p J
  intro k x₀ hx₀
  obtain ⟨loss, base, δ, hδ, hb⟩ := hbound k x₀ hx₀
  refine ⟨loss, base, δ, hδ, fun s hs => ?_⟩
  obtain ⟨C, hC, hnorm⟩ := hb s hs
  refine ⟨C, hC, fun x hx hnear v => ?_⟩
  rw [hJ k x hx v]
  exact hnorm x hx hnear v

end ContinuousFlexibility.Statements
