module

public import ContinuousFlexibility.Analysis.N05CanonicalNormalJetBounds
public import ContinuousFlexibility.Analysis.N05CanonicalFiniteBlockSums

/-!
# Continuous linear restrictions of the fixed normal angular jets

The actual weak radial and angular identities exclude both default choice
branches. Finite truncations therefore converge to these very derivatives
of the original inverse, with one extra angular order on the source.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Filter
open scoped BigOperators Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {base loss : ℕ} {ε γw γ M0 M1 MN : ℝ} {G : RadialSource → RadialUnknown}
  (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)
  (hγw : 0 < γw) (hG : ReferenceInverseProperties D γw M0 M1 G)
  (hN : FirstNormalInverseEstimate D γw M0 MN G)
  (hV : IsVolumeModel T S K V) (hgap : γw < γ)

include hD hT hS h hcoordinates hγw hG hN hV hgap

theorem n05CanonicalGlobalInverse_normal_linear_combination {t : ℝ} {s : ℕ}
    (v w : V.level γ t (s + 1)) (c d : ℝ) :
    n05CanonicalRadialJetSequence S K
        (n05CanonicalGlobalInverse D S C K G (V.forget γ t (s + 1) (c • v + d • w))).1 =
      c • n05CanonicalRadialJetSequence S K
          (n05CanonicalGlobalInverse D S C K G (V.forget γ t (s + 1) v)).1 +
        d • n05CanonicalRadialJetSequence S K
          (n05CanonicalGlobalInverse D S C K G (V.forget γ t (s + 1) w)).1 := by
  obtain ⟨_, _, hb⟩ :=
    n05CanonicalGlobalInverse_normalJets_bound hD hT hS h hcoordinates hγw hG hN hV hgap t s
  rw [n05CanonicalGlobalInverse_linear_combination hD hT hS h hcoordinates hγw hG hV hgap v w c d]
  exact n05CanonicalRadialJetSequence_linear_combination (hb v).1 (hb w).1 c d

theorem n05CanonicalGlobalInverse_normalJet_linear_combination {t : ℝ} {s : ℕ}
    (v w : V.level γ t (s + 1)) (j : Fin (s + 1)) (c d : ℝ) :
    n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
        (n05CanonicalGlobalInverse D S C K G (V.forget γ t (s + 1) (c • v + d • w))).1) j.val =
      c • n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
          (n05CanonicalGlobalInverse D S C K G (V.forget γ t (s + 1) v)).1) j.val +
        d • n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
          (n05CanonicalGlobalInverse D S C K G (V.forget γ t (s + 1) w)).1) j.val := by
  obtain ⟨_, _, hb⟩ :=
    n05CanonicalGlobalInverse_normalJets_bound hD hT hS h hcoordinates hγw hG hN hV hgap t s
  rw [n05CanonicalGlobalInverse_normal_linear_combination
    hD hT hS h hcoordinates hγw hG hN hV hgap v w c d]
  exact n05CanonicalAngularJetSequence_linear_combination
    ((hb v).2.2 j).1 ((hb w).2.2 j).1 c d

def n05CanonicalInverseNormalJetLinear (t : ℝ) (s : ℕ) (j : Fin (s + 1)) :
    V.level γ t (s + 1) →ₗ[ℝ] CanonicalL2Sequence S K where
  toFun v := n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
    (n05CanonicalGlobalInverse D S C K G (V.forget γ t (s + 1) v)).1) j.val
  map_add' v w := by
    simpa only [one_smul] using n05CanonicalGlobalInverse_normalJet_linear_combination
      hD hT hS h hcoordinates hγw hG hN hV hgap v w j 1 1
  map_smul' c v := by
    simpa only [zero_smul, add_zero, RingHom.id_apply] using
      n05CanonicalGlobalInverse_normalJet_linear_combination
        hD hT hS h hcoordinates hγw hG hN hV hgap v v j c 0

def n05CanonicalInverseNormalJetCLM (t : ℝ) (s : ℕ) (j : Fin (s + 1)) :
    V.level γ t (s + 1) →L[ℝ] CanonicalL2Sequence S K :=
  (n05CanonicalInverseNormalJetLinear hD hT hS h hcoordinates
    hγw hG hN hV hgap t s j).mkContinuousOfExistsBound (by
      obtain ⟨B, _, hb⟩ := n05CanonicalGlobalInverse_normalJets_norm_bound
        hD hT hS h hcoordinates hγw hG hN hV hgap t s
      exact ⟨B, fun v => hb v j⟩)

@[simp] theorem n05CanonicalInverseNormalJetCLM_apply (t : ℝ) (s : ℕ) (j : Fin (s + 1))
    (v : V.level γ t (s + 1)) :
    n05CanonicalInverseNormalJetCLM hD hT hS h hcoordinates hγw hG hN hV hgap t s j v =
      n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
        (n05CanonicalGlobalInverse D S C K G (V.forget γ t (s + 1) v)).1) j.val := by
  rw [n05CanonicalInverseNormalJetCLM, LinearMap.mkContinuousOfExistsBound_apply]
  rfl

omit hV

set_option backward.isDefEq.respectTransparency false in
theorem n05CanonicalGlobalInverse_finite_normalJet_sum (t : ℝ) (s : ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γ t (s + 1))
    (q : Finset ℕ) (j : Fin (s + 1)) (k : ℕ) :
    n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
        (n05CanonicalGlobalInverse D S C K G
          ((n05CanonicalVolumeModel T S K).forget γ t (s + 1)
            (n05CanonicalFiniteTruncate S K (s + 1) q v))).1) j.val k =
      ∑ m ∈ q, n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
        (n05CanonicalGlobalInverse D S C K G
          (Pi.single m (n05CanonicalSampleWeight T S K γ t m • v.val m 0))).1) j.val k := by
  let J := n05CanonicalInverseNormalJetCLM hD hT hS h hcoordinates hγw hG hN
    (n05CanonicalVolumeModel_actual hD.1 hT S K) hgap t s j
  let P := (lp.evalCLM ℝ (fun m => CanonicalL2 S K m) 2 k).comp J
  have hP (w : (n05CanonicalVolumeModel T S K).level γ t (s + 1)) :
      P w = n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
        (n05CanonicalGlobalInverse D S C K G
          ((n05CanonicalVolumeModel T S K).forget γ t (s + 1) w)).1) j.val k := by
    simp only [P, J, ContinuousLinearMap.comp_apply, lp.evalCLM,
      LinearMap.mkContinuous_apply, lp.evalₗ_apply, n05CanonicalInverseNormalJetCLM_apply]
  have he := map_sum P (fun m => n05CanonicalFiniteTruncate S K (s + 1) {m} v) q
  rw [← n05CanonicalFiniteTruncate_sum_singletons] at he
  calc
    _ = P (n05CanonicalFiniteTruncate S K (s + 1) q v) :=
      (hP (n05CanonicalFiniteTruncate S K (s + 1) q v)).symm
    _ = ∑ m ∈ q, P (n05CanonicalFiniteTruncate S K (s + 1) {m} v) := he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      exact (hP (n05CanonicalFiniteTruncate S K (s + 1) {m} v)).trans
        (congrArg (fun F : CanonicalSequence S K =>
          n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
            (n05CanonicalGlobalInverse D S C K G F).1) j.val k)
          (n05CanonicalFiniteTruncate_forget_singleton T S K γ t (s + 1) m v))

set_option backward.isDefEq.respectTransparency false in
theorem n05CanonicalGlobalInverse_finite_normalJet_tendsto (t : ℝ) (s : ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γ t (s + 1)) (j : Fin (s + 1)) (k : ℕ) :
    Tendsto (fun q : Finset ℕ => n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
      (n05CanonicalGlobalInverse D S C K G
        ((n05CanonicalVolumeModel T S K).forget γ t (s + 1)
          (n05CanonicalFiniteTruncate S K (s + 1) q v))).1) j.val k) atTop
      (𝓝 (n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
        (n05CanonicalGlobalInverse D S C K G
          ((n05CanonicalVolumeModel T S K).forget γ t (s + 1) v)).1) j.val k)) := by
  let J := n05CanonicalInverseNormalJetCLM hD hT hS h hcoordinates hγw hG hN
    (n05CanonicalVolumeModel_actual hD.1 hT S K) hgap t s j
  let P := (lp.evalCLM ℝ (fun m => CanonicalL2 S K m) 2 k).comp J
  have hP (w : (n05CanonicalVolumeModel T S K).level γ t (s + 1)) :
      P w = n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
        (n05CanonicalGlobalInverse D S C K G
          ((n05CanonicalVolumeModel T S K).forget γ t (s + 1) w)).1) j.val k := by
    simp only [P, J, ContinuousLinearMap.comp_apply, lp.evalCLM,
      LinearMap.mkContinuous_apply, lp.evalₗ_apply, n05CanonicalInverseNormalJetCLM_apply]
  have ht := P.continuous.tendsto v |>.comp
    (n05CanonicalFiniteTruncate_tendsto S K (s + 1) v)
  change Tendsto (fun q : Finset ℕ =>
    P (n05CanonicalFiniteTruncate S K (s + 1) q v)) atTop (𝓝 (P v)) at ht
  simpa only [hP] using ht

end ContinuousFlexibility.Statements
