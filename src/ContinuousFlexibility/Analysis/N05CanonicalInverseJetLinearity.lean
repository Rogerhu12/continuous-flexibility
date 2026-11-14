module

public import ContinuousFlexibility.Analysis.N05CanonicalInverseJetBounds
public import ContinuousFlexibility.Analysis.N05CanonicalFiniteBlockSums

/-!
# Continuous linear restrictions of the actual fixed inverse jets

Weak derivative uniqueness proves linearity only on source levels where
the fixed choices are genuine derivatives. Finite source truncations then
give exact finite sums and converge to the jets of the original global
inverse, without introducing another inverse or a second limiting output.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Filter
open scoped BigOperators Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {base loss : ℕ} {ε γw γ M0 M1 : ℝ} {G : RadialSource → RadialUnknown}
  (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)
  (hγw : 0 < γw) (hG : ReferenceInverseProperties D γw M0 M1 G)
  (hV : IsVolumeModel T S K V) (hgap : γw < γ)

include hD hT hS h hcoordinates hγw hG hV hgap

theorem n05CanonicalGlobalInverse_jet_linear_combination {t : ℝ} {s : ℕ}
    (v w : V.level γ t s) (j : Fin (s + 1)) (c d : ℝ) :
    n05CanonicalAngularJetSequence S K
        (n05CanonicalGlobalInverse D S C K G (V.forget γ t s (c • v + d • w))).1 j.val =
      c • n05CanonicalAngularJetSequence S K
          (n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)).1 j.val +
        d • n05CanonicalAngularJetSequence S K
          (n05CanonicalGlobalInverse D S C K G (V.forget γ t s w)).1 j.val := by
  obtain ⟨_, _, hb⟩ :=
    n05CanonicalGlobalInverse_angularJets_bound hD hT hS h hcoordinates hγw hG hV hgap t s
  rw [n05CanonicalGlobalInverse_linear_combination hD hT hS h hcoordinates hγw hG hV hgap v w c d]
  exact n05CanonicalAngularJetSequence_linear_combination (hb v j).1 (hb w j).1 c d

def n05CanonicalInverseJetLinear (t : ℝ) (s : ℕ) (j : Fin (s + 1)) :
    V.level γ t s →ₗ[ℝ] CanonicalL2Sequence S K where
  toFun v := n05CanonicalAngularJetSequence S K
    (n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)).1 j.val
  map_add' v w := by
    simpa only [one_smul] using n05CanonicalGlobalInverse_jet_linear_combination
      hD hT hS h hcoordinates hγw hG hV hgap v w j 1 1
  map_smul' c v := by
    simpa only [zero_smul, add_zero, RingHom.id_apply] using
      n05CanonicalGlobalInverse_jet_linear_combination
        hD hT hS h hcoordinates hγw hG hV hgap v v j c 0

def n05CanonicalInverseJetCLM (t : ℝ) (s : ℕ) (j : Fin (s + 1)) :
    V.level γ t s →L[ℝ] CanonicalL2Sequence S K :=
  (n05CanonicalInverseJetLinear hD hT hS h hcoordinates
    hγw hG hV hgap t s j).mkContinuousOfExistsBound (by
      obtain ⟨B, _, hb⟩ := n05CanonicalGlobalInverse_angularJets_norm_bound
        hD hT hS h hcoordinates hγw hG hV hgap t s
      exact ⟨B, fun v => hb v j⟩)

@[simp] theorem n05CanonicalInverseJetCLM_apply (t : ℝ) (s : ℕ) (j : Fin (s + 1))
    (v : V.level γ t s) :
    n05CanonicalInverseJetCLM hD hT hS h hcoordinates hγw hG hV hgap t s j v =
      n05CanonicalAngularJetSequence S K
        (n05CanonicalGlobalInverse D S C K G (V.forget γ t s v)).1 j.val := by
  rw [n05CanonicalInverseJetCLM, LinearMap.mkContinuousOfExistsBound_apply]
  rfl

omit hV

set_option backward.isDefEq.respectTransparency false in
/-- Every summand is the fixed weak jet of the same global inverse
applied to its actual weighted single-coordinate source. -/
theorem n05CanonicalGlobalInverse_finite_jet_sum (t : ℝ) (s : ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γ t s)
    (q : Finset ℕ) (j : Fin (s + 1)) (k : ℕ) :
    n05CanonicalAngularJetSequence S K
        (n05CanonicalGlobalInverse D S C K G
          ((n05CanonicalVolumeModel T S K).forget γ t s
            (n05CanonicalFiniteTruncate S K s q v))).1 j.val k =
      ∑ m ∈ q, n05CanonicalAngularJetSequence S K
        (n05CanonicalGlobalInverse D S C K G
          (Pi.single m (n05CanonicalSampleWeight T S K γ t m • v.val m 0))).1 j.val k := by
  let J := n05CanonicalInverseJetCLM hD hT hS h hcoordinates hγw hG
    (n05CanonicalVolumeModel_actual hD.1 hT S K) hgap t s j
  let P := (lp.evalCLM ℝ (fun m => CanonicalL2 S K m) 2 k).comp J
  have hP (w : (n05CanonicalVolumeModel T S K).level γ t s) :
      P w = n05CanonicalAngularJetSequence S K
        (n05CanonicalGlobalInverse D S C K G
          ((n05CanonicalVolumeModel T S K).forget γ t s w)).1 j.val k := by
    simp only [P, J, ContinuousLinearMap.comp_apply, lp.evalCLM,
      LinearMap.mkContinuous_apply, lp.evalₗ_apply, n05CanonicalInverseJetCLM_apply]
  have he := map_sum P (fun m => n05CanonicalFiniteTruncate S K s {m} v) q
  rw [← n05CanonicalFiniteTruncate_sum_singletons] at he
  calc
    _ = P (n05CanonicalFiniteTruncate S K s q v) :=
      (hP (n05CanonicalFiniteTruncate S K s q v)).symm
    _ = ∑ m ∈ q, P (n05CanonicalFiniteTruncate S K s {m} v) := he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      exact (hP (n05CanonicalFiniteTruncate S K s {m} v)).trans
        (congrArg (fun F : CanonicalSequence S K =>
          n05CanonicalAngularJetSequence S K
            (n05CanonicalGlobalInverse D S C K G F).1 j.val k)
          (n05CanonicalFiniteTruncate_forget_singleton T S K γ t s m v))

set_option backward.isDefEq.respectTransparency false in
/-- Coordinate limits are the genuine jets of the original global
inverse, by continuity of that very restriction on the source level. -/
theorem n05CanonicalGlobalInverse_finite_jet_tendsto (t : ℝ) (s : ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γ t s) (j : Fin (s + 1)) (k : ℕ) :
    Tendsto (fun q : Finset ℕ => n05CanonicalAngularJetSequence S K
      (n05CanonicalGlobalInverse D S C K G
        ((n05CanonicalVolumeModel T S K).forget γ t s
          (n05CanonicalFiniteTruncate S K s q v))).1 j.val k) atTop
      (𝓝 (n05CanonicalAngularJetSequence S K
        (n05CanonicalGlobalInverse D S C K G
          ((n05CanonicalVolumeModel T S K).forget γ t s v)).1 j.val k)) := by
  let J := n05CanonicalInverseJetCLM hD hT hS h hcoordinates hγw hG
    (n05CanonicalVolumeModel_actual hD.1 hT S K) hgap t s j
  let P := (lp.evalCLM ℝ (fun m => CanonicalL2 S K m) 2 k).comp J
  have hP (w : (n05CanonicalVolumeModel T S K).level γ t s) :
      P w = n05CanonicalAngularJetSequence S K
        (n05CanonicalGlobalInverse D S C K G
          ((n05CanonicalVolumeModel T S K).forget γ t s w)).1 j.val k := by
    simp only [P, J, ContinuousLinearMap.comp_apply, lp.evalCLM,
      LinearMap.mkContinuous_apply, lp.evalₗ_apply, n05CanonicalInverseJetCLM_apply]
  have ht := P.continuous.tendsto v |>.comp
    (n05CanonicalFiniteTruncate_tendsto S K s v)
  change Tendsto (fun q : Finset ℕ => P (n05CanonicalFiniteTruncate S K s q v))
    atTop (𝓝 (P v)) at ht
  simpa only [hP] using ht

end ContinuousFlexibility.Statements
