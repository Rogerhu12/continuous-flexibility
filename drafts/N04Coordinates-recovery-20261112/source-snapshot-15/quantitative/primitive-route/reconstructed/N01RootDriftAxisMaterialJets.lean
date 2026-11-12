import ContinuousFlexibility.Analysis.N01CharacteristicDriftMaterialJets
import ContinuousFlexibility.Analysis.N01ActualRootGeometry
import ContinuousFlexibility.Analysis.PointwiseAffineMaterialJets

/-!
# Actual drift jets on the two unit root axes

Translation and the inward orientation have operator norm one. The
actual characteristic drift therefore has exactly the same material
envelope on the root axis, before any arbitrary model collar or flow
normalization is selected. The full ordinary jets include order zero.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem norm_iteratedFDeriv_rootProfileShift_le
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : PolarPoint → Y} {r σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {x : PolarPoint} (hf : ContDiffAt ℝ ∞ f (rootProfileShift r σ x)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f (rootProfileShift r σ y)) x‖ ≤
      ‖iteratedFDeriv ℝ n f (rootProfileShift r σ x)‖ := by
  let L : PolarPoint →L[ℝ] PolarPoint :=
    (σ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hLapply (q : PolarPoint) : L q = (σ * q.1, q.2) := by
    simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  have hσnorm : ‖σ‖ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound L zero_le_one
    intro q
    simp only [hLapply, Prod.norm_def, norm_mul, hσnorm, one_mul]
  have hpoint (q : PolarPoint) : (r, (0 : ℝ)) + L q = rootProfileShift r σ q := by
    simp only [hLapply, Prod.mk_add_mk, zero_add, rootProfileShift]
  have hf' : ContDiffAt ℝ ∞ f ((r, (0 : ℝ)) + L x) := by
    rw [hpoint]
    exact hf
  have hshift : ContDiffAt ℝ ∞ (fun y => f ((r, (0 : ℝ)) + y)) (L x) :=
    hf'.comp (L x) (contDiffAt_const.add contDiffAt_id)
  have hb := norm_iteratedFDeriv_comp_linear_le_at L hshift n
  rw [iteratedFDeriv_comp_add_left] at hb
  have he : (fun y : PolarPoint => f ((r, (0 : ℝ)) + y)) ∘ L =
      fun y => f (rootProfileShift r σ y) := by
    funext y
    exact congrArg f (hpoint y)
  simpa only [he, hpoint] using hb.trans
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg L) hL))

theorem contDiffAt_characteristicDrift_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {q : PolarPoint} (hq : q ∈ annularOpen D) :
    ContDiffAt ℝ ∞
      (characteristicDrift (stateProfile D S C z.1) (stateHeight D S C z)) q := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have ha : ContDiffAt ℝ ∞ (originalCoefficients D S C z).a q := by
    simpa only [canonicalCoefficientComponent, ↓reduceIte] using
      (contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz hs (0 : Fin 3)).contDiffAt
        (hU.mem_nhds hq)
  have hb : ContDiffAt ℝ ∞ (originalCoefficients D S C z).b q := by
    simpa only [canonicalCoefficientComponent,
      if_neg (show (1 : Fin 3) ≠ 0 by decide), if_pos rfl] using
      (contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz hs (1 : Fin 3)).contDiffAt
        (hU.mem_nhds hq)
  have hapos : 0 < (originalCoefficients D S C z).a q :=
    (div_pos (hN.1.1.choose_spec.1.2.2.2.2.1 q.1 hq.1)
      (by norm_num : (0 : ℝ) < 16)).trans_le
        (hN.originalRadialCoefficient_ge_sixteenth_profile hz hs hq)
  apply (hb.div ha hapos.ne').congr_of_eventuallyEq
  exact eventually_of_mem (hU.mem_nhds hq)
    (fun x hx => n01_characteristicDrift_eq_original_ratio hS hT hN hz hs hx)

theorem n01_orientedRootDrift_axis_material_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ C0 : ℝ, ∃ low outLoss : ℕ, 1 ≤ C0 ∧
      (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      ∀ rightEnd : Bool, ∀ θ : ℝ,
        let d := orientedCharacteristicDrift
          (stateProfile D S C z.1) (stateHeight D S C z)
          (n01ComponentRoot C m rightEnd) (n01ComponentRootOrientation rightEnd)
        ContDiffAt ℝ ∞ d (0, θ) ∧ ∀ n : ℕ,
          ‖iteratedFDeriv ℝ n d (0, θ)‖ ≤
            B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
              (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
                (z - (C.referenceState, 0))) := by
  obtain ⟨C0, low, outLoss, hC0, hfloor, B, hB, hbound⟩ :=
    n01_characteristicDrift_component_material_jets hS hT hN
  refine ⟨C0, low, outLoss, hC0, hfloor, B, hB, ?_⟩
  intro z hz hs hzlow m j hhost side θ
  let r := n01ComponentRoot C m side
  let σ := n01ComponentRootOrientation side
  let f := characteristicDrift (stateProfile D S C z.1) (stateHeight D S C z)
  have hσ : σ = 1 ∨ σ = -1 := n01ComponentRootOrientation_eq side
  have hσabs : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hroot := n01_component_root_data hN m side
  have hcomp := n01Properties_negativeRadialComponent hN m
  have hr : r ∈ Icc (C.left m) (C.right m) := by
    cases side <;> simp only [r, n01ComponentRoot, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc]
    · exact ⟨le_rfl, hcomp.2.1.le⟩
    · exact ⟨hcomp.2.1.le, le_rfl⟩
  have hf : ContDiffAt ℝ ∞ f (r, θ) :=
    contDiffAt_characteristicDrift_of_n01 hS hT hN hz hs ⟨hroot.1, mem_univ _⟩
  have hpoint : rootProfileShift r σ (0, θ) = (r, θ) := by
    simp only [rootProfileShift, mul_zero, add_zero]
  have hf' : ContDiffAt ℝ ∞ f (rootProfileShift r σ (0, θ)) := by
    rw [hpoint]
    exact hf
  have hshift : ContDiff ℝ ∞ (rootProfileShift r σ) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hfs : ContDiffAt ℝ ∞ (fun y => f (rootProfileShift r σ y)) (0, θ) := by
    simpa only [Function.comp_def] using hf'.comp (0, θ) hshift.contDiffAt
  refine ⟨contDiffAt_const.mul hfs, ?_⟩
  intro n
  change ‖iteratedFDeriv ℝ n (fun y => σ • f (rootProfileShift r σ y)) (0, θ)‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hfs.of_le (by simp : (n : ℕ∞ω) ≤ ∞)),
    norm_smul, Real.norm_eq_abs, hσabs, one_mul]
  have hb := norm_iteratedFDeriv_rootProfileShift_le hσ hf' n
  rw [hpoint] at hb
  exact hb.trans (hbound z hz hs hzlow m j hhost (r, θ) hr n)

end ContinuousFlexibility.Analysis
