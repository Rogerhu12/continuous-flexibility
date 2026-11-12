import ContinuousFlexibility.Analysis.N07aAngularReferenceRemainderVolume
import ContinuousFlexibility.Analysis.N07aAngularReferenceColumnIdentity
import ContinuousFlexibility.Analysis.N07aAngularReferenceCompatibleSource
import ContinuousFlexibility.Analysis.N07aScalarColumnVolumes

/-!
# The genuine compatible reference source in the prescribed volume graph

The reference source of an arbitrary transported height is its actual
remainder differential plus the original left and distinguished columns.
All three summands have already been constructed in the same volume
space. No membership assumption on the candidate source is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}

local instance n07aReferenceSourceVolumeLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aReferenceSourceVolumeLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _

theorem n07a_referenceCompatibleSource_on_piece
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {v : PolarPoint → ℝ} (aL μ : ℝ) {m : ℕ}
    (hv : ContDiffOn ℝ ∞ v (referencePhysicalPieceOpen S K m))
    {p : PolarPoint} (hp : p ∈ referencePhysicalPieceOpen S K m) :
    n07aReferenceCompatibleSource D K v μ p =
      n07aReferenceRemainderDifferential D S v aL p +
        aL * divergenceOperator (L.coefficients (C.referenceState, 0))
          (fun q : PolarPoint => S.chiLeft q.1) p +
        μ * nuColumnField D S C (C.referenceState, 0) p := by
  have hpD : p ∈ annularOpen D := ⟨(h04.1.referenceBounds m).2.2 hp.1, mem_univ _⟩
  have hχ : ContDiffOn ℝ ∞ (fun q : PolarPoint => S.chiLeft q.1)
      (referencePhysicalPieceOpen S K m) := (hS.2.2.1.1.comp contDiff_fst).contDiffOn
  let r₀ : PolarPoint → ℝ := fun q => v q - aL * S.chiLeft q.1
  have hr : ContDiffOn ℝ ∞ r₀ (referencePhysicalPieceOpen S K m) :=
    hv.sub (contDiffOn_const.mul hχ)
  have he : v = fun q => r₀ q + aL * S.chiLeft q.1 := by
    funext q
    dsimp only [r₀]
    ring
  have hd : n07aReferenceDifferential D v p =
      n07aReferenceDifferential D r₀ p +
        aL * n07aReferenceDifferential D (fun q : PolarPoint => S.chiLeft q.1) p := by
    calc
      _ = n07aReferenceDifferential D (fun q => r₀ q + aL * S.chiLeft q.1) p :=
        congrArg (fun f : PolarPoint → ℝ => n07aReferenceDifferential D f p) he
      _ = _ := (n07a_referenceDifferential_add_on (isOpen_Ioo.prod isOpen_univ)
        hr (contDiffOn_const.mul hχ) hp).trans (congrArg
          (n07aReferenceDifferential D r₀ p + ·)
          (n07a_referenceDifferential_const_mul_on (isOpen_Ioo.prod isOpen_univ) hχ aL hp))
  simp only [n07aReferenceCompatibleSource, n07aReferenceInteriorDifferential_on_piece v hp,
    hd, n07a_referenceCutoff_column hS hT h01 h02 h03 hpD,
    n07a_nuColumnField_reference hS hT h01 hpD, n07aReferenceRemainderDifferential, r₀]

theorem n07a_referenceCompatibleSource_volume
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (hV : IsVolumeModel T S K V)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S) (μ : ℝ) {v : PolarPoint → ℝ}
    (hvp : Function.Periodic v (0, Real.pi)) (hve : ∀ r θ, v (r, -θ) = v (r, θ))
    (hv : ∀ m, EqOn v (n07aReferencePieceHeight C K (liftSectorParameter S C z)
      (K.inverseChart (liftSectorParameter S C z)) u.2 (heightPairField S u) m)
      (referencePhysicalPieceOpen S K m)) (t s : ℕ) :
    ∃ Fts : V.level (3 / 4 : ℝ) (t : ℝ) s,
      ∀ m, (V.forget (3 / 4 : ℝ) (t : ℝ) s Fts m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          canonicalSource S K (C.referenceState, 0) m
            (n07aReferenceCompatibleSource D K v μ) := by
  let remainder := n07a_referenceRemainderSource_volume
    hD hT hS h01 h04 href hcur hRatio hV z hz u hvp hve hv t s
  let F : V.level (3 / 4 : ℝ) (t : ℝ) s := remainder.choose
  have hF := remainder.choose_spec
  let columns := n07a_referenceScalarColumns_volume
    hD hS hT h01 h03 h04 href hV (3 / 4 : ℝ) (t : ℝ) s
  let W : Fin 3 → V.level (3 / 4 : ℝ) (t : ℝ) s := columns.choose
  have hW := columns.choose_spec
  refine ⟨F + u.2 • W 0 + μ • W 1, fun m => ?_⟩
  let col := n07aReferenceScalarOpenCoefficient href m (h04.1.referenceBounds m).2.1
  have hW₀ : V.forget (3 / 4 : ℝ) (t : ℝ) s (W 0) m = (col 0).toLp :=
    congrFun (hW 0) m
  have hW₁ : V.forget (3 / 4 : ℝ) (t : ℝ) s (W 1) m = (col 1).toLp :=
    congrFun (hW 1) m
  have hf : V.forget (3 / 4 : ℝ) (t : ℝ) s (F + u.2 • W 0 + μ • W 1) m =
      V.forget (3 / 4 : ℝ) (t : ℝ) s F m + u.2 • (col 0).toLp + μ • (col 1).toLp := by
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, hW₀, hW₁]
  have hfeq : (V.forget (3 / 4 : ℝ) (t : ℝ) s
      (F + u.2 • W 0 + μ • W 1) m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m]
        ((V.forget (3 / 4 : ℝ) (t : ℝ) s F m +
          u.2 • (col 0).toLp + μ • (col 1).toLp : CanonicalL2 S K m) : PolarPoint → ℝ) :=
    Filter.Eventually.of_forall (fun p : PolarPoint =>
      congrArg (fun v : CanonicalL2 S K m => v p) hf)
  refine hfeq.trans ?_
  have hsum := Lp.coeFn_add
    (V.forget (3 / 4 : ℝ) (t : ℝ) s F m + u.2 • (col 0).toLp) (μ • (col 1).toLp)
  have hsum₀ := Lp.coeFn_add (V.forget (3 / 4 : ℝ) (t : ℝ) s F m) (u.2 • (col 0).toLp)
  filter_upwards [hsum, hsum₀, Lp.coeFn_smul u.2 (col 0).toLp,
    Lp.coeFn_smul μ (col 1).toLp, hF m, (col 0).toLp_ae, (col 1).toLp_ae,
    n07a_canonicalOpen_ae (S := S) (K := K) (m := m)]
    with p hs₂ hs₁ hsm₀ hsm₁ hfp hc₀ hc₁ hp
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs₂ hs₁ hsm₀ hsm₁
  rw [hs₂, hs₁, hsm₀, hsm₁, hfp, hc₀, hc₁]
  have hphys := (h04.1.charts (C.referenceState, 0)
    (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector m).2.1 hp
  rw [h04.1.referenceDomain m] at hphys
  have hsrc := n07a_referenceCompatibleSource_on_piece hS hT h01 h02 h03 h04 u.2 μ
    (n07a_referenceTransport_piece_smooth hS h01 h04 z hz u hv m) hphys
  have hcol₀ : (col 0).value p = canonicalSource S K (C.referenceState, 0) m
        (divergenceOperator (L.coefficients (C.referenceState, 0))
          (fun q : PolarPoint => S.chiLeft q.1)) p := by
    simpa only [n07aScalarColumn, Matrix.cons_val_zero] using
      congrFun (n07aReferenceScalarOpenCoefficient_value href m (h04.1.referenceBounds m).2.1 0) p
  have hcol₁ : (col 1).value p = canonicalSource S K (C.referenceState, 0) m
      (nuColumnField D S C (C.referenceState, 0)) p := by
    simpa only [n07aScalarColumn, Matrix.cons_val_one, Matrix.cons_val_zero] using
      congrFun (n07aReferenceScalarOpenCoefficient_value href m (h04.1.referenceBounds m).2.1 1) p
  refine (congrArg₂ (fun a b : ℝ => canonicalSource S K (C.referenceState, 0) m
    (n07aReferenceRemainderDifferential D S v u.2) p + u.2 * a + μ * b) hcol₀ hcol₁).trans ?_
  simp only [canonicalSource]
  rw [hsrc]
  ring

end ContinuousFlexibility.Analysis
