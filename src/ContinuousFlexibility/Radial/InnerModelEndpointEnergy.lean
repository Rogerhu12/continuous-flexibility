import ContinuousFlexibility.Radial.RetainedMorsePoissonBound
import ContinuousFlexibility.Radial.FixedCentralModelColumnCost

/-!
# Actual endpoint density is controlled by the same physical cut energy

Height and radius dilations cancel exactly.  These estimates pay the
Hardy endpoint term using the original model diagonal.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff

namespace InnerRadialModelChart

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central piece : Fin (n + 1)} {column : RadialModeL2 D}
  (A : InnerRadialModelChart D G bordered j central column piece)

theorem endpoint_weight_le_of_kappa (k : Fin 2 → ℝ)
    (hkappa : ∀ i, A.kappa i =
      A.height * A.scale (bufferCut A.buffer i) ^ 2 * k i)
    {L : ℝ} (hvelocity : ∀ i,
      deriv A.radius (bufferCut A.buffer i) / A.radius (bufferCut A.buffer i) ≤ L * k i)
    (i : Fin 2) :
    D.w (if i = 0 then G.left piece else G.right piece) /
      (if i = 0 then G.left piece else G.right piece) ≤ L * A.kappa i := by
  have hx : bufferCut A.buffer i ∈ Icc A.buffer.l A.buffer.h := by
    unfold bufferCut
    split_ifs
    · exact left_mem_Icc.mpr A.buffer_hypotheses.1.le
    · exact right_mem_Icc.mpr A.buffer_hypotheses.1.le
  have hcut : (if i = 0 then G.left piece else G.right piece) =
      A.radius (bufferCut A.buffer i) := by
    unfold bufferCut
    split_ifs <;> first | exact A.left_eq | exact A.right_eq
  rw [hcut, A.weight_identity _ hx, hkappa]
  calc
    _ = (A.height * A.scale (bufferCut A.buffer i) ^ 2) *
        (deriv A.radius (bufferCut A.buffer i) / A.radius (bufferCut A.buffer i)) := by ring
    _ ≤ (A.height * A.scale (bufferCut A.buffer i) ^ 2) * (L * k i) :=
      mul_le_mul_of_nonneg_left (hvelocity i)
        (mul_nonneg A.height_pos.le (sq_nonneg _))
    _ = _ := by ring

end InnerRadialModelChart

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
  (P : SeedRetainedPair S K q length) {D : ReferenceData}
  (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
  (G₀ : MorseChainGeometryWitness S.chain)
  (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
  {n : ℕ} (H : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
  (central piece : Fin (n + 1)) (column : RadialModeL2 D)
  (side : Bool) (m : ℕ) (hm : S.chain.index ≤ m) (haway : piece ≠ central)
  (hleft : H.left piece = P.sideRadius side * innerMorseChainCut S.chain side m 0)
  (hright : H.right piece = P.sideRadius side * innerMorseChainCut S.chain side m 1)
  {Cmodel Kmodel : ℝ}
  (hB : BufferHypotheses
    (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m)
      j (8 * (S.chain.d m : ℝ) ^ 9)))
  (M : InnerBufferLocalizedData
    (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m)
      j (8 * (S.chain.d m : ℝ) ^ 9)) Cmodel Kmodel)


theorem retainedMorseModelChart_endpoint_weight_bound
    (hj : 1 ≤ j) (hC : 0 < Cmodel) (i : Fin 2) :
    D.w (if i = 0 then H.left piece else H.right piece) /
      (if i = 0 then H.left piece else H.right piece) ≤
      (30000 * Cmodel) *
        (P.retainedMorseModelChart hw hS G₀ hband H bordered j central piece column
          side m hm haway hleft hright hB M).kappa i := by
  let A := P.retainedMorseModelChart hw hS G₀ hband H bordered j central piece column
    side m hm haway hleft hright hB M
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hjpos : 0 < j := zero_lt_one.trans_le hj
  apply A.endpoint_weight_le_of_kappa (fun k => (M.column k).inwardEnergy)
    (by
      intro k
      simpa only [one_pow, mul_one] using
        (P.retainedMorseModelChart_kappa hw hS G₀ hband H bordered j central piece column
          side m hm haway hleft hright hB M k)) ?_ i
  intro k
  let x := bufferCut A.buffer k
  have hx : x ∈ uIcc (bufferCut A.buffer k) (bufferInnerWall A.buffer k) := left_mem_uIcc
  have hr := hreal.radius_positive side m hm x
    (innerMorseChain_buffer_subset hreal side hm (innerBuffer_closedSpan_subset hB k hx))
  have he : deriv A.radius x / A.radius x =
      deriv (S.chain.radius side m) x / S.chain.radius side m x := by
    change deriv (fun y => P.sideRadius side * S.chain.radius side m y) x /
      (P.sideRadius side * S.chain.radius side m x) = _
    rw [deriv_const_mul_field]
    field_simp [(P.sideRadius_pos side).ne', hr.ne'] <;> ring
  rw [he]
  have hmass := buffer_mass_pos hB k
  have hv := (div_le_iff₀ hmass).mp
    (innerMorseChain_buffer_cap_ratio hreal side
      ((by norm_num : 10 ≤ 100).trans G₀.start_large) hm hjpos
      (8 * (S.chain.d m : ℝ) ^ 9) k hx)
  have hmα : A.buffer.mass k ≤ (M.column k).inwardEnergy * Cmodel :=
    (div_le_iff₀ hC).mp (M.column k).inward_lower
  have hjdiv : 30000 / j ≤ (30000 : ℝ) := by
    apply (div_le_iff₀ hjpos).mpr
    nlinarith only [hj]
  calc
    _ ≤ |deriv (S.chain.radius side m) x / S.chain.radius side m x| := le_abs_self _
    _ ≤ (30000 / j) * A.buffer.mass k := hv
    _ ≤ 30000 * ((M.column k).inwardEnergy * Cmodel) :=
      mul_le_mul hjdiv hmα hmass.le (by norm_num)
    _ = _ := by ring

end SeedRetainedPair

section Central

variable (B : FixedCentralBorder) (D : ReferenceData)
  (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
  {n : ℕ} (G : InnerRadialChainGeometry D n) (central : Fin (n + 1))
  (q : ℕ) {T B₀ C K : ℝ} (hT : 8 ≤ T)
  (hcap : sqrt centralOscillatorA + 2 ≤ T)
  (hcolumn : referenceColumn D = fixedCentralColumn B.chi)
  (hcore : Ioo (centralRadius (-T)) (centralRadius T) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc (-T) T,
    D.w (centralRadius x) = 1 * centralDensityRoot x ^ 2 * deriv centralRadius x)
  (hleft : G.left central = centralRadius (-T))
  (hright : G.right central = centralRadius T)
  (hB : BufferHypotheses (B.modelBuffer q T B₀))
  (M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K)

theorem fixedCentralPhysicalModelChart_endpoint_weight_bound (hq : 1 ≤ q)
    (hC : 0 < C)
    (henergy : ∀ i, 0 < fixedCentralModelCutEnergy M i ∧
      (M.column i).inwardEnergy ≤ 2 * fixedCentralModelCutEnergy M i) (i : Fin 2) :
    D.w (if i = 0 then G.left central else G.right central) /
      (if i = 0 then G.left central else G.right central) ≤
      (16 * C * centralRadiusWeightConstant) *
        (fixedCentralPhysicalModelChart B D hD hborder G central q hT hcap
          hcolumn hcore hw hleft hright hB M).kappa i := by
  let A := fixedCentralPhysicalModelChart B D hD hborder G central q hT hcap
    hcolumn hcore hw hleft hright hB M
  apply A.endpoint_weight_le_of_kappa (fixedCentralModelCutEnergy M)
    (fixedCentralPhysicalModelChart_kappa B D hD hborder G central q hT hcap
      hcolumn hcore hw hleft hright hB M) ?_ i
  intro k
  have hx : bufferCut A.buffer k ∈ Icc (-T) T := by
    change (if k = 0 then -T else T) ∈ Icc (-T) T
    split_ifs <;> constructor <;> linarith only [hT]
  have hv := (le_abs_self _).trans (A.log_deriv_bound _ hx)
  have hmα : centralBufferMass (2 * (q : ℝ)) T ≤ (M.column k).inwardEnergy * C :=
    (div_le_iff₀ hC).mp (M.column k).inward_lower
  have hαk := mul_le_mul_of_nonneg_right (henergy k).2 hC.le
  have hj : (2 : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * q)
  have hm : T / 2 ≤ centralBufferMass (2 * (q : ℝ)) T := by
    dsimp only [centralBufferMass]
    nlinarith only [mul_le_mul_of_nonneg_right hj (by linarith only [hT] : 0 ≤ T)]
  have hTk : T ≤ 4 * C * fixedCentralModelCutEnergy M k := by
    nlinarith only [hm, hmα, hαk]
  have hu : centralRadiusWeightConstant * (1 + T) ≤
      (16 * C * centralRadiusWeightConstant) * fixedCentralModelCutEnergy M k := by
    have h1T : 1 + T ≤ 2 * T := by linarith only [hT]
    have hmul := mul_le_mul_of_nonneg_left h1T centralRadiusWeightConstant_pos.le
    have hmul' := mul_le_mul_of_nonneg_left hTk
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) centralRadiusWeightConstant_pos.le)
    have hpos := mul_nonneg
      (mul_nonneg hC.le centralRadiusWeightConstant_pos.le) (henergy k).1.le
    nlinarith only [hmul, hmul', hpos]
  exact hv.trans hu

end Central

end ContinuousFlexibility.Radial
