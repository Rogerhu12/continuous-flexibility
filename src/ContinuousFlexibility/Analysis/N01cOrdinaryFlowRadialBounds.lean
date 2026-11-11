import ContinuousFlexibility.Analysis.N01cOrdinaryFlowFixedBounds
import ContinuousFlexibility.Analysis.N01cAngularPrefixTransport
import ContinuousFlexibility.Analysis.N01cRadialPrefixConstants
import ContinuousFlexibility.Analysis.N01cWeightAbsorption

/-!
# Positive parameter prefixes of the actual positive-radial flow

The common base and radius are selected before every parameter prefix.
The raw speed loss and both interpolation losses are fixed there. The
angular prefix changes only the additive high-order loss. Finite
uniformization of the physical and parameter orders changes only the
material constants, and one canonical tower precedes all its orders.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

private theorem n01c_radialPrefix_commonNeighborhood
    {base loss : ℕ} {ε : ℝ}
    {Angular B Smooth Pos Target : ℕ → ℝ → Prop}
    {Zero : ∀ b e, B b e → Smooth b e → ℕ → Prop}
    {Whole : ℕ → ℕ → ℝ → Type*}
    {TimeTowers RadialTowers : ℕ → ℝ → Type*}
    {Interpolation : ℕ → ℕ → ℕ → Prop}
    (hangular : ∃ b e, base ≤ b ∧ 0 < e ∧ e ≤ min ε (1 / 2) ∧
      ∀ b', b ≤ b' → ∀ e', 0 < e' → e' ≤ e → Angular b' e')
    (hzero : ∃ b e, base ≤ b ∧ 0 < e ∧ e ≤ min ε (1 / 2) ∧
      ∃ hB : B b e, ∃ hG : Smooth b e, ∃ d : ℕ, Zero b e hB hG d)
    (hwhole : ∃ b e l, base ≤ b ∧ 0 < e ∧ e ≤ min ε (1 / 2) ∧
      ∀ b', b ≤ b' → ∀ e', 0 < e' → e' ≤ e → Nonempty (Whole b' l e'))
    (htower : ∃ b e, base ≤ b ∧ 0 < e ∧ e ≤ ε ∧
      ∀ b', b ≤ b' → ∀ e', 0 < e' → e' ≤ e →
        B b' e' ∧ Pos b' e' ∧ Nonempty (TimeTowers b' e') ∧
          Nonempty (RadialTowers b' e'))
    (hinterp : ∀ o : ℕ, ∃ b l : ℕ, Interpolation b l o)
    (hinterp_mono : ∀ b b' l o, b ≤ b' → Interpolation b l o →
      Interpolation b' l o)
    (hfinish : ∀ bq eq (hBq : B bq eq) (hGq : Smooth bq eq) d₀,
      Zero bq eq hBq hGq d₀ →
      ∀ lossRaw lossIz lossIp base' ε', bq ≤ base' → ε' ≤ eq →
      0 < ε' → ε' ≤ 1 / 2 → Angular base' ε' →
      ∀ hB' : B base' ε', Pos base' ε' →
      Whole base' lossRaw ε' → TimeTowers base' ε' → RadialTowers base' ε' →
      Interpolation base' lossIz (loss + d₀ + 2) →
      Interpolation base' lossIp 0 → Target base' ε') :
    ∃ base₀ : ℕ, ∃ ε₀ : ℝ,
      base ≤ base₀ ∧ 0 < ε₀ ∧ ε₀ ≤ min ε (1 / 2) ∧
      ∀ base', base₀ ≤ base' → ∀ ε', 0 < ε' → ε' ≤ ε₀ → Target base' ε' := by
  obtain ⟨ba, ea, hba, hea, heae, ha⟩ := hangular
  obtain ⟨bq, eq, _, heq, _, hBq, hGq, d₀, hQ⟩ := hzero
  obtain ⟨bw, ew, lossRaw, _, hew, _, hw⟩ := hwhole
  obtain ⟨bt, et, _, het, _, ht⟩ := htower
  obtain ⟨bz, lossIz, hiz⟩ := hinterp (loss + d₀ + 2)
  obtain ⟨bp, lossIp, hip⟩ := hinterp 0
  let base₀ : ℕ := max ba (max bq (max bw (max bt (max bz bp))))
  let ε₀ : ℝ := min ea (min eq (min ew et))
  have hbase₀ : base ≤ base₀ := hba.trans (le_max_left _ _)
  have hε₀ : 0 < ε₀ := lt_min hea (lt_min heq (lt_min hew het))
  have hε₀e : ε₀ ≤ min ε (1 / 2) := (min_le_left _ _).trans heae
  refine ⟨base₀, ε₀, hbase₀, hε₀, hε₀e, ?_⟩
  intro base' hbase' ε' hε' he'
  rcases max_le_iff.mp hbase' with ⟨hba', hbrest⟩
  rcases max_le_iff.mp hbrest with ⟨hbq', hbrest⟩
  rcases max_le_iff.mp hbrest with ⟨hbw', hbrest⟩
  rcases max_le_iff.mp hbrest with ⟨hbt', hbrest⟩
  rcases max_le_iff.mp hbrest with ⟨hbz', hbp'⟩
  rcases le_min_iff.mp he' with ⟨hea', herest⟩
  rcases le_min_iff.mp herest with ⟨heq', herest⟩
  rcases le_min_iff.mp herest with ⟨hew', het'⟩
  have he2 : ε' ≤ 1 / 2 := (hea'.trans heae).trans (min_le_right _ _)
  obtain ⟨hB', hpos, ⟨JT⟩, ⟨JR⟩⟩ := ht base' hbt' ε' hε' het'
  obtain ⟨W⟩ := hw base' hbw' ε' hε' hew'
  exact hfinish bq eq hBq hGq d₀ hQ lossRaw lossIz lossIp base' ε'
    hbq' heq' hε' he2 (ha base' hba' ε' hε' hea') hB' hpos W JT JR
    (hinterp_mono bz base' lossIz (loss + d₀ + 2) hbz' hiz)
    (hinterp_mono bp base' lossIp 0 hbp' hip)

theorem n01_exists_ordinaryFlowRadialPositivePrefixBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hSpeed : CharacteristicSpeedTameBounds D T S C base loss ε) :
    ∃ base₀ : ℕ, ∃ ε₀ : ℝ,
      base ≤ base₀ ∧ 0 < ε₀ ∧ ε₀ ≤ min ε (1 / 2) ∧
      ∀ base' : ℕ, base₀ ≤ base' →
      ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₀ →
      ∀ K : ℕ, ∃ dK : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
        ∀ m a b (q : PolarPoint), 0 < a → a + b ≤ s →
        q.1 ∈ Ioo (C.left m) (C.right m) →
        ∃ J : SmoothDirections (stateNeighborhood S C base' ε')
          (fun z => mixedDerivative a b (fun q => C.minusFlow z m q.1 q.2) q),
        ∀ j : ℕ, j ≤ K → 0 < j →
        ∀ z ∈ stateNeighborhood S C base' ε', ∀ v : Fin j → (AnnularState S × ℝ),
          min (q.1 - C.left m) (C.right m - q.1) ^ a * |J.D j z v| ≤
            B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
              T.E0 (T.sample (C.cell m)) ^ B *
              oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
                base' (s + loss + dK) (z - (C.referenceState, 0)) v := by
  let p := pairGrading (stateGrading S) realGrading
  have hp : Monotone p := jointStateGrading_monotone S
  refine n01c_radialPrefix_commonNeighborhood
    (loss := loss)
    (B := fun b e => N01PartB D S C b e)
    (Smooth := fun b e => ∀ z ∈ stateNeighborhood S C b e, ∀ m,
      ContDiff ℝ ∞ (fun q : PolarPoint => componentCosineSpeed D S C m (z, q)))
    (Zero := fun b e hBq hGq d₀ =>
      OrdinaryFlowZeroAngularGrowth hS hT hA hBq hGq loss d₀)
    (Interpolation := SpatialPowerInterpolation p)
    (n01_exists_ordinaryFlowAngularPositivePrefixBounds hS hT hA hε hB hG hE hSpeed)
    (n01_exists_ordinaryFlowZeroAngularGrowth hS hT hA hε hB hG hSpeed)
    (n01_exists_stable_commonWholeSpeed_powerControl hS hT hA hε hB hG hE)
    (n01_exists_stable_commonSpeed_towers hS hT hA hε hB hG hE)
    (fun o => exists_seminorm_spatialPower_bound p hp (jointStateGrading_hasInterpolation hS) o)
    (fun b b' l o hb hI => SpatialPowerInterpolation.mono_base hI hp hb) ?_
  intro bq eq hBq hGq d₀ hQ lossRaw lossIz lossIp base' ε'
    hbq' heq' hε' he2 ha hB' hpos W JT JR hIz hIp
  let o₀ : ℕ := loss + d₀ + 2
  have hsubq : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C bq eq :=
    stateNeighborhood_subset hbq' heq'
  have hzero : ∀ β : ℕ, 1 ≤ β → ∃ M : ℝ, 0 < M ∧
      ∀ m r, r ∈ Ioo (C.left m) (C.right m) → ∀ θ z,
      z ∈ stateNeighborhood S C base' ε' →
        |iteratedDeriv β (fun η => C.minusFlow z m r η) θ| ≤
          M * (1 + p (β - 1 + o₀) (z - (C.referenceState, 0))) := by
    intro β hβ
    obtain ⟨M, hM, hb⟩ := hQ.2 β hβ
    exact ⟨M, hM, fun m r hr θ z hz =>
      hb z (hsubq hz) m r ⟨hr.1.le, hr.2.le⟩ θ⟩
  have hsample (m : ℕ) : T.sample (C.cell m) ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
  have hH (m : ℕ) : 0 ≤ T.H (T.sample (C.cell m)) :=
    (hT.2.1 _ (hsample m)).2.1.le
  have hΘ (m : ℕ) : ∀ z ∈ stateNeighborhood S C base' ε',
      ContDiffOn ℝ ∞ (fun q : PolarPoint => C.minusFlow z m q.1 q.2)
        (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :=
    fun z hz => contDiffOn_minusFlow_of_cosineSpeed hS hT hA hB' hz m
      (contDiff_componentCosineSpeed hS hT hA hB' hpos hz m)
  intro K
  obtain ⟨offset, hpositive⟩ :=
    ordinaryFlowAngularPositivePrefix_to_fixedBounds (ha K)
  let L : ℕ := max lossRaw (max lossIz lossIp)
  let P : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → Prop := fun n b k s M A =>
    ∀ m r, r ∈ Ioo (C.left m) (C.right m) → ∀ θ : ℝ,
    ∀ J : SmoothDirections (stateNeighborhood S C base' ε')
      (fun z => mixedDerivative (n + 1) b (fun q => C.minusFlow z m q.1 q.2) (r, θ)),
    ∀ z ∈ stateNeighborhood S C base' ε', ∀ v : Fin k → (AnnularState S × ℝ),
      min (r - C.left m) (C.right m - r) ^ (n + 1) * |J.D k z v| ≤
        M * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ A *
          oneHighVariationWeight p base'
            (physicalFlowGraphTop s K offset + L) (z - (C.referenceState, 0)) v
  have hmono : ∀ n b k s M A M' A', 1 ≤ M → 0 ≤ A → M ≤ M' → A ≤ A' →
      P n b k s M A → P n b k s M' A' := by
    intro n b k s M A M' A' hM _ hMM hAA hb m r hr θ J z hz v
    have hfac : M * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ A ≤
        M' * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ A' :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right hMM (Real.rpow_nonneg (hH m) _))
        (Real.rpow_le_rpow_of_exponent_le (hE _ (hsample m)) hAA)
        (Real.rpow_nonneg (zero_le_one.trans (hE _ (hsample m))) _)
        (mul_nonneg ((zero_le_one.trans hM).trans hMM)
          (Real.rpow_nonneg (hH m) _))
    exact (hb m r hr θ J z hz v).trans
      (mul_le_mul_of_nonneg_right hfac (oneHighVariationWeight_nonneg p base' _ _ v))
  have hpoint : ∀ n b k s, 0 < k → k ≤ K → n + 1 + b ≤ s →
      ∃ M A : ℝ, 1 ≤ M ∧ 0 ≤ A ∧ P n b k s M A := by
    intro n b k s hk hkK hab
    exact ordinaryFlow_positiveMixed_fixed_bound hS hT hA hB' hpos hE he2
      W JT JR hIz hIp K offset n b k (physicalFlowGraphTop s K offset) hk hkK
      (physicalFlowGraph_slots_offset_le_top hab hkK)
      (physicalFlowGraph_order_le_top hab hkK) hzero hpositive
  have hprefix := n01c_finite_radial_prefix_constants P K hmono hpoint
  let dK : ℕ := (offset + 1) * (K + 1) + L
  refine ⟨dK, fun s => ?_⟩
  obtain ⟨M, A, hM, hA₀, hb⟩ := hprefix s
  obtain ⟨B, hBpos, habsorb⟩ :=
    exists_sameConstant_materialWeight_bound M A (3 / 4 : ℝ)
  refine ⟨B, hBpos, ?_⟩
  intro m a b q ha hab hq
  cases a with
  | zero => omega
  | succ n =>
      let J : SmoothDirections (stateNeighborhood S C base' ε')
          (fun z => mixedDerivative (n + 1) b (fun q => C.minusFlow z m q.1 q.2) q) :=
        ordinaryFlowPositiveMixedSmoothDirections hB' m (W.regular m).spatial (hΘ m)
          hq (fun a => JR m a q.1 hq)
          (ordinaryFlowJointSmoothDirections hS hT hA hB' hpos m (JT m)
            ⟨hq.1.le, hq.2.le⟩) n b q.2
      refine ⟨J, ?_⟩
      intro j hj hjpos z hz v
      have hraw := hb n b j hjpos hj (by simpa only [Nat.succ_eq_add_one] using hab)
        m q.1 hq q.2 J z hz v
      have hnormalized := habsorb
        (T.H (T.sample (C.cell m))) (T.E0 (T.sample (C.cell m)))
        (oneHighVariationWeight p base' (physicalFlowGraphTop s K offset + L)
          (z - (C.referenceState, 0)) v)
        (hH m) (hE _ (hsample m)) (oneHighVariationWeight_nonneg p base' _ _ v)
      exact (hraw.trans hnormalized).trans
        (n01c_materialOneHigh_mono p hp base'
          (by dsimp only [physicalFlowGraphTop, dK]; omega)
          hBpos.le le_rfl (hH m) (hE _ (hsample m)) (3 / 4 : ℝ)
          (z - (C.referenceState, 0)) v)

end ContinuousFlexibility.Blueprint
