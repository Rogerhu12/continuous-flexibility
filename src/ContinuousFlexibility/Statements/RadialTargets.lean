import ContinuousFlexibility.Statements.Radial

/-!
# Remaining radial milestone targets

Every declaration ending in `Statement` is a closed proposition to be proved.
The auxiliary records contain concrete functions and numbers; their properties
are expanded below and are not supplied as arbitrary proposition fields.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory Real
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

def radialOpenSpan (a b : ℝ) : Set ℝ := Ioo (min a b) (max a b)

abbrev RadialMatrix := Fin 2 → Fin 2 → ℝ

def radialMatrixApply (M : RadialMatrix) (x : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  ∑ j, M i j * x j

def radialMatrixProduct (M N : RadialMatrix) (i j : Fin 2) : ℝ :=
  ∑ k, M i k * N k j

def radialMatrixIdentity (i j : Fin 2) : ℝ := if i = j then 1 else 0

def radialAngleSine (v w : ℝ × ℝ) : ℝ :=
  |v.1 * w.2 - v.2 * w.1| /
    (sqrt (v.1 ^ 2 + v.2 ^ 2) * sqrt (w.1 ^ 2 + w.2 ^ 2))

def radialState (D : ReferenceData) (j : ℕ) (r scale : ℝ)
    (u : ℝ → ℝ) : ℝ × ℝ :=
  (u r, D.w r / scale * (r * deriv u r / (j : ℝ) ^ 2 - u r))

def radialFrequencyThreshold (T : MorseChainData) (C : ℝ) (n : ℕ) : ℝ :=
  C * radialQ n / sqrt (morseChainA T n)

def radialFrequencyBand (T : MorseChainData) (C : ℝ) (n j : ℕ) : Prop :=
  T.index ≤ n ∧
    (if n = T.index then (2 : ℝ) else radialFrequencyThreshold T C (n - 1)) ≤ j ∧
    (j : ℝ) < radialFrequencyThreshold T C n

def RadialHomogeneousOn (D : ReferenceData) (j : ℕ) (J : Set ℝ)
    (u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ u J ∧ ∀ r ∈ J, Radial.radialJacobi ((j : ℝ) ^ 2) D.w u r = 0

def radialTailInterval (D : ReferenceData) (right : Bool) (entry : ℝ) : Set ℝ :=
  if right then Ioo entry D.b else Ioo D.a entry

def RadialNaturalTail (D : ReferenceData) (right : Bool) (j : ℕ)
    (entry : ℝ) (u : ℝ → ℝ) : Prop :=
  ContDiffAt ℝ ∞ u entry ∧
    RadialHomogeneousOn D j (radialTailInterval D right entry) u ∧
    MemLp u 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right entry)) ∧
    (∃ r ∈ radialTailInterval D right entry, u r ≠ 0)

structure SelectedTailData where
  chain : MorseChainData
  family : (ℕ → ℝ) → ReferenceData
  constants : ℕ → ℝ
  sigma : ℕ → ℝ
  Cstar : ℝ
  c₀ : ℝ
  cut : Bool → ℕ → ℝ
  joinInner : Bool → ℕ → ℝ
  entry : Bool → ℕ → ℝ
  incoming : Bool → ℕ → ℝ → ℝ
  outgoing : Bool → ℕ → ℝ → ℝ

def IsSelectedTail (S : SelectedTailData) : Prop :=
  0 < S.Cstar ∧ 0 < S.c₀ ∧ (∀ n, 1 ≤ S.sigma n ∧ S.sigma n ≤ 2) ∧
    (∀ τ, (∀ n, 1 ≤ τ n ∧ τ n ≤ 2) →
      MorseChainRealization S.chain τ (S.family τ) S.constants ∧
      MorseMassResistanceBounds S.chain τ (S.family τ) S.constants) ∧
    (∀ j : ℕ, 2 ≤ j → Even j → ∃! n, radialFrequencyBand S.chain S.Cstar n j) ∧
    (∀ right n j, 2 ≤ j → Even j → radialFrequencyBand S.chain S.Cstar n j →
      let D := S.family S.sigma
      let c := S.cut right n
      let e := S.entry right n
      let join := S.joinInner right n
      let u := S.incoming right j
      let v := S.outgoing right j
      c ∈ radialCore D ∧ e ∈ radialCore D ∧ join ∈ radialCore D ∧ 0 < D.w join ∧
      (if right then c < join ∧ join < e else e < join ∧ join < c) ∧
      e = S.chain.radius right n
        (if right then S.chain.leftX right n else S.chain.rightX right n) ∧
      (if n = S.chain.index then
        (∃ scale : ℝ, 0 < scale ∧ D.w =ᶠ[𝓝 c] fun r => scale * r) ∧
        u c = 1 ∧ deriv u c = (if right then (j : ℝ) else -(j : ℝ)) / c
       else u c = 0 ∧ u join = 1 ∧
        (if right then 0 < deriv u c else deriv u c < 0)) ∧
      (∀ r ∈ radialOpenSpan c join, 0 < deriv D.w r) ∧
      ContDiffAt ℝ ∞ u c ∧ ContDiffAt ℝ ∞ u e ∧
      RadialHomogeneousOn D j (uIcc c e) u ∧
      RadialNaturalTail D right j e v ∧
      radialAngleSine (radialState D j e (D.w join) u)
        (radialState D j e (D.w join) v) ≥ S.c₀ * exp (-(n : ℝ) ^ 2))

/-- R07, §5 `lem:radial-product-selection`: one sequence before all frequencies. -/
def R07Statement : Prop := ∃ S : SelectedTailData, IsSelectedTail S

def CentralPatch (D : ReferenceData) (l h : ℝ) : Prop :=
  D.a < l ∧ l < Radial.centralRadius (-sqrt Radial.centralOscillatorA) ∧
    Radial.centralRadius (sqrt Radial.centralOscillatorA) < h ∧ h < D.b ∧
    ∃ scale amplitude : ℝ, 0 < scale ∧ amplitude ≠ 0 ∧
      (∀ r ∈ Ioo l h, D.w r = Radial.centralRadialProfile scale r) ∧
      (∀ r ∈ Ioo l h, D.phi r = amplitude * Radial.centralKernelHeight r)

/-- R08, §6 central target connection: actual nonzero global mode and
unchanged selected tails/negative components, with free positive-head length. -/
def R08Statement : Prop :=
  ∀ requiredHead : ℝ, 0 < requiredHead →
    ∃ S : SelectedTailData, IsSelectedTail S ∧ ∃ D : ReferenceData,
      IsAccumulatingProfile D ∧
      (∀ r ∈ radialCore D, Radial.radialJacobi 4 D.w D.phi r = 0) ∧
      ∃ l h : ℝ, CentralPatch D l h ∧
        (∃ l₁ l₂ h₁ h₂ cL cR : ℝ,
          D.a < l₁ ∧ l₁ < l₂ ∧ l₂ < l ∧ h < h₁ ∧ h₁ < h₂ ∧ h₂ < D.b ∧
          0 < cL ∧ 0 < cR ∧ log (l₂ / l₁) ≥ requiredHead ∧
          log (h₂ / h₁) ≥ requiredHead ∧
          (∀ r ∈ Ioo l₁ l₂, D.w r = cL * r) ∧
          (∀ r ∈ Ioo h₁ h₂, D.w r = cR * r) ∧
          (∀ r ∈ Ioo l₂ l, 0 < deriv D.w r) ∧
          (∀ r ∈ Ioo h h₁, 0 < deriv D.w r)) ∧
        (∀ right : Bool, ∃ radiusScale heightScale amplitude : ℝ,
          0 < radiusScale ∧ 0 < heightScale ∧ amplitude ≠ 0 ∧
          (if right then D.b = radiusScale * (S.family S.sigma).b
           else D.a = radiusScale * (S.family S.sigma).a) ∧
          (∀ r ∈ radialTailInterval (S.family S.sigma) right
            (S.entry right S.chain.index),
            radiusScale * r ∈ radialTailInterval D right (if right then h else l) ∧
            D.w (radiusScale * r) =
              heightScale * radiusScale * (S.family S.sigma).w r ∧
            D.phi (radiusScale * r) = amplitude * S.outgoing right 2 r) ∧
          (∀ l₁ h₁, NegativeRadialComponent (S.family S.sigma) l₁ h₁ →
            Ioo l₁ h₁ ⊆ radialTailInterval (S.family S.sigma) right
              (S.entry right S.chain.index) →
            NegativeRadialComponent D (radiusScale * l₁) (radiusScale * h₁) ∧
              radialTravel D (radiusScale * l₁) (radiusScale * h₁) =
                radialTravel (S.family S.sigma) l₁ h₁))

/-! ## Actual positive-buffer compression (R09) -/

def IntervalEnergyCore (V : ℝ → ℝ) (l h : ℝ) :
    Set (RadialL2 × RadialL2 × RadialL2) :=
  {p | p ∈ SchrodingerEnergyCore V ∧
    (p.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo l h)ᶜ)] (fun _ => 0)}

def IntervalFormGraph (V : ℝ → ℝ) (l h : ℝ) (u f : RadialL2) : Prop :=
  ∃ d q : RadialL2, (u, d, q) ∈ closure (IntervalEnergyCore V l h) ∧
    ∀ p ∈ closure (IntervalEnergyCore V l h),
      ⟪f, p.1⟫_ℝ = ⟪d, p.2.1⟫_ℝ + ∫ x : ℝ, V x * u x * p.1 x

def BorderedFullGraph (V : ℝ → ℝ) (g : RadialL2) (bordered : Bool)
    (U F : RadialL2 × ℝ) : Prop :=
  if bordered then
    WeakSchrodingerGraph V U.1 (F.1 - U.2 • g) ∧ ⟪g, U.1⟫_ℝ = F.2
  else WeakSchrodingerGraph V U.1 F.1 ∧ U.2 = 0 ∧ F.2 = 0

def BorderedIntervalGraph (V : ℝ → ℝ) (g : RadialL2) (bordered : Bool) (l h : ℝ)
    (U F : RadialL2 × ℝ) : Prop :=
  if bordered then
    IntervalFormGraph V l h U.1 (F.1 - U.2 • g) ∧ ⟪g, U.1⟫_ℝ = F.2
  else IntervalFormGraph V l h U.1 F.1 ∧ U.2 = 0 ∧ F.2 = 0

structure BufferData where
  bordered : Bool
  potential : ℝ → ℝ
  border : RadialL2
  l : ℝ
  h : ℝ
  mass : Fin 2 → ℝ
  action : Fin 2 → ℝ
  B₀ : ℝ
  layerBound : ℝ
  borderFunction : ℝ → ℝ

def bufferCut (B : BufferData) (i : Fin 2) : ℝ := if i = 0 then B.l else B.h
def bufferSign (i : Fin 2) : ℝ := if i = 0 then -1 else 1

def bufferInnerWall (B : BufferData) (i : Fin 2) : ℝ :=
  bufferCut B i - bufferSign i * (B.action i + 6) / B.mass i

def bufferExterior (B : BufferData) (i : Fin 2) : Set ℝ :=
  if i = 0 then Iio B.l else Ioi B.h

def BufferHypotheses (B : BufferData) : Prop :=
  B.l < B.h ∧ bufferInnerWall B 0 < bufferInnerWall B 1 ∧
    0 < B.B₀ ∧ 0 < B.layerBound ∧ ContDiff ℝ ∞ B.potential ∧
    ActualClosedFormRealization B.potential ∧
    ContDiff ℝ ∞ B.borderFunction ∧ HasCompactSupport B.borderFunction ∧
    ((B.border : ℝ → ℝ) =ᵐ[volume] B.borderFunction) ∧
    Function.support B.borderFunction ⊆
      Ioo (bufferInnerWall B 0) (bufferInnerWall B 1) ∧
    (∀ i, 0 < B.mass i ∧ 0 < B.action i) ∧
    ((B.border : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0)) ∧
    (∀ i x, (if i = 0 then x ≤ B.l + (B.action i + 6) / B.mass i
      else B.h - (B.action i + 6) / B.mass i ≤ x) → B.mass i ^ 2 ≤ B.potential x) ∧
    (∀ i x, |x - bufferCut B i| ≤ 4 / B.mass i ∨
      |x - bufferInnerWall B i| ≤ 4 / B.mass i →
      B.potential x ≤ B.layerBound * B.mass i ^ 2) ∧
    (∃ H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ), ‖H‖ ≤ B.B₀ ∧
      (∀ F, (B.bordered = false → F.2 = 0) →
        BorderedFullGraph B.potential B.border B.bordered (H F) F) ∧
      (∀ U F, BorderedFullGraph B.potential B.border B.bordered U F → H F = U))

def BufferCompressionConclusion (B : BufferData) (C : ℝ) : Prop :=
  ∃ G : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ),
    ‖G‖ ≤ B.B₀ + C * ∑ i, (B.mass i)⁻¹ ^ 2 ∧
    (∀ F : RadialL2 × ℝ, (B.bordered = false → F.2 = 0) →
      ((F.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0)) →
      BorderedIntervalGraph B.potential B.border B.bordered B.l B.h (G F) F) ∧
    (∀ U F, BorderedIntervalGraph B.potential B.border B.bordered B.l B.h U F → G F = U) ∧
    ∃ pin pout p : Fin 2 → ℝ → ℝ, ∃ P : Fin 2 → RadialL2,
    ∃ scalar αin αout : Fin 2 → ℝ,
      (∀ i,
        ContDiffOn ℝ 2 (pin i) (uIcc (bufferCut B i) (bufferInnerWall B i)) ∧
        ContDiffOn ℝ 2 (pout i) (closure (bufferExterior B i)) ∧
        IntervalIntegrable (fun x => deriv (pin i) x ^ 2 + B.potential x * pin i x ^ 2)
          volume (bufferCut B i) (bufferInnerWall B i) ∧
        IntegrableOn (fun x => deriv (pout i) x ^ 2 + B.potential x * pout i x ^ 2)
          (bufferExterior B i) volume ∧
        ContDiffAt ℝ ∞ (pin i) (bufferCut B i) ∧
        ContDiffAt ℝ ∞ (pout i) (bufferCut B i) ∧
        pin i (bufferCut B i) = 1 ∧ pin i (bufferInnerWall B i) = 0 ∧
        pout i (bufferCut B i) = 1 ∧
        MemLp (pout i) 2 (volume.restrict (bufferExterior B i)) ∧
        (∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
          -deriv (deriv (pin i)) x + B.potential x * pin i x = 0) ∧
        (∀ x ∈ bufferExterior B i,
          -deriv (deriv (pout i)) x + B.potential x * pout i x = 0) ∧
        αin i = bufferSign i * deriv (pin i) (bufferCut B i) ∧
        αout i = -bufferSign i * deriv (pout i) (bufferCut B i) ∧
        αin i = (∫ x in min (bufferCut B i) (bufferInnerWall B i)..
          max (bufferCut B i) (bufferInnerWall B i),
            deriv (pin i) x ^ 2 + B.potential x * pin i x ^ 2) ∧
        αout i = (∫ x in bufferExterior B i,
          deriv (pout i) x ^ 2 + B.potential x * pout i x ^ 2) ∧
        B.mass i / C ≤ αin i ∧ αin i ≤ C * B.mass i ∧
        B.mass i / C ≤ αout i ∧ αout i ≤ C * B.mass i) ∧
      (∀ i, ContDiffAt ℝ ∞ (p i) B.l ∧ ContDiffAt ℝ ∞ (p i) B.h ∧
        ContDiffOn ℝ ∞ (p i) (Ioo B.l B.h) ∧
        ContinuousOn (p i) (Icc B.l B.h) ∧
        ((P i : ℝ → ℝ) =ᵐ[volume.restrict (Ioo B.l B.h)] p i) ∧
        ((P i : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0)) ∧
        (if B.bordered then ⟪B.border, P i⟫_ℝ = 0 else scalar i = 0) ∧
        (∀ x ∈ Ioo B.l B.h,
          -deriv (deriv (p i)) x + B.potential x * p i x +
            scalar i * B.borderFunction x = 0) ∧
        ∀ j, p i (bufferCut B j) = if i = j then 1 else 0) ∧
      (∀ z : Fin 2 → ℝ,
        sqrt (‖∑ i, z i • P i‖ ^ 2 + (∑ i, z i * scalar i) ^ 2) ≤
          C * sqrt (∑ i, (B.mass i)⁻¹ ^ 2) *
          sqrt (∑ i, (αin i + αout i) * z i ^ 2)) ∧
      (∀ z : Fin 2 → ℝ, z ≠ 0 →
        0 < ∑ i, ∑ j, z i * bufferSign i * deriv (p j) (bufferCut B i) * z j) ∧
      (∀ i j, |(bufferSign i * deriv (p j) (bufferCut B i) -
        (if i = j then αin i else 0)) / sqrt ((αin i + αout i) * (αin j + αout j))| ≤
          C * B.B₀ * B.mass i * B.mass j * exp (-B.action i - B.action j))

/-- R09, §6 `lem:fence-compression`, retaining the actual differential
Dirichlet domain, symmetric border and true Poisson/conormal columns. -/
def R09Statement : Prop :=
  ∀ C₀ : ℝ, 0 < C₀ → ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ B : BufferData,
    B.layerBound ≤ C₀ → BufferHypotheses B →
    (∀ i, B.B₀ * B.mass i ^ 2 * exp (-B.action i) < ε) →
    BufferCompressionConclusion B C

/-! ## The matched global inverse and the fixed geometry (R10--R12, X01) -/

abbrev RadialModeL2 (D : ReferenceData) := MeasureTheory.Lp ℝ 2 (radialHilbertMeasure D)
abbrev RadialModePair (D : ReferenceData) := RadialModeL2 D × ℝ

def modePairing (D : ReferenceData) (U F : RadialModePair D) : ℝ :=
  ⟪U.1, F.1⟫_ℝ + U.2 * F.2

/-- Here B_j=-varpi⁻¹L_j, the source is in varpi dr, and the model
scalar is the negative of the physical L_j-border scalar.  The displayed
weak equation makes both conversions explicit. -/
def ModeLocalEquation (D : ReferenceData) (j : ℕ) (J : Set ℝ)
    (U F : RadialModePair D) : Prop :=
  ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → Function.support ψ ⊆ J →
    (∫ r in D.a..D.b, U.1 r * Radial.radialJacobi ((j : ℝ) ^ 2) D.w ψ r) -
      U.2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
      -(∫ r in D.a..D.b, (12 * D.w r / r ^ 2) * F.1 r * ψ r)

def ModeFullGraph (D : ReferenceData) (j : ℕ) (U F : RadialModePair D) : Prop :=
  ModeLocalEquation D j (radialCore D) U F ∧
    (if j = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * U.1 r) = F.2
     else U.2 = 0 ∧ F.2 = 0)

def ModeInverseProperties (D : ReferenceData) (j : ℕ)
    (G : RadialModePair D →L[ℝ] RadialModePair D) : Prop :=
  (∀ F, (j ≠ 2 → F.2 = 0) → ModeFullGraph D j (G F) F) ∧
    (∀ U F, ModeFullGraph D j U F → G F = U)

structure RadialMatchingData (D : ReferenceData) where
  frequency : ℕ
  transitionIndex : ℕ
  margin : ℝ
  D0 : Fin 2 → ℝ
  innerLeft : ℝ
  innerRight : ℝ
  boundaryScale : Fin 2 → ℝ
  sourceInner : RadialModePair D → RadialModePair D
  sourceOuter : RadialModePair D → RadialModePair D
  innerInverse : RadialModePair D →L[ℝ] RadialModePair D
  outerInverse : RadialModePair D →L[ℝ] RadialModePair D
  innerRepresentative : RadialModePair D → ℝ → ℝ
  outerRepresentative : RadialModePair D → ℝ → ℝ
  innerPoisson : Fin 2 → RadialModePair D
  outerPoisson : Fin 2 → RadialModePair D
  innerFunction : Fin 2 → ℝ → ℝ
  outerFunction : Fin 2 → ℝ → ℝ
  A : RadialMatrix
  B : RadialMatrix
  Db : RadialMatrix
  Kinv : RadialMatrix

def matchingCut (D : ReferenceData) (M : RadialMatchingData D) (i : Fin 2) : ℝ :=
  if i = 0 then M.innerLeft else M.innerRight

def matchingOuterRegion (D : ReferenceData) (M : RadialMatchingData D) : Set ℝ :=
  Ioo D.a M.innerLeft ∪ Ioo M.innerRight D.b

def matchingInnerFlux (D : ReferenceData) (M : RadialMatchingData D)
    (p : ℝ → ℝ) (i : Fin 2) : ℝ :=
  bufferSign i * D.w (matchingCut D M i) *
    derivWithin p (Icc M.innerLeft M.innerRight) (matchingCut D M i) /
      sqrt (M.boundaryScale i)

def matchingOuterFlux (D : ReferenceData) (M : RadialMatchingData D)
    (p : ℝ → ℝ) (i : Fin 2) : ℝ :=
  bufferSign i * D.w (matchingCut D M i) *
    derivWithin p (closure (matchingOuterRegion D M)) (matchingCut D M i) /
      sqrt (M.boundaryScale i)

def ModeInnerDirichletGraph (D : ReferenceData) (M : RadialMatchingData D)
    (U F : RadialModePair D) : Prop :=
  ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) U F ∧
  (if M.frequency = 2 then (∫ r in D.a..D.b, referenceColumn D r * U.1 r) = F.2
   else U.2 = 0 ∧ F.2 = 0) ∧
  ∃ u : ℝ → ℝ, ((U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u) ∧
    ContDiffOn ℝ 1 u (Icc M.innerLeft M.innerRight) ∧
    (∀ r ∈ matchingOuterRegion D M, u r = 0) ∧
    u M.innerLeft = 0 ∧ u M.innerRight = 0

def ModeOuterSeparatedGraph (D : ReferenceData) (M : RadialMatchingData D)
    (U F : RadialModePair D) : Prop :=
  ModeLocalEquation D M.frequency (matchingOuterRegion D M) U F ∧ U.2 = 0 ∧
  ∃ u : ℝ → ℝ, ((U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u) ∧
    ContDiffOn ℝ 1 u (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) ∧
    (∀ r ∈ Ioo M.innerLeft M.innerRight, u r = 0) ∧
    ∀ i, M.A i i * sqrt (M.boundaryScale i) * u (matchingCut D M i) +
      M.B i i * matchingOuterFlux D M u i = 0

def MatchingLocalRealizations (D : ReferenceData) (M : RadialMatchingData D) : Prop :=
  (∀ F, (M.frequency ≠ 2 → F.2 = 0) →
    ModeInnerDirichletGraph D M (M.innerInverse (M.sourceInner F)) (M.sourceInner F) ∧
    ModeOuterSeparatedGraph D M (M.outerInverse (M.sourceOuter F)) (M.sourceOuter F)) ∧
  (∀ U F, ModeInnerDirichletGraph D M U F → M.innerInverse F = U) ∧
  (∀ U F, ModeOuterSeparatedGraph D M U F → M.outerInverse F = U) ∧
  (∀ F, (M.sourceInner F).2 = F.2 ∧ (M.sourceOuter F).2 = 0 ∧
    ((M.sourceInner F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => if r ∈ Ioo M.innerLeft M.innerRight then F.1 r else 0) ∧
    ((M.sourceOuter F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => if r ∈ Ioo M.innerLeft M.innerRight then 0 else F.1 r)) ∧
  (∀ F,
    ((M.innerInverse (M.sourceInner F)).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      M.innerRepresentative F ∧
    ((M.outerInverse (M.sourceOuter F)).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      M.outerRepresentative F ∧
    ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight)
      (M.innerInverse (M.sourceInner F)) (M.sourceInner F) ∧
    ModeLocalEquation D M.frequency (matchingOuterRegion D M)
      (M.outerInverse (M.sourceOuter F)) (M.sourceOuter F) ∧
    ContDiffOn ℝ 1 (M.innerRepresentative F) (Icc M.innerLeft M.innerRight) ∧
    ContDiffOn ℝ 1 (M.outerRepresentative F)
      (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) ∧
    (∀ r ∈ matchingOuterRegion D M, M.innerRepresentative F r = 0) ∧
    (∀ r ∈ Ioo M.innerLeft M.innerRight, M.outerRepresentative F r = 0) ∧
    (if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * M.innerRepresentative F r) = F.2
     else (M.innerInverse (M.sourceInner F)).2 = 0) ∧
    (M.outerInverse (M.sourceOuter F)).2 = 0 ∧
    (∀ i, M.innerRepresentative F (matchingCut D M i) = 0) ∧
    (∀ i, M.A i i * sqrt (M.boundaryScale i) *
      M.outerRepresentative F (matchingCut D M i) +
      M.B i i * matchingOuterFlux D M (M.outerRepresentative F) i = 0)) ∧
  (∀ i,
    ((M.innerPoisson i).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] M.innerFunction i ∧
    ((M.outerPoisson i).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] M.outerFunction i ∧
    ((M.innerPoisson i).1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (matchingOuterRegion D M)] (fun _ => 0) ∧
    ((M.outerPoisson i).1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo M.innerLeft M.innerRight)] (fun _ => 0) ∧
    ContDiffOn ℝ 2 (M.innerFunction i) (Icc M.innerLeft M.innerRight) ∧
    ContDiffOn ℝ 2 (M.outerFunction i)
      (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) ∧
    (M.outerPoisson i).2 = 0 ∧
    ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (M.innerPoisson i) 0 ∧
    ModeLocalEquation D M.frequency (matchingOuterRegion D M) (M.outerPoisson i) 0 ∧
    (if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * M.innerFunction i r) = 0
     else (M.innerPoisson i).2 = 0) ∧
    (∀ k,
      M.innerFunction i (matchingCut D M k) = (if i = k then 1 else 0) /
        sqrt (M.boundaryScale k) ∧
      M.Db k i = matchingInnerFlux D M (M.innerFunction i) k ∧
      M.outerFunction i (matchingCut D M k) = M.A k i / sqrt (M.boundaryScale k) ∧
      matchingOuterFlux D M (M.outerFunction i) k = M.B k i))

def ActualMatchedRepresentation (D : ReferenceData)
    (G : RadialModePair D →L[ℝ] RadialModePair D) (M : RadialMatchingData D) : Prop :=
  D.a < M.innerLeft ∧ M.innerLeft < M.innerRight ∧ M.innerRight < D.b ∧
    Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight ∧
    0 < M.margin ∧
    (∀ i, 0 < M.boundaryScale i ∧ 0 < M.D0 i ∧ M.D0 i ≤ 1 / 2 ∧
      M.margin ≤ |M.A i i * M.D0 i - M.B i i|) ∧
    (∀ i j, |M.Db i j - (if i = j then M.D0 i else 0)| ≤ M.margin / 16) ∧
    (∀ i j, |M.Kinv i j| ≤ 4 / M.margin) ∧
    MatchingLocalRealizations D M ∧
    (∀ i j, M.Db i j = M.Db j i) ∧
    (∀ i j, i ≠ j → M.A i j = 0 ∧ M.B i j = 0) ∧
    (∀ i, M.A i i ^ 2 + M.B i i ^ 2 = 1) ∧
    radialMatrixProduct M.Kinv
      (fun i j => radialMatrixProduct M.A M.Db i j - M.B i j) = radialMatrixIdentity ∧
    radialMatrixProduct (fun i j => radialMatrixProduct M.A M.Db i j - M.B i j)
      M.Kinv = radialMatrixIdentity ∧
    (∀ F,
      let fh := M.sourceInner F
      let fo := M.sourceOuter F
      let h := fun i => modePairing D (M.innerPoisson i) fh
      let o := fun i => modePairing D (M.outerPoisson i) fo
      let x := radialMatrixApply M.Kinv (fun i => o i + radialMatrixApply M.A h i)
      let y := fun i => radialMatrixApply
        (fun a b => M.A a b + radialMatrixProduct M.B M.Db a b) x i -
          radialMatrixApply M.B h i
      G F = M.innerInverse fh + M.outerInverse fo +
        (∑ i, x i • M.innerPoisson i) + (∑ i, y i • M.outerPoisson i))

/-- R10, §6 actual matched inverse at every nonzero even mode.  The
Hilbert density and ordinary source conversion are explicit in ModeLocalEquation. -/
def R10Statement : Prop :=
  ∃ D : ReferenceData, IsAccumulatingProfile D ∧ RadialTrueBorder D ∧
    ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ G : RadialModePair D →L[ℝ] RadialModePair D,
        ModeInverseProperties D j G ∧
        ∃ M : RadialMatchingData D, M.frequency = j ∧ ActualMatchedRepresentation D G M

/-- R11, §6: the same geometry, border and inverse at all three exponents. -/
def R11Statement : Prop :=
  ∃ D : ReferenceData, IsAccumulatingProfile D ∧ RadialTrueBorder D ∧
    ∃ ε M₀ M₁ : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      ∃ G : RadialSource → RadialUnknown,
        (∀ j : ℕ, 2 ≤ j → Even j →
          ∃ Gmode : RadialModePair D →L[ℝ] RadialModePair D,
            ModeInverseProperties D j Gmode ∧
            ∃ M : RadialMatchingData D, M.frequency = j ∧ ActualMatchedRepresentation D Gmode M) ∧
        ∀ γ : ℝ, γ = referenceBeta - ε ∨ γ = referenceBeta ∨ γ = referenceBeta + ε →
          ReferenceInverseProperties D γ M₀ M₁ G ∧
          FirstNormalInverseEstimate D γ M₀ M₁ G

/-- Primitive geometry retained by the same radial construction that supplies
the natural graph and inverse. The optical assertion concerns the reference
profile alone, on each actual containing cell. It asserts no nonlinear
coefficient, speed, parameter derivative or flow estimate. -/
def RadialConstructionGeometry (D : ReferenceData) : Prop :=
  tsupport D.chi ⊆ radialCore D ∧
  ∃ K : ℝ, 0 < K ∧ ∀ l h m,
    NegativeRadialComponent D l h → Ioo l h ⊆ D.cells m →
    ∀ r ∈ Ioo l h,
      K⁻¹ * radialE (D.cellIndex m) ^ (-K) * min (r - l) (h - r) ≤
        -deriv D.w r / (r * D.w r)

/-- R12, §4 `prop:rad-fixed-theorem` and §6 `lem:rad-green-completion`.
The final border and optical geometry belong to this very reference;
independent existential witnesses cannot be combined here. -/
def R12Statement : Prop :=
  ∃ A : RadialReference, RadialConstructionGeometry A.val

/-- X01: first choose the actual geometry and inverse, then quantify over
all compact exponent intervals.  No interval-dependent profile is allowed. -/
def X01Statement : Prop :=
  ∃ D : ReferenceData, IsAccumulatingProfile D ∧ RadialNaturalKernels D ∧
    RadialReturnMargins D ∧ RadialTrueBorder D ∧
    ∃ G : RadialSource → RadialUnknown,
      ∀ γlo γhi : ℝ, 0 < γlo → γlo ≤ γhi → γhi < 1 →
        ∃ M₀ M₁ C : ℝ, 0 < C ∧ ∀ γ ∈ Icc γlo γhi,
          ReferenceInverseProperties D γ M₀ M₁ G ∧
          ReferenceGraphClosed D γ M₀ M₁ ∧ ReferenceSmoothCoreClosure D γ M₀ M₁ ∧
          ReferenceGreenReciprocity D γ M₀ M₁ ∧ FirstNormalInverseEstimate D γ M₀ M₁ G ∧
          (∀ F, SourceMember D γ M₀ F → ∃ aL : ℝ,
            OutputRealization D γ M₁ aL (G F) ∧
              outputNormSquare D γ M₁ aL (G F) ≤ C ^ 2 * sourceNormSquare D γ M₀ F) ∧
          (∀ F fθ, SourceMember D γ M₀ F → WeakAngularDerivative D F.1 fθ →
            SourceMember D γ M₀ (fθ, 0) → ∃ ur : PolarPoint → ℝ,
              WeakNormalDerivative D (G F).1 ur ∧ OutputRealization D γ M₁ 0 (ur, 0) ∧
              outputNormSquare D γ M₁ 0 (ur, 0) ≤ C ^ 2 *
                (sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (fθ, 0)))

end ContinuousFlexibility.Statements
