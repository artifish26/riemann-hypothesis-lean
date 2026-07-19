import RiemannHypothesisProject.RiemannVonMangoldt.BellottiWongGammaIntervalMonotonicity

/-!
# Finite interval boxes for Bennett's Gamma certificate

This module packages the monotone-component decomposition from the published
Proposition 3.2 notebook into endpoint bounds that can be checked interval by
interval.  The only nonmonotone component, `g11`, is replaced by a uniform
rational majorant.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- A uniform rational majorant for the notebook's `g11` component. -/
theorem bennettGammaIntervalRpowComponent_le_eight_div_eightyOne
    {T : Real} (hT : 0 < T) :
    bennettGammaIntervalRpowComponent T <= 8 / 81 := by
  let B : Real := 81 + 4 * T ^ 2
  have hB_pos : 0 < B := by dsimp [B]; positivity
  have hB_linear : 36 * T <= B := by
    dsimp [B]
    nlinarith [sq_nonneg (2 * T - 9)]
  have hsqrt_nine : 9 <= Real.sqrt B := by
    apply Real.le_sqrt_of_sq_le
    dsimp [B]
    nlinarith
  have hden : 324 * T <= B ^ (3 / 2 : Real) := by
    rw [show B ^ (3 / 2 : Real) = B * Real.sqrt B by
      dsimp [B]
      exact bennettGammaDenominator_rpow_three_halves T]
    calc
      324 * T = (36 * T) * 9 := by ring
      _ <= B * Real.sqrt B :=
        mul_le_mul hB_linear hsqrt_nine (by norm_num) hB_pos.le
  have hden_pos : 0 < B ^ (3 / 2 : Real) := Real.rpow_pos_of_pos hB_pos _
  unfold bennettGammaIntervalRpowComponent
  rw [Real.rpow_neg hB_pos.le]
  change 32 * T / B ^ (3 / 2 : Real) <= 8 / 81
  apply (div_le_iff₀ hden_pos).2
  nlinarith

/-- Sharp `g11` endpoint control on an interval below the critical height. -/
theorem bennettGammaIntervalRpowComponent_le_right_endpoint
    {a b T : Real} (ha : 0 <= a) (hab : a <= b)
    (hcritical : 8 * b ^ 2 <= 81) (haT : a <= T) (hTb : T <= b) :
    bennettGammaIntervalRpowComponent T <=
      bennettGammaIntervalRpowComponent b := by
  have hb : 0 <= b := ha.trans hab
  have hT : 0 <= T := ha.trans haT
  exact bennettGammaIntervalRpowComponent_monotoneOn_Icc hb hcritical
    (Set.mem_Icc.mpr ⟨hT, hTb⟩) (Set.mem_Icc.mpr ⟨hb, le_rfl⟩) hTb

/-- Sharp `g11` endpoint control on an interval above the critical height. -/
theorem bennettGammaIntervalRpowComponent_le_left_endpoint
    {a b T : Real} (ha : 0 <= a) (hcritical : 81 <= 8 * a ^ 2)
    (haT : a <= T) (hTb : T <= b) :
    bennettGammaIntervalRpowComponent T <=
      bennettGammaIntervalRpowComponent a := by
  exact bennettGammaIntervalRpowComponent_antitoneOn_Ici ha hcritical
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr haT) haT

/-- Upper endpoint box for the scaled upper envelope on `[a,b]`. -/
def bennettGammaScaledUpperIntervalBox (r a b : Real) : Real :=
  ((1 / 120 : Real) + 1 / (90 * Real.pi)) * r -
    1 / (3 * Real.pi) * bennettGammaIntervalRationalComponent a +
    1 / Real.pi *
      (2 * bennettGammaIntervalArctanComponent (1 / 2) b +
        2 * bennettGammaIntervalArctanComponent (5 / 2) b -
          (7 / 2 : Real) * bennettGammaIntervalArctanComponent (9 / 2) a) +
    1 / (2 * Real.pi) * bennettGammaIntervalLogComponent b

/-- Lower endpoint box for the scaled lower envelope on `[a,b]`. -/
def bennettGammaScaledLowerIntervalBox (r a b : Real) : Real :=
  (-(1 / 120 : Real) - 1 / (90 * Real.pi)) * r -
    1 / (3 * Real.pi) * bennettGammaIntervalRationalComponent b +
    1 / Real.pi *
      (2 * bennettGammaIntervalArctanComponent (1 / 2) a +
        2 * bennettGammaIntervalArctanComponent (5 / 2) a -
          (7 / 2 : Real) * bennettGammaIntervalArctanComponent (9 / 2) b) +
    1 / (2 * Real.pi) * bennettGammaIntervalLogComponent a

/-- Every scaled upper-envelope value on `[a,b]` lies below its endpoint box. -/
theorem bennettGammaScaledUpperEnvelope_le_intervalBox
    {r a b T : Real} (ha : 0 < a) (haT : a <= T) (hTb : T <= b)
    (hrpow : bennettGammaIntervalRpowComponent T <= r) :
    bennettGammaScaledUpperEnvelope T <=
      bennettGammaScaledUpperIntervalBox r a b := by
  have hT : 0 < T := ha.trans_le haT
  have hb : 0 < b := hT.trans_le hTb
  have hrational := bennettGammaIntervalRationalComponent_monotoneOn
    (Set.mem_Ici.mpr ha.le) (Set.mem_Ici.mpr hT.le) haT
  have hatanHalf := bennettGammaIntervalArctanComponent_monotoneOn
    (by norm_num : (0 : Real) <= 1 / 2)
    (Set.mem_Ioi.mpr hT) (Set.mem_Ioi.mpr hb) hTb
  have hatanFive := bennettGammaIntervalArctanComponent_monotoneOn
    (by norm_num : (0 : Real) <= 5 / 2)
    (Set.mem_Ioi.mpr hT) (Set.mem_Ioi.mpr hb) hTb
  have hatanNine := bennettGammaIntervalArctanComponent_monotoneOn
    (by norm_num : (0 : Real) <= 9 / 2)
    (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hT) haT
  have hlog := bennettGammaIntervalLogComponent_monotoneOn
    (Set.mem_Ioi.mpr hT) (Set.mem_Ioi.mpr hb) hTb
  unfold bennettGammaScaledUpperEnvelope bennettGammaScaledUpperIntervalBox
  gcongr

/-- Every scaled lower-envelope value on `[a,b]` lies above its endpoint box. -/
theorem bennettGammaScaledLowerIntervalBox_le_envelope
    {r a b T : Real} (ha : 0 < a) (haT : a <= T) (hTb : T <= b)
    (hrpow : bennettGammaIntervalRpowComponent T <= r) :
    bennettGammaScaledLowerIntervalBox r a b <=
      bennettGammaScaledLowerEnvelope T := by
  have hT : 0 < T := ha.trans_le haT
  have hb : 0 < b := hT.trans_le hTb
  have hrational := bennettGammaIntervalRationalComponent_monotoneOn
    (Set.mem_Ici.mpr hT.le) (Set.mem_Ici.mpr hb.le) hTb
  have hatanHalf := bennettGammaIntervalArctanComponent_monotoneOn
    (by norm_num : (0 : Real) <= 1 / 2)
    (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hT) haT
  have hatanFive := bennettGammaIntervalArctanComponent_monotoneOn
    (by norm_num : (0 : Real) <= 5 / 2)
    (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hT) haT
  have hatanNine := bennettGammaIntervalArctanComponent_monotoneOn
    (by norm_num : (0 : Real) <= 9 / 2)
    (Set.mem_Ioi.mpr hT) (Set.mem_Ioi.mpr hb) hTb
  have hlog := bennettGammaIntervalLogComponent_monotoneOn
    (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hT) haT
  have hnegativeRpow :
      (-(1 / 120 : Real) - 1 / (90 * Real.pi)) * r <=
        (-(1 / 120 : Real) - 1 / (90 * Real.pi)) *
          bennettGammaIntervalRpowComponent T :=
    mul_le_mul_of_nonpos_left hrpow
      (sub_nonpos.mpr (by
        have h : (0 : Real) <= 1 / (90 * Real.pi) := by positivity
        linarith))
  have hnegativeRational :
      -(1 / (3 * Real.pi)) * bennettGammaIntervalRationalComponent b <=
        -(1 / (3 * Real.pi)) * bennettGammaIntervalRationalComponent T :=
    mul_le_mul_of_nonpos_left hrational (neg_nonpos.mpr (by positivity))
  have hatanCombined :
      2 * bennettGammaIntervalArctanComponent (1 / 2) a +
          2 * bennettGammaIntervalArctanComponent (5 / 2) a -
            (7 / 2 : Real) * bennettGammaIntervalArctanComponent (9 / 2) b <=
        2 * bennettGammaIntervalArctanComponent (1 / 2) T +
          2 * bennettGammaIntervalArctanComponent (5 / 2) T -
            (7 / 2 : Real) * bennettGammaIntervalArctanComponent (9 / 2) T := by
    linarith
  have hatanScaled := mul_le_mul_of_nonneg_left hatanCombined
    (by positivity : (0 : Real) <= 1 / Real.pi)
  have hlogScaled := mul_le_mul_of_nonneg_left hlog
    (by positivity : (0 : Real) <= 1 / (2 * Real.pi))
  unfold bennettGammaScaledLowerEnvelope bennettGammaScaledLowerIntervalBox
  linarith

/-- The two numerical endpoint checks required at one interval-box leaf. -/
def BennettGammaScaledIntervalBoxValid (r a b : Real) : Prop :=
  -(1 / 25 : Real) <= bennettGammaScaledLowerIntervalBox r a b ∧
    bennettGammaScaledUpperIntervalBox r a b <= 1 / 25

/-- A finite binary subdivision certificate for a compact interval. -/
inductive BennettGammaScaledIntervalCertificate : Real -> Real -> Prop
  | box {a b : Real} (r : Real)
      (rpowBound : ∀ T : Real, a <= T -> T <= b ->
        bennettGammaIntervalRpowComponent T <= r)
      (valid : BennettGammaScaledIntervalBoxValid r a b) :
      BennettGammaScaledIntervalCertificate a b
  | split {a b : Real} (m : Real) (left_le : a <= m) (mid_le : m <= b)
      (left : BennettGammaScaledIntervalCertificate a m)
      (right : BennettGammaScaledIntervalCertificate m b) :
      BennettGammaScaledIntervalCertificate a b

/-- A finite interval certificate bounds both scaled envelopes at every point. -/
theorem BennettGammaScaledIntervalCertificate.bounds
    {a b : Real} (certificate : BennettGammaScaledIntervalCertificate a b)
    (ha : 0 < a) {T : Real} (haT : a <= T) (hTb : T <= b) :
    -(1 / 25 : Real) <= bennettGammaScaledLowerEnvelope T ∧
      bennettGammaScaledUpperEnvelope T <= 1 / 25 := by
  induction certificate generalizing T with
  | box r rpowBound valid =>
      have hrpow := rpowBound T haT hTb
      exact ⟨valid.1.trans
          (bennettGammaScaledLowerIntervalBox_le_envelope ha haT hTb hrpow),
        (bennettGammaScaledUpperEnvelope_le_intervalBox ha haT hTb hrpow).trans valid.2⟩
  | split m left_le mid_le left right left_ih right_ih =>
      by_cases hTm : T <= m
      · exact left_ih ha haT hTm
      · have hmT : m <= T := le_of_lt (lt_of_not_ge hTm)
        exact right_ih (ha.trans_le left_le) hmT hTb

/-- A checked finite subdivision discharges the compact notebook estimate. -/
theorem bennettGammaCompactScaledIntervalEstimate_of_certificate
    (certificate : BennettGammaScaledIntervalCertificate ((5 : Real) / 7) 8) :
    BennettGammaCompactScaledIntervalEstimate := by
  intro T hT hT8
  exact certificate.bounds (by norm_num) hT hT8

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
