import QSB.ByteLayout
import QSB.KeyRolls

/-!
A local first-selection overshoot analysis. At the beginning of the first
signed selection, the lock has pushed 302 fixed byte cells above the arbitrary
post-pinning stack. The candidate below makes the first selected commitment
come from the attacker-controlled stack. Even when that cell matches the
displaced opening, this initial-stack family cannot survive the next
fixed-index ScriptNum parse. The following eight cells are arbitrary bytes;
the later tail is bounded only for the modeled stack-size limit.
-/
namespace QSB.FirstOvershoot
open ByteMachine
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def pushValue : Op → Option Bytes
  | .push value => some value
  | _ => none

def fixedRegion : List Bytes :=
  (((ByteLayout.program.drop 6).take 302).filterMap pushValue).reverse

def pushedValues : List Bytes :=
  ((ByteLayout.program.drop 6).take 302).filterMap pushValue

def segment : List Op := (ByteLayout.program.drop 308).take 17

theorem fixed_region_length : fixedRegion.length = 302 := by decide

theorem generated_region_is_pushes :
    (ByteLayout.program.drop 6).take 302 = pushedValues.map Op.push := by decide

theorem generated_push_values_small :
    ∀ value ∈ pushedValues, value.length ≤ 520 := by
  have checked : List.Forall (fun value => value.length ≤ 520) pushedValues := by
    decide
  exact List.forall_iff_forall_mem.mp checked

theorem generated_region_pushes (hashes : Hashes)
    (stack : List Bytes) (outcomes : List Bool)
    (capacity : 302 + stack.length ≤ 1000) :
    run hashes ((ByteLayout.program.drop 6).take 302)
      (State.mk stack outcomes 5) =
      some (State.mk (fixedRegion ++ stack) outcomes 5) := by
  rw [generated_region_is_pushes]
  have count : pushedValues.length = 302 := by decide
  have enough : pushedValues.length + stack.length ≤ 1000 := by
    simpa [count] using capacity
  simpa [fixedRegion, pushedValues] using
    (ByteMachine.run_pushes hashes pushedValues stack outcomes 5
      generated_push_values_small enough (by omega))

theorem generated_prefix_split :
    ByteLayout.program.take 308 =
      ByteLayout.program.take 6 ++ (ByteLayout.program.drop 6).take 302 := by
  decide

def pinSignature : Bytes :=
  match ByteLayout.program[0]? with
  | some (Op.push sig) => sig
  | _ => []

theorem generated_pinning_opcodes : ByteLayout.program.take 6 =
    [.push pinSignature, .over, .checksigverify,
     .sha256, .swap, .checksigverify] := by decide

theorem pin_signature_fits : pinSignature.length ≤ 520 := by decide

theorem modeled_pinning_consumes_two_keys (hashes : Hashes)
    (nonce puzzle : Bytes) (stack : List Bytes)
    (outcomes : List Bool) (small : stack.length ≤ 996) :
    run hashes (ByteLayout.program.take 6)
      (State.mk (nonce :: puzzle :: stack) (true :: true :: outcomes) 0) =
      some (State.mk stack outcomes 5) := by
  rw [generated_pinning_opcodes]
  unfold run step
  have pinSize : ¬ (pinSignature.length > 520) := by
    exact Nat.not_lt.mpr pin_signature_fits
  simp [pinSize]
  constructor
  · omega
  · unfold run step
    simp
    constructor
    · omega
    · unfold run step
      simp
      constructor
      · omega
      · unfold run step
        simp
        constructor
        · omega
        · unfold run step
          simp
          constructor
          · omega
          · unfold run step
            simp
            constructor
            · omega
            · rfl

theorem generated_prefix_after_pinning (hashes : Hashes)
    (initial : State) (stack : List Bytes) (outcomes : List Bool)
    (pinning : run hashes (ByteLayout.program.take 6) initial =
      some (State.mk stack outcomes 5))
    (capacity : 302 + stack.length ≤ 1000) :
    run hashes (ByteLayout.program.take 308) initial =
      some (State.mk (fixedRegion ++ stack) outcomes 5) := by
  rw [generated_prefix_split, ByteMachine.run_append, pinning]
  simp [generated_region_pushes hashes stack outcomes capacity]

theorem segment_is_first_two_selection_prefix : segment =
    [.push [0x2e, 0x01], .roll, .push [0x98, 0x00], .min,
     .dup, .push [0x97, 0x00], .add, .roll,
     .push [0x37, 0x01], .roll, .hash160, .equalverify, .roll,
     .push [0x2d, 0x01], .roll, .push [0x98, 0x00], .min] := by decide

def firstCommitment : Bytes := (fixedRegion[152]?).getD []
def lastCommitment : Bytes := (fixedRegion[301]?).getD []

theorem first_commitment_is_twenty_bytes : firstCommitment.length = 20 := by decide
theorem last_commitment_is_twenty_bytes : lastCommitment.length = 20 := by decide
theorem last_commitment_is_not_scriptnum :
    ByteIndex.parseScriptNum lastCommitment = none := by decide

theorem shifted_last_from_any_tail (tail : List Bytes) :
    (fixedRegion.eraseIdx 152 ++ tail)[300]? = some lastCommitment := by
  rw [List.getElem?_append_left (by decide)]
  decide

theorem first_index_roll (external : Bytes) (tail : List Bytes) :
    KeyRolls.rollAt 302
      (fixedRegion ++ [0x98, 0x00] :: external :: tail) =
      some ([0x98, 0x00] :: fixedRegion ++ external :: tail) := by
  rfl

theorem first_index_roll_raw (raw external : Bytes) (tail : List Bytes) :
    KeyRolls.rollAt 302 (fixedRegion ++ raw :: external :: tail) =
      some (raw :: fixedRegion ++ external :: tail) := by
  rfl

theorem external_commitment_roll (external : Bytes) (tail : List Bytes) :
    KeyRolls.rollAt 303
      ([0x98, 0x00] :: (fixedRegion ++ external :: tail)) =
      some (external :: [0x98, 0x00] :: (fixedRegion ++ tail)) := by
  rfl

theorem displaced_preimage_roll
    (external a b c d e f g h : Bytes) (tail : List Bytes) :
    KeyRolls.rollAt 311
      (external :: [0x98, 0x00] :: (fixedRegion ++
        a :: b :: c :: d :: e :: f :: g :: h :: tail)) =
      some (h :: external :: [0x98, 0x00] :: (fixedRegion ++
        a :: b :: c :: d :: e :: f :: g :: tail)) := by
  rfl

theorem retained_index_roll (tail : List Bytes) :
    KeyRolls.rollAt 152 (fixedRegion ++ tail) =
      some (firstCommitment :: fixedRegion.eraseIdx 152 ++ tail) := by
  rfl

theorem byte_roll_matches_list_roll (hashes : Hashes)
    (raw : Bytes) (n : Nat) (stack : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (decoded : ByteIndex.parseScriptNum raw = some (Int.ofNat n))
    (budget : cost + 1 ≤ 201) :
    step hashes .roll (State.mk (raw :: stack) outcomes cost) =
      (KeyRolls.rollAt n stack).map
        (fun next => State.mk next outcomes (cost + 1)) := by
  unfold step KeyRolls.rollAt
  have within : ¬ (cost + 1 > 201) := by omega
  simp [within, decoded]

/-- After the retained 152 is rolled, it gathers the first lock commitment.
The next fixed 301-roll, independent of all attacker cells below this region,
then selects the last lock commitment as the next numeric index. -/
theorem next_index_is_lock_commitment (tail : List Bytes) :
    (KeyRolls.rollAt 301
      (firstCommitment :: fixedRegion.eraseIdx 152 ++ tail)).bind
      (fun stack => stack.head?) = some lastCommitment := by
  simp [KeyRolls.rollAt, shifted_last_from_any_tail]

def afterSecondRoll (tail : List Bytes) : List Bytes :=
  (firstCommitment :: (fixedRegion.eraseIdx 152 ++ tail)).eraseIdx 301

theorem next_index_roll_full (tail : List Bytes) :
    KeyRolls.rollAt 301
      (firstCommitment :: (fixedRegion.eraseIdx 152 ++ tail)) =
      some (lastCommitment :: afterSecondRoll tail) := by
  simp [KeyRolls.rollAt, shifted_last_from_any_tail, afterSecondRoll]

theorem second_min_rejects_commitment (hashes : Hashes)
    (tail : List Bytes) (outcomes : List Bool) (cost : Nat) :
    step hashes .min
      (State.mk ([0x98, 0x00] :: lastCommitment :: tail) outcomes cost) = none := by
  unfold step
  by_cases limitExceeded : cost + 1 > 201
  · simp [limitExceeded]
  · simp [limitExceeded, last_commitment_is_not_scriptnum]

theorem parse_151 : ByteIndex.parseScriptNum [0x97, 0x00] = some 151 := by decide
theorem encode_303 : ByteIndex.encodeScriptNum 303 = some [0x2f, 0x01] := by decide
theorem parse_303 : ByteIndex.parseScriptNum [0x2f, 0x01] = some 303 := by decide
theorem parse_311 : ByteIndex.parseScriptNum [0x37, 0x01] = some 311 := by decide

/-- The first signed selection normalizes every nonnegative ScriptNum value at
least 152 to the same canonical two-byte value after `OP_MIN`, including
nonminimal raw encodings accepted by the parser. -/
theorem oversized_index_clamps_to_152 (raw : Bytes) (value : Int)
    (parsed : ByteIndex.parseScriptNum raw = some value)
    (large : 152 ≤ value) :
    (do
      let cap ← ByteIndex.parseScriptNum [0x98, 0x00]
      let index ← ByteIndex.parseScriptNum raw
      ByteIndex.encodeScriptNum (min cap index)) = some [0x98, 0x00] := by
  simp [ByteIndex.positive_152, parsed, min_eq_left large,
    ByteIndex.encode_positive_152]

theorem oversized_index_min_step (hashes : Hashes)
    (raw : Bytes) (value : Int) (stack : List Bytes)
    (outcomes : List Bool) (cost : Nat)
    (parsed : ByteIndex.parseScriptNum raw = some value)
    (large : 152 ≤ value) (budget : cost + 1 ≤ 201) :
    step hashes .min
      (State.mk ([0x98, 0x00] :: raw :: stack) outcomes cost) =
      some (State.mk ([0x98, 0x00] :: stack) outcomes (cost + 1)) := by
  unfold step
  have within : ¬ (cost + 1 > 201) := by omega
  simp [within, ByteIndex.positive_152, parsed,
    min_eq_left large, ByteIndex.encode_positive_152]

def forcedFailureSuffix : List Op :=
  [.roll, .push [0x2d, 0x01], .roll, .push [0x98, 0x00], .min]

def firstSelectionPrefix : List Op := (ByteLayout.program.drop 308).take 12

def firstIndexPrefix : List Op := (ByteLayout.program.drop 308).take 4
def firstComparisonLead : List Op := (ByteLayout.program.drop 312).take 6
def beforeFirstComparison : List Op := (ByteLayout.program.drop 308).take 10

theorem first_index_prefix_opcodes : firstIndexPrefix =
    [.push [0x2e, 0x01], .roll, .push [0x98, 0x00], .min] := by decide

theorem segment_split_first_index :
    segment = firstIndexPrefix ++ segment.drop 4 := by decide

theorem first_comparison_lead_opcodes : firstComparisonLead =
    [.dup, .push [0x97, 0x00], .add, .roll,
      .push [0x37, 0x01], .roll] := by decide

theorem before_first_comparison_split :
    beforeFirstComparison = firstIndexPrefix ++ firstComparisonLead := by decide

theorem oversized_first_index_prefix (hashes : Hashes)
    (raw external : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (value : Int)
    (parsed : ByteIndex.parseScriptNum raw = some value)
    (large : 152 ≤ value) (small : tail.length ≤ 690) :
    run hashes firstIndexPrefix
      (State.mk (fixedRegion ++ raw :: external :: tail) outcomes 5) =
      some (State.mk
        ([0x98, 0x00] :: fixedRegion ++ external :: tail) outcomes 7) := by
  rw [first_index_prefix_opcodes]
  unfold run step
  simp
  constructor
  · rw [fixed_region_length]
    omega
  · unfold run
    rw [byte_roll_matches_list_roll hashes [0x2e, 0x01] 302
      (fixedRegion ++ raw :: external :: tail) outcomes 5 (by decide) (by omega)]
    rw [first_index_roll_raw]
    simp
    constructor
    · rw [fixed_region_length]
      omega
    · unfold run
      unfold step
      simp
      constructor
      · rw [fixed_region_length]
        omega
      · unfold run
        rw [oversized_index_min_step hashes raw value
          (fixedRegion ++ external :: tail) outcomes 6 parsed large (by omega)]
        simp
        rw [fixed_region_length]
        constructor
        · omega
        · rfl

theorem first_comparison_lead_reaches_opening (hashes : Hashes)
    (external a b c d e f g h : Bytes)
    (tail : List Bytes) (outcomes : List Bool)
    (small : tail.length ≤ 680) :
    run hashes firstComparisonLead
      (State.mk
        ([0x98, 0x00] :: fixedRegion ++
          external :: a :: b :: c :: d :: e :: f :: g :: h :: tail)
        outcomes 7) =
      some (State.mk
        (h :: external :: [0x98, 0x00] :: fixedRegion ++
          a :: b :: c :: d :: e :: f :: g :: tail)
        outcomes 11) := by
  rw [first_comparison_lead_opcodes]
  unfold run step
  simp
  constructor
  · rw [fixed_region_length]
    omega
  · unfold run
    unfold step
    simp
    constructor
    · rw [fixed_region_length]
      omega
    · unfold run
      unfold step
      simp [parse_151, ByteIndex.positive_152, encode_303]
      constructor
      · rw [fixed_region_length]
        omega
      · unfold run
        rw [byte_roll_matches_list_roll hashes [0x2f, 0x01] 303
          ([0x98, 0x00] :: (fixedRegion ++
            external :: a :: b :: c :: d :: e :: f :: g :: h :: tail))
          outcomes 9 parse_303 (by omega)]
        rw [external_commitment_roll]
        simp
        constructor
        · rw [fixed_region_length]
          omega
        · unfold run
          unfold step
          simp
          constructor
          · rw [fixed_region_length]
            omega
          · unfold run
            rw [byte_roll_matches_list_roll hashes [0x37, 0x01] 311
              (external :: [0x98, 0x00] ::
                (fixedRegion ++ a :: b :: c :: d :: e :: f :: g :: h :: tail))
              outcomes 10 parse_311 (by omega)]
            rw [displaced_preimage_roll]
            simp
            constructor
            · rw [fixed_region_length]
              omega
            · rfl

theorem oversized_before_first_comparison (hashes : Hashes)
    (raw external : Bytes) (value : Int)
    (a b c d e f g h : Bytes) (tail : List Bytes)
    (outcomes : List Bool)
    (parsed : ByteIndex.parseScriptNum raw = some value)
    (large : 152 ≤ value) (small : tail.length ≤ 680) :
    run hashes beforeFirstComparison
      (State.mk
        (fixedRegion ++ [raw, external, a, b, c, d, e, f, g, h] ++ tail)
        outcomes 5) =
      some (State.mk
        (h :: external :: [0x98, 0x00] :: fixedRegion ++
          a :: b :: c :: d :: e :: f :: g :: tail)
        outcomes 11) := by
  rw [before_first_comparison_split, run_append]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [oversized_first_index_prefix hashes raw external
    (a :: b :: c :: d :: e :: f :: g :: h :: tail)
    outcomes value parsed large (by simp; omega)]
  simp only [Option.bind_some]
  exact first_comparison_lead_reaches_opening hashes external
    a b c d e f g h tail outcomes small

theorem first_selection_prefix_opcodes : firstSelectionPrefix =
    [.push [0x2e, 0x01], .roll, .push [0x98, 0x00], .min,
     .dup, .push [0x97, 0x00], .add, .roll,
     .push [0x37, 0x01], .roll, .hash160, .equalverify] := by decide

theorem segment_split : segment = firstSelectionPrefix ++ forcedFailureSuffix := by
  decide

theorem segment_split_comparison :
    segment = beforeFirstComparison ++ [.hash160, .equalverify] ++
      forcedFailureSuffix := by decide

theorem overshoot_suffix_fails (hashes : Hashes)
    (tail : List Bytes) (outcomes : List Bool) (cost : Nat) :
    run hashes forcedFailureSuffix
      (State.mk ([0x98, 0x00] :: fixedRegion ++ tail) outcomes cost) = none := by
  unfold forcedFailureSuffix run
  by_cases budget1 : cost + 1 ≤ 201
  · simp only [List.cons_append]
    rw [byte_roll_matches_list_roll hashes [0x98, 0x00] 152
      (fixedRegion ++ tail) outcomes cost (by decide) budget1]
    rw [retained_index_roll]
    simp
    intro lengthOk
    unfold run
    unfold step
    simp
    intro budget2 size2
    unfold run
    by_cases budget3 : cost + 2 ≤ 201
    · rw [byte_roll_matches_list_roll hashes [0x2d, 0x01] 301
        (firstCommitment :: (fixedRegion.eraseIdx 152 ++ tail))
        outcomes (cost + 1) (by decide) (by omega)]
      rw [next_index_roll_full]
      simp
      intro size3
      unfold run
      unfold step
      simp
      intro budget4 size4
      unfold run
      rw [second_min_rejects_commitment]
      rfl
    · have exceeded : cost + 2 > 201 := by omega
      unfold step
      simp [exceeded]
  · have exceeded : cost + 1 > 201 := by omega
    unfold step
    simp [exceeded]

theorem first_selection_reaches_forced_suffix (hashes : Hashes)
    (a b c d e f g h : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (small : tail.length ≤ 680) :
    run hashes firstSelectionPrefix
      (State.mk
        (fixedRegion ++ [[0x98, 0x00], hashes.h160 h,
          a, b, c, d, e, f, g, h] ++ tail) outcomes 5) =
      some (State.mk
        ([0x98, 0x00] :: fixedRegion ++ [a, b, c, d, e, f, g] ++ tail)
        outcomes 13) := by
  rw [first_selection_prefix_opcodes]
  unfold run step
  simp
  constructor
  · rw [fixed_region_length]
    omega
  · unfold run
    rw [byte_roll_matches_list_roll hashes [0x2e, 0x01] 302
      (fixedRegion ++ [0x98, 0x00] :: hashes.h160 h ::
        a :: b :: c :: d :: e :: f :: g :: h :: tail)
      outcomes 5 (by decide) (by omega)]
    rw [first_index_roll]
    simp
    constructor
    · rw [fixed_region_length]
      omega
    · unfold run
      unfold step
      simp
      constructor
      · rw [fixed_region_length]
        omega
      · unfold run
        unfold step
        simp [ByteIndex.positive_152, ByteIndex.encode_positive_152]
        constructor
        · rw [fixed_region_length]
          omega
        · unfold run
          unfold step
          simp
          constructor
          · rw [fixed_region_length]
            omega
          · unfold run
            unfold step
            simp
            constructor
            · rw [fixed_region_length]
              omega
            · unfold run
              unfold step
              simp [parse_151, ByteIndex.positive_152, encode_303]
              constructor
              · rw [fixed_region_length]
                omega
              · unfold run
                rw [byte_roll_matches_list_roll hashes [0x2f, 0x01] 303
                  ([0x98, 0x00] :: (fixedRegion ++
                    hashes.h160 h :: a :: b :: c :: d :: e :: f :: g :: h :: tail))
                  outcomes 9 parse_303 (by omega)]
                rw [external_commitment_roll]
                simp
                constructor
                · rw [fixed_region_length]
                  omega
                · unfold run
                  unfold step
                  simp
                  constructor
                  · rw [fixed_region_length]
                    omega
                  · unfold run
                    rw [byte_roll_matches_list_roll hashes [0x37, 0x01] 311
                      (hashes.h160 h :: [0x98, 0x00] ::
                        (fixedRegion ++ a :: b :: c :: d :: e :: f :: g :: h :: tail))
                      outcomes 10 parse_311 (by omega)]
                    rw [displaced_preimage_roll]
                    simp
                    constructor
                    · rw [fixed_region_length]
                      omega
                    · unfold run
                      unfold step
                      simp
                      constructor
                      · rw [fixed_region_length]
                        omega
                      · unfold run
                        unfold step
                        simp
                        constructor
                        · rw [fixed_region_length]
                          omega
                        · rfl

theorem matched_first_overshoot_segment_fails (hashes : Hashes)
    (a b c d e f g h : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (small : tail.length ≤ 680) :
    run hashes segment
      (State.mk
        (fixedRegion ++ [[0x98, 0x00], hashes.h160 h,
          a, b, c, d, e, f, g, h] ++ tail) outcomes 5) = none := by
  rw [segment_split, run_append,
    first_selection_reaches_forced_suffix hashes a b c d e f g h tail outcomes small]
  simpa only [Option.bind_some, List.cons_append] using
    (overshoot_suffix_fails hashes (a :: b :: c :: d :: e :: f :: g :: tail)
      outcomes 13)

theorem oversized_first_overshoot_segment_fails (hashes : Hashes)
    (raw : Bytes) (value : Int) (a b c d e f g h : Bytes)
    (tail : List Bytes) (outcomes : List Bool)
    (parsed : ByteIndex.parseScriptNum raw = some value)
    (large : 152 ≤ value) (small : tail.length ≤ 680) :
    run hashes segment
      (State.mk
        (fixedRegion ++ [raw, hashes.h160 h,
          a, b, c, d, e, f, g, h] ++ tail) outcomes 5) = none := by
  have canonical :
      run hashes (segment.drop 4)
        (State.mk
          ([0x98, 0x00] :: fixedRegion ++
            hashes.h160 h :: a :: b :: c :: d :: e :: f :: g :: h :: tail)
          outcomes 7) = none := by
    have rejected := matched_first_overshoot_segment_fails hashes
      a b c d e f g h tail outcomes small
    rw [segment_split_first_index, run_append] at rejected
    simp only [List.append_assoc, List.cons_append, List.nil_append] at rejected
    rw [oversized_first_index_prefix hashes [0x98, 0x00]
      (hashes.h160 h) (a :: b :: c :: d :: e :: f :: g :: h :: tail)
      outcomes 152 (by decide) (by omega) (by simp; omega)] at rejected
    simpa only [Option.bind_some] using rejected
  rw [segment_split_first_index, run_append]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [oversized_first_index_prefix hashes raw
    (hashes.h160 h) (a :: b :: c :: d :: e :: f :: g :: h :: tail)
    outcomes value parsed large (by simp; omega)]
  simpa only [Option.bind_some] using canonical

/-- With this initial-stack shape, no external commitment value lets a parsed
first index of at least 152 survive the first two signed selections. A
mismatched marker fails the first HASH160 comparison; a matched one reaches
the later ScriptNum failure. -/
theorem oversized_any_marker_segment_fails (hashes : Hashes)
    (raw external : Bytes) (value : Int)
    (a b c d e f g h : Bytes)
    (tail : List Bytes) (outcomes : List Bool)
    (parsed : ByteIndex.parseScriptNum raw = some value)
    (large : 152 ≤ value) (small : tail.length ≤ 680) :
    run hashes segment
      (State.mk
        (fixedRegion ++ [raw, external,
          a, b, c, d, e, f, g, h] ++ tail) outcomes 5) = none := by
  by_cases matching : external = hashes.h160 h
  · subst external
    exact oversized_first_overshoot_segment_fails hashes raw value
      a b c d e f g h tail outcomes parsed large small
  · cases result : run hashes segment
        (State.mk
          (fixedRegion ++ [raw, external,
            a, b, c, d, e, f, g, h] ++ tail) outcomes 5) with
    | none => rfl
    | some final =>
        have accepted : run hashes
            (beforeFirstComparison ++ .hash160 :: .equalverify ::
              forcedFailureSuffix)
            (State.mk
              (fixedRegion ++ [raw, external,
                a, b, c, d, e, f, g, h] ++ tail) outcomes 5) =
            some final := by
          rw [segment_split_comparison] at result
          simpa only [List.append_assoc, List.cons_append,
            List.nil_append] using result
        have eq := ByteMachine.successful_hash_comparison_in_context
          hashes beforeFirstComparison forcedFailureSuffix
          (State.mk
            (fixedRegion ++ [raw, external,
              a, b, c, d, e, f, g, h] ++ tail) outcomes 5)
          h external
          ([0x98, 0x00] :: fixedRegion ++
            a :: b :: c :: d :: e :: f :: g :: tail)
          outcomes 11 final
          (oversized_before_first_comparison hashes raw external value
            a b c d e f g h tail outcomes parsed large small)
          accepted
        exact (matching eq.symm).elim

theorem generated_program_split :
    ByteLayout.program =
      ByteLayout.program.take 308 ++ segment ++ ByteLayout.program.drop 325 := by
  decide

/-- For the exact generated lock, a prefix state with this matched external
commitment shape cannot lead to acceptance. The premise about the prefix state
is not yet derived for every Bitcoin scriptSig or even every modeled witness. -/
theorem matched_first_overshoot_cannot_finish (hashes : Hashes)
    (initial : State) (a b c d e f g h : Bytes)
    (tail : List Bytes) (outcomes : List Bool)
    (small : tail.length ≤ 680)
    (prefix_state : run hashes (ByteLayout.program.take 308) initial =
      some (State.mk
        (fixedRegion ++ [[0x98, 0x00], hashes.h160 h,
          a, b, c, d, e, f, g, h] ++ tail) outcomes 5)) :
    run hashes ByteLayout.program initial = none := by
  rw [generated_program_split, List.append_assoc, run_append, prefix_state]
  simp only [Option.bind_some]
  rw [run_append, matched_first_overshoot_segment_fails hashes
    a b c d e f g h tail outcomes small]
  rfl

/-- The 302 generated pushes supply the exact region required above an
attacker stack after pinning. Only the pinning result remains a premise. -/
theorem matched_first_overshoot_after_pinning_fails (hashes : Hashes)
    (initial : State) (a b c d e f g h : Bytes)
    (tail : List Bytes) (outcomes : List Bool)
    (small : tail.length ≤ 680)
    (pinning : run hashes (ByteLayout.program.take 6) initial =
      some (State.mk
        ([[0x98, 0x00], hashes.h160 h, a, b, c, d, e, f, g, h] ++ tail)
        outcomes 5)) :
    run hashes ByteLayout.program initial = none := by
  apply matched_first_overshoot_cannot_finish hashes initial
    a b c d e f g h tail outcomes small
  apply generated_prefix_after_pinning hashes initial
    ([[0x98, 0x00], hashes.h160 h, a, b, c, d, e, f, g, h] ++ tail)
    outcomes pinning
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- The modeled full lock rejects this entire family of initial byte stacks.
The first two signature outcomes are assumed true to give the proposed escape
its best chance; if they fail, pinning rejects earlier. This is not a theorem
about arbitrary scriptSig layouts or Bitcoin Core's ECDSA checker. -/
theorem matched_external_initial_stack_rejected (hashes : Hashes)
    (nonce puzzle a b c d e f g h : Bytes)
    (tail : List Bytes) (outcomes : List Bool)
    (small : tail.length ≤ 680) :
    run hashes ByteLayout.program
      (State.mk
        (nonce :: puzzle ::
          ([[0x98, 0x00], hashes.h160 h, a, b, c, d, e, f, g, h] ++ tail))
        (true :: true :: outcomes) 0) = none := by
  apply matched_first_overshoot_after_pinning_fails hashes
    (State.mk
      (nonce :: puzzle ::
        ([[0x98, 0x00], hashes.h160 h, a, b, c, d, e, f, g, h] ++ tail))
      (true :: true :: outcomes) 0)
    a b c d e f g h tail outcomes small
  apply modeled_pinning_consumes_two_keys hashes nonce puzzle
    ([[0x98, 0x00], hashes.h160 h, a, b, c, d, e, f, g, h] ++ tail)
    outcomes
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- The same modeled full-lock rejection holds for every raw first index whose
ScriptNum value is at least 152. This includes nonminimal encodings that the
model parser accepts, and is conditional on the two pin signatures succeeding.
It does not quantify over arbitrary unlocking scripts. -/
theorem oversized_external_initial_stack_rejected (hashes : Hashes)
    (nonce puzzle raw : Bytes) (value : Int)
    (a b c d e f g h : Bytes)
    (tail : List Bytes) (outcomes : List Bool)
    (parsed : ByteIndex.parseScriptNum raw = some value)
    (large : 152 ≤ value) (small : tail.length ≤ 680) :
    run hashes ByteLayout.program
      (State.mk
        (nonce :: puzzle ::
          ([raw, hashes.h160 h, a, b, c, d, e, f, g, h] ++ tail))
        (true :: true :: outcomes) 0) = none := by
  have pinning :
      run hashes (ByteLayout.program.take 6)
        (State.mk
          (nonce :: puzzle ::
            ([raw, hashes.h160 h, a, b, c, d, e, f, g, h] ++ tail))
          (true :: true :: outcomes) 0) =
        some (State.mk
          ([raw, hashes.h160 h, a, b, c, d, e, f, g, h] ++ tail)
          outcomes 5) := by
    apply modeled_pinning_consumes_two_keys
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have prefix_state := generated_prefix_after_pinning hashes
    (State.mk
      (nonce :: puzzle ::
        ([raw, hashes.h160 h, a, b, c, d, e, f, g, h] ++ tail))
      (true :: true :: outcomes) 0)
    ([raw, hashes.h160 h, a, b, c, d, e, f, g, h] ++ tail)
    outcomes pinning (by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
  rw [generated_program_split, List.append_assoc, run_append, prefix_state]
  simp only [Option.bind_some]
  rw [← List.append_assoc]
  rw [run_append, oversized_first_overshoot_segment_fails hashes raw value
    a b c d e f g h tail outcomes parsed large small]
  rfl

/-- No attacker-supplied marker byte string escapes through this full-lock
initial-stack family when the first index parses to at least 152. -/
theorem oversized_any_marker_initial_stack_rejected (hashes : Hashes)
    (nonce puzzle raw external : Bytes) (value : Int)
    (a b c d e f g h : Bytes)
    (tail : List Bytes) (outcomes : List Bool)
    (parsed : ByteIndex.parseScriptNum raw = some value)
    (large : 152 ≤ value) (small : tail.length ≤ 680) :
    run hashes ByteLayout.program
      (State.mk
        (nonce :: puzzle ::
          ([raw, external, a, b, c, d, e, f, g, h] ++ tail))
        (true :: true :: outcomes) 0) = none := by
  have pinning :
      run hashes (ByteLayout.program.take 6)
        (State.mk
          (nonce :: puzzle ::
            ([raw, external, a, b, c, d, e, f, g, h] ++ tail))
          (true :: true :: outcomes) 0) =
        some (State.mk
          ([raw, external, a, b, c, d, e, f, g, h] ++ tail)
          outcomes 5) := by
    apply modeled_pinning_consumes_two_keys
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have prefix_state := generated_prefix_after_pinning hashes
    (State.mk
      (nonce :: puzzle ::
        ([raw, external, a, b, c, d, e, f, g, h] ++ tail))
      (true :: true :: outcomes) 0)
    ([raw, external, a, b, c, d, e, f, g, h] ++ tail)
    outcomes pinning (by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
  rw [generated_program_split, List.append_assoc, run_append, prefix_state]
  simp only [Option.bind_some]
  rw [← List.append_assoc]
  rw [run_append, oversized_any_marker_segment_fails hashes raw external value
    a b c d e f g h tail outcomes parsed large small]
  rfl

end QSB.FirstOvershoot
