import QSB.DynamicFinalInit

/-!
Value-independent source classification for a reached final-round signed
comparison. The actual seven-block interpreter proof is still separate; these
lemmas state the stack geometry it must preserve for dynamic commitment and
nonce bytes. No commitment-byte injectivity is assumed.
-/
namespace QSB.DynamicSignedSource
open ByteMachine
open FinalSignedLoop
open PoolRollInvariant
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def signedPrefixN (nonce retained : Bytes)
    (gathered dummies : List Bytes) : List Bytes :=
  [retained] ++ gathered ++ [nonce, []] ++ dummies

def region (nonce retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes) : List Bytes :=
  signedPrefixN nonce retained gathered dummies ++
    (commitments ++ prior :: tail)

def nextRawFrontN (nonce prior : Bytes)
    (gathered dummies commitments : List Bytes) : List Bytes :=
  gathered ++ [nonce, []] ++ dummies ++ commitments ++ [prior]

theorem literal_region (retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes) :
    region finalNonce retained prior gathered dummies commitments tail =
      signedRegion retained gathered dummies commitments prior tail := rfl

theorem literal_next_raw_front (prior : Bytes)
    (gathered dummies commitments : List Bytes) :
    nextRawFrontN finalNonce prior gathered dummies commitments =
      nextRawFront prior gathered dummies commitments := rfl

theorem next_raw_front_length (nonce prior : Bytes)
    (gathered dummies commitments : List Bytes)
    (shape : PoolShape gathered dummies commitments) :
    (nextRawFrontN nonce prior gathered dummies commitments).length =
      303 - gathered.length := by
  simp only [nextRawFrontN, List.length_append, List.length_cons,
    List.length_nil]
  rw [shape.commitmentCount]
  have count := shape.poolCount
  omega

/-- The literal fixed raw-index pair still fetches tail cell 283 when only
the final nonce and commitment bytes vary. -/
theorem accepted_fixed_raw_pair_dynamic (hashes : Hashes) (k : Fin 7)
    (nonce prior : Bytes) (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (count : gathered.length = k.val)
    (outcomes : List Bool) (cost : Nat) (after : State)
    (accepted : run hashes [.push (fixedRawIndex k), .roll]
      (State.mk (nextRawFrontN nonce prior gathered dummies commitments ++
        tail) outcomes cost) = some after) :
    ∃ enough : 283 < tail.length,
      after = State.mk
        (tail[283] :: nextRawFrontN nonce prior gathered dummies
          commitments ++ tail.eraseIdx 283) outcomes (cost + 1) := by
  have frontLength := next_raw_front_length nonce prior gathered dummies
    commitments shape
  have depth :
      (nextRawFrontN nonce prior gathered dummies commitments).length + 283 =
        586 - k.val := by
    rw [frontLength, count]
    omega
  have parsed := generated_fixed_raw_index_decodes k
  rw [← depth] at parsed
  exact accepted_push_roll_tail_shape hashes (fixedRawIndex k)
    (nextRawFrontN nonce prior gathered dummies commitments) tail
    outcomes cost after 283 parsed accepted

/-- The arbitrary commitment/nonce data block followed by the first fixed
raw-index pair fetches the same witness-tail cell 283 as the literal lock.
The preceding round's Boolean is an explicit one-byte-width premise at later
comparisons; this theorem only records its position. -/
theorem accepted_first_raw_pair_from_data (hashes : Hashes)
    (nonce prior : Bytes) (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (tail : List Bytes) (outcomes : List Bool) (cost : Nat)
    (after : State)
    (accepted : run hashes
      (DynamicFinalInit.dataOps nonce commitmentAt ++
        [.push (fixedRawIndex ⟨0, by decide⟩), .roll])
      (State.mk (prior :: tail) outcomes cost) = some after) :
    ∃ enough : 283 < tail.length,
      after = State.mk
        (tail[283] :: nextRawFrontN nonce prior [] finalDummyPool
          (DynamicFinalInit.commitmentPool commitmentAt) ++
          tail.eraseIdx 283) outcomes (cost + 1) := by
  rw [run_append] at accepted
  cases reached : run hashes (DynamicFinalInit.dataOps nonce commitmentAt)
      (State.mk (prior :: tail) outcomes cost) with
  | none => simp [reached] at accepted
  | some middle =>
      have dataShape := DynamicFinalInit.accepted_data_shape hashes nonce
        commitmentAt (prior :: tail) outcomes cost middle reached
      simp only [reached, Option.bind_some] at accepted
      rw [dataShape] at accepted
      have stackEq :
          nonce :: [] :: finalDummyPool ++
            DynamicFinalInit.commitmentPool commitmentAt ++ prior :: tail =
          nextRawFrontN nonce prior [] finalDummyPool
            (DynamicFinalInit.commitmentPool commitmentAt) ++ tail := by
        simp [nextRawFrontN, List.append_assoc]
      rw [stackEq] at accepted
      exact accepted_fixed_raw_pair_dynamic hashes ⟨0, by decide⟩
        nonce prior [] finalDummyPool
        (DynamicFinalInit.commitmentPool commitmentAt) tail
        (DynamicFinalInit.initial_pool_shape commitmentAt width)
        (by decide) outcomes cost after accepted

private def firstK : Fin 7 := ⟨0, by decide⟩

/-- The dynamic final-round prefix through its first HASH160/EQUALVERIFY.
This stops before the paired dummy roll; it does not assume the comparison
result or the later six signed blocks. -/
def firstComparisonProgram (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) : List Op :=
  (DynamicFinalInit.dataOps nonce commitmentAt ++
    [.push (fixedRawIndex firstK), .roll]) ++
    (signedCapAddOps firstK ++ signedComparisonOps firstK)

theorem literal_first_comparison_program :
    firstComparisonProgram finalNonce generatedCommitmentAt =
      (ByteLayout.program.drop 447).take 314 := by decide

/-- If the retained raw index can execute its later nonnegative `OP_ROLL`,
the earlier MIN/ADD comparison depth is at least the generated gap. The
serializer/reparser bounds matter here: the intermediate bytes need not be
minimal, and a negative original raw value is not ruled out directly. -/
theorem signed_offset_lower_of_nonnegative_retained (k : Fin 7)
    (retained offset : Bytes) (source operand index : Int)
    (retainedEncoded :
      ByteIndex.encodeScriptNum (min (152 : Int) source) = some retained)
    (retainedParsed : ByteIndex.parseScriptNum retained = some operand)
    (operandNonnegative : 0 ≤ operand)
    (offsetEncoded : ByteIndex.encodeScriptNum
      (Int.ofNat (151 - k.val) + operand) = some offset)
    (offsetParsed : ByteIndex.parseScriptNum offset = some index) :
    Int.ofNat (151 - k.val) ≤ index := by
  have operandBound := encoded_reparse_preserves_upper_bound
    (min (152 : Int) source) operand 152 retained
    (min_le_left _ _) (by omega) (by omega)
    retainedEncoded retainedParsed
  have gapNonnegative : 0 ≤ Int.ofNat (151 - k.val) :=
    Int.natCast_nonneg _
  have gapBound : Int.ofNat (151 - k.val) ≤ 151 := by
    exact Int.ofNat_le.mpr (Nat.sub_le 151 k.val)
  have sumNonnegative : 0 ≤ Int.ofNat (151 - k.val) + operand := by omega
  have sumBound : Int.ofNat (151 - k.val) + operand ≤ 303 := by omega
  have exact := encoded_nonnegative_reparse_exact
    (Int.ofNat (151 - k.val) + operand) index offset
    sumNonnegative sumBound offsetEncoded offsetParsed
  omega

theorem prefix_length (nonce retained : Bytes)
    (gathered dummies : List Bytes)
    (poolCount : gathered.length + dummies.length = 150) :
    (signedPrefixN nonce retained gathered dummies).length = 153 := by
  simp [signedPrefixN]
  omega

/-- Every shallow source at or after the two fixed nonce/zero cells is a
nine-byte dummy. This does not constrain the nonce's width. -/
theorem late_shallow_source_is_dummy (nonce retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (n : Nat) (late : gathered.length + 3 ≤ n)
    (shallow : n < 153) :
    ∃ j : Nat, j < dummies.length ∧
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        dummies[j]? := by
  let j := n - (gathered.length + 3)
  have within : j < dummies.length := by
    have count := shape.poolCount
    dsimp [j]
    omega
  have frontLength :
      ([retained] ++ gathered ++ [nonce, []]).length =
        gathered.length + 3 := by simp
  have position : n - ([retained] ++ gathered ++ [nonce, []]).length = j := by
    rw [frontLength]
  refine ⟨j, within, ?_⟩
  have regionEq : region nonce retained prior gathered dummies
      commitments tail =
      ([retained] ++ gathered ++ [nonce, []]) ++
        (dummies ++ (commitments ++ prior :: tail)) := by
    simp [region, signedPrefixN, List.append_assoc]
  rw [regionEq]
  rw [List.getElem?_append_right (by rw [frontLength]; omega)]
  rw [position]
  exact List.getElem?_append_left within

/-- For all seven generated signed rounds, any shallow depth at least 145
lands in the dummy pool. A 20-byte HASH160 result cannot match it, even if
the nonce signature itself is 20 bytes. -/
theorem high_shallow_hash_match_impossible (hashes : Hashes)
    (nonce retained prior opening : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (gatheredSmall : gathered.length ≤ 6)
    (n : Nat) (high : 145 ≤ n) (shallow : n < 153)
    (matched :
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some (hashes.h160 opening)) : False := by
  have late : gathered.length + 3 ≤ n := by omega
  obtain ⟨j, within, source⟩ :=
    late_shallow_source_is_dummy nonce retained prior gathered dummies
      commitments tail shape n late shallow
  rw [source] at matched
  have chosen : dummies[j] = hashes.h160 opening := by
    simpa [List.getElem?_eq_getElem within] using matched
  have width := shape.dummyWidth dummies[j] (List.getElem_mem within)
  rw [chosen] at width
  have hashWidth := hashes.h160_width opening
  omega

theorem prefix_wrong_width (nonce retained : Bytes)
    (gathered dummies commitments : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (nonceWrong : nonce.length ≠ 20) :
    ∀ x ∈ signedPrefixN nonce retained gathered dummies, x.length ≠ 20 := by
  intro x hx
  simp only [signedPrefixN, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with hfront | dummyHit
  · rcases hfront with hbefore | hnonceOrZero
    · rcases hbefore with hretained | gatheredHit
      · subst x
        omega
      · have width := shape.gatheredWidth x gatheredHit
        omega
    · rcases hnonceOrZero with hnonce | hzero
      · subst x
        exact nonceWrong
      · subst x
        decide
  · have width := shape.dummyWidth x dummyHit
    omega

/-- A twenty-byte value in the shallow window can only be the nonce
signature. This remains true even if its bytes equal some other value outside
that window. -/
theorem prefix_twenty_is_nonce (nonce retained : Bytes)
    (gathered dummies commitments : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (x : Bytes) (hit : x ∈ signedPrefixN nonce retained gathered dummies)
    (width : x.length = 20) :
    x = nonce := by
  simp only [signedPrefixN, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hit
  rcases hit with hfront | dummyHit
  · rcases hfront with hbefore | hnonceOrZero
    · rcases hbefore with hretained | gatheredHit
      · subst x
        omega
      · have gatheredWidth := shape.gatheredWidth x gatheredHit
        omega
    · rcases hnonceOrZero with hnonce | hzero
      · exact hnonce
      · subst x
        simp at width
  · have dummyWidth := shape.dummyWidth x dummyHit
    omega

theorem shallow_hash_match_is_nonce (hashes : Hashes)
    (nonce retained prior opening : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (n : Nat) (shallow : n < 153)
    (matched :
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some (hashes.h160 opening)) :
    nonce.length = 20 ∧ hashes.h160 opening = nonce := by
  have within : n < (signedPrefixN nonce retained gathered dummies).length := by
    rw [prefix_length nonce retained gathered dummies shape.poolCount]
    exact shallow
  let x := (signedPrefixN nonce retained gathered dummies)[n]
  have source :
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some x := by
    unfold region
    rw [List.getElem?_append_left within]
    exact List.getElem?_eq_getElem within
  have same : x = hashes.h160 opening :=
    Option.some.inj (source.symm.trans matched)
  have width : x.length = 20 := by
    rw [same]
    exact hashes.h160_width opening
  have isNonce : x = nonce :=
    prefix_twenty_is_nonce nonce retained gathered dummies commitments
      shape retainedSmall x (List.getElem_mem within) width
  exact ⟨isNonce ▸ width, same.symm.trans isNonce⟩

theorem shallow_source_wrong_width (nonce retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (nonceWrong : nonce.length ≠ 20)
    (n : Nat) (shallow : n < 153) :
    ∃ chosen : Bytes,
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some chosen ∧ chosen.length ≠ 20 := by
  have within : n < (signedPrefixN nonce retained gathered dummies).length := by
    rw [prefix_length nonce retained gathered dummies shape.poolCount]
    exact shallow
  let chosen := (signedPrefixN nonce retained gathered dummies)[n]
  have source :
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some chosen := by
    unfold region
    rw [List.getElem?_append_left within]
    exact List.getElem?_eq_getElem within
  exact ⟨chosen, source,
    prefix_wrong_width nonce retained gathered dummies commitments
      shape retainedSmall nonceWrong chosen (List.getElem_mem within)⟩

theorem commitment_source (nonce retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (poolCount : gathered.length + dummies.length = 150)
    (j : Nat) (within : j < commitments.length) :
    (region nonce retained prior gathered dummies commitments tail)[153 + j]? =
      commitments[j]? := by
  unfold region
  rw [List.getElem?_append_right (by
    rw [prefix_length nonce retained gathered dummies poolCount]
    omega)]
  have index : 153 + j -
      (signedPrefixN nonce retained gathered dummies).length = j := by
    rw [prefix_length nonce retained gathered dummies poolCount]
    omega
  rw [index]
  exact List.getElem?_append_left within

theorem capped_source_is_prior (nonce retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments) :
    (region nonce retained prior gathered dummies commitments tail)[303 -
      gathered.length]? = some prior := by
  have prefixLength := prefix_length nonce retained gathered dummies
    shape.poolCount
  have frontLength :
      (signedPrefixN nonce retained gathered dummies ++ commitments).length =
        303 - gathered.length := by
    simp only [List.length_append]
    rw [prefixLength, shape.commitmentCount]
    have count := shape.poolCount
    omega
  unfold region
  rw [← List.append_assoc]
  rw [List.getElem?_append_right (by rw [frontLength])]
  rw [frontLength]
  simp

/-- A bounded selection matching a twenty-byte HASH160 output cannot come
from the retained index, nonce, dummy signatures, or prior Boolean. It is one
of the current commitment cells, for arbitrary commitment bytes and stack
tail. The selected original index is recovered by a separate alignment fact. -/
theorem bounded_hash_match_is_commitment (hashes : Hashes)
    (nonce retained prior opening : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (nonceWrong : nonce.length ≠ 20)
    (priorWrong : prior.length ≠ 20)
    (n : Nat) (bounded : n ≤ 303 - gathered.length)
    (matched :
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some (hashes.h160 opening)) :
    ∃ j : Nat, j < commitments.length ∧ n = 153 + j ∧
      commitments[j]? = some (hashes.h160 opening) := by
  by_cases shallow : n < 153
  · obtain ⟨chosen, source, wrong⟩ :=
      shallow_source_wrong_width nonce retained prior gathered dummies
        commitments tail shape retainedSmall nonceWrong n shallow
    have same : chosen = hashes.h160 opening :=
      Option.some.inj (source.symm.trans matched)
    exact False.elim (wrong (same ▸ hashes.h160_width opening))
  let j := n - 153
  by_cases within : j < commitments.length
  · have index : n = 153 + j := by omega
    have source := commitment_source nonce retained prior gathered
      dummies commitments tail shape.poolCount j within
    rw [index] at matched
    exact ⟨j, within, index, source.symm.trans matched⟩
  · have capIndex : n = 303 - gathered.length := by
      have count := shape.poolCount
      have commitmentCount := shape.commitmentCount
      omega
    have source := capped_source_is_prior nonce retained prior gathered
      dummies commitments tail shape
    rw [capIndex] at matched
    have same : prior = hashes.h160 opening :=
      Option.some.inj (source.symm.trans matched)
    exact False.elim (priorWrong (same ▸ hashes.h160_width opening))

/-- Without a nonce-width premise, a matched bounded signed selection has
one additional possible source class: the nonce bytes themselves must be a
twenty-byte HASH160 output. A dynamic-lock theorem must exclude or charge
this branch rather than silently treating every match as a HORS commitment. -/
theorem bounded_hash_match_nonce_or_commitment (hashes : Hashes)
    (nonce retained prior opening : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (priorWrong : prior.length ≠ 20)
    (n : Nat) (bounded : n ≤ 303 - gathered.length)
    (matched :
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some (hashes.h160 opening)) :
    (nonce.length = 20 ∧ hashes.h160 opening = nonce) ∨
    (∃ j : Nat, j < commitments.length ∧ n = 153 + j ∧
      commitments[j]? = some (hashes.h160 opening)) := by
  by_cases shallow : n < 153
  · exact Or.inl <|
      shallow_hash_match_is_nonce hashes nonce retained prior opening
        gathered dummies commitments tail shape retainedSmall n
        shallow matched
  · let j := n - 153
    by_cases within : j < commitments.length
    · have index : n = 153 + j := by omega
      have source := commitment_source nonce retained prior gathered
        dummies commitments tail shape.poolCount j within
      rw [index] at matched
      exact Or.inr ⟨j, within, index, source.symm.trans matched⟩
    · have capIndex : n = 303 - gathered.length := by
        have count := shape.poolCount
        have commitmentCount := shape.commitmentCount
        omega
      have source := capped_source_is_prior nonce retained prior gathered
        dummies commitments tail shape
      rw [capIndex] at matched
      have same : prior = hashes.h160 opening :=
        Option.some.inj (source.symm.trans matched)
      exact False.elim (priorWrong (same ▸ hashes.h160_width opening))

/-- A parsed comparison depth in the generated signed-round high range
cannot select the nonce, regardless of its byte width. With the capped
upper bound, a matching 20-byte target must be a current commitment. -/
theorem bounded_high_hash_match_is_commitment (hashes : Hashes)
    (nonce retained prior opening : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (gatheredSmall : gathered.length ≤ 6)
    (priorWrong : prior.length ≠ 20)
    (n : Nat) (high : 145 ≤ n)
    (bounded : n ≤ 303 - gathered.length)
    (matched :
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some (hashes.h160 opening)) :
    ∃ j : Nat, j < commitments.length ∧ n = 153 + j ∧
      commitments[j]? = some (hashes.h160 opening) := by
  by_cases shallow : n < 153
  · exact False.elim <|
      high_shallow_hash_match_impossible hashes nonce retained prior
        opening gathered dummies commitments tail shape gatheredSmall n
        high shallow matched
  let j := n - 153
  by_cases within : j < commitments.length
  · have index : n = 153 + j := by omega
    have source := commitment_source nonce retained prior gathered
      dummies commitments tail shape.poolCount j within
    rw [index] at matched
    exact ⟨j, within, index, source.symm.trans matched⟩
  · have capIndex : n = 303 - gathered.length := by
      have count := shape.poolCount
      have commitmentCount := shape.commitmentCount
      omega
    have source := capped_source_is_prior nonce retained prior gathered
      dummies commitments tail shape
    rw [capIndex] at matched
    have same : prior = hashes.h160 opening :=
      Option.some.inj (source.symm.trans matched)
    exact False.elim (priorWrong (same ▸ hashes.h160_width opening))

/-- The nonce-width exception disappears when the retained raw index has a
nonnegative parsed value, as required by its later dummy `OP_ROLL`. This
This theorem makes that parse condition explicit; a full-block run must
derive it from the reached final roll. -/
theorem matched_postadd_with_nonnegative_retained_is_commitment
    (hashes : Hashes) (k : Fin 7)
    (nonce retained prior offset opening : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (count : gathered.length = k.val)
    (priorWrong : prior.length ≠ 20)
    (source operand index : Int)
    (retainedEncoded :
      ByteIndex.encodeScriptNum (min (152 : Int) source) = some retained)
    (retainedParsed : ByteIndex.parseScriptNum retained = some operand)
    (operandNonnegative : 0 ≤ operand)
    (offsetEncoded : ByteIndex.encodeScriptNum
      (Int.ofNat (151 - k.val) + operand) = some offset)
    (offsetParsed : ByteIndex.parseScriptNum offset = some index)
    (indexNonnegative : 0 ≤ index)
    (matched :
      (region nonce retained prior gathered dummies commitments tail)[index.toNat]? =
        some (hashes.h160 opening)) :
    ∃ j : Nat, j < commitments.length ∧ index.toNat = 153 + j ∧
      commitments[j]? = some (hashes.h160 opening) := by
  have lower := signed_offset_lower_of_nonnegative_retained k
    retained offset source operand index retainedEncoded retainedParsed
    operandNonnegative offsetEncoded offsetParsed
  have upper := signed_cap_add_index_bound k retained offset source
    operand index retainedEncoded retainedParsed offsetEncoded offsetParsed
  have indexEq : index = Int.ofNat index.toNat :=
    Int.eq_natCast_toNat.mpr indexNonnegative
  have high : 145 ≤ index.toNat := by
    have small := k.isLt
    have gapHigh : 145 ≤ 151 - k.val := by omega
    rw [indexEq] at lower
    have lowerNat := Int.ofNat_le.mp lower
    omega
  have bounded : index.toNat ≤ 303 - gathered.length := by
    rw [indexEq] at upper
    have upperNat := Int.ofNat_le.mp upper
    rw [count]
    exact upperNat
  have gatheredSmall : gathered.length ≤ 6 := by
    rw [count]
    have small := k.isLt
    omega
  exact bounded_high_hash_match_is_commitment hashes nonce retained prior
    opening gathered dummies commitments tail shape gatheredSmall priorWrong
    index.toNat high bounded matched

/-- Alignment turns the matched current commitment cell into its original
HORS position. Equality of commitment bytes at different positions is allowed:
the index comes from the pool erasure history, not a reverse hash lookup. -/
theorem bounded_hash_match_has_original_position (hashes : Hashes)
    (commitmentAt : Fin 150 → Bytes)
    (ids : List (Fin 150))
    (nonce retained prior opening : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (aligned : DynamicFinalInit.AlignedPool commitmentAt ids
      dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (nonceWrong : nonce.length ≠ 20)
    (priorWrong : prior.length ≠ 20)
    (n : Nat) (bounded : n ≤ 303 - gathered.length)
    (matched :
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some (hashes.h160 opening)) :
    ∃ (id : Fin 150) (j : Nat),
      j < ids.length ∧ n = 153 + j ∧ ids[j]? = some id ∧
      hashes.h160 opening = commitmentAt id := by
  obtain ⟨j, within, index, hit⟩ :=
    bounded_hash_match_is_commitment hashes nonce retained prior opening
      gathered dummies commitments tail shape retainedSmall nonceWrong
      priorWrong n bounded matched
  have withinIds : j < ids.length := by
    rw [aligned.commitmentMap] at within
    simpa using within
  let id := ids[j]
  have source : commitments[j]? = some (commitmentAt id) := by
    simp [aligned.commitmentMap, id, withinIds]
  have equal : hashes.h160 opening = commitmentAt id :=
    Option.some.inj (hit.symm.trans source)
  exact ⟨id, j, withinIds, index,
    List.getElem?_eq_getElem withinIds, equal⟩

/-- Successful execution of the generated five-opcode comparison, starting
from an explicitly reached dynamic post-ADD stack, yields an opening whose
HASH160 target is either the nonce or a current commitment cell. The dynamic
seven-block invariant must still establish this starting stack and cap. -/
theorem accepted_comparison_nonce_or_commitment (hashes : Hashes)
    (k : Fin 7) (nonce retained prior offset : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (priorWrong : prior.length ≠ 20)
    (index : Nat)
    (parsed : ByteIndex.parseScriptNum offset = some (Int.ofNat index))
    (bounded : index ≤ 303 - gathered.length)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (signedComparisonOps k)
      (State.mk (offset :: region nonce retained prior gathered dummies
        commitments tail) outcomes cost) = some final) :
    ∃ opening : Bytes,
      (nonce.length = 20 ∧ hashes.h160 opening = nonce) ∨
      (∃ j : Nat, j < commitments.length ∧ index = 153 + j ∧
        commitments[j]? = some (hashes.h160 opening)) := by
  rw [generated_signed_comparison_ops] at accepted
  obtain ⟨afterRoll, rolled, _, suffix⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .roll
      [.push (preimageIndex k), .roll, .hash160, .equalverify]
      (State.mk (offset :: region nonce retained prior gathered dummies
        commitments tail) outcomes cost) final accepted
  have budget := ByteFinalCounts.roll_success_budget hashes offset
    (region nonce retained prior gathered dummies commitments tail)
    outcomes cost afterRoll rolled
  rw [FirstOvershoot.byte_roll_matches_list_roll hashes offset index
    (region nonce retained prior gathered dummies commitments tail)
    outcomes cost parsed budget] at rolled
  unfold KeyRolls.rollAt at rolled
  cases source : (region nonce retained prior gathered dummies
      commitments tail)[index]? with
  | none => simp [source] at rolled
  | some selected =>
      simp [source] at rolled
      rw [← rolled] at suffix
      have preimageParsed := generated_preimage_index_decodes k
      obtain ⟨opening, hit⟩ :=
        successful_target_matches_hash160_at hashes (preimageIndex k)
          (595 - 2 * k.val) preimageParsed (by omega)
          selected ((region nonce retained prior gathered dummies
            commitments tail).eraseIdx index) outcomes (cost + 1) final
          suffix
      have matched :
          (region nonce retained prior gathered dummies commitments tail)[index]? =
            some (hashes.h160 opening) := by
        rw [hit]
        exact source
      exact ⟨opening,
        bounded_hash_match_nonce_or_commitment hashes nonce retained prior
          opening gathered dummies commitments tail shape retainedSmall
          priorWrong index bounded matched⟩

/-- With the paired-pool erasure history, the successful comparison's
commitment branch names its original HORS position. -/
theorem accepted_comparison_nonce_or_original_position (hashes : Hashes)
    (commitmentAt : Fin 150 → Bytes) (ids : List (Fin 150))
    (k : Fin 7) (nonce retained prior offset : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (aligned : DynamicFinalInit.AlignedPool commitmentAt ids
      dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (priorWrong : prior.length ≠ 20)
    (index : Nat)
    (parsed : ByteIndex.parseScriptNum offset = some (Int.ofNat index))
    (bounded : index ≤ 303 - gathered.length)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (signedComparisonOps k)
      (State.mk (offset :: region nonce retained prior gathered dummies
        commitments tail) outcomes cost) = some final) :
    ∃ opening : Bytes,
      (nonce.length = 20 ∧ hashes.h160 opening = nonce) ∨
      (∃ (id : Fin 150) (j : Nat),
        j < ids.length ∧ index = 153 + j ∧ ids[j]? = some id ∧
        hashes.h160 opening = commitmentAt id) := by
  obtain ⟨opening, nonceHit | commitmentHit⟩ :=
    accepted_comparison_nonce_or_commitment hashes k nonce retained prior
      offset gathered dummies commitments tail shape retainedSmall
      priorWrong index parsed bounded outcomes cost final accepted
  · exact ⟨opening, Or.inl nonceHit⟩
  · obtain ⟨j, within, indexEq, hit⟩ := commitmentHit
    have withinIds : j < ids.length := by
      rw [aligned.commitmentMap] at within
      simpa using within
    let id := ids[j]
    have source : commitments[j]? = some (commitmentAt id) := by
      simp [aligned.commitmentMap, id, withinIds]
    have equal : hashes.h160 opening = commitmentAt id :=
      Option.some.inj (hit.symm.trans source)
    exact ⟨opening, Or.inr ⟨id, j, withinIds, indexEq,
      List.getElem?_eq_getElem withinIds, equal⟩⟩

theorem accepted_first_comparison_nonce_or_original_position
    (hashes : Hashes) (nonce prior : Bytes)
    (commitmentAt : Fin 150 → Bytes)
    (width : ∀ i, (commitmentAt i).length = 20)
    (priorWrong : prior.length ≠ 20)
    (tail : List Bytes) (outcomes : List Bool) (cost : Nat)
    (final : State)
    (accepted : run hashes (firstComparisonProgram nonce commitmentAt)
      (State.mk (prior :: tail) outcomes cost) = some final) :
    ∃ opening : Bytes,
      (nonce.length = 20 ∧ hashes.h160 opening = nonce) ∨
      (∃ (id : Fin 150) (j : Nat),
        j < (List.finRange 150).length ∧
        (List.finRange 150)[j]? = some id ∧
        (DynamicFinalInit.commitmentPool commitmentAt)[j]? =
          some (commitmentAt id) ∧
        hashes.h160 opening = commitmentAt id) := by
  unfold firstComparisonProgram at accepted
  rw [run_append] at accepted
  cases first : run hashes
      (DynamicFinalInit.dataOps nonce commitmentAt ++
        [.push (fixedRawIndex firstK), .roll])
      (State.mk (prior :: tail) outcomes cost) with
  | none => simp [first] at accepted
  | some afterFirst =>
      obtain ⟨enough, firstShape⟩ :=
        accepted_first_raw_pair_from_data hashes nonce prior commitmentAt
          width tail outcomes cost afterFirst first
      simp only [first, Option.bind_some] at accepted
      rw [firstShape, run_append] at accepted
      simp only [List.cons_append] at accepted
      cases cap : run hashes (signedCapAddOps firstK)
          (State.mk
            (tail[283] :: (nextRawFrontN nonce prior [] finalDummyPool
              (DynamicFinalInit.commitmentPool commitmentAt) ++
              tail.eraseIdx 283)) outcomes (cost + 1)) with
      | none => simp [cap] at accepted
      | some afterCap =>
          obtain ⟨source, operand, retained, offset, rawParsed,
              retainedEncoded, retainedParsed, offsetEncoded, capShape⟩ :=
            accepted_signed_cap_add_shape hashes firstK tail[283]
              (nextRawFrontN nonce prior [] finalDummyPool
                (DynamicFinalInit.commitmentPool commitmentAt) ++
                tail.eraseIdx 283) outcomes (cost + 1) afterCap cap
          simp only [cap, Option.bind_some] at accepted
          rw [capShape] at accepted
          have baseEq : retained ::
              (nextRawFrontN nonce prior [] finalDummyPool
                (DynamicFinalInit.commitmentPool commitmentAt) ++
                tail.eraseIdx 283) =
              region nonce retained prior [] finalDummyPool
                (DynamicFinalInit.commitmentPool commitmentAt)
                (tail.eraseIdx 283) := by
            simp [region, signedPrefixN, nextRawFrontN,
              List.append_assoc]
          rw [baseEq] at accepted
          have comparisonRun : run hashes (signedComparisonOps firstK)
              (State.mk (offset :: region nonce retained prior []
                finalDummyPool (DynamicFinalInit.commitmentPool commitmentAt)
                (tail.eraseIdx 283)) outcomes (cost + 4)) = some final := by
            simpa only [Nat.add_assoc] using accepted
          rw [generated_signed_comparison_ops] at comparisonRun
          obtain ⟨afterRoll, rollStep, _, _rest⟩ :=
            FirstAcceptedOrigin.run_cons_success hashes .roll
              [.push (preimageIndex firstK), .roll, .hash160, .equalverify]
              (State.mk (offset :: region nonce retained prior []
                finalDummyPool (DynamicFinalInit.commitmentPool commitmentAt)
                (tail.eraseIdx 283)) outcomes (cost + 4))
              final comparisonRun
          obtain ⟨index, parsedOffset, nonnegative⟩ :=
            FinalSignedAccepted.accepted_roll_parses_nonnegative hashes
              offset (region nonce retained prior [] finalDummyPool
                (DynamicFinalInit.commitmentPool commitmentAt)
                (tail.eraseIdx 283)) outcomes (cost + 4) afterRoll rollStep
          have boundInt := signed_cap_add_index_bound firstK retained offset
            source operand index retainedEncoded retainedParsed offsetEncoded
            parsedOffset
          have indexEq : index = Int.ofNat index.toNat :=
            Int.eq_natCast_toNat.mpr nonnegative
          have indexBound : index.toNat ≤ 303 := by
            rw [indexEq] at boundInt
            simpa [firstK] using Int.ofNat_le.mp boundInt
          have parsedNat : ByteIndex.parseScriptNum offset =
              some (Int.ofNat index.toNat) := by
            rw [← indexEq]
            exact parsedOffset
          have comparisonAccepted : run hashes (signedComparisonOps firstK)
              (State.mk (offset :: region nonce retained prior []
                finalDummyPool (DynamicFinalInit.commitmentPool commitmentAt)
                (tail.eraseIdx 283)) outcomes (cost + 4)) = some final := by
            rw [generated_signed_comparison_ops]
            exact comparisonRun
          obtain ⟨opening, nonceHit | commitmentHit⟩ :=
            accepted_comparison_nonce_or_original_position hashes
              commitmentAt (List.finRange 150) firstK nonce retained prior
              offset [] finalDummyPool
              (DynamicFinalInit.commitmentPool commitmentAt)
              (tail.eraseIdx 283)
              (DynamicFinalInit.initial_pool_shape commitmentAt width)
              (DynamicFinalInit.initial_alignment commitmentAt)
              (ByteIndexSign.parsed_bytes_are_short retained operand
                retainedParsed) priorWrong index.toNat parsedNat
              (by simpa using indexBound) outcomes (cost + 4) final
              comparisonAccepted
          · exact ⟨opening, Or.inl nonceHit⟩
          · obtain ⟨id, j, within, _index, idAt, hit⟩ := commitmentHit
            have source :
                (DynamicFinalInit.commitmentPool commitmentAt)[j]? =
                  some (commitmentAt id) := by
              change ((List.finRange 150).map commitmentAt)[j]? =
                some (commitmentAt id)
              rw [List.getElem?_map, idAt]
              rfl
            exact ⟨opening, Or.inr ⟨id, j, within, idAt, source, hit⟩⟩

end QSB.DynamicSignedSource
